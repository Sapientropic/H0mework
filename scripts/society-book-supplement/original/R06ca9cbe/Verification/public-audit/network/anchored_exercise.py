"""Actual rollback/crash attacks against independently stored monotonic anchors."""
from __future__ import annotations

from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
import copy
import json
import os
from pathlib import Path
import secrets
import shutil
import signal
import sqlite3
import subprocess
import sys
import tempfile
import time

from anchor import Client as AnchorClient, ledger_hash, public_key, verify_commit
from client import check_result, exchange
from crypto import app_private, canonical, connect, create_pki, digest, receive, send, sign, verify
from exercise import ROOT, HERE, Worker, replay, require
from verify import verify_disclosure


@contextmanager
def connection(path):
    db = sqlite3.connect(path)
    try:
        with db:
            yield db
    finally:
        db.close()


def launch(role, config, log, *, initialize=False, recover=False, phase=None, marker=None):
    command = [sys.executable,str(HERE / ("fault_service.py" if phase else role + ".py"))]
    if phase:
        command += ["audit" if role == "service" else role,phase,str(marker)]
    command += [str(config)]
    if initialize:
        command.append("--initialize")
    if recover:
        command.append("--recover-from-anchor")
    error = log.open("a")
    process = subprocess.Popen(command,stdout=subprocess.PIPE,stderr=error,text=True,start_new_session=True)
    line = process.stdout.readline()
    if not line:
        process.wait(timeout=10)
        error.close()
        raise RuntimeError("STARTUP_REJECTED: " + log.read_text()[-1200:])
    return process,json.loads(line)["port"],error


def stop(job, *, crash=False):
    process,_,error = job
    if process.poll() is None:
        if crash:
            os.killpg(process.pid,signal.SIGKILL)
        else:
            process.terminate()
        try:
            process.wait(timeout=15)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid,signal.SIGKILL)
            process.wait(timeout=5)
    error.close()


def stopped_at(marker):
    deadline = time.monotonic() + 60
    while not marker.exists():
        if time.monotonic() > deadline:
            raise RuntimeError("fault boundary was not reached: " + str(marker))
        time.sleep(0.02)


def backup(source, destination):
    with connection(source) as original,connection(destination) as archive:
        original.backup(archive)


def restore(snapshot, destination):
    for suffix in ("-wal","-shm"):
        Path(str(destination) + suffix).unlink(missing_ok=True)
    shutil.copyfile(snapshot,destination)


def rejected_start(config, box, name, code):
    result = subprocess.run([sys.executable,str(HERE / "service.py"),str(config)],capture_output=True,text=True,timeout=30)
    (box / (name + ".log")).write_text(result.stderr)
    require(result.returncode != 0 and not result.stdout and code in result.stderr,"bad snapshot served: " + name)


def snapshot_rows(database):
    with connection(database) as db:
        return db.execute("SELECT id,previous,hash,message FROM events ORDER BY id").fetchall()


def verify_external(local, external, registry, source, stream):
    """Public keys only: compare both literal stores, not a producer PASS field."""
    with connection(external) as db:
        rows = db.execute("SELECT seq,previous,hash,message,receipt FROM entries WHERE stream=? ORDER BY seq",(stream,)).fetchall()
    local_rows = snapshot_rows(local)
    require([row[:4] for row in rows] == local_rows,"local/external literal journal differs")
    previous = "0" * 64
    for expected,(seq,before,head,text,receipt) in enumerate(rows,1):
        message = json.loads(text)
        event = verify(public_key(registry["server"]),"ledger",message)
        require(seq == expected and before == previous and ledger_hash(before,message) == head,"external chain")
        require(event["source"] == source and event["stream"] == stream,"external namespace")
        verify_commit(registry["anchor"],json.loads(receipt),source=source,stream=stream,seq=seq,head=head,previous=before,message=message)
        previous = head
    return {"count":len(rows),"head":previous}


def capture_head(config, path):
    endpoint = config["anchor"]
    body = dict(op="head",source=config["source"],stream=config["stream"],nonce=secrets.token_hex(32),expires=time.time()+30)
    message = sign(app_private(Path(config["pki"]) / "server"),"anchor-request",body)
    with connect(Path(config["pki"]) / "server",endpoint["port"],hostname=endpoint["hostname"],host=endpoint["host"]) as connection:
        send(connection,message)
        response = receive(connection)
    value = verify(public_key(endpoint["identity"]),"anchor-response",response)
    require(value["request"] == digest(message),"captured head response")
    path.write_text(json.dumps(response))


def run(box, source, count=256):
    require(not box.exists(),"refuse to mix an existing attack run")
    box.mkdir(parents=True)
    external = box / "external-domain"
    external.mkdir()
    tests, all_records = [],[]
    with tempfile.TemporaryDirectory(prefix="public-anchor-credentials-") as temporary:
        pki = Path(temporary) / "audit"
        registry = create_pki(pki,anchor=True)
        anchor_pki = Path(temporary) / "external"
        anchor_pki.mkdir()
        shutil.move(str(pki / "anchor"),anchor_pki / "anchor")
        shutil.copyfile(pki / "ca.pem",anchor_pki / "ca.pem")
        (box / "public-keys.json").write_text(json.dumps(registry,indent=2))
        anchor_config = {"pki":str(anchor_pki),"registry":registry,"database":str(external / "journal.sqlite"),
                         "streams":{world:{"source":source,"writer":registry["server"]} for world in ("one","two")}}
        anchor_path = Path(temporary) / "anchor.json"
        anchor_path.write_text(json.dumps(anchor_config))
        anchor_job = launch("anchor",anchor_path,box / "anchor.log",initialize=True)
        anchor_config["port"] = anchor_job[1]
        anchor_path.write_text(json.dumps(anchor_config))
        try:
            for world in ("one","two"):
                local = box / (world + "-audit-domain")
                local.mkdir()
                database = local / "ledger.sqlite"
                config = {"pki":str(pki),"source":source,"stream":world,"registry":registry,"lean":str(ROOT / "Lean"),
                          "database":str(database),"backend_error":str(box / "source.log"),
                          "backend":["lake","env","lean","--trust=0","-DwarningAsError=true","-DElab.async=false","-j1","--run","scripts/verification/public-scoped-audit-source.lean","private-"+world],
                          "anchor":{"host":"127.0.0.1","hostname":"anchor.local","port":anchor_job[1],"identity":registry["anchor"]}}
                config_path = Path(temporary) / (world + ".json")
                config_path.write_text(json.dumps(config))
                for label in ("auditor1","auditor2","rotated2"):
                    (pki / label / "stream.json").write_text(json.dumps(world))
                job = launch("service",config_path,box / "service.log")
                workers = {label:Worker(pki / label) for label in ("auditor1","auditor2","rotated2")}
                records, requests = [],[]
                first_snapshot = local / "first-snapshot.sqlite"
                rotated_snapshot = local / "rotated-snapshot.sqlite"
                stale_reply = box / (world + "-old-head.json")
                capture_head(config,stale_reply)
                try:
                    for index in range(count):
                        label = "auditor1" if index < 2 else "auditor2" if index < 4 else "rotated2"
                        query = {"slots":63 if index < 4 else (1 << (index % 6)) | (1 << ((index+1)%6)),"fields":1 if index == 2 else (index % 3)+1}
                        if index in (0,1,3,7):
                            query = {"slots":63,"fields":3}
                        if index == 4:
                            query = {"slots":1,"fields":2}
                        if index == 5:
                            query = {"slots":62,"fields":3}
                        if index == 6:
                            query = {"slots":0,"fields":3}

                        if index == 12:
                            before = snapshot_rows(database)
                            bad = workers[label].call({"port":job[1],"source":source,"stream":"two" if world=="one" else "one","query":query})
                            require(bad["error"]=="CLIENT_STREAM_BINDING" and snapshot_rows(database)==before,"another live stream was accepted")
                            tests.append(world+"_caller_pinned_stream_rejects_substitution")
                        if index == 160:
                            stop(job)
                            before = snapshot_rows(database)
                            with connection(database) as db:
                                db.execute("DELETE FROM used WHERE rowid=(SELECT min(rowid) FROM used)")
                            rejected_start(config_path,box,world+"-damaged-replay-table","RESTORE_STATE_TABLES")
                            job = launch("service",config_path,box / "service.log",recover=True)
                            require(snapshot_rows(database)==before,"corrupt-table repair changed original events")
                            tests.append(world+"_damaged_local_state_rebuilt_from_external_events")
                        if index in (16,128,240):
                            stop(job)
                            current_rows = snapshot_rows(database)
                            snapshot = first_snapshot if index != 128 else rotated_snapshot
                            restore(snapshot,database)
                            rejected_start(config_path,box,world+f"-rollback-{index}","ANCHOR_RECOVERY_REQUIRED")
                            job = launch("service",config_path,box / "service.log",recover=True)
                            require(snapshot_rows(database) == current_rows,"rollback recovery rewrote original events")
                            require(workers["auditor2"].call({"port":job[1],"source":source})["error"] == "KEY_REVOKED","rollback resurrected old key")
                            bad = workers["auditor1"].call({"port":job[1],"source":source,"replay":requests[0]})
                            require("error" in bad,"rollback resurrected old request")
                            tests.append(world+f"_whole_snapshot_{index}_refused_and_exactly_recovered")

                        if index == 64:
                            stop(job)
                            before_fork = snapshot_rows(database)
                            row = before_fork[-1]
                            message = json.loads(row[3])
                            event = message["body"]
                            event["record"]["query"] = {"slots":1,"fields":3}
                            event["request"]["body"]["query"] = event["record"]["query"]
                            event["request"] = sign(app_private(pki / "rotated2"),"audit",event["request"]["body"])
                            forged = sign(app_private(pki / "server"),"ledger",event)
                            hashed = ledger_hash(row[1],forged)
                            with connection(database) as db:
                                db.execute("UPDATE events SET hash=?,message=? WHERE id=?",(hashed,canonical(forged).decode(),row[0]))
                            rejected_start(config_path,box,world+"-valid-local-fork","ANCHOR_RECOVERY_REQUIRED")
                            try:
                                AnchorClient(config).append(row[0],row[1],forged)
                            except ValueError as error:
                                require(str(error)=="ANCHOR_FORK","wrong fork disposition")
                            else:
                                raise RuntimeError("external anchor accepted a signed cross-slot fork")
                            job = launch("service",config_path,box / "service.log",recover=True)
                            require(snapshot_rows(database)==before_fork,"fork recovery altered accepted history")
                            tests.append(world+"_signed_cross_slot_fork_rejected")

                        if index in (4,5,6):
                            phase = {4:"before-anchor",5:"after-anchor",6:"after-local-commit"}[index]
                            stop(job)
                            marker = box / (world+"-"+phase)
                            job = launch("service",config_path,box / "service.log",phase=phase,marker=marker)
                            before = snapshot_rows(database)
                            with ThreadPoolExecutor(max_workers=1) as pool:
                                pending = pool.submit(workers[label].call,{"port":job[1],"source":source,"query":query})
                                stopped_at(marker)
                                stop(job,crash=True)
                                unknown = pending.result(timeout=15)
                            require(unknown["error"]=="OUTCOME_UNKNOWN","crash reported a false final outcome")
                            if index == 5:
                                rejected_start(config_path,box,world+"-anchor-ahead","ANCHOR_RECOVERY_REQUIRED")
                            job = launch("service",config_path,box / "service.log",recover=index==5)
                            recovered = workers[label].call({"port":job[1],"source":source,"lookup":unknown["request"]})
                            if index == 4:
                                require(recovered["error"]=="REQUEST_NOT_COMMITTED" and snapshot_rows(database)==before,"unanchored crash consumed request")
                                answer = workers[label].call({"port":job[1],"source":source,"query":query})
                            else:
                                require("response" in recovered,"committed result was not recoverable")
                                answer = recovered
                            tests.append(world+"_"+phase+"_crash_recovered_once")
                        elif index == 8:
                            with connection(database) as db:
                                db.executescript("CREATE TABLE commit_parent(id PRIMARY KEY); CREATE TABLE commit_guard(id REFERENCES commit_parent(id) DEFERRABLE INITIALLY DEFERRED); CREATE TRIGGER commit_fault AFTER INSERT ON events BEGIN INSERT INTO commit_guard VALUES(1); END;")
                            failed = workers[label].call({"port":job[1],"source":source,"query":query})
                            require(failed["error"]=="ANCHOR_COMMITTED_RECOVERY_REQUIRED","lost external commit on SQLite failure")
                            with connection(database) as db:
                                db.executescript("DROP TRIGGER commit_fault; DROP TABLE commit_guard; DROP TABLE commit_parent;")
                            stop(job)
                            job = launch("service",config_path,box / "service.log",recover=True)
                            answer = workers[label].call({"port":job[1],"source":source,"lookup":failed["request"]})
                            tests.append(world+"_sqlite_failure_keeps_external_commit")
                        elif index == 10:
                            stop(anchor_job)
                            marker = box / (world+"-anchor-ack-lost")
                            anchor_job = launch("anchor",anchor_path,box / "anchor.log",phase="anchor-ack-lost",marker=marker)
                            with ThreadPoolExecutor(max_workers=1) as pool:
                                pending = pool.submit(workers[label].call,{"port":job[1],"source":source,"query":query})
                                stopped_at(marker)
                                stop(anchor_job,crash=True)
                                failed = pending.result(timeout=15)
                            require(failed["error"]=="ANCHOR_RECONCILIATION_REQUIRED","lost anchor acknowledgement looked uncommitted")
                            anchor_job = launch("anchor",anchor_path,box / "anchor.log")
                            stop(job)
                            job = launch("service",config_path,box / "service.log",recover=True)
                            answer = workers[label].call({"port":job[1],"source":source,"lookup":failed["request"]})
                            tests.append(world+"_lost_anchor_ack_recovered_once")
                        else:
                            if index in (9,20):
                                before = snapshot_rows(database)
                                stop(anchor_job)
                                if index == 20:
                                    anchor_job = launch("anchor",anchor_path,box / "anchor.log",phase="stale-head",marker=stale_reply)
                                failed = workers[label].call({"port":job[1],"source":source,"query":query})
                                require("error" in failed and snapshot_rows(database)==before,"unavailable or stale anchor admitted a request")
                                if index == 20:
                                    require(failed["error"]=="ANCHOR_FRESHNESS","stale signed head was accepted")
                                    stop(anchor_job)
                                anchor_job = launch("anchor",anchor_path,box / "anchor.log")
                                tests.append(world+("_anchor_offline_fail_closed" if index==9 else "_old_signed_head_rejected"))
                            answer = workers[label].call({"port":job[1],"source":source,"query":query})
                        require("response" in answer,str(answer))
                        result = answer["response"]
                        original = result["event"]["request"]
                        records.append(result["event"]["record"])
                        requests.append(original)
                        require(answer["tls"]=="TLSv1.3","transport downgrade")
                        if index == 0:
                            backup(database,first_snapshot)
                        if index == 3:
                            rotated = exchange(pki / "auditor2",job[1],source,query,rotation=registry["rotated2"],new_profile=pki / "rotated2")
                            require("response" in rotated,"actual key rotation failed")
                            backup(database,rotated_snapshot)
                        if index == 32:
                            client = AnchorClient(config)
                            point = result["anchor"]["body"]
                            with ThreadPoolExecutor(max_workers=2) as pool:
                                results = list(pool.map(lambda _:AnchorClient(config).append(point["seq"],point["previous"],result["ledger"]),range(2)))
                            require(results==[result["anchor"]]*2,"idempotent CAS returned different commits")
                            try:
                                client.append(point["seq"]+1,point["head"],json.loads(snapshot_rows(database)[0][3]))
                            except ValueError as error:
                                require(str(error)=="ANCHOR_EVENT_REPLAY","old event was not classified as replay")
                            else:
                                raise RuntimeError("old signed event extended the external journal")
                            tests.append(world+"_concurrent_idempotence_and_old_event_extension_rejected")

                    statuses = Counter(record["access"] for record in records)
                    require(statuses=={"admitted":7,"unauthorized":1,"unfunded":7,"expired":count-15},"source outcomes changed under recovery")
                    require(sum(int(record["labor"]) for record in records)==14,"recovery double charged")
                    require(verify_disclosure(records[3])["lifecycle"]==["verified"]*6,"six-slot delivery lost")
                    require(verify_disclosure(records[2])["lifecycle"]==["insufficient"]*6,"missing evidence became violation")
                    replayed,head = replay(config,registry)
                    require(replayed==records,"recovered source or cumulative disclosure changed")
                    certificate = verify_external(database,external / "journal.sqlite",registry,source,world)
                    require(certificate["count"]==count+1 and certificate["head"]==head,"external final head")
                    (box / (world+"-observations.json")).write_text(json.dumps(records))
                    (box / (world+"-final.json")).write_text(json.dumps({**certificate,"statuses":statuses,"labor":14}))
                    all_records.append(records)
                    print(f"ANCHORED {world} PASS: {count} actual cross-slot requests; {count+1} external commits; rollback/crash recovery",flush=True)
                finally:
                    for worker in workers.values():
                        worker.close()
                    stop(job)
        finally:
            stop(anchor_job)
    require(all_records[0]==all_records[1],"attacks changed pooled private-world observations")
    receipt = {"source":source,"requests_each":count,"histories":2,"tests":tests,"observations_equal":True,
               "rollback_domain":"external process, independent credentials and database", "query_labor_each":14}
    (box / "receipt.json").write_text(json.dumps(receipt,indent=2))
    print("EXTERNAL MONOTONIC ANCHOR PASS: full snapshots, signed forks, crash windows, receipt lookup, long cross-slot disclosure",flush=True)
    return receipt


if __name__ == "__main__":
    run(Path(sys.argv[1]),sys.argv[2],int(sys.argv[3]) if len(sys.argv)>3 else 256)
