"""Four isolated journals, real network partitions, rollback and disaster recovery."""
from __future__ import annotations

from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from contextlib import ExitStack
import copy
import json
import hashlib
import os
from pathlib import Path
import shutil
import signal
import socket
import socketserver
import ssl
import subprocess
import sys
import tempfile
import threading

from anchor import Client as AnchorClient
from anchored_exercise import backup, connection, restore, snapshot_rows, stop, stopped_at
from client import exchange
from crypto import app_private, canonical, create_pki, digest, sign
from exercise import HERE, ROOT, require
from quorum import Client, membership, verify_certificate
from verify import verify_disclosure


def policy(denied):
    return "(version 1)(allow default)" + "".join("(deny file-read* file-write* (subpath " + json.dumps(str(path.resolve())) + "))" for path in denied)


def sandbox(command, denied):
    return ["/usr/bin/sandbox-exec","-p",policy(denied),*command]


def isolation(label, own, denied, box):
    probe = """import json,sys
own,denied=json.loads(sys.argv[1]),json.loads(sys.argv[2])
with open(own,'rb') as f: assert f.read(1)
results=[]
for path in denied:
 for mode in ('rb','r+b'):
  try:
   with open(path,mode): pass
  except PermissionError: results.append(True)
  else: results.append(False)
assert all(results),results
print(json.dumps({'denied_operations':len(results),'own_read':True}))
"""
    result = subprocess.run(sandbox([sys.executable,"-c",probe,json.dumps(str(own.resolve())),json.dumps([str(path.resolve()) for path in denied])],denied),capture_output=True,text=True)
    require(result.returncode==0,"OS isolation failed: "+label+result.stderr)
    return {"role":label,**json.loads(result.stdout),"policy":digest(policy(denied))}


class Gate:
    def __init__(self, target):
        self.blocked = False
        self.refused = 0
        self.connections = 0
        owner = self

        class Handler(socketserver.BaseRequestHandler):
            def handle(self):
                if owner.blocked:
                    owner.refused += 1
                    return
                owner.connections += 1
                try:
                    upstream = socket.create_connection(("127.0.0.1",target),timeout=5)
                except OSError:
                    return
                def relay(source, destination):
                    try:
                        while data := source.recv(65536):
                            destination.sendall(data)
                    except OSError:
                        pass
                    finally:
                        try: destination.shutdown(socket.SHUT_WR)
                        except OSError: pass
                thread = threading.Thread(target=relay,args=(upstream,self.request),daemon=True)
                thread.start()
                relay(self.request,upstream)
                thread.join(timeout=5)
                upstream.close()

        class Server(socketserver.ThreadingTCPServer):
            allow_reuse_address = True
            daemon_threads = True
        self.server = Server(("127.0.0.1",0),Handler)
        self.port = self.server.server_address[1]
        self.thread = threading.Thread(target=self.server.serve_forever,kwargs={"poll_interval":0.05},daemon=True)
        self.thread.start()

    def close(self):
        self.server.shutdown()
        self.server.server_close()
        self.thread.join()


def launch(role, config, log, denied, *, initialize=False, recover=False, phase=None, marker=None):
    command = [sys.executable,str(HERE / ("quorum_fault.py" if phase else role+".py"))]
    if phase:
        command += [phase,str(marker)]
    command += [str(config)]
    if initialize: command += ["--initialize"]
    if recover: command += ["--recover-from-anchor"]
    error = log.open("a")
    process = subprocess.Popen(sandbox(command,denied),stdout=subprocess.PIPE,stderr=error,text=True,start_new_session=True)
    line = process.stdout.readline()
    if not line:
        process.wait(timeout=10)
        error.close()
        raise RuntimeError("STARTUP_REJECTED: "+log.read_text()[-1500:])
    return process,json.loads(line)["port"],error


def rejected(config, box, name, code, denied):
    result = subprocess.run(sandbox([sys.executable,str(HERE / "service.py"),str(config)],denied),capture_output=True,text=True,timeout=45)
    (box / (name+".log")).write_text(result.stderr)
    require(result.returncode!=0 and not result.stdout and code in result.stderr,"incorrect startup: "+name+result.stderr[-1000:])


def run(box, source, count=256):
    require(not box.exists(),"refuse to overwrite prior actual run")
    box.mkdir(parents=True)
    tests, snapshots, observations, isolations = [],[],[],[]
    jobs, gates = {},{}
    with tempfile.TemporaryDirectory(prefix="public-quorum-credentials-") as temporary, ExitStack() as cleanup:
        def close():
            for job in jobs.values(): stop(job)
            for gate in gates.values(): gate.close()
        cleanup.callback(close)
        temporary = Path(temporary).resolve()
        pki = temporary / "audit"
        registry = create_pki(pki)
        configs, paths, endpoint_paths, databases, private = {},{},{},{},{}
        for name in ("a","b","c","d"):
            complete = temporary / (name+"-pki")
            node_registry = create_pki(complete,anchor=True)
            private[name] = temporary / (name+"-anchor")
            private[name].mkdir()
            shutil.move(str(complete / "anchor"),private[name] / "anchor")
            shutil.copyfile(complete / "ca.pem",private[name] / "ca.pem")
            endpoint_paths[name] = temporary / (name+"-writer")
            endpoint_paths[name].mkdir()
            shutil.move(str(complete / "server"),endpoint_paths[name] / "server")
            shutil.copyfile(complete / "ca.pem",endpoint_paths[name] / "ca.pem")
            shutil.rmtree(complete)
            databases[name] = box / (name+"-external-domain")
            databases[name].mkdir()
            configs[name] = {"pki":str(private[name]),"registry":{**registry,"anchor":node_registry["anchor"]},
                             "transport_writer":node_registry["server"],"database":str(databases[name] / "journal.sqlite"),
                             "streams":{world:{"source":source,"writer":registry["server"]} for world in ("one","two")}}
            paths[name] = private[name] / "config.json"
        trust = {"version":1,"threshold":3,"members":{name:config["registry"]["anchor"] for name,config in configs.items()}}
        cluster = membership(trust)
        keypins = {"audit":registry,"trust":trust,"transport":{name:config["transport_writer"] for name,config in configs.items()}}
        keypins["tls_roots"] = {name:(private[name] / "ca.pem").read_text() for name in private}
        (box / "public-keys.json").write_text(json.dumps(keypins,indent=2))
        for label in ("auditor1","auditor2","rotated2"):
            (pki / label / "anchors.json").write_text(json.dumps(trust))
        local_dirs = [box / (world+"-audit-domain") for world in ("one","two")]
        for directory in local_dirs: directory.mkdir()
        node_denied = {name:[pki,*endpoint_paths.values(),*local_dirs,*[private[key] for key in private if key!=name],*[databases[key] for key in databases if key!=name]] for name in configs}
        service_denied = [*private.values(),*databases.values()]
        for name,config in configs.items():
            config["cluster"] = cluster
            paths[name].write_text(json.dumps(config))
            jobs[name] = launch("anchor",paths[name],box / (name+"-anchor.log"),node_denied[name],initialize=True)
            config["port"] = jobs[name][1]
            paths[name].write_text(json.dumps(config))
            gates[name] = Gate(jobs[name][1])
        for name in configs:
            # These are the same OS policies applied to the actual daemons.
            forbidden = [pki / "server/app.key",*[private[key] / "anchor/app.key" for key in private if key!=name],
                         *[databases[key] / "journal.sqlite" for key in databases if key!=name]]
            isolations.append(isolation(name,private[name] / "anchor/app.key",forbidden,box))
        isolations.append(isolation("service",pki / "server/app.key",[private[name] / "anchor/app.key" for name in private]+[databases[name] / "journal.sqlite" for name in databases],box))
        (box / "isolation.json").write_text(json.dumps(isolations,indent=2))
        tests.append("independent_CA_keys_transport_and_OS_read_write_isolation")
        endpoints = {name:{"host":"127.0.0.1","hostname":"anchor.local","port":gates[name].port,"pki":str(endpoint_paths[name])} for name in configs}
        try:
            for world in ("one","two"):
                database = box / (world+"-audit-domain/ledger.sqlite")
                config = {"pki":str(pki),"source":source,"stream":world,"registry":registry,"lean":str(ROOT / "Lean"),
                          "database":str(database),"backend_error":str(box / "source.log"),
                          "backend":["lake","env","lean","--trust=0","-DwarningAsError=true","-DElab.async=false","-j1","--run","scripts/verification/public-scoped-audit-source.lean","private-"+world],
                          "anchors":{"trust":trust,"endpoints":endpoints}}
                path = temporary / (world+"-service.json")
                path.write_text(json.dumps(config))
                def heal_other_streams():
                    for prior in ("one",) if world=="two" else ():
                        Client({**config,"stream":prior}).head()
                for label in ("auditor1","auditor2","rotated2"):
                    (pki / label / "stream.json").write_text(json.dumps(world))
                job = launch("service",path,box / "service.log",service_denied)
                records, requests = [],[]
                snapshot = box / (world+"-snapshot.sqlite")
                try:
                    for index in range(count):
                        label = "auditor1" if index<2 else "auditor2" if index<4 else "rotated2"
                        query = {"slots":63 if index<4 else (1 << (index%6)) | (1 << ((index+1)%6)),"fields":1 if index==2 else (index%3)+1}
                        if index in (0,1,3,7): query={"slots":63,"fields":3}
                        if index==4: query={"slots":1,"fields":2}
                        if index==5: query={"slots":62,"fields":3}
                        if index==6: query={"slots":0,"fields":3}
                        call = lambda **extra:exchange(pki / label,job[1],source,query,**extra)
                        if index==0:
                            other_path=temporary / (world+"-second-writer.json")
                            other_path.write_text(json.dumps({**config,"database":str(database)+".other"}))
                            rejected(other_path,box,world+"-second-writer","QUORUM_WRITER_ALREADY_ACTIVE",service_denied)
                            tests.append(world+"_same_credential_second_writer_is_fenced")
                        if index in (4,6):
                            phase = "partial" if index==4 else "after-quorum"
                            stop(job)
                            marker = box / (world+"-"+phase)
                            job = launch("service",path,box / "service.log",service_denied,phase=phase,marker=marker)
                            with ThreadPoolExecutor(max_workers=1) as pool:
                                pending = pool.submit(call)
                                stopped_at(marker)
                                stop(job,crash=True)
                                unknown = pending.result(timeout=20)
                            require(unknown["error"]=="OUTCOME_UNKNOWN","crash invented a final outcome")
                            if index==4:
                                shutil.copyfile(str(database)+".pending.json",box / (world+"-pending-intent.json"))
                                stop(jobs["a"])
                                for suffix in ("","-wal","-shm"):
                                    Path(str(databases["a"] / "journal.sqlite")+suffix).unlink(missing_ok=True)
                                jobs["a"]=launch("anchor",paths["a"],box / "a-anchor.log",node_denied["a"],initialize=True)
                                heal_other_streams()
                                tests.append(world+"_pending_intent_survives_only_partial_signer_loss")
                            rejected(path,box,world+"-"+phase+"-needs-recovery","ANCHOR_RECOVERY_REQUIRED",service_denied)
                            job = launch("service",path,box / "service.log",service_denied,recover=True)
                            answer = call(lookup=unknown["request"])
                            tests.append(world+"_"+phase+"_original_result_recovered_once")
                        elif index==5:
                            stop(job)
                            marker = box / (world+"-partition-during-append")
                            job = launch("service",path,box / "service.log",service_denied,phase="before-append",marker=marker)
                            before = snapshot_rows(database)
                            with ThreadPoolExecutor(max_workers=1) as pool:
                                pending = pool.submit(call)
                                stopped_at(marker)
                                gates["c"].blocked = gates["d"].blocked = True
                                os.kill(job[0].pid,signal.SIGCONT)
                                unknown = pending.result(timeout=30)
                            require(unknown["error"]=="ANCHOR_RECONCILIATION_REQUIRED" and snapshot_rows(database)==before,"partial quorum returned success or local commit")
                            stop(job)
                            gates["c"].blocked = gates["d"].blocked = False
                            job = launch("service",path,box / "service.log",service_denied,recover=True)
                            answer = call(lookup=unknown["request"])
                            tests.append(world+"_two_ack_partition_is_unknown_then_exact_recovery")
                        else:
                            if index==8:
                                gates["d"].blocked=True
                            if index==10:
                                before = snapshot_rows(database)
                                gates["c"].blocked=True
                                refused = call()
                                require(refused["error"]=="QUORUM_UNAVAILABLE" and snapshot_rows(database)==before,"two-node minority wrote")
                                stop(job)
                                rejected(path,box,world+"-minority-start","QUORUM_UNAVAILABLE",service_denied)
                                gates["c"].blocked=False
                                job = launch("service",path,box / "service.log",service_denied)
                                tests.append(world+"_two_two_partition_has_no_write_or_false_genesis")
                            if index==12:
                                gates["d"].blocked=False
                                Client(config).head()
                                tests.append(world+"_three_node_majority_progress_and_rejoin_catchup")
                            if index==24:
                                stop(jobs["d"])
                                jobs["d"]=launch("anchor",paths["d"],box / "d-anchor.log",node_denied["d"],phase="bad-anchor",marker=box / (world+"-bad-signature.json"))
                            if index==25:
                                stop(jobs["d"])
                                jobs["d"]=launch("anchor",paths["d"],box / "d-anchor.log",node_denied["d"])
                                Client(config).head()
                                tests.append(world+"_invalid_member_signature_excluded_three_valid_nodes_continue")
                            if index in (16,128,240):
                                stop(job)
                                before=snapshot_rows(database)
                                restore(snapshot,database)
                                rejected(path,box,world+f"-whole-rollback-{index}","ANCHOR_RECOVERY_REQUIRED",service_denied)
                                job=launch("service",path,box / "service.log",service_denied,recover=True)
                                require(snapshot_rows(database)==before,"quorum recovery rewrote original events")
                                require(exchange(pki / "auditor2",job[1],source,query)["error"]=="KEY_REVOKED","old snapshot resurrected old key")
                                tests.append(world+f"_whole_local_snapshot_{index}_exact_recovery")
                            if index in (32,160):
                                stop(jobs["d"])
                                before=snapshot_rows(database)
                                archive = box / (world+"-d-old.sqlite")
                                if index==32:
                                    backup(databases["d"] / "journal.sqlite",archive)
                                    # Restore the complete earlier external journal,
                                    # including its binding and signed receipts.
                                    restore(box / (world+"-anchor-old.sqlite"),databases["d"] / "journal.sqlite")
                                    tests.append(world+"_one_external_full_snapshot_rollback_healed")
                                else:
                                    for suffix in ("","-wal","-shm"):
                                        Path(str(databases["d"] / "journal.sqlite")+suffix).unlink(missing_ok=True)
                                    result=subprocess.run(sandbox([sys.executable,str(HERE / "anchor.py"),str(paths["d"])],node_denied["d"]),capture_output=True,text=True)
                                    require(result.returncode!=0 and "ANCHOR_STORAGE_MISSING" in result.stderr,"lost node silently recreated genesis")
                                    (box / (world+"-lost-node.log")).write_text(result.stderr)
                                    tests.append(world+"_lost_external_database_explicit_rebuild_from_surviving_quorum")
                                jobs["d"]=launch("anchor",paths["d"],box / "d-anchor.log",node_denied["d"],initialize=index==160)
                                if index==160: heal_other_streams()
                                Client(config).head()
                                require(snapshot_rows(database)==before,"external repair changed local history")
                            if index==64:
                                receipts=[]
                                original=json.loads(snapshot_rows(database)[-1][3])
                                seq,previous=snapshot_rows(database)[-1][:2]
                                fork=copy.deepcopy(original["body"])
                                fork["record"]["query"]={"slots":1,"fields":3}
                                fork["request"]["body"]["query"]=fork["record"]["query"]
                                fork["request"]=sign(app_private(pki / label),"audit",fork["request"]["body"])
                                forged=sign(app_private(pki / "server"),"ledger",fork)
                                # A rolled-back signer can equivocate at its old
                                # slot; the three surviving original signers refuse.
                                stop(jobs["d"])
                                restore(box / (world+"-fork-prefix.sqlite"),databases["d"] / "journal.sqlite")
                                jobs["d"]=launch("anchor",paths["d"],box / "d-anchor.log",node_denied["d"])
                                for name,node in Client(config).nodes.items():
                                    try: receipts.append({"member":name,"receipt":node.append(seq,previous,forged)})
                                    except ValueError as error: require(str(error)=="ANCHOR_FORK","wrong fork refusal")
                                require([vote["member"] for vote in receipts]==["d"],"fork gained a quorum")
                                (box / (world+"-equivocation.json")).write_text(json.dumps({"original":original,"fork":forged,"votes":receipts}))
                                try: Client(config).head()
                                except ValueError as error: require(str(error)=="QUORUM_FORK","fork became history")
                                else: raise RuntimeError("divergent anchor was accepted")
                                stop(jobs["d"])
                                restore(box / (world+"-d-before-fork.sqlite"),databases["d"] / "journal.sqlite")
                                jobs["d"]=launch("anchor",paths["d"],box / "d-anchor.log",node_denied["d"])
                                Client(config).head()
                                tests.append(world+"_one_equivocating_signer_cannot_form_fork_quorum")
                            answer=call()
                        require("response" in answer,str(answer))
                        result=answer["response"]
                        records.append(result["event"]["record"])
                        requests.append(result["event"]["request"])
                        require(answer["tls"]=="TLSv1.3","TLS downgrade")
                        if index==0: backup(database,snapshot)
                        if index==3:
                            rotated=exchange(pki / "auditor2",job[1],source,query,rotation=registry["rotated2"],new_profile=pki / "rotated2")
                            require("response" in rotated,"key rotation failed")
                            for name in configs:
                                with connection(databases[name] / "journal.sqlite") as db: db.execute("PRAGMA wal_checkpoint(FULL)")
                            backup(databases["d"] / "journal.sqlite",box / (world+"-anchor-old.sqlite"))
                        if index==62:
                            backup(databases["d"] / "journal.sqlite",box / (world+"-fork-prefix.sqlite"))
                        if index==63:
                            backup(databases["d"] / "journal.sqlite",box / (world+"-d-before-fork.sqlite"))
                        if index==20:
                            point=result["anchor"]["body"]
                            binding=dict(source=source,stream=world,seq=point["seq"],head=point["head"],previous=point["previous"],message=result["ledger"])
                            malformed=copy.deepcopy(result["anchor"])
                            malformed["votes"]=[malformed["votes"][0]]*3
                            try: verify_certificate(trust,malformed,**binding)
                            except ValueError: pass
                            else: raise RuntimeError("one identity counted three times")
                            wrong=copy.deepcopy(trust)
                            wrong["threshold"]=2
                            try: membership(wrong)
                            except ValueError: pass
                            else: raise RuntimeError("threshold downgrade")
                            tests.append(world+"_duplicate_vote_and_threshold_downgrade_rejected")
                            wrong=copy.deepcopy(config)
                            wrong["anchors"]["endpoints"]["b"]["pki"]=endpoints["a"]["pki"]
                            try: Client(wrong)
                            except ValueError as error: require(str(error)=="QUORUM_SHARED_TLS_ROOT","wrong shared-root error")
                            else: raise RuntimeError("same root accepted as independent CA")
                            confused={**endpoints["b"],"pki":endpoints["a"]["pki"],"identity":trust["members"]["b"],"cluster":cluster}
                            try: AnchorClient({**config,"anchor":confused}).head()
                            except ssl.SSLError: pass
                            else: raise RuntimeError("one node credential authenticated to a different root")
                            tests.append(world+"_shared_TLS_root_and_cross_node_credentials_refused")
                    Client(config).head()
                    statuses=Counter(record["access"] for record in records)
                    require(statuses=={"admitted":7,"unauthorized":1,"unfunded":7,"expired":count-15},"actual source outcome changed")
                    require(sum(int(record["labor"]) for record in records)==14,"recovery charged twice")
                    require(verify_disclosure(records[3])["lifecycle"]==["verified"]*6,"original six-slot service missing")
                    require(verify_disclosure(records[2])["lifecycle"]==["insufficient"]*6,"missing evidence became violation")
                    (box / (world+"-observations.json")).write_text(json.dumps(records))
                    (box / (world+"-final.json")).write_text(json.dumps({"count":len(snapshot_rows(database)),"head":snapshot_rows(database)[-1][2],"statuses":statuses,"labor":14}))
                    observations.append(records)
                    print(f"QUORUM ACTUAL {world} PASS: {count} original source requests; 4 journals; 3-signature commits",flush=True)
                finally:
                    stop(job)
        finally:
            (box / "network-gates.json").write_text(json.dumps({name:{"refused":gate.refused,"connections":gate.connections} for name,gate in gates.items()}))
    require(observations[0]==observations[1],"private histories disclosed different cumulative views")
    result={"source":source,"cluster":cluster,"histories":2,"requests_each":count,"tests":tests,"query_labor_each":14}
    (box / "receipt.json").write_text(json.dumps(result,indent=2))
    print("FOUR INDEPENDENT ANCHORS ACTUAL PASS: partition, rollback, single-node loss, exact recovery, pooled disclosure",flush=True)
    return result


if __name__=="__main__":
    run(Path(sys.argv[1]),sys.argv[2],int(sys.argv[3]) if len(sys.argv)>3 else 256)
