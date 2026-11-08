"""Real multi-process TLS exercise and independent source/ledger replay."""
from __future__ import annotations

from collections import Counter
import hashlib
import copy
import json
from pathlib import Path
import socket
import sqlite3
import ssl
import subprocess
import sys
import tempfile
import threading

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

from client import exchange
from crypto import canonical, connect, create_pki, receive, verify
from service import Backend
from verify import verify_disclosure

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


class Worker:
    def __init__(self, profile, *, allow_unanchored=False):
        self.process = subprocess.Popen([sys.executable, str(HERE / "client.py"), str(profile)] + (["--allow-unanchored"] if allow_unanchored else []), stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)

    def call(self, request):
        self.process.stdin.write(json.dumps(request) + "\n")
        self.process.stdin.flush()
        line = self.process.stdout.readline()
        require(bool(line), "auditor exited")
        return json.loads(line)

    def close(self):
        self.process.stdin.close()
        self.process.wait(timeout=10)
        require(self.process.returncode == 0, self.process.stderr.read())


def start_server(config_path, error_path):
    error = open(error_path, "a")
    process = subprocess.Popen([sys.executable, str(HERE / "service.py"), str(config_path)], stdout=subprocess.PIPE, stderr=error, text=True)
    line = process.stdout.readline()
    require(bool(line), "service failed; inspect retained service log")
    return process, json.loads(line)["port"], error


def stop_server(process, error):
    process.terminate()
    process.wait(timeout=15)
    error.close()


def ciphertext_probe(profile, target_port):
    listener = socket.socket()
    listener.bind(("127.0.0.1", 0))
    listener.listen(1)
    proxy_port = listener.getsockname()[1]
    modified = []

    def proxy():
        client, _ = listener.accept()
        upstream = socket.create_connection(("127.0.0.1", target_port), timeout=5)
        def back():
            try:
                while data := upstream.recv(65536):
                    client.sendall(data)
            except OSError:
                pass
            finally:
                client.close()
        thread = threading.Thread(target=back, daemon=True)
        thread.start()
        try:
            while True:
                header = bytearray()
                while len(header) < 5:
                    piece = client.recv(5 - len(header))
                    if not piece:
                        return
                    header.extend(piece)
                length = int.from_bytes(header[3:5], "big")
                body = bytearray()
                while len(body) < length:
                    part = client.recv(length - len(body))
                    if not part:
                        return
                    body.extend(part)
                if header[0] == 23 and not modified:
                    body[-1] ^= 1
                    modified.append(True)
                upstream.sendall(header + body)
        except OSError:
            pass
        finally:
            upstream.close()
            client.close()
            listener.close()
    thread = threading.Thread(target=proxy, daemon=True)
    thread.start()
    rejected = False
    try:
        with connect(profile, proxy_port) as connection:
            receive(connection)
    except (ssl.SSLError, OSError, EOFError):
        rejected = True
    thread.join(timeout=10)
    require(modified and rejected, "modified TLS ciphertext was accepted")


def replay(config, registry):
    database = sqlite3.connect(config["database"])
    server_key = Ed25519PublicKey.from_public_bytes(bytes.fromhex(registry["server"]["app"]))
    keys = {registry[name]["actor"]: registry[name] for name in ("auditor1", "auditor2")}
    previous = "0" * 64
    sequences, nonces, requests = {}, set(), set()
    observations = []
    # The uniform Lean theorem allows this consumer to use the public canonical
    # branch; it never receives the producer's private source input.
    canonical_config = {**config, "backend": config["backend"][:-1] + ["private-one"]}
    backend = Backend(canonical_config)
    try:
        for before, hashed, text in database.execute("SELECT previous,hash,message FROM events ORDER BY id"):
            message = json.loads(text)
            event = verify(server_key, "ledger", message)
            require(before == previous and hashlib.sha256(bytes.fromhex(before) + canonical(message)).hexdigest() == hashed,
                    "ledger hash chain")
            require(event["source"] == config["source"], "ledger source")
            request = event["request"]
            body = request["body"]
            actor = body["actor"]
            entry = keys[actor]
            verify(Ed25519PublicKey.from_public_bytes(bytes.fromhex(entry["app"])), request["kind"], request)
            require(body["source"] == config["source"] and body["seq"] == sequences.get(actor, 0) + 1,
                    "source/sequence replay")
            require(body["nonce"] not in nonces and body["request_id"] not in requests, "duplicate event")
            nonces.add(body["nonce"])
            requests.add(body["request_id"])
            sequences[actor] = body["seq"]
            if event["type"] == "disclosure":
                state = backend.call({"op": "inspect"})
                require(state["cut"] == body["cut"] and state["version"] == body["epoch"] and state["actor"] == int(actor),
                        "request is not the original source event")
                require(event["peer"] == entry["fingerprint"] and event["record"]["query"] == body["query"], "request certificate/scope")
                actual = backend.call({"op": "advance", "cut": state["cut"], "query": body["query"]})
                require(actual == event["record"], "source data replay differs")
                verify_disclosure(actual)
                observations.append(actual)
            else:
                require(actor == "2" and event["new"] == registry["rotated2"], "rotation destination")
                require(event["old"] == entry["fingerprint"] and event["new"]["actor"] == actor, "key rotation identity")
                new = event["new"]
                proof = verify(Ed25519PublicKey.from_public_bytes(bytes.fromhex(new["app"])), "new-key", body["new_signature"])
                challenge = {field: body[field] for field in ("source", "stream", "actor", "nonce", "seq", "cut", "epoch", "expires") if field in body}
                from crypto import digest
                require(body["rotation"] == new and proof == {"challenge": digest(challenge), "rotation": new}, "new-key proof")
                keys[actor] = new
            previous = hashed
    finally:
        backend.close()
        database.close()
    return observations, previous


def run(box: Path, source: str, count: int = 128):
    box.mkdir(parents=True, exist_ok=True)
    tests = []
    all_observations = []
    with tempfile.TemporaryDirectory(prefix="public-audit-keys-") as temporary:
        pki = Path(temporary) / "keys"
        registry = create_pki(pki)
        (box / "public-keys.json").write_text(json.dumps(registry, indent=2) + "\n")
        (box / "ca.pem").write_bytes((pki / "ca.pem").read_bytes())
        for world in ("one", "two"):
            config = {"allow_unanchored": True, "pki": str(pki), "source": source, "registry": registry,
                      "lean": str(ROOT / "Lean"), "database": str(box / (world + ".sqlite")),
                      "backend_error": str(box / "source.log"),
                      "backend": ["lake", "env", "lean", "--trust=0", "-DwarningAsError=true", "-DElab.async=false", "-j1",
                                  "--run", "scripts/verification/public-scoped-audit-source.lean", "private-" + world]}
            path = box / (world + "-config.json")
            path.write_text(json.dumps(config))
            process, port, error = start_server(path, box / "service.log")
            workers = {label: Worker(pki / label,allow_unanchored=True) for label in ("auditor1", "auditor2", "rotated2")}
            try:
                if world == "one":
                    for tamper in ("scope", "epoch", "actor"):
                        bad = workers["auditor1"].call({"port": port, "source": source, "tamper": tamper})
                        require("error" in bad, "tampered request accepted: " + tamper)
                        tests.append(tamper + "_rejected")
                    try:
                        exchange(pki / "auditor1", port, source, {"slots": 63, "fields": 3}, hostname="wrong.local",allow_unanchored=True)
                    except ssl.SSLError:
                        tests.append("wrong_server_name_rejected")
                    else:
                        raise RuntimeError("hostname not verified")
                    try:
                        exchange(pki / "expired", port, source, {"slots": 63, "fields": 3},allow_unanchored=True)
                    except (ssl.SSLError, EOFError):
                        tests.append("expired_certificate_rejected")
                    else:
                        raise RuntimeError("expired certificate accepted")
                    context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
                    context.load_verify_locations(str(pki / "ca.pem"))
                    context.minimum_version = context.maximum_version = ssl.TLSVersion.TLSv1_3
                    try:
                        with socket.create_connection(("127.0.0.1", port), timeout=5) as raw:
                            with context.wrap_socket(raw, server_hostname="audit.local") as connection:
                                receive(connection)
                    except (ssl.SSLError, EOFError):
                        tests.append("missing_client_certificate_rejected")
                    else:
                        raise RuntimeError("mTLS accepted no client certificate")
                    ciphertext_probe(pki / "auditor1", port)
                    tests.append("ciphertext_modification_rejected")
                observations = []
                first_request = None
                for index in range(count):
                    profile = "auditor1" if index < 2 else ("auditor2" if index < 4 else "rotated2")
                    query = {"slots": 63, "fields": 1 if index == 2 else 3}
                    if index == 4:
                        query = {"slots": 1, "fields": 2}
                    elif index == 5:
                        query = {"slots": 62, "fields": 3}
                    elif index == 6:
                        query = {"slots": 0, "fields": 3}
                    answer = workers[profile].call({"port": port, "source": source, "query": query})
                    require("response" in answer, str(answer))
                    require(answer["tls"] == "TLSv1.3", "TLS downgrade")
                    record = answer["response"]["event"]["record"]
                    observations.append(record)
                    if index == 0:
                        first_request = answer["request"]
                        duplicate = workers["auditor1"].call({"port": port, "source": source, "replay": first_request})
                        require("error" in duplicate, "replay accepted")
                    if index == 0 and world == "one":
                        # A deferred FK makes SQLite reject COMMIT after the source
                        # cache advances. The source must restore from the unchanged ledger.
                        with sqlite3.connect(config["database"]) as fault:
                            fault.executescript("CREATE TABLE commit_parent(id PRIMARY KEY); CREATE TABLE commit_guard(id REFERENCES commit_parent(id) DEFERRABLE INITIALLY DEFERRED); CREATE TRIGGER commit_fault AFTER INSERT ON events BEGIN INSERT INTO commit_guard VALUES(1); END;")
                            before = fault.execute("SELECT count(*) FROM events").fetchone()[0]
                        failed = workers["auditor1"].call({"port": port, "source": source, "query": query})
                        require("error" in failed, "failed COMMIT accepted")
                        with sqlite3.connect(config["database"]) as fault:
                            require(fault.execute("SELECT count(*) FROM events").fetchone()[0] == before, "failed COMMIT consumed event")
                            fault.executescript("DROP TRIGGER commit_fault; DROP TABLE commit_guard; DROP TABLE commit_parent;")
                        tests.append("failed_commit_restores_original_source_cursor")
                    if index == 3:
                        rotation = exchange(pki / "auditor2", port, source, query,
                                            rotation=registry["rotated2"], new_profile=pki / "rotated2",allow_unanchored=True)
                        require("response" in rotation, "actual key rotation failed")
                        require(workers["auditor2"].call({"port": port, "source": source})["error"] == "KEY_REVOKED", "old application key remained live")
                    if index == 16:
                        stop_server(process, error)
                        process, port, error = start_server(path, box / "service.log")
                        old = workers["auditor1"].call({"port": port, "source": source, "replay": first_request})
                        require("error" in old, "restart accepted old request")
                tests += [world + "_replay_rejected", world + "_rotation_and_revocation", world + "_restart_recovered"]
                statuses = Counter(item["access"] for item in observations)
                require(statuses["admitted"] == 7 and statuses["unauthorized"] == 1 and statuses["unfunded"] > 0 and statuses["expired"] > 0,
                        "missing actual paid/denied/funding/expiry branches")
                require(sum(int(item["labor"]) for item in observations) == 14, "source query labor was not conserved")
                restored = verify_disclosure(observations[3])
                require(restored["payment"] == restored["lifecycle"] == ["verified"] * 6, "new auditor did not independently verify all six original slots")
                if world == "one":
                    for label, mutate in (("extra_private_field", lambda row: row["evidence"][0]["payment"].update(private_feed=39)),
                                          ("unknown_access", lambda row: row.update(access="garbage"))):
                        bad = copy.deepcopy(observations[3])
                        mutate(bad)
                        try:
                            verify_disclosure(bad)
                        except ValueError:
                            tests.append(label + "_rejected")
                        else:
                            raise RuntimeError("non-scoped payload accepted: " + label)
                    wrong_row = copy.deepcopy(observations[3])
                    wrong_row["evidence"][0]["payment"]["row"] += 1
                    checked = verify_disclosure(wrong_row)
                    require(checked["payment"][0] == checked["lifecycle"][0] == "insufficient", "wrong original responsibility accepted")
                    tests.append("wrong_original_row_insufficient")
                missing = verify_disclosure(observations[2])
                require(missing["payment"] == missing["lifecycle"] == ["insufficient"] * 6, "missing evidence was misclassified")
                partial = verify_disclosure(observations[4])
                require(partial["payment"] == ["verified"] and partial["lifecycle"] == ["insufficient"], "second client depended on first verdict")
                if world == "one":
                    for label, mutation in (("chain", "UPDATE events SET hash='" + "1" * 64 + "' WHERE id=1"),
                                            ("keys", "UPDATE keys SET public='00' WHERE actor='2'"),
                                            ("replay", "DELETE FROM used WHERE rowid=(SELECT min(rowid) FROM used)")):
                        corrupt = box / (label + "-corrupt.sqlite")
                        with sqlite3.connect(config["database"]) as original, sqlite3.connect(corrupt) as archive:
                            original.backup(archive)
                            archive.execute(mutation)
                        bad_config = box / (label + "-corrupt-config.json")
                        bad_config.write_text(json.dumps({**config, "database": str(corrupt)}))
                        rejected = subprocess.run([sys.executable, str(HERE / "service.py"), str(bad_config)], text=True, capture_output=True, timeout=15)
                        (box / (label + "-corrupt.log")).write_text(rejected.stderr)
                        require(rejected.returncode != 0 and not rejected.stdout, "damaged ledger or state table resumed: " + label)
                        bad_config.unlink()
                        tests.append(label + "_corruption_rejected_before_source_start")
                replayed, head = replay(config, registry)
                require(replayed == observations, "independent source/crypto replay differs")
                (box / (world + "-observations.json")).write_text(json.dumps(observations))
                (box / (world + "-replay.json")).write_text(json.dumps({"count": count, "head": head, "statuses": statuses}))
                all_observations.append(observations)
                print("NETWORK", world, "PASS:", count, "actual requests;", dict(statuses), flush=True)
            finally:
                for worker in workers.values():
                    worker.close()
                stop_server(process, error)
                # Configs name ephemeral key paths; receipts retain only public key material.
                path.unlink(missing_ok=True)
    require(all_observations[0] == all_observations[1], "private histories changed pooled network application observations")
    result = {"source": source, "histories": 2, "requests_each": count, "tls": "TLSv1.3", "negative_controls": tests,
              "pooled_observations_equal": True, "query_labor_each": 14, "total_source_labor_each": 19}
    (box / "network-receipt.json").write_text(json.dumps(result, indent=2) + "\n")
    print("NETWORK CRYPTO PASS: mTLS; Ed25519; scoped six-slot evidence; live Lean source; rotation; replay; restart; fixed frames", flush=True)
    return result


if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit("usage: exercise.py EVIDENCE_DIRECTORY SOURCE_DIGEST")
    run(Path(sys.argv[1]), sys.argv[2])
