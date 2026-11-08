"""Independent, signed compare-and-append journal; no disclosure authority."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import secrets
import signal
import socketserver
import sqlite3
import threading
import time

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

from crypto import app_private, canonical, connect, digest, peer, receive, send, sign, tls_context, verify

ZERO = "0" * 64


def ledger_hash(previous, message):
    return hashlib.sha256(bytes.fromhex(previous) + canonical(message)).hexdigest()


def public_key(entry):
    return Ed25519PublicKey.from_public_bytes(bytes.fromhex(entry["app"]))


def verify_commit(identity, receipt, *, source, stream, seq, head, previous, message, cluster=None):
    point = verify(public_key(identity), "anchor-commit", receipt)
    expected = dict(source=source, stream=stream, seq=seq, head=head, previous=previous, message=digest(message))
    if cluster is not None:
        expected["cluster"] = cluster
    if point != expected:
        raise ValueError("ANCHOR_COMMIT_BINDING")
    return point


class Client:
    def __init__(self, config):
        self.config = config
        self.endpoint = config["anchor"]
        self.profile = Path(self.endpoint.get("pki",config["pki"])) / "server"
        self.key = app_private(self.profile)

    def call(self, operation, **values):
        body = dict(op=operation, source=self.config["source"], stream=self.config["stream"],
                    nonce=secrets.token_hex(32), expires=time.time() + 30, **values)
        request = sign(self.key, "anchor-request", body)
        endpoint = self.endpoint
        with connect(self.profile, endpoint["port"], host=endpoint["host"], hostname=endpoint["hostname"]) as connection:
            uri, fingerprint, key = peer(connection)
            if uri != "urn:public-audit:anchor" or fingerprint != endpoint["identity"]["fingerprint"] or key.public_bytes_raw().hex() != endpoint["identity"]["app"]:
                raise ValueError("ANCHOR_IDENTITY")
            send(connection, request)
            response = receive(connection)
            result = verify(key, "anchor-response", response)
            if result["request"] != digest(request) or result["nonce"] != body["nonce"]:
                raise ValueError("ANCHOR_FRESHNESS")
            if "error" in result:
                raise ValueError(result["error"])
            return result["result"]

    def head(self):
        result = self.call("head")
        if (result["source"], result["stream"]) != (self.config["source"], self.config["stream"]):
            raise ValueError("ANCHOR_NAMESPACE")
        return result

    def append(self, seq, previous, message):
        head = ledger_hash(previous, message)
        result = self.call("append", seq=seq, previous=previous, head=head, message=message)
        verify_commit(self.endpoint["identity"], result["receipt"], source=self.config["source"],
                      stream=self.config["stream"], seq=seq, head=head, previous=previous, message=message, cluster=self.endpoint.get("cluster"))
        return result["receipt"]

    def get(self, seq):
        result = self.call("get", seq=seq)
        point = result["receipt"]["body"]
        verify_commit(self.endpoint["identity"], result["receipt"], source=self.config["source"],
                      stream=self.config["stream"], seq=seq, head=point["head"], previous=point["previous"], message=result["message"], cluster=self.endpoint.get("cluster"))
        if ledger_hash(point["previous"], result["message"]) != point["head"]:
            raise ValueError("ANCHOR_RECORD_HASH")
        return result


class Journal:
    def __init__(self, config, initialize=False):
        self.config = config
        path = Path(config["database"])
        if path.exists() and initialize:
            raise ValueError("ANCHOR_ALREADY_INITIALIZED")
        if not path.exists() and not initialize:
            raise ValueError("ANCHOR_STORAGE_MISSING")
        self.key = app_private(Path(config["pki"]) / "anchor")
        self.lock = threading.RLock()
        self.db = sqlite3.connect(path, check_same_thread=False, isolation_level=None)
        self.db.execute("PRAGMA journal_mode=WAL")
        self.db.execute("PRAGMA synchronous=FULL")
        self.db.executescript("""
          CREATE TABLE IF NOT EXISTS binding(value TEXT NOT NULL);
          CREATE TABLE IF NOT EXISTS entries(stream TEXT,seq INTEGER,previous TEXT,hash TEXT,message TEXT,receipt TEXT,
            PRIMARY KEY(stream,seq), UNIQUE(stream,hash));
          CREATE TRIGGER IF NOT EXISTS entries_no_update BEFORE UPDATE ON entries BEGIN SELECT RAISE(ABORT,'APPEND_ONLY'); END;
          CREATE TRIGGER IF NOT EXISTS entries_no_delete BEFORE DELETE ON entries BEGIN SELECT RAISE(ABORT,'APPEND_ONLY'); END;
        """)
        binding_value = {"streams": config["streams"], "identity": config["registry"]["anchor"]}
        if "cluster" in config:
            binding_value["cluster"] = config["cluster"]
        if "transport_writer" in config:
            binding_value["transport_writer"] = config["transport_writer"]
        binding = canonical(binding_value).decode()
        existing = self.db.execute("SELECT value FROM binding").fetchall()
        if not existing and initialize:
            self.db.execute("INSERT INTO binding VALUES(?)", (binding,))
        elif existing != [(binding,)]:
            raise ValueError("ANCHOR_BINDING")
        for stream in config["streams"]:
            previous = ZERO
            expected_seq = 1
            for seq, before, head, text, receipt in self.db.execute("SELECT seq,previous,hash,message,receipt FROM entries WHERE stream=? ORDER BY seq", (stream,)):
                message = json.loads(text)
                self.validate_message(stream, message)
                if seq != expected_seq or before != previous or ledger_hash(before, message) != head:
                    raise ValueError("ANCHOR_STORAGE_CHAIN")
                verify_commit(config["registry"]["anchor"], json.loads(receipt), source=config["streams"][stream]["source"],
                              stream=stream, seq=seq, head=head, previous=before, message=message, cluster=config.get("cluster"))
                previous = head
                expected_seq += 1

    def validate_message(self, stream, message):
        entry = self.config["streams"][stream]
        event = verify(public_key(entry["writer"]), "ledger", message)
        if event.get("source") != entry["source"] or event.get("stream") != stream:
            raise ValueError("ANCHOR_LEDGER_NAMESPACE")

    def head(self, stream):
        row = self.db.execute("SELECT seq,hash FROM entries WHERE stream=? ORDER BY seq DESC LIMIT 1", (stream,)).fetchone()
        return dict(source=self.config["streams"][stream]["source"], stream=stream, seq=row[0] if row else 0, head=row[1] if row else ZERO)

    def validate_extension(self, stream, message):
        keys = {self.config["registry"][label]["actor"]: self.config["registry"][label]
                for label in ("auditor1","auditor2")}
        sequences, seen, last_cut = {}, set(), -1
        for text, in self.db.execute("SELECT message FROM entries WHERE stream=? ORDER BY seq", (stream,)):
            prior = json.loads(text)["body"]
            request = prior["request"]["body"]
            sequences[request["actor"]] = request["seq"]
            seen.update((request["nonce"],request["request_id"]))
            if prior["type"] == "rotation":
                keys[request["actor"]] = prior["new"]
            elif prior["type"] == "disclosure":
                last_cut = prior["record"]["cut"]
        event, request = message["body"], message["body"]["request"]
        from source_extension import guard
        from governance import rows_of
        guard(self.config, rows_of(self.db, stream), event)
        from governance import registration_bound
        registration_bound(event)
        body = request["body"]
        actor = body["actor"]
        identity = keys[actor]
        verify(public_key(identity),request["kind"],request)
        if (body.get("stream") != stream or body["source"] != event["source"]
                or body["seq"] != sequences.get(actor,0) + 1
                or body["nonce"] in seen or body["request_id"] in seen):
            raise ValueError("ANCHOR_EVENT_REPLAY")
        if event["type"] == "disclosure" and request["kind"] == "audit":
            record = event["record"]
            if (record["cut"] <= last_cut or record["cut"] != body["cut"] or record["actor"] != int(actor)
                    or record["version"] != body["epoch"] or record["query"] != body["query"] or event["peer"] != identity["fingerprint"]):
                raise ValueError("ANCHOR_EVENT_SCOPE")
            if "registration" in event:
                from governance import expected,rows_of
                expected(self.config,rows_of(self.db,stream),event,native=False)
        elif event["type"] == "native-response" and request["kind"] == "native-response":
            if event['peer']!=identity['fingerprint']:
                raise ValueError('NATIVE_MEMBER_CERTIFICATE')
            from governance import expected,rows_of
            expected(self.config,rows_of(self.db,stream),event,native=False)
        elif event['type'] in {'energy-renewal','energy-audit'} and request['kind']==event['type']:
            if event['peer']!=identity['fingerprint']:
                raise ValueError('ENERGY_MEMBER_CERTIFICATE')
            from energy import expected
            from governance import rows_of
            expected(self.config,rows_of(self.db,stream),event,native=False)
        elif event['type']=='energy-continuation' and request['kind']==event['type']:
            if event['peer']!=identity['fingerprint']:
                raise ValueError('CONTINUATION_MEMBER_CERTIFICATE')
            from continuation import expected
            from governance import rows_of
            expected(self.config,rows_of(self.db,stream),event,native=False)
        elif event['type']=='energy-handoff' and request['kind']==event['type']:
            if event['peer']!=identity['fingerprint']:
                raise ValueError('HANDOFF_MEMBER_CERTIFICATE')
            from handoff import expected
            from governance import rows_of
            expected(self.config,rows_of(self.db,stream),event,native=False)
        elif event['type'] in {'source-extension', 'energy-regeneration', 'material-extension', 'energy-material', 'productive-extension', 'energy-productive', 'arrival-extension', 'energy-arrival', 'donor-extension', 'energy-donor'} and request['kind']==event['type']:
            if event['peer']!=identity['fingerprint']:
                raise ValueError('SOURCE_EXTENSION_MEMBER_CERTIFICATE')
            if event['type']=='source-extension':
                from source_extension import expected
                expected(self.config,rows_of(self.db,stream),event)
            elif event['type']=='material-extension':
                from material_extension import expected
                expected(self.config,rows_of(self.db,stream),event)
            elif event['type'] in {'donor-extension','energy-donor'}:
                from donor_arrival_live import expected
                expected(self.config,rows_of(self.db,stream),event,native=False)
            elif event['type']=='arrival-extension':
                from arrival_extension import expected
                expected(self.config,rows_of(self.db,stream),event)
            elif event['type']=='energy-arrival':
                from arrival_regeneration import expected
                expected(self.config,rows_of(self.db,stream),event,native=False)
            elif event['type']=='productive-extension':
                from productive_extension import expected
                expected(self.config,rows_of(self.db,stream),event)
            elif event['type']=='energy-productive':
                from productive_regeneration import expected
                expected(self.config,rows_of(self.db,stream),event,native=False)
            elif event['type']=='energy-material':
                from material_regeneration import expected
                expected(self.config,rows_of(self.db,stream),event,native=False)
            else:
                from regeneration import expected
                expected(self.config,rows_of(self.db,stream),event,native=False)
        elif event["type"] == "rotation" and request["kind"] == "rotate":
            new = event["new"]
            challenge = {key: body[key] for key in ("source","stream","actor","nonce","seq","cut","epoch","expires")}
            proof = verify(public_key(new),"new-key",body["new_signature"])
            if (actor != "2" or new != self.config["registry"]["rotated2"] or body["rotation"] != new
                    or event["old"] != identity["fingerprint"] or proof != {"challenge":digest(challenge),"rotation":new}):
                raise ValueError("ANCHOR_KEY_ROTATION")
        else:
            raise ValueError("ANCHOR_EVENT_KIND")

    def execute(self, body):
        stream = body["stream"]
        if body["source"] != self.config["streams"][stream]["source"]:
            raise ValueError("ANCHOR_SOURCE")
        if body["op"] == "head":
            return self.head(stream)
        seq = body["seq"]
        if type(seq) is not int or seq < 1:
            raise ValueError("ANCHOR_SEQUENCE")
        if body["op"] == "get":
            row = self.db.execute("SELECT message,receipt FROM entries WHERE stream=? AND seq=?", (stream,seq)).fetchone()
            if not row:
                raise ValueError("ANCHOR_NOT_FOUND")
            return {"message": json.loads(row[0]), "receipt": json.loads(row[1])}
        if body["op"] != "append":
            raise ValueError("ANCHOR_OPERATION")
        self.validate_message(stream, body["message"])
        if ledger_hash(body["previous"], body["message"]) != body["head"]:
            raise ValueError("ANCHOR_HASH")
        self.db.execute("BEGIN IMMEDIATE")
        try:
            old = self.db.execute("SELECT previous,hash,message,receipt FROM entries WHERE stream=? AND seq=?", (stream,seq)).fetchone()
            if old:
                if old[:3] != (body["previous"], body["head"], canonical(body["message"]).decode()):
                    raise ValueError("ANCHOR_FORK")
                receipt = json.loads(old[3])
            else:
                current = self.head(stream)
                if current["seq"] + 1 != seq or current["head"] != body["previous"]:
                    raise ValueError("ANCHOR_CAS")
                self.validate_extension(stream,body["message"])
                point = dict(source=body["source"], stream=stream, seq=seq, head=body["head"],
                             previous=body["previous"], message=digest(body["message"]))
                if "cluster" in self.config:
                    point["cluster"] = self.config["cluster"]
                receipt = sign(self.key, "anchor-commit", point)
                self.db.execute("INSERT INTO entries VALUES(?,?,?,?,?,?)", (stream,seq,body["previous"],body["head"],canonical(body["message"]).decode(),canonical(receipt).decode()))
            self.db.execute("COMMIT")
        except BaseException:
            if self.db.in_transaction:
                self.db.execute("ROLLBACK")
            raise
        return {"receipt": receipt}


class Server(socketserver.ThreadingTCPServer):
    allow_reuse_address = True
    daemon_threads = True

    def get_request(self):
        connection, address = super().get_request()
        connection.settimeout(15)
        try:
            return self.context.wrap_socket(connection, server_side=True), address
        except BaseException:
            connection.close()
            raise


class Handler(socketserver.BaseRequestHandler):
    def handle(self):
        journal = self.server.journal
        request = None
        try:
            uri, fingerprint, key = peer(self.request)
            request = receive(self.request)
            body = verify(key, "anchor-request", request)
            writer = journal.config.get("transport_writer",journal.config["streams"][body["stream"]]["writer"])
            if uri != "urn:public-audit:server" or fingerprint != writer["fingerprint"] or key.public_bytes_raw().hex() != writer["app"]:
                raise ValueError("ANCHOR_WRITER")
            if not time.time() <= body["expires"] <= time.time() + 31:
                raise ValueError("ANCHOR_EXPIRED")
            with journal.lock:
                result = journal.execute(body)
            response = {"result": result}
        except Exception as error:
            response = {"error": str(error) if isinstance(error,(ValueError,KeyError)) else type(error).__name__}
        if request is not None:
            response.update(request=digest(request), nonce=request.get("body",{}).get("nonce"))
            send(self.request, sign(journal.key, "anchor-response", response))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("config", type=Path)
    parser.add_argument("--initialize", action="store_true")
    args = parser.parse_args()
    config = json.loads(args.config.read_text())
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(SystemExit(0)))
    journal = Journal(config, args.initialize)
    try:
        with Server((config.get("bind", "127.0.0.1"), config.get("port", 0)), Handler) as server:
            server.journal = journal
            server.context = tls_context(Path(config["pki"]) / "anchor", server=True)
            print(json.dumps({"port": server.server_address[1], "role": "external-monotonic-anchor"}), flush=True)
            server.serve_forever(poll_interval=0.1)
    finally:
        journal.db.close()


if __name__ == "__main__":
    main()
