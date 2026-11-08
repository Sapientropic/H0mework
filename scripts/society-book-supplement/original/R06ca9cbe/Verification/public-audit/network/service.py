"""mTLS audit transport. Disclosure and permission outcomes come from the live Lean producer."""
from __future__ import annotations

import argparse
import hashlib
import fcntl
import json
import os
from pathlib import Path
import secrets
import signal
import socketserver
import sqlite3
import subprocess
import threading
import time

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

from crypto import app_private, canonical, digest, peer, receive, send, sign, tls_context, verify
from verify import verify_disclosure
from anchor import Client as AnchorClient, ZERO, ledger_hash, verify_commit


class Backend:
    def __init__(self, config: dict):
        self.error_file = open(config["backend_error"], "a")
        self.process = subprocess.Popen(config["backend"], cwd=config["lean"], stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, stderr=self.error_file, text=True)

    def call(self, message: dict) -> dict:
        self.process.stdin.write(json.dumps(message) + "\n")
        self.process.stdin.flush()
        line = self.process.stdout.readline()
        if not line:
            raise RuntimeError("SOURCE_PRODUCER_EXITED")
        result = json.loads(line)
        if "error" in result:
            raise RuntimeError(result["error"])
        return result

    def close(self):
        self.process.stdin.close()
        try:
            self.process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            self.process.terminate()
            self.process.wait(timeout=5)
        self.error_file.close()


class Store:
    def __init__(self, config: dict):
        self.config = config
        self.lock = threading.RLock()
        self.poisoned = False
        if "anchor" in config and "anchors" in config:
            raise ValueError("AMBIGUOUS_ANCHOR_CONFIGURATION")
        if not ({"anchor","anchors"} & config.keys()) and config.get("allow_unanchored") is not True:
            raise ValueError("EXTERNAL_ANCHOR_REQUIRED")
        if "anchors" in config:
            from quorum import Client as QuorumClient
            self.anchor = QuorumClient(config)
            # All local instances holding this writer credential share a lock,
            # even if they point at different local database paths.
            lock_id = digest({"source":config["source"],"stream":config["stream"],"trust":config["anchors"]["trust"]})
            self.writer_lock = (Path(config["pki"]) / "server" / (lock_id+".writer.lock")).open("a")
            try:
                fcntl.flock(self.writer_lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            except BlockingIOError:
                self.writer_lock.close()
                raise ValueError("QUORUM_WRITER_ALREADY_ACTIVE") from None
            self.pending_path = Path(config["database"]+".pending.json")
        else:
            self.anchor = AnchorClient(config) if "anchor" in config else None
        self.key = app_private(Path(config["pki"]) / "server")
        new_database = not Path(config["database"]).exists()
        self.database = sqlite3.connect(config["database"], check_same_thread=False, isolation_level=None)
        self.database.execute("PRAGMA journal_mode=WAL")
        self.database.execute("PRAGMA foreign_keys=ON")
        self.database.execute("PRAGMA synchronous=FULL")
        self.database.executescript("""
          CREATE TABLE IF NOT EXISTS keys(actor TEXT PRIMARY KEY, fingerprint TEXT, public TEXT);
          CREATE TABLE IF NOT EXISTS events(id INTEGER PRIMARY KEY, previous TEXT, hash TEXT UNIQUE, message TEXT);
          CREATE TABLE IF NOT EXISTS used(nonce TEXT PRIMARY KEY, request_id TEXT UNIQUE, actor TEXT, seq INTEGER);
          CREATE TABLE IF NOT EXISTS sequences(actor TEXT PRIMARY KEY, seq INTEGER);
          CREATE TABLE IF NOT EXISTS anchor_receipts(seq INTEGER PRIMARY KEY, receipt TEXT);
        """)
        if new_database:
            for label in ("auditor1", "auditor2"):
                entry = config["registry"][label]
                self.database.execute("INSERT INTO keys VALUES(?,?,?)", (entry["actor"], entry["fingerprint"], entry["app"]))
        damaged = False
        try:
            self.validate_ledger()
        except Exception:
            if not self.anchor or not config.get("recover_from_anchor",False):
                raise
            damaged = True
        if self.anchor:
            if "anchors" in config:
                self.reconcile_pending(config.get("recover_from_anchor",False))
            self.reconcile_anchor(config.get("recover_from_anchor",False),force=damaged)
            if "anchors" in config:
                self.clear_pending()
        self.backend = Backend(config)
        try:
            self.restore_source()
        except BaseException:
            self.backend.close()
            self.database.close()
            raise

    def validate_ledger(self):
        keys = {self.config["registry"][label]["actor"]: self.config["registry"][label]
                for label in ("auditor1", "auditor2")}
        sequences, used = {}, set()
        previous = "0" * 64
        server_key = self.key.public_key()
        for expected_id, (row_id, before, hashed, text) in enumerate(self.database.execute("SELECT id,previous,hash,message FROM events ORDER BY id"), 1):
            if row_id != expected_id:
                raise ValueError("RESTORE_LEDGER_SEQUENCE")
            message = json.loads(text)
            event = verify(server_key, "ledger", message)
            from governance import registration_bound
            registration_bound(event)
            if before != previous or hashlib.sha256(bytes.fromhex(before) + canonical(message)).hexdigest() != hashed:
                raise ValueError("RESTORE_CHAIN")
            request = event["request"]
            body = request["body"]
            actor = body["actor"]
            entry = keys[actor]
            verify(Ed25519PublicKey.from_public_bytes(bytes.fromhex(entry["app"])), request["kind"], request)
            identity = (body["nonce"], body["request_id"], actor, body["seq"])
            if self.anchor and (event.get("stream") != self.config["stream"] or body.get("stream") != self.config["stream"]):
                raise ValueError("RESTORE_STREAM")
            if (event["source"] != self.config["source"] or body["source"] != self.config["source"]
                    or body["seq"] != sequences.get(actor, 0) + 1
                    or any(row[0] == identity[0] or row[1] == identity[1] for row in used)):
                raise ValueError("RESTORE_REQUEST")
            if event["type"] == "disclosure" and request["kind"] == "audit":
                record = event["record"]
                if (event["peer"] != entry["fingerprint"] or record["actor"] != int(actor)
                        or record["version"] != body["epoch"] or record["cut"] != body["cut"] or record["query"] != body["query"]):
                    raise ValueError("RESTORE_SCOPE")
                verify_disclosure(record)
                if "registration" in event:
                    from governance import expected, rows_of
                    expected(self.config,[row for row in rows_of(self.database) if row[0]<expected_id],event)
            elif event["type"] == "native-response" and request["kind"] == "native-response":
                if event["peer"]!=entry["fingerprint"]:
                    raise ValueError("NATIVE_MEMBER_CERTIFICATE")
                from governance import expected, rows_of
                expected(self.config,[row for row in rows_of(self.database) if row[0]<expected_id],event)
            elif event['type'] in {'energy-renewal','energy-audit'} and request['kind']==event['type']:
                if event['peer']!=entry['fingerprint']:
                    raise ValueError('ENERGY_MEMBER_CERTIFICATE')
                from energy import expected
                from governance import rows_of
                expected(self.config,[row for row in rows_of(self.database) if row[0]<expected_id],event)
            elif event['type']=='energy-continuation' and request['kind']==event['type']:
                if event['peer']!=entry['fingerprint']:
                    raise ValueError('CONTINUATION_MEMBER_CERTIFICATE')
                from continuation import expected
                from governance import rows_of
                expected(self.config,[row for row in rows_of(self.database) if row[0]<expected_id],event)
            elif event['type']=='energy-handoff' and request['kind']==event['type']:
                if event['peer']!=entry['fingerprint']:
                    raise ValueError('HANDOFF_MEMBER_CERTIFICATE')
                from handoff import expected
                from governance import rows_of
                expected(self.config,[row for row in rows_of(self.database) if row[0]<expected_id],event)
            elif event['type'] in {'source-extension','energy-regeneration','material-extension','energy-material','productive-extension','energy-productive','arrival-extension','energy-arrival','donor-extension','energy-donor'} and request['kind']==event['type']:
                if event['peer']!=entry['fingerprint']:
                    raise ValueError('SOURCE_EXTENSION_MEMBER_CERTIFICATE')
                from governance import rows_of
                if event['type']=='source-extension':
                    from source_extension import expected
                elif event['type']=='material-extension':
                    from material_extension import expected
                elif event['type'] in {'donor-extension','energy-donor'}:
                    from donor_arrival_live import expected
                elif event['type']=='arrival-extension':
                    from arrival_extension import expected
                elif event['type']=='energy-arrival':
                    from arrival_regeneration import expected
                elif event['type']=='productive-extension':
                    from productive_extension import expected
                elif event['type']=='energy-productive':
                    from productive_regeneration import expected
                elif event['type']=='energy-material':
                    from material_regeneration import expected
                else:
                    from regeneration import expected
                expected(self.config,[row for row in rows_of(self.database) if row[0]<expected_id],event)
            elif event["type"] == "rotation" and request["kind"] == "rotate":
                rotation = event["new"]
                challenge = {key: body[key] for key in ("source", "stream", "actor", "nonce", "seq", "cut", "epoch", "expires") if key in body}
                proof = verify(Ed25519PublicKey.from_public_bytes(bytes.fromhex(rotation["app"])), "new-key", body["new_signature"])
                if (actor != "2" or rotation != self.config["registry"]["rotated2"] or body["rotation"] != rotation
                        or event["old"] != entry["fingerprint"] or proof != {"challenge": digest(challenge), "rotation": rotation}):
                    raise ValueError("RESTORE_ROTATION")
                keys[actor] = rotation
            else:
                raise ValueError("RESTORE_EVENT_KIND")
            sequences[actor] = body["seq"]
            used.add(identity)
            previous = hashed
        expected_keys = {(actor, entry["fingerprint"], entry["app"]) for actor, entry in keys.items()}
        if (set(self.database.execute("SELECT actor,fingerprint,public FROM keys")) != expected_keys
                or dict(self.database.execute("SELECT actor,seq FROM sequences")) != sequences
                or set(self.database.execute("SELECT nonce,request_id,actor,seq FROM used")) != used):
            raise ValueError("RESTORE_STATE_TABLES")

    def restore_source(self):
        for message, in self.database.execute("SELECT message FROM events ORDER BY id"):
            event = json.loads(message)["body"]
            if event["type"] == "disclosure":
                state = self.backend.call({"op": "inspect"})
                if state["cut"] != event["record"]["cut"]:
                    raise RuntimeError("RESTORE_SOURCE_CUT")
                record = self.backend.call({"op": "advance", "cut": state["cut"], "query": event["record"]["query"]})
                if record != event["record"]:
                    raise RuntimeError("RESTORE_SOURCE_RECORD")

    def source_state(self):
        from governance import response_at, rows_of
        rows=rows_of(self.database)
        if self.config.get('donor'):
            from donor_arrival_live import committed,context
            if committed(self.config,rows) is not None:
                _,scope,current,_=context(self.config,rows)
                return {**current,'actor':1,'energy_scope':scope}
        if self.config.get('arrival'):
            from arrival_extension import committed
            if committed(self.config,rows) is not None:
                from arrival_regeneration import context
                _,scope,current=context(self.config,rows)
                return {**current,'actor':1,'energy_scope':scope}
        if self.config.get('productive'):
            from productive_extension import committed
            if committed(self.config,rows) is not None:
                from productive_regeneration import context
                _,scope,current=context(self.config,rows)
                return {**current,'actor':1,'energy_scope':scope}
        if self.config.get('refeed'):
            from material_extension import committed
            if committed(self.config,rows) is not None:
                from material_regeneration import context
                _,scope,current=context(self.config,rows)
                return {**current,'actor':1,'energy_scope':scope}
        if self.config.get('regeneration'):
            from source_extension import committed
            if committed(self.config,rows) is not None:
                from regeneration import context
                _,scope,current=context(self.config,rows)
                return {**current,'actor':1,'energy_scope':scope}
        from handoff import latest as latest_handoff
        swapped=latest_handoff(rows)
        if swapped:
            return {**swapped['native']['next'],'cut':swapped['native']['nextCut'],
                    'actor':swapped['request']['body']['actor'],'energy_scope':swapped['scope']}
        from continuation import latest as latest_continuation
        continued=latest_continuation(rows)
        if continued:
            return {**continued['native']['next'],'cut':continued['native']['nextCut'],
                    'actor':continued['request']['body']['actor'],
                    'energy_scope':continued['nextScope'] or continued['scope']}
        from energy import latest
        renewed=latest(rows)
        if renewed:
            return {**renewed['native']['epoch']['next'],'cut':renewed['native']['nextCut'],
                    'actor':renewed['request']['body']['actor'],'energy_scope':renewed['scope']}
        prior=response_at(rows)
        if prior:
            return {**prior['native']['next'],'actor':1,'native_scope_required':True}
        return self.backend.call({"op":"inspect"})

    def rollback_source_cache(self):
        self.poisoned = True
        self.backend.close()
        self.validate_ledger()
        self.backend = Backend(self.config)
        self.restore_source()
        self.poisoned = False

    def head(self):
        row = self.database.execute("SELECT hash FROM events ORDER BY id DESC LIMIT 1").fetchone()
        return row[0] if row else "0" * 64

    def save_pending(self, seq, previous, message):
        # Fsync the exact already-generated event before the first remote call.
        # This survives loss of all subquorum copies without inventing a retry.
        temporary = self.pending_path.with_suffix(".tmp")
        with temporary.open("wb") as output:
            os.chmod(temporary,0o600)
            output.write(canonical({"seq":seq,"previous":previous,"message":message}))
            output.flush()
            os.fsync(output.fileno())
        temporary.replace(self.pending_path)
        self.sync_pending_directory()

    def sync_pending_directory(self):
        descriptor = os.open(self.pending_path.parent,os.O_RDONLY)
        try: os.fsync(descriptor)
        finally: os.close(descriptor)

    def clear_pending(self):
        self.pending_path.unlink(missing_ok=True)
        self.sync_pending_directory()

    def reconcile_pending(self, recover):
        if not self.pending_path.is_file(): return
        pending=json.loads(self.pending_path.read_text())
        if set(pending)!={"seq","previous","message"} or type(pending["seq"]) is not int or pending["seq"]<1:
            raise ValueError("QUORUM_PENDING_RECORD")
        remote=self.anchor.head()
        if remote["seq"]<pending["seq"]:
            if not recover: raise ValueError("ANCHOR_RECOVERY_REQUIRED")
            if remote["seq"]+1!=pending["seq"] or remote["head"]!=pending["previous"]:
                raise ValueError("QUORUM_PENDING_PREFIX")
            self.anchor.append(pending["seq"],pending["previous"],pending["message"])
        entry=self.anchor.get(pending["seq"])
        if entry["message"]!=pending["message"] or entry["receipt"]["body"]["previous"]!=pending["previous"]:
            raise ValueError("QUORUM_PENDING_FORK")

    def require_current_anchor(self):
        remote = self.anchor.head()
        count = self.database.execute("SELECT count(*) FROM events").fetchone()[0]
        if remote["seq"] != count or remote["head"] != self.head():
            self.poisoned = True
            raise ValueError("ANCHOR_RECOVERY_REQUIRED")
        return remote

    def reconcile_anchor(self, recover, *, force=False):
        remote = self.anchor.head()
        count = self.database.execute("SELECT count(*) FROM events").fetchone()[0]
        if not force and remote["seq"] == count and remote["head"] == self.head():
            self.validate_anchor_receipts()
            return
        if not force and remote["seq"] < count:
            raise ValueError("ANCHOR_BEHIND_LOCAL_HISTORY")
        if not recover:
            raise ValueError("ANCHOR_RECOVERY_REQUIRED")
        entries = [self.anchor.get(seq) for seq in range(1,remote["seq"] + 1)]
        previous = ZERO
        for entry in entries:
            point = entry["receipt"]["body"]
            if point["previous"] != previous:
                raise ValueError("ANCHOR_RECOVERY_CHAIN")
            previous = point["head"]
        if previous != remote["head"]:
            raise ValueError("ANCHOR_RECOVERY_HEAD")
        db = self.database
        db.execute("BEGIN IMMEDIATE")
        try:
            for table in ("events","used","sequences","keys","anchor_receipts"):
                db.execute("DELETE FROM " + table)
            for label in ("auditor1","auditor2"):
                identity = self.config["registry"][label]
                db.execute("INSERT INTO keys VALUES(?,?,?)", (identity["actor"],identity["fingerprint"],identity["app"]))
            for seq, entry in enumerate(entries,1):
                point, message = entry["receipt"]["body"], entry["message"]
                event = message["body"]
                request = event["request"]["body"]
                db.execute("INSERT INTO events VALUES(?,?,?,?)", (seq,point["previous"],point["head"],canonical(message).decode()))
                db.execute("INSERT INTO used VALUES(?,?,?,?)", (request["nonce"],request["request_id"],request["actor"],request["seq"]))
                db.execute("INSERT INTO sequences VALUES(?,?) ON CONFLICT(actor) DO UPDATE SET seq=excluded.seq", (request["actor"],request["seq"]))
                if event["type"] == "rotation":
                    identity = event["new"]
                    db.execute("UPDATE keys SET fingerprint=?,public=? WHERE actor=?", (identity["fingerprint"],identity["app"],identity["actor"]))
                db.execute("INSERT INTO anchor_receipts VALUES(?,?)", (seq,canonical(entry["receipt"]).decode()))
            self.validate_ledger()
            self.validate_anchor_receipts()
            db.execute("COMMIT")
        except BaseException:
            if db.in_transaction:
                db.execute("ROLLBACK")
            raise
        self.require_current_anchor()

    def validate_anchor_receipts(self):
        rows = self.database.execute("SELECT id,previous,hash,message FROM events ORDER BY id").fetchall()
        receipts = dict(self.database.execute("SELECT seq,receipt FROM anchor_receipts"))
        if set(receipts) != {row[0] for row in rows}:
            raise ValueError("ANCHOR_RECEIPT_INVENTORY")
        for seq, previous, head, text in rows:
            binding = dict(source=self.config["source"],stream=self.config["stream"],seq=seq,head=head,previous=previous,message=json.loads(text))
            if "anchors" in self.config:
                from quorum import verify_certificate
                verify_certificate(self.config["anchors"]["trust"],json.loads(receipts[seq]),**binding)
            else:
                verify_commit(self.config["anchor"]["identity"],json.loads(receipts[seq]),**binding)

    def response_for(self, seq):
        row = self.database.execute("SELECT hash,message FROM events WHERE id=?", (seq,)).fetchone()
        message = json.loads(row[1])
        event, request = message["body"], message["body"]["request"]
        body = request["body"]
        result = {"source": self.config["source"], "stream": self.config.get("stream",self.config["source"]),
                  "request": digest(request), "request_id": body["request_id"], "seq": body["seq"],
                  "cut": body["cut"], "epoch": body["epoch"], "head": row[0], "event": event, "ledger": message}
        if self.anchor:
            result["anchor"] = json.loads(self.database.execute("SELECT receipt FROM anchor_receipts WHERE seq=?", (seq,)).fetchone()[0])
        return result

    def lookup(self, actor, request_id):
        for seq, text in self.database.execute("SELECT id,message FROM events ORDER BY id"):
            request = json.loads(text)["body"]["request"]["body"]
            if request["request_id"] == request_id and request["actor"] == actor:
                return self.response_for(seq)
        raise ValueError("REQUEST_NOT_COMMITTED")

    def append(self, body: dict):
        message = sign(self.key, "ledger", body)
        previous = self.head()
        hashed = hashlib.sha256(bytes.fromhex(previous) + canonical(message)).hexdigest()
        self.database.execute("INSERT INTO events(previous,hash,message) VALUES(?,?,?)", (previous, hashed, canonical(message).decode()))
        return hashed


class Server(socketserver.ThreadingTCPServer):
    allow_reuse_address = True
    daemon_threads = True

    def get_request(self):
        connection, address = super().get_request()
        connection.settimeout(10)
        try:
            return self.context.wrap_socket(connection, server_side=True), address
        except BaseException:
            connection.close()
            raise


class Handler(socketserver.BaseRequestHandler):
    def handle(self):
        store = self.server.store
        try:
            uri, fingerprint, certified_key = peer(self.request)
            actor = uri.removeprefix("urn:public-audit:")
            with store.lock:
                if store.poisoned:
                    raise RuntimeError("SOURCE_RECOVERY_REQUIRED")
                if store.anchor:
                    store.require_current_anchor()
                registered = store.database.execute("SELECT fingerprint,public FROM keys WHERE actor=?", (actor,)).fetchone()
                if not registered or registered[0] != fingerprint:
                    send(self.request, sign(store.key, "error", {"code": "KEY_REVOKED"}))
                    return
                if certified_key.public_bytes_raw().hex() != registered[1]:
                    raise ValueError("CERTIFICATE_KEY_BINDING")
                state = store.source_state()
                seq_row = store.database.execute("SELECT seq FROM sequences WHERE actor=?", (actor,)).fetchone()
                challenge = {"source": store.config["source"], "stream": store.config.get("stream",store.config["source"]), "actor": actor, "nonce": secrets.token_hex(32),
                             "seq": seq_row[0] + 1 if seq_row else 1, "cut": state["cut"],
                             "epoch": state["version"], "expires": time.time() + 30}
            send(self.request, sign(store.key, "challenge", challenge))
            message = receive(self.request)
            kind = message["kind"]
            if kind not in {"audit", "rotate", "lookup", "native-response", "energy-renewal", "energy-audit", "energy-continuation", "energy-handoff", "source-extension", "energy-regeneration", "material-extension", "energy-material", "productive-extension", "energy-productive", "arrival-extension", "energy-arrival", "donor-extension", "energy-donor"}:
                raise ValueError("REQUEST_KIND")
            body = verify(certified_key, kind, message)
            if any(body.get(field) != challenge[field] for field in ("source", "stream", "actor", "nonce", "seq", "cut", "epoch", "expires")):
                raise ValueError("CHALLENGE_BINDING")
            if time.time() > challenge["expires"]:
                raise ValueError("CHALLENGE_EXPIRED")
            with store.lock:
                if store.poisoned:
                    raise RuntimeError("SOURCE_RECOVERY_REQUIRED")
                if kind == "lookup":
                    current_key = store.database.execute("SELECT fingerprint FROM keys WHERE actor=?",(actor,)).fetchone()
                    if not current_key or current_key[0] != fingerprint:
                        raise ValueError("KEY_REVOKED")
                    if store.anchor:
                        store.require_current_anchor()
                    result = store.lookup(actor, body["lookup_id"])
                    if store.config.get('donor_result_codec'):
                        from donor_result_codec import enabled,encode_result
                        result=encode_result(result,admitted=enabled(store.config))
                    send(self.request, sign(store.key, "lookup-response", {"request": digest(message), "result": result}))
                    return
                db = store.database
                db.execute("BEGIN IMMEDIATE")
                source_may_have_advanced = False
                publication_attempted = False
                anchor_receipt = None
                try:
                    current_key = db.execute("SELECT fingerprint FROM keys WHERE actor=?", (actor,)).fetchone()
                    current_seq = db.execute("SELECT seq FROM sequences WHERE actor=?", (actor,)).fetchone()
                    if current_key[0] != fingerprint:
                        raise ValueError("KEY_REVOKED")
                    if body["seq"] != (current_seq[0] + 1 if current_seq else 1):
                        raise ValueError("STALE_SEQUENCE")
                    if db.execute("SELECT 1 FROM used WHERE nonce=? OR request_id=?", (body["nonce"], body["request_id"])).fetchone():
                        raise ValueError("REPLAY")
                    if kind == "audit":
                        if store.source_state().get('energy_scope'):
                            raise ValueError('NATIVE_ENERGY_QUERY_REQUIRED')
                        if store.source_state().get('native_scope_required'):
                            raise ValueError('NATIVE_NEW_SCOPE_REQUIRED')
                        state = store.backend.call({"op": "inspect"})
                        if state["cut"] != body["cut"] or state["version"] != body["epoch"] or state["actor"] != int(actor):
                            raise ValueError("SOURCE_EPOCH_OR_IDENTITY")
                        query = body["query"]
                        if set(query) != {"slots", "fields"} or any(type(query[k]) is not int for k in query) or not 0 <= query["slots"] < 64 or not 0 <= query["fields"] < 4:
                            raise ValueError("QUERY_MASK")
                        record = store.backend.call({"op": "preview", "cut": state["cut"], "query": query})
                        verify_disclosure(record)
                        event = {"type": "disclosure", "source": store.config["source"], "stream": store.config.get("stream",store.config["source"]), "record": record,
                                 "request": message, "peer": fingerprint}
                        if "registration" in body:
                            from governance import produce,rows_of
                            event=produce(store.config,rows_of(db),event)
                    elif kind == "native-response":
                        state=store.source_state()
                        if state.get('native_scope_required'):
                            raise ValueError('NATIVE_NEW_SCOPE_REQUIRED')
                        if state['cut']!=body['cut'] or state['version']!=body['epoch']:
                            raise ValueError('NATIVE_SOURCE_CURRENT')
                        from governance import produce,rows_of
                        event=produce(store.config,rows_of(db),{'type':'native-response','source':store.config['source'],
                          'stream':store.config['stream'],'request':message,'peer':fingerprint})
                    elif kind == 'source-extension':
                        from source_extension import produce
                        from governance import rows_of
                        event=produce(store.config,rows_of(db),{'type':kind,'source':store.config['source'],
                          'stream':store.config['stream'],'request':message,'peer':fingerprint})
                    elif kind in {'donor-extension','energy-donor'}:
                        from donor_arrival_live import produce
                        from governance import rows_of
                        event=dict(type=kind,source=store.config['source'],stream=store.config['stream'],request=message,peer=fingerprint)
                        if kind=='energy-donor':event['scope']=body['scope']
                        event=produce(store.config,rows_of(db),event)
                    elif kind == 'arrival-extension':
                        from arrival_extension import produce
                        from governance import rows_of
                        event=produce(store.config,rows_of(db),{'type':kind,'source':store.config['source'],
                          'stream':store.config['stream'],'request':message,'peer':fingerprint})
                    elif kind == 'energy-arrival':
                        from arrival_regeneration import produce
                        from governance import rows_of
                        event=produce(store.config,rows_of(db),{'type':kind,'source':store.config['source'],
                          'stream':store.config['stream'],'request':message,'peer':fingerprint,'scope':body['scope']})
                    elif kind == 'productive-extension':
                        from productive_extension import produce
                        from governance import rows_of
                        event=produce(store.config,rows_of(db),{'type':kind,'source':store.config['source'],
                          'stream':store.config['stream'],'request':message,'peer':fingerprint})
                    elif kind == 'energy-productive':
                        from productive_regeneration import produce
                        from governance import rows_of
                        event=produce(store.config,rows_of(db),{'type':kind,'source':store.config['source'],
                          'stream':store.config['stream'],'request':message,'peer':fingerprint,'scope':body['scope']})
                    elif kind == 'material-extension':
                        from material_extension import produce
                        from governance import rows_of
                        event=produce(store.config,rows_of(db),{'type':kind,'source':store.config['source'],
                          'stream':store.config['stream'],'request':message,'peer':fingerprint})
                    elif kind == 'energy-material':
                        from material_regeneration import produce
                        from governance import rows_of
                        event=produce(store.config,rows_of(db),{'type':kind,'source':store.config['source'],
                          'stream':store.config['stream'],'request':message,'peer':fingerprint,'scope':body['scope']})
                    elif kind == 'energy-regeneration':
                        from regeneration import produce
                        from governance import rows_of
                        event=produce(store.config,rows_of(db),{'type':kind,'source':store.config['source'],
                          'stream':store.config['stream'],'request':message,'peer':fingerprint,'scope':body['scope']})
                    elif kind == 'energy-continuation':
                        from continuation import produce
                        from governance import rows_of
                        event=produce(store.config,rows_of(db),{'type':kind,'source':store.config['source'],
                          'stream':store.config['stream'],'request':message,'peer':fingerprint,'scope':body['scope']})
                    elif kind == 'energy-handoff':
                        from handoff import produce
                        from governance import rows_of
                        event=produce(store.config,rows_of(db),{'type':kind,'source':store.config['source'],
                          'stream':store.config['stream'],'request':message,'peer':fingerprint,'scope':body['scope']})
                    elif kind in {'energy-renewal','energy-audit'}:
                        from energy import produce,scope_id
                        from governance import rows_of
                        prefix=rows_of(db)
                        scope=scope_id(store.config,body['parent'],body['candidate']) if kind=='energy-renewal' else body['scope']
                        event=produce(store.config,prefix,{'type':kind,'source':store.config['source'],
                          'stream':store.config['stream'],'request':message,'peer':fingerprint,'scope':scope})
                    else:
                        rotation = body["rotation"]
                        expected = store.config["registry"]["rotated2"]
                        if actor != "2" or rotation != expected:
                            raise ValueError("ROTATION_IDENTITY")
                        proof = body["new_signature"]
                        verify(Ed25519PublicKey.from_public_bytes(bytes.fromhex(rotation["app"])), "new-key", proof)
                        if proof["body"] != {"challenge": digest(challenge), "rotation": rotation}:
                            raise ValueError("NEW_KEY_POSSESSION")
                        db.execute("UPDATE keys SET fingerprint=?,public=? WHERE actor=?", (rotation["fingerprint"], rotation["app"], actor))
                        event = {"type": "rotation", "source": store.config["source"], "stream": store.config.get("stream",store.config["source"]), "request": message,
                                 "old": fingerprint, "new": rotation}
                    head = store.append(event)
                    accepted_id = db.execute("SELECT max(id) FROM events").fetchone()[0]
                    db.execute("INSERT INTO used VALUES(?,?,?,?)", (body["nonce"], body["request_id"], actor, body["seq"]))
                    db.execute("INSERT INTO sequences VALUES(?,?) ON CONFLICT(actor) DO UPDATE SET seq=excluded.seq", (actor, body["seq"]))
                    if kind == "audit":
                        source_may_have_advanced = True
                        actual = store.backend.call({"op": "advance", "cut": state["cut"], "query": query})
                        if actual != record:
                            raise RuntimeError("SOURCE_COMMIT_MISMATCH")
                    if store.anchor:
                        entry = db.execute("SELECT id,previous,message FROM events ORDER BY id DESC LIMIT 1").fetchone()
                        publication_attempted = True
                        if "anchors" in store.config:
                            store.save_pending(entry[0],entry[1],json.loads(entry[2]))
                        anchor_receipt = store.anchor.append(entry[0],entry[1],json.loads(entry[2]))
                        db.execute("INSERT INTO anchor_receipts VALUES(?,?)", (entry[0],canonical(anchor_receipt).decode()))
                    db.execute("COMMIT")
                    if "anchors" in store.config:
                        store.clear_pending()
                except BaseException:
                    if db.in_transaction:
                        db.execute("ROLLBACK")
                    if publication_attempted:
                        store.poisoned = True
                    elif source_may_have_advanced:
                        store.rollback_source_cache()
                    raise
            response = store.response_for(accepted_id)
            if store.config.get('donor_result_codec'):
                from donor_result_codec import enabled,encode_result
                response=encode_result(response,admitted=enabled(store.config))
            send(self.request, sign(store.key, "response", response))
        except Exception as error:
            if store.poisoned:
                code = "ANCHOR_COMMITTED_RECOVERY_REQUIRED" if locals().get("anchor_receipt") else "ANCHOR_RECONCILIATION_REQUIRED"
            else:
                code = str(error) if isinstance(error,(ValueError,KeyError,TypeError)) else type(error).__name__
            detail = {"code": code}
            if locals().get("anchor_receipt"):
                detail.update(anchor=anchor_receipt, request=digest(message))
            send(self.request, sign(store.key, "error", detail))



def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("config", type=Path)
    parser.add_argument("--recover-from-anchor", action="store_true")
    args = parser.parse_args()
    config = json.loads(args.config.read_text())
    config["recover_from_anchor"] = args.recover_from_anchor
    def stop(_signal, _frame):
        raise SystemExit(0)
    signal.signal(signal.SIGTERM, stop)
    store = Store(config)
    try:
        with Server(("127.0.0.1", 0), Handler) as server:
            server.store = store
            server.context = tls_context(Path(config["pki"]) / "server", server=True)
            print(json.dumps({"port": server.server_address[1], "source": config["source"]}), flush=True)
            server.serve_forever(poll_interval=0.1)
    finally:
        store.backend.close()
        store.database.close()
        from governance import close_readers
        close_readers()
        from energy import close_readers as close_energy_readers
        close_energy_readers()


if __name__ == "__main__":
    main()
