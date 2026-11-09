"""A verifier retains original inputs and evidence in its existing fence file."""

from __future__ import annotations

from contextlib import closing, contextmanager
import json
import sqlite3

from terminal_peace_anchor import _fence
from terminal_peace_worker import HEAD, _digest, _json, _transaction
from crypto import sign, verify

from .protocol import BOOT, BOOT_AUTH, STATUS, STORED, VOTE, Block, Timeline, boot_point, compare, legacy


def status_point(admission, name, nonce, evidence):
    return {"policy": admission.identity, "member": name, "challenge": nonce, "evidence": _digest(evidence)}


def stored_point(timeline, name, nonce):
    return {"bootstrap": timeline.bootstrap, "epoch": timeline.epoch, "member": name,
            "challenge": nonce, "current": timeline.current.reply()}


def challenge(value):
    if not isinstance(value, str) or not HEAD.fullmatch(value):
        raise Block("invalid-verifier-challenge")
    return value


class Replica:
    def __init__(self, path, admission, member, key, version, original):
        self.path = path
        self.admission = admission
        self.member = member
        self.key = key
        self.public = key.public_key().public_bytes_raw().hex()
        self.version = version
        self.original = original

    @contextmanager
    def transaction(self, migrate=False):
        if not self.path.is_file():
            raise Block("verifier-fence-missing", member=self.member)
        uri = self.path.resolve().as_uri() + "?mode=rw"
        with closing(sqlite3.connect(uri, uri=True, isolation_level=None)) as db:
            db.execute("PRAGMA synchronous=FULL")
            with _transaction(db):
                identity = db.execute("SELECT policy, member, seq, head FROM fence").fetchall()
                if len(identity) != 1 or identity[0][:2] != (self.admission.identity, self.member):
                    raise Block("verifier-fence-identity", member=self.member)
                if migrate:
                    db.execute("CREATE TABLE IF NOT EXISTS replica (one INTEGER PRIMARY KEY CHECK(one=1), "
                               "key TEXT NOT NULL, seq INTEGER NOT NULL, head TEXT, "
                               "bootstrap TEXT, bundle TEXT, pending TEXT)")
                    db.execute("INSERT OR IGNORE INTO replica (one, key, seq, head) VALUES (1, ?, ?, ?)",
                               (self.public, *identity[0][2:]))
                    for operation in ("INSERT", "UPDATE", "DELETE"):
                        db.execute(f"CREATE TRIGGER IF NOT EXISTS frozen_original_fence_{operation} "
                                   f"BEFORE {operation} ON fence BEGIN "
                                   "SELECT RAISE(ABORT, 'original fence moved to signed replica protocol'); END")
                if not db.execute("SELECT 1 FROM sqlite_schema WHERE name='replica'").fetchone():
                    raise Block("verifier-not-yet-replicated", member=self.member)
                key, seq, head, boot, bundle, pending = db.execute(
                    "SELECT key, seq, head, bootstrap, bundle, pending FROM replica WHERE one=1"
                ).fetchone()
                if key != self.public:
                    raise Block("verifier-replica-key-changed", member=self.member)
                values = {name: json.loads(value) if value is not None else None for name, value in
                          (("bootstrap", boot), ("bundle", bundle), ("pending", pending))}
                yield db, values, seq, head

    def enroll(self):
        # Only a never-enrolled identity may be initialized without its old fence.
        if self.member in self.admission.members:
            raise Block("original-verifier-must-adopt-its-old-fence", member=self.member)
        _fence(self.path, self.admission, self.member)
        with self.transaction(migrate=True):
            pass

    def bootstrap(self, prefix, authorization, native):
        expected = self.admission.members.get(self.member)
        if expected is None or expected.public_bytes_raw().hex() != self.public:
            raise Block("bootstrap-needs-original-verifier", member=self.member)
        current = legacy(prefix, self.admission, self.version, self.original, native)
        point = boot_point(prefix, self.admission, current)
        if _json(verify(self.admission.owner, BOOT_AUTH, authorization)) != _json(point):
            raise Block("wrong-original-bootstrap-authorization", head=current.head)
        receipt = sign(self.key, BOOT, point)
        with self.transaction(migrate=True) as (db, stored, seq, head):
            if stored["bundle"] is not None:
                installed = self.timeline(stored["bundle"])
                if installed.bootstrap != _digest(point):
                    raise Block("bootstrap-already-installed", member=self.member, head=installed.current.head)
                return receipt
            if stored["bootstrap"] is not None:
                if _json(stored["bootstrap"]["receipt"]) != _json(receipt):
                    raise Block("bootstrap-already-fenced", member=self.member)
                return receipt
            if seq > current.cursor or (head is not None and prefix["rows"][seq - 1][5] != head):
                raise Block("uncovered-original-vote", member=self.member, cursor=seq, head=head)
            prepared = {"prefix": prefix, "owner": authorization, "receipt": receipt}
            db.execute("UPDATE replica SET bootstrap=? WHERE one=1", (_json(prepared),))
        return receipt

    def timeline(self, bundle, native=None):
        return Timeline(bundle, self.admission, self.version, self.original, native)

    def status(self, nonce):
        nonce = challenge(nonce)
        with self.transaction() as (_, stored, seq, head):
            evidence = {**stored, "fence": {"cursor": seq, "head": head}, "key": self.public}
            return {"evidence": evidence, "receipt": sign(self.key, STATUS,
                    status_point(self.admission, self.member, nonce, evidence))}

    def _install(self, db, stored, seq, incoming):
        bundle = incoming.bundle
        if stored["bootstrap"] is not None:
            point = stored["bootstrap"]["receipt"]["body"]
            if incoming.bootstrap != _digest(point):
                raise Block("bootstrap-already-fenced", member=self.member)
        if stored["bundle"] is not None:
            existing = self.timeline(stored["bundle"])
            if compare(incoming, existing) < 0:
                raise Block("verifier-already-has-newer-original", member=self.member, head=existing.current.head)
            rows = existing.bundle["prefix"]["rows"]
            prefix = bundle["prefix"]
            bundle = {**bundle, "prefix": {**prefix, "rows": rows + prefix["rows"][len(rows):]}}
        pending = stored["pending"] if seq > incoming.current.cursor else None
        db.execute("UPDATE replica SET bootstrap=NULL, bundle=?, pending=? WHERE one=1",
                   (_json(bundle), _json(pending) if pending is not None else None))

    def store(self, bundle, native, nonce):
        nonce = challenge(nonce)
        timeline = self.timeline(bundle, native)
        if timeline.known.get(self.member) != self.public:
            raise Block("verifier-has-no-signed-enrollment", member=self.member, epoch=timeline.epoch)
        with self.transaction() as (db, stored, seq, _):
            self._install(db, stored, seq, timeline)
        return sign(self.key, STORED, stored_point(timeline, self.member, nonce))

    def prepare(self, bundle, intent, native):
        timeline = self.timeline(bundle, native)
        proposal = timeline.candidate(intent)
        if timeline.permitted(proposal).get(self.member) != self.public:
            raise Block("verifier-outside-current-or-incoming-roster", member=self.member, epoch=timeline.epoch)
        timeline.evaluate(native, proposal)
        receipt = sign(self.key, VOTE, proposal.point)
        candidate = proposal.successor
        with self.transaction() as (db, stored, seq, head):
            if candidate.cursor < seq or (candidate.cursor == seq and head != candidate.head):
                raise Block("original-vote-already-fenced", member=self.member, cursor=seq, head=head)
            self._install(db, stored, seq, timeline)
            pending = _json({"intent": intent, "vote": receipt})
            db.execute("UPDATE replica SET seq=?, head=?, pending=? WHERE one=1",
                       (candidate.cursor, candidate.head, pending))
        return receipt
