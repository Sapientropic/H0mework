"""Materialize the independently recovered source in the original primary journal."""

from __future__ import annotations

from contextlib import closing
import json
import sqlite3

from terminal_peace_anchor import _snapshot
from terminal_peace_submit import _save_intent, _sync_parent
from terminal_peace_worker import _initialize, _json, _rows, _transaction, _unique_keys

from .protocol import QUORUM, Block, legacy


class Primary:
    def __init__(self, state, quorum, open_native):
        self.state = state
        self.intent = state.with_name(state.name + ".intent")
        self.quorum = quorum
        self.open_native = open_native

    def install(self, timeline):
        with self.open_native() as (native, original):
            checked = self.quorum.timeline(timeline.bundle, native)
            if checked.original != original:
                raise Block("foreign-native-genesis")
        path = self.state
        created = not path.exists()
        with closing(sqlite3.connect(path, isolation_level=None)) as db:
            db.execute("PRAGMA synchronous=FULL")
            with _transaction(db):
                _initialize(db, self.quorum.version, checked.original)
                if "replicated" not in {row[1] for row in db.execute("PRAGMA table_info(source)")}:
                    db.execute("ALTER TABLE source ADD COLUMN replicated TEXT")
                bound, boot = db.execute("SELECT admission, replicated FROM source WHERE one=1").fetchone()
                policy = self.quorum.admission.identity
                if bound not in (None, policy) or boot not in (None, checked.bootstrap):
                    raise Block("different-primary-binding")
                local, recovered = list(_rows(db)), timeline.bundle["prefix"]["rows"]
                if len(local) > len(recovered):
                    raise Block("primary-ahead-of-independent-evidence", cursor=local[-1][0], head=local[-1][5])
                for before, after in zip(local, recovered):
                    if list(before[:6]) != list(after[:6]):
                        raise Block("divergent-primary-row", cursor=before[0], local=before[5], signed=after[5])
                    if before[6] != after[6]:
                        db.execute("UPDATE inputs SET certificate=? WHERE seq=?", (after[6], after[0]))
                db.executemany("INSERT INTO inputs VALUES (?, ?, ?, ?, ?, ?, ?)", recovered[len(local):])
                db.execute("UPDATE source SET admission=?, replicated=? WHERE one=1", (policy, checked.bootstrap))
                db.execute("CREATE TRIGGER IF NOT EXISTS replicated_input_only BEFORE INSERT ON inputs "
                           "WHEN NEW.certificate IS NULL OR json_type(NEW.certificate, '$.intent') IS NULL "
                           "BEGIN SELECT RAISE(ABORT, 'signed replica input required'); END")
        if created:
            path.chmod(0o600)
            _sync_parent(path)

    def bootstrap(self, key):
        if self.intent.exists():
            raise Block("unresolved-legacy-intent")
        prefix = _snapshot(self.state)
        with self.open_native() as (native, original):
            current = legacy(prefix, self.quorum.admission, self.quorum.version, original, native)
        timeline = self.quorum.bootstrap(prefix, current, key)
        self.install(timeline)
        return timeline

    def _clear(self):
        self.intent.unlink()
        _sync_parent(self.intent)

    @staticmethod
    def read_result(timeline, request_id):
        row = timeline.ids[request_id]
        return dict(json.loads(row[4]), head=row[5])

    def _pending(self, timeline, independent, votes):
        if not self.intent.exists():
            return independent, votes
        intent = json.loads(self.intent.read_text(), object_pairs_hook=_unique_keys)
        name = intent["owner"]["body"]["request"]["id"]
        if name in timeline.ids:
            saved = json.loads(timeline.ids[name][6] or "{}")
            if _json(saved.get("intent")) != _json(intent):
                raise Block("committed-original-id-disagrees-with-local-intent", id=name)
            self._clear()
            return independent, votes
        local = timeline.candidate(intent)
        if independent is not None and local.successor.head != independent.successor.head:
            raise Block("competing-original-intents", head=timeline.current.head,
                        ids=[name, independent.request["id"]])
        return local, votes

    def _finish(self, timeline, pending, votes):
        if not self.intent.exists():
            _save_intent(self.intent, pending.intent)
        chosen = self.quorum.choose(timeline, pending, votes)
        self.install(chosen)
        self._clear()
        return chosen

    @staticmethod
    def _check_request(request, incoming, expected):
        name, event, roster = expected
        if request["id"] != name:
            raise Block("resume-original-id", id=request["id"], parent=request["parent"], requested=name)
        if request["event"] != event or incoming != roster:
            raise Block("original-id-has-different-terms", id=name, parent=request["parent"])

    def recover(self, expected=None, lookup=None):
        timeline, holding, (proposal, votes) = self.quorum.latest()
        if len(holding) < QUORUM:
            self.quorum.store(timeline)
        self.install(timeline)
        pending, votes = self._pending(timeline, proposal, votes)
        if pending is not None:
            if expected is not None:
                self._check_request(pending.request, pending.incoming, expected)
            if lookup is not None and pending.request["id"] != lookup:
                raise Block("resume-original-id", id=pending.request["id"], requested=lookup)
            return self._finish(timeline, pending, votes), pending.request["id"]
        return timeline, None

    def submit(self, name, event, incoming, key):
        expected = name, event, incoming
        timeline, _ = self.recover(expected=expected)
        if name in timeline.ids:
            row = timeline.ids[name]
            proof = json.loads(row[6] or "{}")
            terms = proof.get("intent", {}).get("owner", {}).get("body", {})
            self._check_request({"id": row[1], "parent": row[2], "event": row[3]}, terms.get("incoming"), expected)
            return self.read_result(timeline, name)
        request = {"op": "submit", "id": name, "parent": timeline.current.head, "event": event}
        with self.open_native() as (native, _):
            active = self.quorum.timeline(timeline.bundle, native)
            proposal = active.propose(native, request, incoming, key)
        chosen = self._finish(timeline, proposal, {})
        return self.read_result(chosen, name)
