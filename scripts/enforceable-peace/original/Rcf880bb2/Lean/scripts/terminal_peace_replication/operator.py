"""Materialize the independently recovered source in the original primary journal."""

from __future__ import annotations

from contextlib import closing
import json
import sqlite3

from terminal_peace_anchor import _snapshot
from terminal_peace_submit import _save_intent, _sync_parent
from terminal_peace_worker import _initialize, _json, _rows, _transaction, _unique_keys
from crypto import sign

from .protocol import QUORUM, Block, legacy
from . import rounds


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
        if request_id in timeline.disposed:
            disposition = timeline.disposed[request_id]
            row = disposition["row"]
            return {"kind": "handoff-withdrawn" if disposition["replacement_roster"] is None else "handoff-reassigned",
                    "id": request_id, "unselected_head": disposition["head"], "resolved_by": row[1],
                    "current": dict(json.loads(row[4]), head=row[5])}
        row = timeline.ids[request_id]
        return dict(json.loads(row[4]), head=row[5])

    def _pending(self, timeline, independent, votes):
        if not self.intent.exists():
            return independent, votes
        intent = json.loads(self.intent.read_text(), object_pairs_hook=_unique_keys)
        name = rounds.request_id(intent)
        if name in timeline.ids or name in timeline.disposed:
            if name in timeline.disposed:
                entry = timeline.disposed[name]
                authorization, row = entry["authorization"], entry["row"]
            else:
                row = timeline.ids[name]
                saved = json.loads(row[6] or "{}")
                authorization = rounds.final_authorization(saved["intent"]) if "intent" in saved else None
            if authorization != rounds.final_authorization(intent) or _json(json.loads(row[4])) != _json(intent["record"]):
                raise Block("committed-original-id-disagrees-with-local-intent", id=name)
            self._clear()
            return independent, votes
        local = timeline.candidate(intent)
        if independent is not None and local.successor.head != independent.successor.head:
            if any(item["head"] == local.successor.head for item in independent.closed):
                return independent, votes
            if any(item["head"] == independent.successor.head for item in local.closed):
                return local, rounds.Evidence(responders=votes.responders)
            raise Block("competing-original-intents", head=timeline.current.head,
                        ids=[name, independent.request["id"]])
        return local, votes

    def _finish(self, timeline, pending, evidence, order=None):
        if not self.intent.exists() or json.loads(self.intent.read_text()) != pending.intent:
            _save_intent(self.intent, pending.intent)
        order = order or evidence.order
        chosen = None
        if order is not None:
            chosen, replacement = self.quorum.resolve(timeline, pending, evidence, order)
            if replacement is not None:
                _save_intent(self.intent, replacement.intent)
                pending, evidence = replacement, rounds.Evidence()
        if chosen is None:
            chosen = self.quorum.choose(timeline, pending, evidence)
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

    def _sync(self):
        timeline, holding, (proposal, votes) = self.quorum.latest()
        if len(holding) < QUORUM:
            self.quorum.store(timeline)
        self.install(timeline)
        pending, votes = self._pending(timeline, proposal, votes)
        return timeline, pending, votes

    def recover(self, expected=None, lookup=None):
        timeline, pending, votes = self._sync()
        name = expected[0] if expected is not None else lookup
        if name in timeline.ids or name in timeline.disposed:
            return timeline, None
        if pending is not None:
            disposed = next((item for item in pending.closed if item["id"] == name), None)
            if expected is not None and disposed is not None:
                self._check_request({"id": name, "event": "due", "parent": pending.request["parent"]},
                                    disposed["proposed_roster"], expected)
            elif expected is not None:
                self._check_request(pending.request, pending.incoming, expected)
            if lookup is not None and pending.request["id"] != lookup and disposed is None:
                raise Block("resume-original-id", id=pending.request["id"], requested=lookup)
            chosen = self._finish(timeline, pending, votes)
            return chosen, chosen.bundle["prefix"]["rows"][-1][1]
        return timeline, None

    def resolve(self, name, replacement_id, incoming, key):
        timeline, pending, evidence = self._sync()
        if name in timeline.ids or name in timeline.disposed:
            return self.read_result(timeline, name)
        if pending is None:
            raise Block("original-handoff-unattested", id=name, head=timeline.current.head)
        if pending.request["id"] != name:
            if (any(item["id"] == name for item in pending.closed) and
                    (pending.request["id"], pending.incoming) == (replacement_id, incoming)):
                return self.read_result(self._finish(timeline, pending, evidence), name)
            raise Block("resume-original-id", id=pending.request["id"], requested=name)
        order = sign(key, rounds.ORDER, timeline.resolution_order(pending, replacement_id, incoming))
        return self.read_result(self._finish(timeline, pending, evidence, order), name)

    def submit(self, name, event, incoming, key):
        expected = name, event, incoming
        timeline, _ = self.recover(expected=expected)
        if name in timeline.disposed:
            disposition = timeline.disposed[name]
            self._check_request({"id": name, "event": "due", "parent": disposition["row"][2]},
                                disposition["proposed_roster"], expected)
            return self.read_result(timeline, name)
        if name in timeline.ids:
            row = timeline.ids[name]
            proof = json.loads(row[6] or "{}")
            terms = rounds.final_authorization(proof["intent"])["body"] if "intent" in proof else {}
            self._check_request({"id": row[1], "parent": row[2], "event": row[3]}, terms.get("incoming"), expected)
            return self.read_result(timeline, name)
        request = {"op": "submit", "id": name, "parent": timeline.current.head, "event": event}
        with self.open_native() as (native, _):
            active = self.quorum.timeline(timeline.bundle, native)
            proposal = active.propose(native, request, incoming, key, ordered=True)
        chosen = self._finish(timeline, proposal, rounds.Evidence())
        return self.read_result(chosen, name)
