"""Validate the original transcript, the chosen input, and its active roster."""

from __future__ import annotations

from dataclasses import dataclass
import json

from terminal_peace_admission import _key
from terminal_peace_worker import (
    IDENTIFIER, _Committed, _commit, _digest, _evaluate, _json, _record, _replay, _valid_submit,
)
from crypto import sign, verify
from . import rounds

BOOT = "terminal-peace-replica-bootstrap/v1"
BOOT_AUTH = "terminal-peace-replica-bootstrap-owner/v1"
OWNER = "terminal-peace-replica-input/v1"
VOTE = "terminal-peace-replica-chosen/v1"
STATUS = "terminal-peace-replica-status/v1"
STORED = "terminal-peace-replica-stored/v1"
QUORUM = 3


class Block(ValueError):
    def __init__(self, code, **details):
        self.code = code
        self.details = details
        super().__init__(_json({"error": code, **details}))


def initial_members(admission):
    return {name: key.public_bytes_raw().hex() for name, key in admission.members.items()}


def legacy(prefix, admission, version, original, native=None):
    if (set(prefix) != {"version", "genesis", "rows"} or prefix["version"] != version
            or _json(prefix["genesis"]) != _json(original.reply())):
        raise Block("foreign-original-source")
    ids = [row[1] for row in prefix["rows"]]
    if len(set(ids)) != len(ids):
        raise Block("repeated-original-id")
    current = _replay(prefix["rows"], native, original, admission)
    if current.cursor <= admission.checkpoint["cursor"]:
        admission.bind(current)
    return current


def boot_point(prefix, admission, current):
    return {"policy": admission.identity, "cut": current.reply(), "transcript": _digest(prefix)}


def roster(value, known, owner):
    if (not isinstance(value, dict) or len(value) != 4
            or any(not IDENTIFIER.fullmatch(name) for name in value)):
        raise Block("invalid-incoming-roster")
    reverse = {key: name for name, key in known.items()}
    for name, key in value.items():
        _key(key)
        if (key == owner or (name in known and known[name] != key)
                or (key in reverse and reverse[key] != name)):
            raise Block("verifier-identity-reused", member=name)
    if len(set(value.values())) != 4:
        raise Block("invalid-incoming-roster")
    return value


def certified_signers(votes, members, kind, point):
    if not isinstance(votes, dict) or not votes.keys() <= members.keys():
        raise Block("unknown-verifier")
    for name, receipt in votes.items():
        if _json(verify(_key(members[name]), kind, receipt)) != _json(point):
            raise Block("verifier-signed-different-occurrence", member=name)
    return votes.keys()


def require(names, members, minimum, phase, **fields):
    present = names & members.keys()
    if len(present) < minimum:
        raise Block("missing-verifier-evidence", phase=phase, required=minimum,
                    present=sorted(present), missing=sorted(members.keys() - names), **fields)


@dataclass(frozen=True)
class Proposal:
    intent: dict
    request: dict
    successor: _Committed
    incoming: dict | None
    point: dict
    ordered: bool = False
    closed: tuple = ()

    @property
    def vote_kind(self):
        return rounds.DECISION if self.ordered else VOTE

    def row(self, votes, ready=None):
        result = self.successor
        proof = {"intent": self.intent, "votes": votes}
        if self.ordered:
            proof["ready"] = ready or {}
        return [result.cursor, self.request["id"], self.request["parent"], self.request["event"],
                _json(result.record), result.head, _json(proof)]


class Timeline:
    def __init__(self, bundle, admission, version, original, native=None):
        if set(bundle) != {"bootstrap", "prefix"}:
            raise Block("missing-replica-bootstrap")
        prefix, boot = bundle["prefix"], bundle["bootstrap"]
        cut = boot["cursor"]
        if (set(boot) != {"cursor", "owner", "votes"} or type(cut) is not int
                or not admission.checkpoint["cursor"] <= cut <= len(prefix["rows"])):
            raise Block("invalid-replica-bootstrap-cut")
        base = {**prefix, "rows": prefix["rows"][:cut]}
        self.current = legacy(base, admission, version, original, native)
        self.members = initial_members(admission)
        self.known = dict(self.members)
        self.admission = admission
        self.owner = admission.owner.public_bytes_raw().hex()
        self.original = original
        point = boot_point(base, admission, self.current)
        if _json(verify(admission.owner, BOOT_AUTH, boot["owner"])) != _json(point):
            raise Block("wrong-original-bootstrap-authorization", head=self.current.head)
        votes = certified_signers(boot["votes"], self.members, BOOT, point)
        require(votes, self.members, 4, "bootstrap", head=self.current.head)
        self.bootstrap = _digest(point)
        self.epoch = self.bootstrap
        self.ids = {row[1]: row for row in base["rows"]}
        self.disposed = {}
        self.ordered = False
        self.bundle = bundle
        for row in prefix["rows"][cut:]:
            self.apply(row, native)

    def authorization(self, request, incoming, record=None):
        terms = {"bootstrap": self.bootstrap, "epoch": self.epoch, "request": request, "incoming": incoming}
        if record is not None:
            terms["native"] = _digest(record)
        return terms

    def _proposal(self, intent, request, incoming, owner, ordered, closed):
        if not _valid_submit(request) or request["parent"] != self.current.head:
            raise Block("wrong-original-parent-or-epoch", head=self.current.head, epoch=self.epoch)
        if request["id"] in self.ids or request["id"] in self.disposed or any(
                item["id"] == request["id"] for item in closed):
            raise Block("original-id-already-disposed", id=request["id"])
        if incoming is not None:
            roster(incoming, self.known, self.owner)
            if incoming == self.members or request["event"] != "due":
                raise Block("handoff-requires-new-roster-and-native-due", id=request["id"])
        record = _record(intent["record"], self.current.cursor + 1)
        terms = {"kind": owner["kind"], "body": owner["body"]} if ordered else owner["body"]
        successor = _commit(self.current.head, request["id"], request["event"], record, terms)
        point = {"epoch": self.epoch, "intent": _digest([owner, record] if ordered else intent),
                 "parent": self.current.reply(), "next": successor.reply()}
        return Proposal(intent, request, successor, incoming, point, ordered, closed)

    def candidate(self, intent):
        if set(intent) not in ({"owner", "record"}, {"owner", "record", "rounds"}):
            raise Block("invalid-original-intent")
        owner = intent["owner"]
        staged = owner["kind"] == rounds.OWNER
        if self.ordered and not staged:
            raise Block("retired-handoff-protocol", epoch=self.epoch)
        terms = verify(self.admission.owner, rounds.OWNER if staged else OWNER, owner)
        request, incoming = terms["request"], terms["incoming"]
        if _json(terms) != _json(self.authorization(request, incoming, intent["record"] if staged else None)):
            raise Block("wrong-original-parent-or-epoch", head=self.current.head, epoch=self.epoch)
        base = {"owner": owner, "record": intent["record"]}
        proposal = self._proposal(base, request, incoming, owner, staged, ())
        history = intent.get("rounds", [])
        if not isinstance(history, list) or ("rounds" in intent and not history):
            raise Block("invalid-handoff-dispositions")
        for i, disposition in enumerate(history):
            if set(disposition) != {"order", "no_decision", "no_ready"}:
                raise Block("invalid-handoff-disposition")
            self.exclusion(proposal, disposition["no_decision"], disposition["no_ready"])
            order = disposition["order"]
            terms = self.resolution_terms(proposal, order)
            request = dict(op="submit", parent=self.current.head, id=terms["id"], event="due")
            closed = (*proposal.closed, {"id": proposal.request["id"], "head": proposal.successor.head,
                      "authorization": rounds.final_authorization(proposal.intent), "proposed_roster": proposal.incoming})
            proposal = self._proposal({**base, "rounds": history[:i + 1]}, request, terms["incoming"], order, True, closed)
        return proposal

    def resolution_order(self, proposal, name, incoming):
        return {"bootstrap": self.bootstrap, "epoch": self.epoch, "parent": self.current.head,
                "target": proposal.successor.head, "id": name, "incoming": incoming}

    def resolution_terms(self, proposal, order):
        terms = verify(self.admission.owner, rounds.ORDER, order)
        name, incoming = terms["id"], terms["incoming"]
        if (proposal.incoming is None or not isinstance(name, str) or not IDENTIFIER.fullmatch(name)
                or name in self.ids or name in self.disposed or name == proposal.request["id"]
                or any(item["id"] == name for item in proposal.closed)
                or _json(terms) != _json(self.resolution_order(proposal, name, incoming))):
            raise Block("invalid-original-resolution-order", id=proposal.request["id"])
        if incoming is not None:
            roster(incoming, self.known, self.owner)
            if incoming in (self.members, proposal.incoming):
                raise Block("reassignment-requires-different-roster", id=name)
        return terms

    def exclusion(self, proposal, no_decision, no_ready):
        old = certified_signers(no_decision, self.members, rounds.NO_DECISION, proposal.point)
        new = certified_signers(no_ready, proposal.incoming or {}, rounds.NO_READY, proposal.point)
        possible = rounds.possible_completion(self.members, proposal.incoming or {}, old, new)
        if possible is not None:
            raise Block("original-handoff-outcome-undetermined", id=proposal.request["id"], head=self.current.head,
                        possible=possible, missing_decision_seals=sorted(self.members.keys() - old),
                        missing_ready_seals=sorted((proposal.incoming or {}).keys() - new))

    def resolved(self, proposal, order, no_decision, no_ready):
        intent = proposal.intent
        disposition = dict(order=order, no_decision=no_decision, no_ready=no_ready)
        return self.candidate({**intent, "rounds": [*intent.get("rounds", []), disposition]})

    def evaluate(self, native, proposal):
        actual, error = _evaluate(native, self.current, proposal.request)
        if error or _json(actual.record) != _json(proposal.successor.record):
            raise Block("native-write-disagrees", id=proposal.request["id"], head=self.current.head)

    def propose(self, native, request, incoming, key, ordered=False):
        if not _valid_submit(request):
            raise Block("invalid-original-input")
        actual, error = _evaluate(native, self.current, request)
        if error:
            raise Block("native-input-rejected", id=request["id"], reason=error)
        tag = rounds.OWNER if ordered or self.ordered else OWNER
        terms = self.authorization(request, incoming, actual.record if tag == rounds.OWNER else None)
        intent = {"owner": sign(key, tag, terms), "record": actual.record}
        return self.candidate(intent)

    def permitted(self, proposal):
        return {**self.members, **(proposal.incoming or {})}

    def verify_ready(self, proposal, ready):
        if proposal.incoming is not None:
            names = certified_signers(ready, proposal.incoming, rounds.READY, proposal.point)
            require(names, proposal.incoming, 4, "incoming-native-replay", id=proposal.request["id"], head=self.current.head)
        elif ready:
            raise Block("unexpected-incoming-readiness")

    def verify_votes(self, proposal, votes, ready=None):
        eligible = self.members if proposal.ordered else self.permitted(proposal)
        names = certified_signers(votes, eligible, proposal.vote_kind, proposal.point)
        fields = {"id": proposal.request["id"], "head": self.current.head}
        require(names, self.members, QUORUM, "original-roster", **fields)
        if proposal.ordered:
            self.verify_ready(proposal, ready or {})
        elif proposal.incoming is not None:
            require(names, proposal.incoming, 4, "incoming-native-replay", **fields)

    def apply(self, row, native):
        proof = json.loads(row[6])
        proposal = self.candidate(proof["intent"])
        ready = proof.get("ready")
        if list(row) != proposal.row(proof["votes"], ready):
            raise Block("literal-source-row-mismatch", id=proposal.request["id"])
        self.verify_votes(proposal, proof["votes"], ready)
        if native is not None:
            self.evaluate(native, proposal)
        self.ids[proposal.request["id"]] = row
        for closed in proposal.closed:
            self.disposed[closed["id"]] = {**closed, "row": row, "replacement_roster": proposal.incoming}
        self.ordered |= proposal.ordered
        self.current = proposal.successor
        if proposal.incoming is not None:
            self.members = proposal.incoming
            self.known.update(self.members)
            self.epoch = self.current.head

    def extended(self, row):
        prefix = self.bundle["prefix"]
        return {**self.bundle, "prefix": {**prefix, "rows": [*prefix["rows"], row]}}


def compare(left, right):
    """Compare verified histories by original occurrence, independent of vote packaging."""
    if left.bootstrap != right.bootstrap:
        raise Block("different-replica-bootstrap")
    a, b = left.bundle["prefix"]["rows"], right.bundle["prefix"]["rows"]
    for x, y in zip(a, b):
        if x[5] != y[5]:
            raise Block("certified-original-fork", cursor=x[0], first=x[5], second=y[5])
    return len(a) - len(b)
