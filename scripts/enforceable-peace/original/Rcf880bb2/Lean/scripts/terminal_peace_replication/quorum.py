"""Recover and advance one original prefix using independent fresh evidence."""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import secrets
import subprocess

from terminal_peace_admission import INVALID_PROOF, _key
from terminal_peace_worker import _digest, _json
from crypto import sign, verify

from .protocol import (BOOT, BOOT_AUTH, QUORUM, STATUS, STORED, Block, Timeline, boot_point,
                       certified_signers, compare, initial_members, legacy, require)
from .replica import status_point, stored_point
from . import rounds

BAD_REPLY = (*INVALID_PROOF, IndexError, RuntimeError, OSError, subprocess.SubprocessError)


class Quorum:
    def __init__(self, admission, version, original, peers):
        self.admission = admission
        self.version = version
        self.original = original
        self.peers = peers

    def timeline(self, bundle, native=None):
        return Timeline(bundle, self.admission, self.version, self.original, native)

    def collect(self, names, op, check, **payload):
        available = sorted(set(names) & self.peers.keys())

        def call(name):
            try:
                return check(name, self.peers[name]({"op": op, **payload}))
            except BAD_REPLY:
                return None

        with ThreadPoolExecutor(max_workers=8) as pool:
            return {name: value for name, value in zip(available, pool.map(call, available)) if value is not None}

    def bootstrap(self, prefix, current, key):
        members = initial_members(self.admission)
        point = boot_point(prefix, self.admission, current)

        def check(name, receipt):
            if verify(_key(members[name]), BOOT, receipt) == point:
                return receipt

        owner = sign(key, BOOT_AUTH, point)
        votes = self.collect(members, "bootstrap", check, prefix=prefix, owner=owner)
        require(votes.keys(), members, 4, "bootstrap", head=current.head)
        result = self.timeline({"bootstrap": {"cursor": current.cursor, "owner": owner, "votes": votes}, "prefix": prefix})
        self.store(result)
        return result

    def _observations(self):
        nonce = secrets.token_hex(32)

        def check(name, result):
            evidence = result["evidence"]
            if (set(evidence) - {"rounds"} != {"key", "fence", "bootstrap", "bundle", "pending"}
                    or set(evidence["fence"]) != {"cursor", "head"}
                    or type(evidence["fence"]["cursor"]) is not int):
                return None
            point = status_point(self.admission, name, nonce, evidence)
            if verify(_key(evidence["key"]), STATUS, result["receipt"]) != point:
                return None
            view = self.timeline(evidence["bundle"]) if evidence["bundle"] is not None else None
            return evidence, view

        return self.collect(self.peers, "status", check, challenge=nonce)

    def _recover_bootstrap(self, observations):
        members = initial_members(self.admission)
        groups = {}
        for name, (evidence, _) in observations.items():
            boot = evidence["bootstrap"]
            if boot is None or members.get(name) != evidence["key"]:
                continue
            try:
                prefix = boot["prefix"]
                current = legacy(prefix, self.admission, self.version, self.original)
                point = boot_point(prefix, self.admission, current)
                if (verify(_key(members[name]), BOOT, boot["receipt"]) != point
                        or verify(self.admission.owner, BOOT_AUTH, boot["owner"]) != point):
                    continue
            except BAD_REPLY:
                continue
            _, _, votes = groups.setdefault(_digest(point), (prefix, boot["owner"], {}))
            votes[name] = boot["receipt"]
        if not groups:
            raise Block("no-independent-original-transcript", observed=sorted(observations),
                        missing=sorted(members.keys() - observations.keys()))
        prefix, owner, votes = max(groups.values(), key=lambda group: len(group[2]))
        require(votes.keys(), members, 4, "recover-bootstrap")
        return self.timeline({"bootstrap": {"cursor": len(prefix["rows"]), "owner": owner, "votes": votes}, "prefix": prefix})

    def _pending(self, evidence, timeline, name):
        if evidence["fence"]["cursor"] <= timeline.current.cursor:
            return None
        pending = evidence["pending"]
        if pending is None:
            raise Block("signed-fence-missing-original-intent", member=name, **evidence["fence"])
        proposal = timeline.candidate(pending["intent"])
        eligible = timeline.members if proposal.ordered else timeline.permitted(proposal)
        if (eligible.get(name) != evidence["key"]
                or evidence["fence"] != {"cursor": proposal.successor.cursor, "head": proposal.successor.head}
                or verify(_key(evidence["key"]), proposal.vote_kind, pending["vote"]) != proposal.point):
            raise Block("invalid-independent-intent", member=name)
        return proposal, {"vote": pending["vote"], "ready_proof": pending.get("ready", {})}

    @staticmethod
    def _absorb(timeline, proposal, evidence, name, entry):
        old, new = timeline.members, proposal.incoming or {}
        voters = old if proposal.ordered else timeline.permitted(proposal)
        for field, keys, kind, target in (
            ("vote", voters, proposal.vote_kind, evidence.votes), ("ready", new, rounds.READY, evidence.ready),
            ("no_decision", old, rounds.NO_DECISION, evidence.no_decision),
            ("no_ready", new, rounds.NO_READY, evidence.no_ready),
        ):
            if field in entry:
                certified_signers({name: entry[field]}, keys, kind, proposal.point)
                target[name] = entry[field]
        if proposal.ordered and "vote" in entry:
            ready = entry.get("ready_proof", {})
            timeline.verify_ready(proposal, ready)
            evidence.ready.update(ready)
        if "order" in entry:
            order = entry["order"]
            timeline.resolution_terms(proposal, order)
            if evidence.order is not None and evidence.order != order:
                raise Block("competing-resolution-orders", id=proposal.request["id"])
            evidence.order = order

    @staticmethod
    def _merge(retained, found, request_id):
        if found.order is not None:
            if retained.order is not None and retained.order != found.order:
                raise Block("competing-resolution-orders", id=request_id)
            retained.order = found.order
        retained.votes.update(found.votes)
        retained.ready.update(found.ready)
        retained.no_decision.update(found.no_decision)
        retained.no_ready.update(found.no_ready)

    def latest(self):
        observations = self._observations()
        timeline = None
        for _, view in observations.values():
            if view is not None and (timeline is None or compare(view, timeline) > 0):
                timeline = view
        if timeline is None:
            timeline = self._recover_bootstrap(observations)
        fresh, holding, pending, failures, responders = set(), set(), {}, {}, {}
        for name, (evidence, view) in observations.items():
            try:
                entries = []
                vote = self._pending(evidence, timeline, name)
                if vote is not None:
                    entries.append(vote)
                if view is not None and view.current.head == timeline.current.head:
                    for entry in evidence.get("rounds", []):
                        proposal = timeline.candidate(entry["intent"])
                        if timeline.permitted(proposal).get(name) == evidence["key"]:
                            entries.append((proposal, entry))
                verified = []
                for proposal, entry in entries:
                    found = rounds.Evidence()
                    self._absorb(timeline, proposal, found, name, entry)
                    verified.append((proposal, found))
            except BAD_REPLY as error:
                failures[name] = error.code if isinstance(error, Block) else "invalid-independent-intent"
                continue
            for proposal, found in verified:
                _, retained = pending.setdefault(proposal.successor.head, (proposal, rounds.Evidence()))
                self._merge(retained, found, proposal.request["id"])
            responders[name] = evidence["key"]
            if timeline.members.get(name) == evidence["key"]:
                fresh.add(name)
                if view is not None and view.current.head == timeline.current.head:
                    holding.add(name)
        require(fresh, timeline.members, QUORUM, "fresh-current-roster", head=timeline.current.head,
                epoch=timeline.epoch, invalid=failures)
        disposed = {item["head"] for proposal, _ in pending.values() for item in proposal.closed}
        pending = {head: value for head, value in pending.items() if head not in disposed}
        if len(pending) > 1:
            raise Block("competing-original-intents", head=timeline.current.head,
                        ids=sorted(p.request["id"] for p, _ in pending.values()))
        proposal, evidence = next(iter(pending.values()), (None, rounds.Evidence()))
        evidence.responders = responders
        return timeline, holding, (proposal, evidence)

    def store(self, timeline, previous=None):
        nonce = secrets.token_hex(32)
        eligible = {**(previous or {}), **timeline.members}

        def check(name, receipt):
            if verify(_key(eligible[name]), STORED, receipt) == stored_point(timeline, name, nonce):
                return receipt

        stored = self.collect(eligible, "store", check, bundle=timeline.bundle, challenge=nonce)
        require(stored.keys(), timeline.members, QUORUM, "durable-current-prefix", head=timeline.current.head)
        if previous is not None:
            require(stored.keys(), previous, QUORUM, "durable-outgoing-prefix", head=timeline.current.head)
        return stored

    def _matching(self, proposal, eligible, kind, name, receipt):
        if _json(verify(_key(eligible[name]), kind, receipt)) == _json(proposal.point):
            return receipt

    def _commit(self, timeline, proposal, evidence):
        timeline.verify_votes(proposal, evidence.votes, evidence.ready)
        result = self.timeline(timeline.extended(proposal.row(evidence.votes, evidence.ready)))
        self.store(result, previous=timeline.members if proposal.incoming is not None else None)
        return result

    def choose(self, timeline, proposal, recovered):
        evidence = recovered if isinstance(recovered, rounds.Evidence) else rounds.Evidence(votes=recovered)
        eligible = timeline.members if proposal.ordered else timeline.permitted(proposal)
        payload = {"bundle": timeline.bundle, "intent": proposal.intent}
        incoming = proposal.incoming or {}
        if proposal.ordered and incoming and len(evidence.ready) < 4:
            staged = self.collect(eligible, "stage", lambda name, receipt:
                                  self._matching(proposal, eligible, rounds.STAGE, name, receipt), **payload)
            require(staged.keys(), eligible, QUORUM, "durable-handoff-intent", id=proposal.request["id"])
            evidence.ready.update(self.collect(incoming.keys() - evidence.ready.keys(), "ready",
                                  lambda name, receipt: self._matching(proposal, incoming, rounds.READY, name, receipt), **payload))
        if proposal.ordered:
            timeline.verify_ready(proposal, evidence.ready)
            payload["ready"] = evidence.ready
        received = self.collect(eligible.keys() - evidence.votes.keys(), "prepare",
                                lambda name, receipt: self._matching(proposal, eligible, proposal.vote_kind, name, receipt), **payload)
        evidence.votes.update(received)
        return self._commit(timeline, proposal, evidence)

    def _already_chosen(self, timeline, proposal, evidence):
        try:
            timeline.verify_votes(proposal, evidence.votes, evidence.ready)
        except Block as error:
            if error.code == "missing-verifier-evidence":
                return None
            raise
        if rounds.possible_completion(timeline.members, proposal.incoming or {},
                                      evidence.no_decision.keys(), evidence.no_ready.keys()) is None:
            raise Block("contradictory-handoff-evidence", id=proposal.request["id"])
        return self._commit(timeline, proposal, evidence)

    def resolve(self, timeline, proposal, evidence, order):
        chosen = self._already_chosen(timeline, proposal, evidence)
        if chosen is not None:
            return chosen, None
        timeline.resolution_terms(proposal, order)
        if evidence.order is not None and evidence.order != order:
            raise Block("original-resolution-order-already-retained", id=proposal.request["id"])
        eligible = timeline.permitted(proposal)
        old, new = timeline.members, proposal.incoming or {}
        if rounds.possible_completion(old, new, evidence.no_decision.keys(), evidence.no_ready.keys()) is None:
            return None, timeline.resolved(proposal, order, evidence.no_decision, evidence.no_ready)
        # An irreversible seal must have a possible use. When even every
        # reachable unvoted role would leave a completion, preserve its vote.
        reachable = {name for name, key in eligible.items() if evidence.responders.get(name) == key}
        decisions = evidence.no_decision.keys() | ((old.keys() & reachable) - evidence.votes.keys())
        already_ready = evidence.ready.keys() if proposal.ordered else evidence.votes.keys()
        readiness = evidence.no_ready.keys() | ((new.keys() & reachable) - already_ready)
        if rounds.possible_completion(old, new, decisions, readiness) is not None:
            timeline.exclusion(proposal, evidence.no_decision, evidence.no_ready)

        def check(name, entry):
            if timeline.candidate(entry["intent"]).successor.head != proposal.successor.head or entry["order"] != order:
                return None
            found = rounds.Evidence()
            self._absorb(timeline, proposal, found, name, entry)
            return found

        sealed = self.collect(eligible, "seal", check, bundle=timeline.bundle, intent=proposal.intent, order=order)
        for item in sealed.values():
            self._merge(evidence, item, proposal.request["id"])
        chosen = self._already_chosen(timeline, proposal, evidence)
        if chosen is not None:
            return chosen, None
        return None, timeline.resolved(proposal, order, evidence.no_decision, evidence.no_ready)
