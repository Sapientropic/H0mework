"""Recover and advance one original prefix using independent fresh evidence."""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import secrets
import subprocess

from terminal_peace_admission import INVALID_PROOF, _key
from terminal_peace_worker import _digest, _json
from crypto import sign, verify

from .protocol import (BOOT, BOOT_AUTH, QUORUM, STATUS, STORED, VOTE, Block, Timeline, boot_point,
                       compare, initial_members, legacy, require)
from .replica import status_point, stored_point

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
            if (set(evidence) != {"key", "fence", "bootstrap", "bundle", "pending"}
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
        if (timeline.permitted(proposal).get(name) != evidence["key"]
                or evidence["fence"] != {"cursor": proposal.successor.cursor, "head": proposal.successor.head}
                or verify(_key(evidence["key"]), VOTE, pending["vote"]) != proposal.point):
            raise Block("invalid-independent-intent", member=name)
        return proposal, pending["vote"]

    def latest(self):
        observations = self._observations()
        timeline = None
        for _, view in observations.values():
            if view is not None and (timeline is None or compare(view, timeline) > 0):
                timeline = view
        if timeline is None:
            timeline = self._recover_bootstrap(observations)
        fresh, holding, pending, failures = set(), set(), {}, {}
        for name, (evidence, view) in observations.items():
            try:
                vote = self._pending(evidence, timeline, name)
            except BAD_REPLY as error:
                failures[name] = error.code if isinstance(error, Block) else "invalid-independent-intent"
                continue
            if timeline.members.get(name) == evidence["key"]:
                fresh.add(name)
                if view is not None and view.current.head == timeline.current.head:
                    holding.add(name)
            if vote is not None:
                proposal, receipt = vote
                _, signed = pending.setdefault(proposal.successor.head, (proposal, {}))
                signed[name] = receipt
        require(fresh, timeline.members, QUORUM, "fresh-current-roster", head=timeline.current.head,
                epoch=timeline.epoch, invalid=failures)
        if len(pending) > 1:
            raise Block("competing-original-intents", head=timeline.current.head,
                        ids=sorted(p.request["id"] for p, _ in pending.values()))
        return timeline, holding, next(iter(pending.values()), (None, {}))

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

    def choose(self, timeline, proposal, recovered_votes):
        eligible = timeline.permitted(proposal)

        def check(name, receipt):
            if _json(verify(_key(eligible[name]), VOTE, receipt)) == _json(proposal.point):
                return receipt

        received = self.collect(eligible.keys() - recovered_votes.keys(), "prepare", check,
                                bundle=timeline.bundle, intent=proposal.intent)
        votes = {**recovered_votes, **received}
        timeline.verify_votes(proposal, votes)
        result = self.timeline(timeline.extended(proposal.row(votes)))
        self.store(result, previous=timeline.members if proposal.incoming is not None else None)
        return result
