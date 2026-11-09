"""Fault-schedule regression with a deterministic native hook and real durable signers."""

from contextlib import closing, contextmanager
from functools import partial
import json
from pathlib import Path
import sqlite3
import sys
from tempfile import TemporaryDirectory

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from terminal_peace_admission import Admission
from terminal_peace_anchor import _fence, _snapshot
from terminal_peace_worker import SOURCE, _Committed, _initialize
from terminal_peace_replication import rounds
from terminal_peace_replication.operator import Primary
from terminal_peace_replication.protocol import Block, certified_signers
from terminal_peace_replication.quorum import Quorum
from terminal_peace_replication.replica import Replica
from crypto import sign


def blocked(code, call, phase=None):
    try:
        call()
    except Block as error:
        assert error.code == code and (phase is None or error.details["phase"] == phase), str(error)
        return error.details
    raise AssertionError(f"expected {code}")


def check(path):
    record = dict(source=SOURCE, cursor=0, kind="due-renewed", clock="20", remaining="0",
                  address=dict(birth=2, item=0, victim=False, payer=True, good=False))
    original, version, compiler = _Committed(record, "a" * 64), "b" * 64, "c" * 40

    @contextmanager
    def open_native():
        cursor = 0

        def native(request):
            nonlocal cursor
            assert request == {"op": "submit", "cursor": cursor, "event": "due"}
            cursor += 1
            return dict(record, cursor=cursor, clock=str(20 + cursor))

        yield native, original

    state, policy = path / "original.sqlite", path / "policy.json"
    with closing(sqlite3.connect(state)) as db:
        _initialize(db, version, original)
        db.commit()
    keys = {name: Ed25519PrivateKey.generate() for name in "abcdefgo"}
    public = {name: key.public_key().public_bytes_raw().hex() for name, key in keys.items()}

    def roster(names):
        return {name: public[name] for name in names}

    policy.write_text(json.dumps(dict(source=SOURCE, version=version, compiler=compiler, owner=public["o"],
                                      members=roster("abcd"), checkpoint=dict(cursor=0, head=original.head))))
    admission = Admission(policy, version, compiler)
    replicas = {name: Replica(path / f"{name}.sqlite", admission, name, key, version, original)
                for name, key in keys.items() if name != "o"}
    for name, replica in replicas.items():
        if name in "abcd":
            _fence(replica.path, admission, name)
        else:
            replica.enroll()

    def rpc(name, request):
        replica, op = replicas[name], request["op"]
        if op == "status":
            return replica.status(request["challenge"])
        with open_native() as (native, _):
            if op == "bootstrap":
                return replica.bootstrap(request["prefix"], request["owner"], native)
            bundle = request["bundle"]
            if op == "store":
                return replica.store(bundle, native, request["challenge"])
            intent = request["intent"]
            if op == "prepare":
                return replica.prepare(bundle, intent, native, request.get("ready"))
            if op == "seal":
                return replica.seal(bundle, intent, request["order"], native)
            return {"ready": replica.ready, "stage": replica.stage}[op](bundle, intent, native)

    quorum = Quorum(admission, version, original, {})
    writer = Primary(state, quorum, open_native)
    owner = keys["o"]

    def reach(names):
        quorum.peers = {name: partial(rpc, name) for name in names}

    def tip():
        return _snapshot(state)["rows"][-1][5]

    def offer(name, names):
        return writer.submit(name, "due", roster(names), owner)

    reach("abcd")
    original_tip = writer.bootstrap(owner)
    with open_native() as (native, _):
        view = quorum.timeline(original_tip.bundle, native)
        old = view.propose(native, dict(op="submit", id="legacy-handoff", parent=view.current.head, event="due"),
                           roster("abce"), owner)
    votes = quorum.collect("a", "prepare", lambda _, r: r, bundle=view.bundle, intent=old.intent)
    assert set(votes) == {"a"} and not old.ordered
    adopted = writer.resolve("legacy-handoff", "activate", None, owner)
    assert adopted["kind"] == "handoff-withdrawn"
    baseline = adopted["current"]
    absence = blocked("missing-verifier-evidence", lambda: offer("missing-e", "abce"), "incoming-native-replay")
    assert absence["missing"] == ["e"] and tip() == baseline["head"]
    timeline, _, (pending, evidence) = quorum.latest()
    assert not evidence.votes
    order = sign(owner, rounds.ORDER, timeline.resolution_order(pending, "withdraw-e", None))
    chosen, replacement = quorum.resolve(timeline, pending, evidence, order)
    assert chosen is None and replacement is not None
    late = rpc("e", {"op": "ready", "bundle": timeline.bundle, "intent": pending.intent})
    old_ready = {**evidence.ready, "e": late}
    blocked("missing-verifier-evidence", lambda: quorum.choose(timeline, pending, rounds.Evidence(ready=old_ready)),
            "original-roster")
    writer.intent.unlink()
    recovered, _ = writer.recover(lookup="missing-e")
    disposed = writer.read_result(recovered, "missing-e")
    assert disposed["kind"] == "handoff-withdrawn" and disposed["resolved_by"] == "withdraw-e"
    assert disposed["current"]["clock"] == "22" and recovered.members == roster("abcd")

    blocked("missing-verifier-evidence", lambda: offer("first-alternative", "abce"), "incoming-native-replay")
    blocked("missing-verifier-evidence", lambda: writer.resolve("first-alternative", "second-alternative", roster("abcf"), owner),
            "incoming-native-replay")
    reach("abcdg")
    result = writer.resolve("second-alternative", "final-alternative", roster("abcg"), owner)
    assert result["kind"] == "handoff-reassigned" and result["current"]["clock"] == "23"
    timeline, _ = writer.recover(lookup="first-alternative")
    assert writer.read_result(timeline, "first-alternative")["resolved_by"] == "final-alternative"
    assert timeline.members == roster("abcg")

    reach("abcfg")
    with open_native() as (native, _):
        timeline = quorum.timeline(timeline.bundle, native)
        pending = timeline.propose(native, dict(op="submit", id="already-chosen", parent=timeline.current.head, event="due"),
                                   roster("abcf"), owner, ordered=True)
    payload = {"bundle": timeline.bundle, "intent": pending.intent}
    ready = quorum.collect("abcf", "ready", lambda _, r: r, **payload)
    decisions = quorum.collect("abc", "prepare", lambda _, r: r, ready=ready, **payload)
    assert len(decisions) == 3
    reach("acfg")
    missing = blocked("original-handoff-outcome-undetermined", lambda: writer.resolve("already-chosen", "would-withdraw", None, owner))
    assert len(missing["possible"]["outgoing"]) == 3 and tip() == result["current"]["head"]
    _, _, (_, stalled) = quorum.latest()
    assert stalled.order is None and not stalled.no_decision
    reach("abcfg")
    same = writer.resolve("already-chosen", "would-withdraw", None, owner)
    assert same == pending.successor.reply() and same["clock"] == "24"
    assert len(_snapshot(state)["rows"]) == 4

    latest, _ = writer.recover()
    with open_native() as (native, _):
        view = quorum.timeline(latest.bundle, native)
        next_handoff = view.propose(native, dict(op="submit", id="fresh-e", parent=view.current.head, event="due"),
                                    roster("abce"), owner, ordered=True)
    blocked("verifier-signed-different-occurrence",
            lambda: certified_signers({"e": late}, roster("abce"), rounds.READY, next_handoff.point))
    reach("abcef")
    payload = {"bundle": view.bundle, "intent": next_handoff.intent}
    ready = quorum.collect("abce", "ready", lambda _, r: r, **payload)
    voted = quorum.collect("a", "prepare", lambda _, r: r, ready=ready, **payload)
    assert set(voted) == {"a"}
    paid = writer.resolve("fresh-e", "withdraw-single-vote", None, owner)
    assert paid["kind"] == "handoff-withdrawn" and paid["current"]["clock"] == "25"
    proof = json.loads(_snapshot(state)["rows"][-1][6])
    assert "a" in proof["votes"] and proof["intent"]["rounds"][-1]["no_decision"].keys() >= set("bcf")
    latest, _ = writer.recover()
    with open_native() as (native, _):
        view = quorum.timeline(latest.bundle, native)
        two = view.propose(native, dict(op="submit", id="two-live-votes", parent=view.current.head, event="due"),
                           roster("abce"), owner, ordered=True)
    payload = {"bundle": view.bundle, "intent": two.intent}
    ready = quorum.collect("abce", "ready", lambda _, r: r, **payload)
    voted = quorum.collect("ab", "prepare", lambda _, r: r, ready=ready, **payload)
    assert set(voted) == set("ab")
    blocked("original-handoff-outcome-undetermined", lambda: writer.resolve("two-live-votes", "would-seal", None, owner))
    _, _, (_, undecided) = quorum.latest()
    assert not undecided.no_decision and undecided.order is None
    recovered, _ = writer.recover(lookup="two-live-votes")
    assert writer.read_result(recovered, "two-live-votes") == two.successor.reply()
    successor = writer.submit("next-paid", "due", None, owner)
    assert successor["address"] == record["address"] and successor["clock"] == "27"


if __name__ == "__main__":
    with TemporaryDirectory(prefix="terminal-peace-handoff-") as scratch:
        check(Path(scratch))
    print("Sealed withdrawal, late readiness, repeated reassignment and hidden selection verified")
