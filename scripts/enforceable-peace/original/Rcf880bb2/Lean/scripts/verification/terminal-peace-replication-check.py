"""Exercise lost and stale primaries, unknown results, and disjoint roster handoff."""

from __future__ import annotations

from contextlib import closing
from functools import partial
import json
import os
from pathlib import Path
import shutil
import sqlite3
import sys
from tempfile import TemporaryDirectory

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
from living_law_runtime import TERMINAL_PEACE_BACKEND, terminal_peace_command
from terminal_peace_admission import Admission, compiler_revision
from terminal_peace_anchor import _fence, _snapshot
from terminal_peace_worker import _consume, _initialize, _open_native, _source_version
from terminal_peace_replication.operator import Primary
from terminal_peace_replication.protocol import Block
from terminal_peace_replication.quorum import Quorum
from terminal_peace_replication.replica import Replica


def expect(code, action, phase=None):
    try:
        action()
    except Block as error:
        assert error.code == code and (phase is None or error.details["phase"] == phase), str(error)
        return error.details
    raise AssertionError(f"expected {code}")


def check(path):
    version = _source_version(ROOT, Path(TERMINAL_PEACE_BACKEND))
    library = Path(sys.argv[1]) if len(sys.argv) > 1 else None
    command = terminal_peace_command(ROOT, 120, library) + ["--live"]
    native_open = partial(_open_native, command, ROOT, version, 120)
    state = path / "original.sqlite"
    with native_open() as (native, origin), closing(sqlite3.connect(state, isolation_level=None)) as db:
        _initialize(db, version, origin)
        current = origin
        for i, event in enumerate(["advance"] * 4 + ["review", "advance", "evidence"]):
            current, _ = _consume(db, native, current, dict(op="submit", parent=current.head, id=f"old-{i}", event=event), None)
    original = current.reply()
    assert original["kind"] == "u8-written" and original["remaining"] == "0"
    keys = {m: Ed25519PrivateKey.generate() for m in "abcdefgho"}
    public = {m: k.public_key().public_bytes_raw().hex() for m, k in keys.items()}
    policy = path / "policy.json"
    members = {m: public[m] for m in "abcd"}
    new = {m: public[m] for m in "efgh"}
    policy.write_text(json.dumps(dict(source=original["source"], version=version,
        compiler=compiler_revision(ROOT, 120), checkpoint={"cursor": current.cursor, "head": current.head},
        owner=public["o"], members=members)))
    admission = Admission(policy, version, compiler_revision(ROOT, 120))
    replicas = {m: Replica(path / f"{m}.sqlite", admission, m, keys[m], version, origin) for m in "abcdefgh"}
    for m in members:
        _fence(replicas[m].path, admission, m)
    for m in new:
        replicas[m].enroll()

    def rpc(m, request):
        replica, op = replicas[m], request["op"]
        if op == "status":
            return replica.status(request["challenge"])
        with native_open() as (native, _):
            if op == "bootstrap":
                return replica.bootstrap(request["prefix"], request["owner"], native)
            if op == "prepare":
                return replica.prepare(request["bundle"], request["intent"], native, request.get("ready"))
            if op == "stage":
                return replica.stage(request["bundle"], request["intent"], native)
            if op == "ready":
                return replica.ready(request["bundle"], request["intent"], native)
            return replica.store(request["bundle"], native, request["challenge"])

    directory = {m: partial(rpc, m) for m in replicas}
    quorum = Quorum(admission, version, origin, {m: directory[m] for m in members})
    writer = Primary(state, quorum, native_open)
    base = writer.bootstrap(keys["o"])
    assert base.current.reply() == original
    old = path / "rollback.sqlite"
    shutil.copy2(state, old)

    def proposal(timeline, name):
        with native_open() as (native, _):
            active = quorum.timeline(timeline.bundle, native)
            return active.propose(native, dict(op="submit", parent=active.current.head, id=name, event="due"), None, keys["o"])

    staged = proposal(base, "prepared-unknown")
    prepared = quorum.collect("abc", "prepare", lambda _, vote: vote, bundle=base.bundle, intent=staged.intent)
    assert set(prepared) == set("abc")
    os.unlink(state)
    stale = replicas["b"].status("0" * 64)
    quorum.peers = {**{m: directory[m] for m in "ad"}, "b": lambda _: stale}
    lack = expect("missing-verifier-evidence", writer.recover, "fresh-current-roster")
    assert lack["missing"] == ["b", "c"] and not state.exists()
    quorum.peers = {m: directory[m] for m in "abd"}
    expect("resume-original-id", lambda: writer.submit("different-id", "due", None, keys["o"]))
    renewed, resumed = writer.recover(lookup="prepared-unknown")
    assert resumed == "prepared-unknown" and renewed.current.head == staged.successor.head
    assert writer.submit(resumed, "due", None, keys["o"]) == renewed.current.reply()
    next_input = proposal(renewed, "chosen-before-local-commit")
    votes = quorum.collect("abd", "prepare", lambda _, vote: vote, bundle=renewed.bundle, intent=next_input.intent)
    chosen = quorum.timeline(renewed.extended(next_input.row(votes)))
    stored = quorum.collect("a", "store", lambda _, receipt: receipt, bundle=chosen.bundle, challenge="1" * 64)
    assert set(stored) == {"a"}
    assert _snapshot(state)["rows"][-1][5] == renewed.current.head
    os.replace(old, state)
    quorum.peers = {m: directory[m] for m in "abc"}
    recovered, resumed = writer.recover(lookup="chosen-before-local-commit")
    assert resumed is None and recovered.current.head == chosen.current.head

    quorum.peers = {m: directory[m] for m in "abcdefg"}
    lack = expect("missing-verifier-evidence", lambda: writer.submit("actual-handoff", "due", new, keys["o"]),
                  "incoming-native-replay")
    assert lack["missing"] == ["h"] and _snapshot(state)["rows"][-1][5] == chosen.current.head
    quorum.peers = directory
    handoff = writer.submit("actual-handoff", "due", new, keys["o"])
    assert handoff["address"] == original["address"] and handoff["remaining"] == "0"
    quorum.peers = {m: directory[m] for m in members}
    expect("missing-verifier-evidence", writer.recover, "fresh-current-roster")
    quorum.peers = {m: directory[m] for m in "efg"}
    os.unlink(state)
    after, _ = writer.recover()
    assert after.current.reply() == handoff and after.members == new and after.epoch == handoff["head"]
    expect("verifier-outside-current-or-incoming-roster", lambda: rpc("a", {
        "op": "prepare", "bundle": after.bundle, "intent": proposal(after, "new-only").intent,
    }))
    next_paid = writer.submit("after-handoff", "due", None, keys["o"])
    assert int(next_paid["clock"]) == int(original["clock"]) + 4
    assert next_paid["address"] == original["address"] and next_paid["remaining"] == "0"
    assert len(_snapshot(state)["rows"]) == original["cursor"] + 4


if __name__ == "__main__":
    with TemporaryDirectory(prefix="terminal-peace-replication-") as directory:
        check(Path(directory))
    print("Original cold recovery, pending and chosen IDs, disjoint handoff and named blocks verified")
