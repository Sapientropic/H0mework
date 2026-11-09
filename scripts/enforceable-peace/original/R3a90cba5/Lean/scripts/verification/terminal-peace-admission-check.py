"""Exercise the signed worker with separate native verifiers and ephemeral keys."""

from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
from copy import deepcopy
import json
from pathlib import Path
import sqlite3
import subprocess
import sys
from tempfile import TemporaryDirectory

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives.serialization import Encoding, NoEncryption, PrivateFormat

ROOT = Path(__file__).resolve().parents[2]
SCRIPTS = ROOT / "scripts"
WORKER = [sys.executable, "-B", str(SCRIPTS / "living_law_runtime.py"),
          "--terminal-peace", "--worker", "--state"]
ANCHOR = [sys.executable, "-B", str(SCRIPTS / "terminal_peace_anchor.py")]
INSPECT = {"op": "inspect"}
sys.path.insert(0, str(SCRIPTS))
from terminal_peace_submit import submit


def run(command, value=None):
    return subprocess.run(command, cwd=ROOT, input=json.dumps(value), text=True,
                          capture_output=True, timeout=130)


def read(result):
    assert result.returncode == 0, result.stderr
    return json.loads(result.stdout)


@contextmanager
def worker(state, policy=None):
    argv = WORKER + [str(state)]
    if policy:
        argv += ["--admission", str(policy)]
    with subprocess.Popen(argv, cwd=ROOT, text=True, stdin=subprocess.PIPE,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE) as process:
        def call(value):
            process.stdin.write(json.dumps(value) + "\n")
            process.stdin.flush()
            line = process.stdout.readline()
            assert line, process.stderr.read()
            return json.loads(line)

        try:
            yield call
        finally:
            process.stdin.close()
            assert process.wait(timeout=130) == 0, process.stderr.read()


def request(prior, name, event):
    return {"op": "submit", "parent": prior["head"], "id": name, "event": event}


def check(path):
    db, policy = path / "original.sqlite", path / "policy.json"
    with worker(db) as call:
        current = call(INSPECT)
        for i, event in enumerate(["advance"] * 4 + ["review", "advance", "due", "due"]):
            current = call(request(current, f"prefix-{i}", event))
    assert current["kind"] == "due-awaiting-evidence" and current["clock"] == "10"
    # Exercise adoption of a journal stored before certificate metadata existed.
    with sqlite3.connect(db) as connection:
        connection.execute("ALTER TABLE source DROP COLUMN admission")
        connection.execute("ALTER TABLE inputs DROP COLUMN certificate")
    snap = ANCHOR + ["snapshot", "--state", str(db)]
    prefix = read(run(snap))
    assert len(prefix["rows"]) == 8 and prefix["rows"][-1][5] == current["head"]
    members = "abcd"
    keys = {}
    for name in members + "o":
        private = Ed25519PrivateKey.generate()
        key_path = path / f"{name}.key"
        key_path.write_bytes(private.private_bytes(Encoding.PEM, PrivateFormat.PKCS8, NoEncryption()))
        key_path.chmod(0o600)
        keys[name] = private.public_key().public_bytes_raw().hex()
    settings = {"source": current["source"], "version": prefix["version"],
                "compiler": subprocess.check_output(["lean", "--githash"], cwd=ROOT, text=True).strip(),
                "checkpoint": {field: current[field] for field in ("cursor", "head")},
                "owner": keys.pop("o"), "members": keys}
    policy.write_text(json.dumps(settings))

    def cmd(operation, member):
        argv = ANCHOR + [operation, "--policy", str(policy), "--key", str(path / f"{member}.key")]
        if operation != "authorize":
            argv += ["--member", member, "--fence", str(path / f"{member}.sqlite")]
        return argv

    for member in members:
        initialized = run(cmd("initialize", member))
        assert initialized.returncode == 0, initialized.stderr

    def argument(value):
        return {"prefix": read(run(snap)), "owner": read(run(cmd("authorize", "o"), value))}

    def certify(value, selected=members):
        envelope = argument(value)
        with ThreadPoolExecutor(max_workers=4) as pool:
            votes = list(pool.map(lambda m: read(run(cmd("vote", m), envelope)), selected))
        record = votes[0]["record"]
        assert all(item["record"] == record for item in votes)
        return dict(value, certificate={"record": record, "owner": envelope["owner"],
                                        "votes": {item["member"]: item["vote"] for item in votes}})

    evidence = request(current, "delayed-revision", "evidence")
    unsigned = argument(evidence)
    unsigned["owner"]["signature"] = "AA=="
    assert "rejected" in run(cmd("vote", "a"), unsigned).stderr
    altered = argument(evidence)
    altered["prefix"]["rows"][-1][2] = "f" * 64
    assert "invalid original parent" in run(cmd("vote", "a"), altered).stderr
    rejected = run(cmd("vote", "a"), argument(request(current, "premature-review", "review")))
    assert rejected.returncode != 0 and "inadmissible-event" in rejected.stderr
    certified = certify(evidence)
    competing = run(cmd("vote", "a"), argument(request(current, "competing-due", "due")))
    assert competing.returncode != 0 and "already fenced" in competing.stderr

    with worker(db, policy) as call:
        assert call(INSPECT) == current
        assert call(evidence)["error"] == "invalid-request"
        short = deepcopy(certified)
        short["certificate"]["votes"].pop("d")
        assert call(short)["error"] == "uncertified-input"
        repeated = deepcopy(certified)
        repeated["certificate"]["votes"]["d"] = repeated["certificate"]["votes"]["a"]
        assert call(repeated)["error"] == "uncertified-input"
        assert call(dict(certified, id="other-id"))["error"] == "uncertified-input"
        revised = call(certified)
        assert revised["kind"] == "u8-written" and revised["clock"] == "10"
        assert revised["remaining"] == "0" and revised["address"] == current["address"]
        assert call(short) == revised
    assert "pinned online policy" in run(WORKER + [str(db)], INSPECT).stderr

    with worker(db, policy) as call:
        assert call(INSPECT) == revised
        assert call(certified) == revised
        due = certify(request(revised, "due-after-restart", "due"), "abc")
        only_two = deepcopy(due)
        only_two["certificate"]["votes"].pop("c")
        assert call(only_two)["error"] == "uncertified-input"
        renewed = call(due)
        assert renewed["kind"] == "due-renewed" and renewed["clock"] == "11"
        assert renewed["address"] == revised["address"] and renewed["remaining"] == "0"
        restored = certify(request(renewed, "due-with-returned-node", "due"), "abd")
        assert call(restored)["clock"] == "12"
    assert read(run(snap))["rows"][:8] == prefix["rows"]

    def deliver(name, selected):
        voters = {m: lambda envelope, m=m: read(run(cmd("vote", m), envelope)) for m in selected}
        return submit(db, policy, path / "o.key", name, "due", voters)

    try:
        deliver("with-retry", "ab")
    except ValueError as error:
        assert "quorum unavailable" in str(error)
    else:
        raise AssertionError("two voters authorized a renewal")
    try:
        deliver("conflicting-intent", "abcd")
    except ValueError as error:
        assert "existing terminal-peace intent" in str(error)
    else:
        raise AssertionError("a second intent replaced the unresolved signed input")
    continued = deliver("with-retry", "abc")
    assert continued["kind"] == "due-renewed" and continued["clock"] == "13"
    assert deliver("with-retry", "") == continued

    with sqlite3.connect(db) as connection:
        connection.execute("UPDATE inputs SET certificate=NULL WHERE seq=9")
    assert "missing an online certificate" in run(WORKER + [str(db), "--admission", str(policy)], INSPECT).stderr


if __name__ == "__main__":
    with TemporaryDirectory(prefix="terminal-peace-admission-") as work:
        check(Path(work))
    print("Four native verifiers admit the exact old head; delayed U8, three-vote renewal and recovery verified")
