"""Deliver a named input to the admitted terminal-peace worker and its verifiers."""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
import fcntl
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys

from living_law_runtime import TERMINAL_PEACE_BACKEND, terminal_peace_command
from terminal_peace_admission import Admission, INVALID_PROOF, OWNER, VOTE, compiler_revision
from terminal_peace_anchor import _key, _snapshot
from terminal_peace_worker import _evaluate, _json, _open_native, _replay, _source_version, _valid_submit
from crypto import sign, verify


ROOT = Path(__file__).resolve().parents[1]


@contextmanager
def _writer(state):
    with state.with_name(state.name + ".writer").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        yield


def _sync_parent(path):
    fd = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def _save_intent(path, intent):
    temp = path.with_suffix(".pending")
    fd = os.open(temp, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(fd, "w") as stream:
        stream.write(_json(intent))
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temp, path)
    _sync_parent(path)


def _call(argv, value, timeout):
    result = subprocess.run(argv, cwd=ROOT, input=_json(value) + "\n", capture_output=True,
                            text=True, timeout=timeout)
    if result.returncode:
        raise RuntimeError(result.stderr.strip() or "terminal-peace subprocess failed")
    return json.loads(result.stdout)


def _collect(admission, owner, current, candidate, prefix, voters):
    point = admission.point(current, owner, candidate)
    envelope = {"owner": owner, "prefix": prefix}

    def vote(member):
        try:
            result = voters[member](envelope)
            if (result["member"] == member and result["record"] == candidate.record
                    and verify(admission.members[member], VOTE, result["vote"]) == point):
                return result["vote"]
        except (*INVALID_PROOF, OSError, RuntimeError, subprocess.SubprocessError):
            pass
        return None

    with ThreadPoolExecutor(max_workers=4) as pool:
        replies = pool.map(vote, admission.members)
        return {member: receipt for member, receipt in zip(admission.members, replies) if receipt is not None}


def submit(state, policy, owner_key, request_id, event, voters, timeout=120, library=None):
    state = state.resolve(strict=True)
    policy = policy.resolve(strict=True)
    intent_path = state.with_name(state.name + ".intent")
    worker = [sys.executable, "-B", str(ROOT / "scripts/living_law_runtime.py"), "--terminal-peace", "--worker",
              "--state", str(state), "--admission", str(policy), "--timeout", str(timeout)]
    if library is not None:
        worker.extend(["--library", str(library.resolve(strict=True))])
    version = _source_version(ROOT, Path(TERMINAL_PEACE_BACKEND))
    admission = Admission(policy, version, compiler_revision(ROOT, timeout))
    key = _key(owner_key, admission.owner)
    with _writer(state):
        observed = _call(worker, {"op": "inspect"}, timeout)
        prefix = _snapshot(state)
        snapshot_head = prefix["rows"][-1][5] if prefix["rows"] else prefix["genesis"]["head"]
        if snapshot_head != observed["head"]:
            raise ValueError("terminal-peace prefix moved while preparing the input")
        intent = json.loads(intent_path.read_text()) if intent_path.exists() else None
        if intent and (intent["request"]["id"], intent["request"]["event"]) != (request_id, event):
            raise ValueError("resume the existing terminal-peace intent before proposing another input")
        for _, name, _, recorded_event, record, head, certificate in prefix["rows"]:
            if name == request_id:
                if certificate is None or recorded_event != event:
                    raise ValueError("request identifier already belongs to a different original input")
                if intent and json.loads(certificate)["owner"] != intent["owner"]:
                    raise ValueError("committed input does not match the outstanding intent")
                if intent:
                    intent_path.unlink()
                    _sync_parent(intent_path)
                return dict(json.loads(record), head=head)
        request = {"op": "submit", "parent": observed["head"], "id": request_id, "event": event}
        if not _valid_submit(request) or (intent and intent["request"] != request):
            raise ValueError("intent has an invalid input or a different original parent")
        command = terminal_peace_command(ROOT, timeout, library) + ["--live"]
        with _open_native(command, ROOT, version, timeout) as (native, original):
            current = _replay(prefix["rows"], native, original, admission)
            if current.reply() != observed:
                raise ValueError("terminal-peace prefix moved while preparing the input")
            candidate, error = _evaluate(native, current, request)
            if error:
                raise ValueError(f"terminal-peace source rejected the input ({error})")
        if intent is None:
            intent = {"request": request, "owner": sign(key, OWNER, admission.authorization(request))}
            _save_intent(intent_path, intent)
        owner = intent["owner"]
        admission.authorize(request, owner)
        votes = _collect(admission, owner, current, candidate, prefix, voters)
        if len(votes) < admission.required(current):
            raise ValueError("terminal-peace quorum unavailable; retry the same request identifier")
        proof = {"owner": owner, "record": candidate.record, "votes": votes}
        committed = _call(worker, dict(request, certificate=proof), timeout)
        if committed != candidate.reply():
            raise RuntimeError("terminal-peace worker did not confirm the proposed original successor")
        intent_path.unlink()
        _sync_parent(intent_path)
        return committed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for flag in ("state", "policy", "owner-key", "voters"):
        parser.add_argument("--" + flag, type=Path, required=True)
    parser.add_argument("--library", type=Path, help="installed terminal-peace Lean import closure")
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("id")
    parser.add_argument("event")
    args = parser.parse_args()
    if not 0 < args.timeout < float("inf"):
        parser.error("timeout must be positive")
    try:
        commands = json.loads(args.voters.read_text())
        voters = {name: lambda envelope, argv=argv: _call(argv, envelope, args.timeout)
                  for name, argv in commands.items()}
        result = submit(args.state, args.policy, args.owner_key, args.id, args.event, voters, args.timeout, args.library)
        print(_json(result))
    except (*INVALID_PROOF, OSError, RuntimeError, sqlite3.Error, subprocess.SubprocessError) as error:
        print(f"terminal-peace submit failed: {error}", file=sys.stderr)
        raise SystemExit(1) from error


if __name__ == "__main__":
    main()
