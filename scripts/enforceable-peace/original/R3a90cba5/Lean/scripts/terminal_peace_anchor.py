"""Replay and sign one original terminal-peace continuation on an independent node."""

from __future__ import annotations

import argparse
from contextlib import closing
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys

from living_law_runtime import TERMINAL_PEACE_BACKEND, terminal_peace_command
from terminal_peace_admission import Admission, INVALID_PROOF, OWNER, VOTE, compiler_revision
from terminal_peace_worker import (
    _evaluate, _json, _open_native, _replay, _source_version, _transaction, _unique_keys, _valid_submit,
)
from cryptography.hazmat.primitives.serialization import load_pem_private_key
from crypto import sign


def _snapshot(path):
    with closing(sqlite3.connect(path.resolve().as_uri() + "?mode=ro", uri=True)) as db:
        db.execute("BEGIN")
        version, genesis = db.execute("SELECT version, genesis FROM source WHERE one=1").fetchone()
        fields = {row[1] for row in db.execute("PRAGMA table_info(inputs)")}
        certificate = "certificate" if "certificate" in fields else "NULL"
        rows = db.execute(f"SELECT seq, request_id, parent, event, record, head, {certificate} "
                          "FROM inputs ORDER BY seq").fetchall()
    return {"version": version, "genesis": json.loads(genesis), "rows": rows}


def _fence(path, admission, member, next_current=None):
    """Retain the signer's latest vote before emitting its signature."""
    if next_current is None:
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        os.close(fd)
    with closing(sqlite3.connect(path.resolve().as_uri() + "?mode=rw", uri=True, isolation_level=None)) as db:
        db.execute("PRAGMA synchronous=FULL")
        with _transaction(db):
            if next_current is None:
                db.execute("CREATE TABLE fence (policy TEXT, member TEXT, seq INTEGER, head TEXT)")
                db.execute("INSERT INTO fence VALUES (?, ?, ?, NULL)",
                           (admission.identity, member, admission.checkpoint["cursor"]))
                return
            rows = db.execute("SELECT policy, member, seq, head FROM fence").fetchall()
            if len(rows) != 1 or rows[0][:2] != (admission.identity, member):
                raise ValueError("terminal-peace signer has a different enrolled policy")
            _, _, seq, head = rows[0]
            if next_current.cursor < seq or (next_current.cursor == seq and next_current.head != head):
                raise ValueError("terminal-peace signer has already fenced a competing or newer write")
            db.execute("UPDATE fence SET seq=?, head=?", (next_current.cursor, next_current.head))


def _key(path, expected):
    key = load_pem_private_key(path.read_bytes(), password=None)
    if key.public_key().public_bytes_raw() != expected.public_bytes_raw():
        raise ValueError("terminal-peace private key does not match its enrolled role")
    return key


def _vote(command, root, version, timeout, admission, member, key, fence, argument):
    if set(argument) != {"prefix", "owner"}:
        raise ValueError("invalid terminal-peace vote input")
    prefix, owner = argument["prefix"], argument["owner"]
    request = owner["body"]["request"]
    if not _valid_submit(request):
        raise ValueError("invalid terminal-peace original input")
    admission.authorize(request, owner)
    if set(prefix) != {"version", "genesis", "rows"} or prefix["version"] != version:
        raise ValueError("terminal-peace transcript has a different installed source")
    ids = [row[1] for row in prefix["rows"]]
    if request["id"] in ids or len(ids) != len(set(ids)):
        raise ValueError("terminal-peace request identifier is already used")
    with _open_native(command, root, version, timeout) as (native, original):
        if prefix["genesis"] != original.reply():
            raise ValueError("terminal-peace transcript has a different original root")
        current = _replay(prefix["rows"], native, original, admission)
        if current.cursor <= admission.checkpoint["cursor"]:
            admission.bind(current)
        if current.head != request["parent"]:
            raise ValueError("terminal-peace request has a different original parent")
        next_current, error = _evaluate(native, current, request)
        if error:
            raise ValueError(f"terminal-peace source rejected the proposed input ({error})")
    _fence(fence, admission, member, next_current)
    return {"member": member, "record": next_current.record,
            "vote": sign(key, VOTE, admission.point(current, owner, next_current))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="op", required=True)
    snapshot = sub.add_parser("snapshot")
    snapshot.add_argument("--state", type=Path, required=True)
    authorize = sub.add_parser("authorize")
    vote = sub.add_parser("vote")
    vote.add_argument("--library", type=Path, help="installed Lean import closure for an isolated verifier")
    for command in (authorize, sub.add_parser("initialize"), vote):
        command.add_argument("--policy", type=Path, required=True)
        command.add_argument("--key", type=Path, required=True)
        command.add_argument("--timeout", type=float, default=120)
        if command is not authorize:
            command.add_argument("--member", required=True)
            command.add_argument("--fence", type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.op == "snapshot":
            print(_json(_snapshot(args.state)))
            return
        if not 0 < args.timeout < float("inf"):
            raise ValueError("timeout must be positive")
        root = Path(__file__).resolve().parents[1]
        version = _source_version(root, Path(TERMINAL_PEACE_BACKEND))
        admission = Admission(args.policy, version, compiler_revision(root, args.timeout))
        if args.op == "authorize":
            request = json.load(sys.stdin, object_pairs_hook=_unique_keys)
            if not _valid_submit(request):
                raise ValueError("invalid terminal-peace original input")
            key = _key(args.key, admission.owner)
            print(_json(sign(key, OWNER, admission.authorization(request))))
            return
        key = _key(args.key, admission.members[args.member])
        if args.op == "initialize":
            _fence(args.fence, admission, args.member)
            return
        command = terminal_peace_command(root, args.timeout, args.library) + ["--live"]
        argument = json.load(sys.stdin, object_pairs_hook=_unique_keys)
        print(_json(_vote(command, root, version, args.timeout, admission, args.member, key, args.fence, argument)))
    except (*INVALID_PROOF, OSError, RuntimeError, sqlite3.Error, subprocess.SubprocessError, IndexError) as error:
        print(f"terminal-peace anchor rejected: {error}", file=sys.stderr)
        raise SystemExit(1) from error


if __name__ == "__main__":
    main()
