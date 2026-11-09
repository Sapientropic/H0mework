"""Run cold recovery and roster changes on the named terminal-peace source."""

from __future__ import annotations

import argparse
from functools import partial
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives.serialization import Encoding, NoEncryption, PrivateFormat, load_pem_private_key

from living_law_runtime import TERMINAL_PEACE_BACKEND, terminal_peace_command
from terminal_peace_admission import Admission, INVALID_PROOF, compiler_revision
from terminal_peace_anchor import _key
from terminal_peace_submit import _call, _sync_parent, _writer
from terminal_peace_worker import IDENTIFIER, _json, _open_native, _source_version, _unique_keys

from terminal_peace_replication.operator import Primary
from terminal_peace_replication.protocol import Block
from terminal_peace_replication.quorum import Quorum
from terminal_peace_replication.replica import Replica

ROOT = Path(__file__).resolve().parents[1]


def read(path):
    return json.loads(path.read_text(), object_pairs_hook=_unique_keys)


def enrolled_key(path):
    key = Ed25519PrivateKey.generate()
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, "wb") as stream:
        stream.write(key.private_bytes(Encoding.PEM, PrivateFormat.PKCS8, NoEncryption()))
        stream.flush()
        os.fsync(stream.fileno())
    _sync_parent(path)
    return key


def node(args, admission, version, open_native):
    argument = json.load(sys.stdin, object_pairs_hook=_unique_keys)
    op = argument["op"]
    if op == "enroll" and args.member in admission.members:
        raise Block("original-verifier-must-adopt-its-old-fence", member=args.member)
    if op == "enroll" and args.fence.exists():
        raise Block("verifier-already-has-fence", member=args.member)
    key = enrolled_key(args.key) if op == "enroll" else load_pem_private_key(args.key.read_bytes(), None)
    if op in {"enroll", "status"}:
        replica = Replica(args.fence, admission, args.member, key, version, None)
        if op == "enroll":
            replica.enroll()
            _sync_parent(args.fence)
            return {"member": args.member, "key": replica.public}
        return replica.status(argument["challenge"])
    with open_native() as (native, original):
        replica = Replica(args.fence, admission, args.member, key, version, original)
        if op == "bootstrap":
            return replica.bootstrap(argument["prefix"], argument["owner"], native)
        if op == "prepare":
            return replica.prepare(argument["bundle"], argument["intent"], native)
        if op == "store":
            return replica.store(argument["bundle"], native, argument["challenge"])
    raise Block("unknown-replica-operation", op=op)


def operator(args, admission, version, open_native):
    with open_native() as (_, original):
        pass
    commands = read(args.peers)
    peers = {name: lambda request, argv=argv: _call(argv, request, args.timeout) for name, argv in commands.items()}
    state = args.state.resolve()
    quorum = Quorum(admission, version, original, peers)
    primary = Primary(state, quorum, open_native)
    with _writer(state):
        if args.op in {"bootstrap", "submit"} and args.owner_key is None:
            raise Block("original-owner-key-required")
        if args.op == "bootstrap":
            return primary.bootstrap(_key(args.owner_key, admission.owner)).current.reply()
        if args.op == "submit":
            return primary.submit(args.id, args.event, read(args.roster) if args.roster else None,
                                  _key(args.owner_key, admission.owner))
        timeline, resumed = primary.recover(lookup=args.id)
        if args.id is not None:
            if args.id not in timeline.ids:
                raise Block("original-id-unattested", id=args.id, head=timeline.current.head,
                            cursor=timeline.current.cursor)
            return primary.read_result(timeline, args.id)
        return {"current": timeline.current.reply(), "epoch": timeline.epoch,
                "members": sorted(timeline.members), "resumed": resumed}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--policy", type=Path, required=True)
    parser.add_argument("--library", type=Path)
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--state", type=Path)
    parser.add_argument("--peers", type=Path)
    parser.add_argument("--owner-key", type=Path)
    sub = parser.add_subparsers(dest="op", required=True)
    verifier = sub.add_parser("node")
    verifier.add_argument("--key", type=Path, required=True)
    verifier.add_argument("--fence", type=Path, required=True)
    verifier.add_argument("--member", required=True)
    sub.add_parser("bootstrap")
    sub.add_parser("recover").add_argument("--id")
    submit = sub.add_parser("submit")
    submit.add_argument("id")
    submit.add_argument("event")
    submit.add_argument("--roster", type=Path)
    args = parser.parse_args()
    if not 0 < args.timeout < float("inf"):
        parser.error("timeout must be positive")
    if args.op == "node" and not IDENTIFIER.fullmatch(args.member):
        parser.error("invalid verifier name")
    if args.op != "node" and (args.state is None or args.peers is None):
        parser.error("--state and --peers are required for the original journal")
    try:
        version = _source_version(ROOT, Path(TERMINAL_PEACE_BACKEND))
        admission = Admission(args.policy, version, compiler_revision(ROOT, args.timeout))
        command = terminal_peace_command(ROOT, args.timeout, args.library) + ["--live"]
        native = partial(_open_native, command, ROOT, version, args.timeout)
        operation = node if args.op == "node" else operator
        print(_json(operation(args, admission, version, native)))
    except Block as error:
        print(error, file=sys.stderr)
        raise SystemExit(2) from error
    except (*INVALID_PROOF, OSError, RuntimeError, sqlite3.Error, subprocess.SubprocessError, IndexError) as error:
        print(_json({"error": "terminal-peace-original-evidence-invalid", "detail": str(error)}), file=sys.stderr)
        raise SystemExit(1) from error


if __name__ == "__main__":
    main()
