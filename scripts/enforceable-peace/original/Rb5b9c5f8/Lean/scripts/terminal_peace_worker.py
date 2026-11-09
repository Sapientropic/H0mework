"""Durable delivery of named inputs to the original Lean terminal-peace root."""

from __future__ import annotations

import hashlib
import json
import re
import sqlite3
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from contextlib import closing, contextmanager
from dataclasses import dataclass
from pathlib import Path


SOURCE = "terminal-peace/original-six"
VERSION = "terminal-peace-ingress/v1"
IMPORTS = re.compile(r"^(?:(?:public|private) )?import (?:all )?([^\s]+)", re.M)
HEAD = re.compile(r"[0-9a-f]{64}\Z")
IDENTIFIER = re.compile(r"[A-Za-z0-9._-]{1,96}\Z")
FIELDS = {"source", "cursor", "kind", "clock", "address", "remaining"}


def _json(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _digest(value):
    return hashlib.sha256(_json(value).encode()).hexdigest()


def _source_inventory(root: Path, entry: Path):
    pending = [entry]
    files = {}
    while pending:
        relative = pending.pop()
        if relative in files:
            continue
        data = (root / relative).read_bytes()
        files[relative] = hashlib.sha256(data).hexdigest()
        for module in IMPORTS.findall(data.decode()):
            dependency = Path(*module.split(".")).with_suffix(".lean")
            if (root / dependency).is_file():
                pending.append(dependency)
    for relative in (Path("lean-toolchain"), Path("lake-manifest.json")):
        files[relative] = hashlib.sha256((root / relative).read_bytes()).hexdigest()
    return {str(path): digest for path, digest in files.items()}


def _source_version(root: Path, entry: Path) -> str:
    """Bind recovery to the project's exact source closure and toolchain."""
    return _digest(_source_inventory(root, entry))


@contextmanager
def _transaction(db):
    db.execute("BEGIN IMMEDIATE")
    try:
        yield
        db.execute("COMMIT")
    except BaseException:
        if db.in_transaction:
            db.execute("ROLLBACK")
        raise


@dataclass(frozen=True)
class _Committed:
    record: dict
    head: str

    @property
    def cursor(self):
        return self.record["cursor"]

    def reply(self):
        return dict(self.record, head=self.head)


def _commit(parent, request_id, event, record, transport=None):
    material = [parent, request_id, event, record]
    if transport is not None:
        material.append(transport)
    return _Committed(record, _digest(material))


def _record(record, cursor):
    if (not isinstance(record, dict) or set(record) != FIELDS or record["source"] != SOURCE
            or type(record["cursor"]) is not int or record["cursor"] != cursor):
        raise RuntimeError("invalid native terminal-peace record")
    return record


def _replay(rows, native, current, admission):
    for seq, request_id, parent, event, encoded, head, proof in rows:
        request = dict(op="submit", id=request_id, parent=parent, event=event)
        saved = _record(json.loads(encoded), current.cursor + 1)
        committed = _commit(parent, request_id, event, saved)
        if (not _valid_submit(request) or seq != current.cursor + 1
                or parent != current.head or committed.head != head):
            raise RuntimeError("terminal-peace journal has an invalid original parent")
        if admission and seq > admission.checkpoint["cursor"]:
            if current.cursor == admission.checkpoint["cursor"]:
                admission.bind(current)
            if proof is None:
                raise RuntimeError("terminal-peace journal is missing an online certificate")
            if _certified(admission, current, request, json.loads(proof, object_pairs_hook=_unique_keys)) != committed:
                raise RuntimeError("terminal-peace journal has an invalid online certificate")
        elif proof is not None:
            raise RuntimeError("unexpected terminal-peace online certificate")
        if native is not None:
            actual = native({"op": "submit", "cursor": current.cursor, "event": event})
            if _json(actual) != _json(saved):
                raise RuntimeError("terminal-peace input replay disagrees with the committed write")
        current = committed
    return current


def _rows(db, cursor=0):
    return db.execute(
        "SELECT seq, request_id, parent, event, record, head, certificate FROM inputs "
        "WHERE seq>? ORDER BY seq", (cursor,),
    )


def _recover(db, native, current, admission):
    if current.cursor and db.execute("SELECT head FROM inputs WHERE seq=?", (current.cursor,)).fetchone() != (current.head,):
        raise RuntimeError("terminal-peace journal lost the already verified prefix")
    return _replay(_rows(db, current.cursor), native, current, admission)


def _initialize(db, version, original):
    tables = {name for (name,) in db.execute("SELECT name FROM sqlite_schema WHERE type='table'")}
    if tables and tables != {"source", "inputs"}:
        raise RuntimeError("state file is not a terminal-peace input journal")
    db.execute("CREATE TABLE IF NOT EXISTS source (one INTEGER PRIMARY KEY CHECK(one=1), "
               "version TEXT NOT NULL, genesis TEXT NOT NULL, admission TEXT)")
    db.execute("CREATE TABLE IF NOT EXISTS inputs (seq INTEGER PRIMARY KEY, "
               "request_id TEXT NOT NULL UNIQUE, parent TEXT NOT NULL, event TEXT NOT NULL, "
               "record TEXT NOT NULL, head TEXT NOT NULL UNIQUE, certificate TEXT)")
    for table, column in (("source", "admission"), ("inputs", "certificate")):
        if column not in {row[1] for row in db.execute(f"PRAGMA table_info({table})")}:
            db.execute(f"ALTER TABLE {table} ADD COLUMN {column} TEXT")
    observed = db.execute("SELECT version, genesis FROM source WHERE one=1").fetchone()
    expected = (version, _json(original.reply()))
    if observed is None:
        if db.execute("SELECT 1 FROM inputs LIMIT 1").fetchone() is not None:
            raise RuntimeError("terminal-peace journal is missing its source binding")
        db.execute("INSERT INTO source (one, version, genesis) VALUES (1, ?, ?)", expected)
    elif observed != expected:
        raise RuntimeError("terminal-peace journal belongs to a different source build or root")


def _binding(db, admission):
    if "replicated" in {row[1] for row in db.execute("PRAGMA table_info(source)")}:
        if db.execute("SELECT replicated FROM source WHERE one=1").fetchone()[0] is not None:
            raise RuntimeError("terminal-peace journal requires signed replica recovery")
    bound, = db.execute("SELECT admission FROM source WHERE one=1").fetchone()
    if bound is not None and (admission is None or bound != admission.identity):
        raise RuntimeError("terminal-peace journal requires its pinned online policy")
    return bound


def _unique_keys(pairs):
    obj = dict(pairs)
    if len(obj) != len(pairs):
        raise ValueError("repeated field")
    return obj


def _valid_submit(value):
    return (isinstance(value, dict) and set(value) == {"op", "parent", "id", "event"}
            and value["op"] == "submit" and all(isinstance(value[key], str) for key in ("parent", "id", "event"))
            and HEAD.fullmatch(value["parent"]) and IDENTIFIER.fullmatch(value["id"])
            and 0 < len(value["event"]) <= 64)


def _request(line, online=False):
    try:
        value = json.loads(line, object_pairs_hook=_unique_keys)
    except (ValueError, RecursionError):
        return None
    if value == {"op": "inspect"}:
        return value
    if not isinstance(value, dict):
        return None
    request = {key: item for key, item in value.items() if key != "certificate"} if online else value
    if _valid_submit(request) and (not online or isinstance(value.get("certificate"), dict)):
        return value
    return None


def _evaluate(native, current, request):
    actual = native({"op": "submit", "cursor": current.cursor, "event": request["event"]})
    if "error" in actual:
        if (set(actual) != {"error", "cursor"} or actual["cursor"] != current.cursor
                or actual["error"] not in {"invalid-request", "inadmissible-event"}):
            raise RuntimeError("native terminal-peace rejection changed the admitted cursor")
        return None, actual["error"]
    return _commit(current.head, request["id"], request["event"], _record(actual, current.cursor + 1)), None


def _certified(admission, current, request, proof):
    from terminal_peace_admission import INVALID_PROOF

    try:
        proposed = _commit(current.head, request["id"], request["event"],
                           _record(proof["record"], current.cursor + 1))
        admission.verify_step(current, request, proposed, proof)
        return proposed
    except (*INVALID_PROOF, RuntimeError):
        return None


def _consume(db, native, current, request, admission):
    if request is None:
        return current, {"error": "invalid-request", "head": current.head}
    if request["op"] == "inspect":
        return current, current.reply()
    proof = request.pop("certificate", None)
    if admission and not admission.accepts_owner(request, proof):
        return current, {"error": "uncertified-input", "head": current.head}
    request_id, parent, event = (request[key] for key in ("id", "parent", "event"))
    prior = db.execute(
        "SELECT parent, event, record, head, certificate FROM inputs WHERE request_id=?", (request_id,)
    ).fetchone()
    if prior is not None:
        if prior[:2] != (parent, event):
            return current, {"error": "conflicting-request-id", "head": current.head}
        if admission:
            saved = json.loads(prior[4]) if prior[4] is not None else None
            if saved is None or proof.get("owner") != saved["owner"]:
                return current, {"error": "uncertified-input", "head": current.head}
        return current, dict(json.loads(prior[2]), head=prior[3])
    if parent != current.head:
        return current, {"error": "stale-parent", "head": current.head}
    if admission and (proposed := _certified(admission, current, request, proof)) is None:
        return current, {"error": "uncertified-input", "head": current.head}
    committed, error = _evaluate(native, current, request)
    if admission and proposed != committed:
        raise RuntimeError("terminal-peace certificate disagrees with the original source")
    if error:
        return current, {"error": error, "head": current.head}
    db.execute("INSERT INTO inputs VALUES (?, ?, ?, ?, ?, ?, ?)",
               (committed.cursor, request_id, parent, event, _json(committed.record), committed.head,
                _json(proof) if admission else None))
    return committed, committed.reply()


@contextmanager
def _open_native(command, root, version, timeout):
    with ThreadPoolExecutor(max_workers=1) as reader, subprocess.Popen(
        command, cwd=root, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1
    ) as process:
        assert process.stdin is not None and process.stdout is not None

        def native(request):
            process.stdin.write(_json(request) + "\n")
            process.stdin.flush()
            line = reader.submit(process.stdout.readline).result(timeout=timeout)
            if not line:
                raise RuntimeError("native terminal-peace process closed without an answer")
            answer = json.loads(line)
            if not isinstance(answer, dict):
                raise RuntimeError("native terminal-peace process returned a non-object answer")
            return answer

        try:
            record = _record(native({"op": "inspect"}), 0)
            yield native, _Committed(record, _digest([VERSION, version, record]))
        finally:
            process.stdin.close()
            try:
                process.wait(timeout=3)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()


def serve(command, root: Path, entry: Path, state: Path, timeout: float, policy: Path | None = None) -> None:
    """Commit the accepted input and verified result before acknowledging it."""
    version = _source_version(root, entry)
    admission = None
    if policy is not None:
        from terminal_peace_admission import Admission, compiler_revision

        admission = Admission(policy, version, compiler_revision(root, timeout))
    with closing(sqlite3.connect(state, isolation_level=None, timeout=timeout)) as db, \
            _open_native(command, root, version, timeout) as (native, original):
        db.execute("PRAGMA synchronous=FULL")
        with _transaction(db):
            _initialize(db, version, original)
            bound = _binding(db, admission)
            current = _recover(db, native, original, admission if bound else None)
            if admission:
                if not bound:
                    admission.bind(current)
                    db.execute("UPDATE source SET admission=? WHERE one=1", (admission.identity,))
                elif current.cursor <= admission.checkpoint["cursor"]:
                    admission.bind(current)
        for line in sys.stdin:
            limit = 16384 if admission else 4096
            request = _request(line, online=admission is not None) if len(line) <= limit else None
            with _transaction(db):
                _binding(db, admission)
                current = _recover(db, native, current, admission)
                current, reply = _consume(db, native, current, request, admission)
            print(_json(reply), flush=True)
