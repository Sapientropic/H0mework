"""Shared local file hashes and lossless, chunk-shared closure snapshots.

Job references are transport metadata. Scientific receipts and source files remain
unchanged; legacy plain closure JSON is readable and can be exported byte-for-byte.
"""
from __future__ import annotations

from collections import OrderedDict
import hashlib
import json
import os
from pathlib import Path
import re
import sqlite3
import stat
import time
import uuid
import zlib

REFERENCE = "computenode-closure-ref/v1"
ROOT_SCHEMA = "computenode-closure-chunks/v1"
HEX = re.compile(r"[0-9a-f]{64}\Z")
ENTRY = re.compile(rb'(?P<key>"(?:[^"\\]|\\.)*")\s*:\s*"[0-9a-f]{64}"')
INLINE_LIMIT = 1024
MIN_CHUNK, MAX_CHUNK = 16 << 10, 256 << 10


def file_stamp(info):
    return info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns


def atomic_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{uuid.uuid4().hex}.tmp")
    try:
        with temporary.open("xb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


class HashCache:
    """One row per physical inode version, shared across aliases, workloads and nodes."""

    def __init__(self, root: Path):
        root.mkdir(parents=True, exist_ok=True)
        self.path = root / "file-hashes.sqlite3"
        self.db = sqlite3.connect(self.path, timeout=30, isolation_level=None)
        self.db.execute("PRAGMA busy_timeout=30000")
        self.db.execute("PRAGMA journal_mode=WAL")
        self.db.execute("PRAGMA synchronous=NORMAL")
        self.db.execute("CREATE TABLE IF NOT EXISTS hashes (dev INTEGER, ino INTEGER, size INTEGER, "
                        "mtime INTEGER, ctime INTEGER, digest BLOB, used INTEGER, PRIMARY KEY(dev,ino)) WITHOUT ROWID")
        self.db.execute("CREATE TABLE IF NOT EXISTS maintenance (name TEXT PRIMARY KEY, stamp INTEGER)")
        self.pending = {}

    def __enter__(self):
        return self

    def __exit__(self, kind, value, traceback):
        try:
            self.flush()
        finally:
            self.db.close()

    def _remember(self, stamp, digest: str):
        self.pending[stamp[:2]] = (*stamp, bytes.fromhex(digest), int(time.time()))
        if len(self.pending) >= 512:
            self.flush()

    def flush(self):
        if not self.pending:
            return
        self.db.execute("BEGIN IMMEDIATE")
        try:
            self.db.executemany("INSERT OR REPLACE INTO hashes VALUES (?,?,?,?,?,?,?)", self.pending.values())
            self.db.execute("COMMIT")
            self.pending.clear()
        except BaseException:
            self.db.execute("ROLLBACK")
            raise

    def digest(self, path: Path) -> str:
        before = path.stat()
        if not stat.S_ISREG(before.st_mode):
            raise ValueError(f"closure input is not a regular file: {path}")
        stamp = file_stamp(before)
        row = self.pending.get(stamp[:2])
        if row is None:
            row = self.db.execute("SELECT dev,ino,size,mtime,ctime,digest,used FROM hashes WHERE dev=? AND ino=?",
                                  stamp[:2]).fetchone()
        if row is not None and tuple(row[:5]) == stamp:
            digest = bytes(row[5]).hex()
            if time.time() - row[6] > 86400:
                self._remember(stamp, digest)
            return digest
        with path.open("rb") as stream:
            if file_stamp(os.fstat(stream.fileno())) != stamp:
                raise ValueError(f"closure input was replaced before hashing: {path}")
            digest = hashlib.file_digest(stream, "sha256").hexdigest()
            if file_stamp(os.fstat(stream.fileno())) != stamp or file_stamp(path.stat()) != stamp:
                raise ValueError(f"closure input changed while hashing: {path}")
        self._remember(stamp, digest)
        return digest

    def import_legacy(self, path: Path) -> dict:
        """Consume old accelerator hints once; edits newer than that cache never qualify."""
        if not path.exists():
            return {"imported": 0, "removed": False}
        before = path.lstat()
        if not stat.S_ISREG(before.st_mode):
            raise ValueError(f"legacy hash cache is not a regular file: {path}")
        packet = json.loads(path.read_text())
        if not isinstance(packet, dict):
            raise ValueError("legacy hash cache must be a path mapping")
        imported = 0
        for name, row in packet.items():
            if (not isinstance(name, str) or not Path(name).is_absolute()
                    or not isinstance(row, list) or len(row) != 3
                    or type(row[0]) is not int or type(row[1]) is not int
                    or not isinstance(row[2], str) or not HEX.fullmatch(row[2])):
                continue
            try:
                source = Path(name).stat()
            except OSError:
                continue
            if (stat.S_ISREG(source.st_mode) and [source.st_size, source.st_mtime_ns] == row[:2]
                    and source.st_ctime_ns <= before.st_mtime_ns):
                stamp = file_stamp(source)
                existing = self.pending.get(stamp[:2])
                if existing is None:
                    existing = self.db.execute("SELECT dev,ino,size,mtime,ctime FROM hashes WHERE dev=? AND ino=?",
                                               stamp[:2]).fetchone()
                if existing is not None and tuple(existing[:5]) == stamp:
                    continue
                self._remember(stamp, row[2])
                imported += 1
        self.flush()
        unchanged = file_stamp(path.lstat()) == file_stamp(before)
        if unchanged:
            path.unlink()
        return {"imported": imported, "removed": unchanged}

    def prune(self, *, max_rows: int = 2_000_000, max_age_days: int = 90) -> int:
        """Disposable acceleration is bounded; never prune closure snapshots here."""
        self.flush()
        now = int(time.time())
        self.db.execute("BEGIN IMMEDIATE")
        try:
            previous = self.db.execute("SELECT stamp FROM maintenance WHERE name='prune'").fetchone()
            if previous and now - previous[0] < 86400:
                self.db.execute("COMMIT")
                return 0
            before = self.db.total_changes
            self.db.execute("DELETE FROM hashes WHERE used < ?", (now - max_age_days * 86400,))
            count = self.db.execute("SELECT COUNT(*) FROM hashes").fetchone()[0]
            if count > max_rows:
                self.db.execute("DELETE FROM hashes WHERE (dev,ino) IN "
                                "(SELECT dev,ino FROM hashes ORDER BY used LIMIT ?)", (count - max_rows,))
            removed = self.db.total_changes - before
            self.db.execute("INSERT OR REPLACE INTO maintenance VALUES ('prune',?)", (now,))
            self.db.execute("COMMIT")
            return removed
        except BaseException:
            self.db.execute("ROLLBACK")
            raise


class ClosureStore:
    def __init__(self, root: Path, *, read_cache_bytes: int = 0):
        self.root = root.resolve()
        self._read_cache = OrderedDict()
        self._read_cache_limit = read_cache_bytes
        self._read_cache_used = 0

    def _path(self, kind: str, digest: str) -> Path:
        if not isinstance(digest, str) or not HEX.fullmatch(digest):
            raise ValueError("invalid closure content address")
        return self.root / "closures" / kind / digest[:2] / digest

    @staticmethod
    def _put(path: Path, data: bytes) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        temporary = path.with_name(f".{path.name}.{uuid.uuid4().hex}.tmp")
        try:
            with temporary.open("xb") as stream:
                stream.write(data); stream.flush(); os.fsync(stream.fileno())
            temporary.chmod(0o444)
            try:
                os.link(temporary, path)
            except FileExistsError:
                pass
        finally:
            temporary.unlink(missing_ok=True)

    def put(self, raw: bytes) -> str:
        digest = hashlib.sha256(raw).hexdigest()
        target = self._path("roots", digest)
        if target.exists():
            # Immutable roots are committed after all chunks. Read verifies the full
            # original before a remote copy can be discarded or an export published.
            return digest
        manifest = json.loads(raw)
        if not isinstance(manifest, dict) or any(not isinstance(k, str) or not isinstance(v, str)
                or not HEX.fullmatch(v) for k, v in manifest.items()):
            raise ValueError("closure must map relative paths to SHA256 values")
        chunks, start, matched = [], 0, 0

        def emit(stop):
            nonlocal start
            data = raw[start:stop]
            key = hashlib.sha256(data).hexdigest()
            path = self._path("chunks", key)
            if key not in self._read_cache and not path.exists():
                self._put(path, zlib.compress(data, 3))
            chunks.append(key); start = stop

        # Anchors follow entries, not byte offsets: inserting one dependency rewrites
        # its nearby chunk rather than shifting every later block of a large table.
        for match in ENTRY.finditer(raw):
            matched += 1
            length = match.end() - start
            key = match['key']
            if length >= MIN_CHUNK and (zlib.crc32(key) & 511 == 0 or length >= MAX_CHUNK):
                emit(match.end())
        if matched != len(manifest):
            raise ValueError("closure JSON cannot be losslessly segmented")
        if start < len(raw):
            emit(len(raw))
        packet = {"schema": ROOT_SCHEMA, "sha256": digest, "bytes": len(raw),
                  "files": len(manifest), "chunks": chunks}
        self._put(target, json.dumps(packet, separators=(",", ":")).encode())
        return digest

    def _read_chunk(self, key: str) -> bytes:
        if key in self._read_cache:
            self._read_cache.move_to_end(key)
            return self._read_cache[key]
        compressed = self._path("chunks", key).read_bytes()
        decoder = zlib.decompressobj()
        data = decoder.decompress(compressed, MAX_CHUNK + (1 << 20))
        if not decoder.eof or decoder.unused_data or hashlib.sha256(data).hexdigest() != key:
            raise ValueError("damaged shared closure chunk")
        # Only disk-read, verified immutable chunks enter this bounded pass-local
        # cache. Newly written chunks still require their first read-back.
        if 0 < len(data) <= self._read_cache_limit:
            while self._read_cache_used + len(data) > self._read_cache_limit:
                _, evicted = self._read_cache.popitem(last=False)
                self._read_cache_used -= len(evicted)
            self._read_cache[key] = data
            self._read_cache_used += len(data)
        return data

    def read(self, digest: str) -> bytes:
        packet = json.loads(self._path("roots", digest).read_text())
        if (packet.get("schema") != ROOT_SCHEMA or packet.get("sha256") != digest
                or type(packet.get("bytes")) is not int or not 0 <= packet["bytes"] <= 2 << 30
                or not isinstance(packet.get("chunks"), list)):
            raise ValueError("invalid shared closure root")
        output = bytearray()
        for key in packet["chunks"]:
            output.extend(self._read_chunk(key))
            if len(output) > packet["bytes"]:
                raise ValueError("shared closure exceeds its original size")
        if len(output) != packet["bytes"] or hashlib.sha256(output).hexdigest() != digest:
            raise ValueError("shared closure failed original SHA256 verification")
        return bytes(output)

    def reference(self, path: Path, raw: bytes, *, original_stat=None) -> None:
        if len(raw) <= INLINE_LIMIT:
            atomic_write(path, raw)
            return
        digest = self.put(raw)
        packet = {"$schema": REFERENCE, "store": os.path.relpath(self.root, path.parent.resolve()),
                  "sha256": digest, "bytes": len(raw)}
        if original_stat is not None:
            packet["original"] = {"mode": stat.S_IMODE(original_stat.st_mode), "mtime_ns": original_stat.st_mtime_ns}
        atomic_write(path, (json.dumps(packet, separators=(",", ":")) + "\n").encode())


def closure_reference(path: Path):
    raw = path.read_bytes()
    if len(raw) > 16384:
        return raw, None
    try:
        packet = json.loads(raw)
    except ValueError:
        return raw, None
    if isinstance(packet, dict) and packet.get("$schema") == REFERENCE:
        if not isinstance(packet.get("store"), str) or type(packet.get("bytes")) is not int:
            raise ValueError("invalid local closure reference")
        return raw, packet
    return raw, None


def closure_bytes(path: Path) -> bytes:
    raw, reference = closure_reference(path)
    if reference is None:
        return raw
    raw = ClosureStore(path.parent / reference["store"]).read(reference["sha256"])
    if len(raw) != reference["bytes"]:
        raise ValueError("local closure reference size mismatch")
    return raw


def read_closure(path: Path) -> dict[str, str]:
    return json.loads(closure_bytes(path))


def closure_sha256(path: Path) -> str:
    """The original JSON digest, so existing scientific bindings keep their identity."""
    return hashlib.sha256(closure_bytes(path)).hexdigest()


def materialize_closure(path: Path, destination: Path | None = None) -> None:
    """Export original JSON for frozen readers or a standalone archived work package."""
    raw, reference = closure_reference(path)
    if destination is None and reference is None:
        return
    if destination is not None and destination.exists():
        raise FileExistsError(destination)
    restored = closure_bytes(path)
    target = destination or path
    atomic_write(target, restored)
    if reference and reference.get("original"):
        old = reference["original"]
        target.chmod(old["mode"])
        os.utime(target, ns=(old["mtime_ns"], old["mtime_ns"]))
