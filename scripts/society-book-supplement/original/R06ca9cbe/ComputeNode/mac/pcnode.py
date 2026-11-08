"""Mac side of the PC compute node: transport, shipping, receipts, and the loop.

A workload adapter (subclass of ``Workload``) decides what to compute and what a
result means; this module moves units to the node and receipts back.  Every step
is idempotent and survives a Mac restart at any instant:

* ship:   candidates -> ``<state>/jobs/<job>/`` (queue.jsonl, meta.json, closure.json) ->
          tar(src payload + closure blobs the node lacks) -> ``<remote>/inbox/<job>.part`` ->
          mv + ``READY`` -> ``job.json`` (the commit marker, written last);
* pull:   receipts not yet in ``incoming/processed.txt`` plus their files, for every open
          job in one SSH session (per-job sessions multiplied flaky-link failures);
* accept: host, Lean githash and file sha256 are checked here, meaning by the adapter;
          a receipt is marked processed only after its outcome is recorded;
* tidy:   once every unit of a job is processed, drop remote src/lib/out and local copies.

Several threads may run loops against one node at once: each workload's ``name`` is its
fair-share bucket there, and a loop refills only its own queue (``low_water``).  Closure
files are content-addressed on the node, so workloads with different versions of a file
never interfere and a file crosses the network once.

Each pass first settles job dirs a crash left without ``job.json`` (recover when the node
already saw READY, otherwise unship).  The loop exits after a pass when its code
changes (``run_supervisor.sh`` restarts it) or when ``<state>/STOP`` exists.

Keep state directories off ``/tmp``: macOS empties it on reboot (the J instance lost
a closure root that way).
"""
from __future__ import annotations

import dataclasses
import contextlib
import datetime as dt
import fcntl
import hashlib
import inspect
import io
import json
import os
import re
import selectors
import shlex
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
import traceback
import uuid
from pathlib import Path

from transport_guard import (PROBE_TIMEOUT, TransportBlocked, TransportFailure,
                             TransportGuard, is_transport_failure)
from local_metadata import ClosureStore, HashCache, closure_bytes, closure_sha256, read_closure

NODE_FILES = ("pcnode_daemon.py", "pcnode_unit.py", "setctl.py", "bench.py")
NODE_DIR = Path(__file__).resolve().parents[1] / "node"
DAEMON_CODE = ("pcnode_daemon.py", "pcnode_unit.py")  # same order as the daemon's code_digest()
MACOS_SETSID = "import os, sys; os.setsid(); os.execvp(sys.argv[1], sys.argv[1:])"

# Publish one complete generation. Running daemons/shims import their immutable directory;
# the stable bin launchers resolve current once, before importing any generation's modules.
PUBLISH = r"""
import ast, fcntl, hashlib, json, os, shutil, subprocess, sys, uuid
from pathlib import Path
staging, home = map(Path, sys.argv[1:3])
expected = json.loads(sys.argv[3])
with (home / ".deploy.lock").open("a") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    data = {}
    for name, want in expected.items():
        raw = (staging / name).read_bytes()
        if hashlib.sha256(raw).hexdigest() != want:
            raise RuntimeError("deployment hash mismatch: " + name)
        ast.parse(raw, filename=name)
        data[name] = raw
    subprocess.run([sys.executable, "-c", "import pcnode_daemon, pcnode_unit, setctl, bench"],
                   cwd=staging, capture_output=True, check=True)
    identity = hashlib.sha256(b"".join(n.encode() + b"\0" + data[n] for n in sorted(data))).hexdigest()
    releases, bin = home / "releases", home / "bin"
    releases.mkdir(exist_ok=True)
    bin.mkdir(exist_ok=True)
    release = releases / identity
    if release.exists():
        shutil.rmtree(staging)
    else:
        staging.rename(release)
    link = bin / (".current-" + uuid.uuid4().hex)
    link.symlink_to(Path("..") / "releases" / identity)
    link.replace(bin / "current")
    launcher = ('from pathlib import Path\nimport runpy, sys\n'
                'entry = (Path(__file__).parent / "current" / Path(__file__).name).resolve()\n'
                'sys.path.insert(0, str(entry.parent))\nrunpy.run_path(str(entry), run_name="__main__")\n')
    for name in expected:
        path = bin / name
        if path.exists() and path.read_text() == launcher:
            continue
        temporary = bin / (name + ".tmp")
        temporary.write_text(launcher)
        temporary.replace(path)
"""

DEFER = r"""
import fcntl, json, sys
from pathlib import Path
home, action = Path(sys.argv[1]), sys.argv[2]
control = home / "control.json"
with (home / "control.lock").open("a") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    data = json.loads(control.read_text()) if control.exists() else {}
    if action == "begin" and "_upgrade_pause" not in data:
        data["_upgrade_pause"] = {"present": "paused" in data, "paused": data.get("paused")}
        data["paused"] = True
    elif action == "finish" and "_upgrade_pause" in data:
        daemon_lock = (home / "daemon.lock").open("a")
        try:
            fcntl.flock(daemon_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise RuntimeError("old daemon still owns the node; deferred upgrade keeps waiting")
        saved = data.pop("_upgrade_pause")
        if data.get("paused") is True:
            if saved["present"]:
                data["paused"] = saved["paused"]
            else:
                data.pop("paused", None)
    else:
        sys.exit(0)
    temporary = control.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(data) + "\n")
    temporary.replace(control)
"""


def log(message: str) -> None:
    print(f"{dt.datetime.now():%m-%d %H:%M:%S} {message}", flush=True)


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def read_jsonl(path: Path) -> list[dict]:
    if not path.exists():
        return []
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def append_jsonl(path: Path, item: dict) -> None:
    with path.open("a") as stream:
        stream.write(json.dumps(item) + "\n")


def queued(beat: dict, workload: str) -> int:
    """Units of this workload waiting on the node (older daemons only report a global count)."""
    if "workloads" not in beat:
        return beat.get("pending", 0)
    return beat["workloads"].get(workload, {}).get("pending", 0)


@dataclasses.dataclass
class Config:
    remote: str                       # ssh target, e.g. administrator@100.110.118.46
    remote_home: str                  # daemon home on Linux/WSL (inbox, control.json, logs)
    remote_lib: str                   # legacy shared Lean store (jobs shipped before closure.json)
    host: str                         # platform.node() of the node; receipts must match
    distro: str = "Ubuntu"
    wsl_user: str = ""
    githash: str = ""                 # expected Lean commit for lean units ("" skips the check)
    # ~1 h of light units at 16 workers stays queued, so a network outage (J run: 100 min
    # over a Tailscale identity clash) does not idle the node after minutes.
    low_water: int = 1000             # ship when this workload's units queued on the node fall below
    max_units: int = 300              # units per job
    interval: int = 60                # seconds per loop
    start_daemon: bool = True         # (re)start the node daemon when its heartbeat is stale
    lib_index: str = ""               # blobs known in the node store; default <state>/../cas-index.json
    transport: str = "wsl"            # explicit; a Linux-looking hostname does not select native SSH
    node_id: str = ""                 # native Linux/macOS: physical instance identity, renewed on replacement
    max_pull_bytes: int = 1 << 30      # complete units; includes uncompressed tar headers and padding
    ship_compresslevel: int = 9       # explicit CPU/size tradeoff for first closure packs; identity is unchanged
    preserve_failed_outputs: bool = True  # diagnostics survive remote out/ cleanup; never accepted results
    transport_control_dir: str = ""   # shared on this control machine, separate from each workload ledger
    storage_roots: dict[str, str] = dataclasses.field(default_factory=dict)  # explicit physical roots for hygiene
    local_metadata_dir: str = ""      # shared local metadata; independent of destination node

    def __post_init__(self) -> None:
        if self.transport not in ("wsl", "linux", "macos"):
            raise ValueError("transport must be 'wsl', 'linux' or 'macos'")
        if self.native and (not isinstance(self.node_id, str) or not self.node_id.strip()):
            raise ValueError("native nodes require node_id; use the cloud instance ID or machine name")
        if type(self.max_pull_bytes) is not int or self.max_pull_bytes < tarfile.RECORDSIZE:
            raise ValueError(f"max_pull_bytes must be an integer >= {tarfile.RECORDSIZE}")
        if type(self.ship_compresslevel) is not int or not 0 <= self.ship_compresslevel <= 9:
            raise ValueError("ship_compresslevel must be an integer between 0 and 9")
        if type(self.preserve_failed_outputs) is not bool:
            raise ValueError("preserve_failed_outputs must be a boolean")
        if not isinstance(self.storage_roots, dict):
            raise ValueError("storage_roots must map top-level scope names to absolute physical directories")
        for name, target in self.storage_roots.items():
            if (not isinstance(name, str) or not re.fullmatch(r"[A-Za-z0-9_][A-Za-z0-9._-]*", name)
                    or not isinstance(target, str) or not target.startswith("/")
                    or "\\" in target or "\0" in target
                    or any(part in ("", ".", "..") for part in target.split("/")[1:])):
                raise ValueError("storage_roots needs a top-level scope name and an absolute physical directory")

    @property
    def native(self) -> bool:
        """Plain SSH to the node's own POSIX shell (Linux or macOS), not through wsl.exe."""
        return self.transport != "wsl"

    def identity(self) -> dict:
        return {"transport": self.transport, "node_id": self.node_id,
                "host": self.host, "remote_home": self.remote_home}

    @classmethod
    def load(cls, path: Path) -> "Config":
        data = json.loads(path.read_text())
        root = path.resolve().parent
        shared = Path(__file__).resolve().parents[1] / "state"
        control = Path(data["transport_control_dir"]) if data.get("transport_control_dir") else shared / "node-control"
        data["transport_control_dir"] = str(control if control.is_absolute() else root / control)
        # Frozen transport configs often live beside individual audit packages. Their
        # location must not create another full cache of the same local dependencies.
        metadata = Path(data["local_metadata_dir"]) if data.get("local_metadata_dir") else shared / "local-metadata"
        data["local_metadata_dir"] = str(metadata if metadata.is_absolute() else root / metadata)
        names = {f.name for f in dataclasses.fields(cls)}
        config = cls(**{k: v for k, v in data.items() if k in names})
        if not config.lib_index:
            tag = hashlib.sha256(json.dumps(config.identity(), sort_keys=True).encode()).hexdigest()[:16]
            config.lib_index = str(shared / f"cas-index-{tag}.json")
        return config


class Workload:
    """Adapter contract.  Units are dicts with a unique ``id`` and a ``kind``
    (``lean`` or ``cmd``, see ``node/pcnode_unit.py``); ids are never shipped twice,
    so an adapter retries by minting a new id (e.g. id = name@source-sha).  Units may
    declare ``slots``, ``mem_gb`` and ``gpu`` for the node's admission control."""

    name = "workload"   # job-name prefix and fair-share bucket on the node: one per tenant
    priority = 0        # strict tier on the node; equal tiers share slots fairly

    def candidates(self, shipped: set[str]) -> list[dict]:
        """Units ready to run now, excluding accepted ones and ids in ``shipped``."""
        raise NotImplementedError

    def payload(self, units: list[dict]) -> list[tuple[Path, str]]:
        """(local file, path under the job's ``src/``) needed by these units."""
        return []

    def closure(self, units: list[dict]) -> list[tuple[Path, str]]:
        """(local file, path in the node's shared lib store); only changed files travel."""
        return []

    def accept(self, record: dict, files: dict[str, Path]) -> str:
        """Verified exit-0 receipt; ``files`` maps out/-relative paths to local copies
        (move what you keep).  Return ``promoted``, ``paid`` (already had it) or ``failed``."""
        raise NotImplementedError

    def failed(self, record: dict, reasons: list[str]) -> None:
        """A unit failed on the node or failed verification (already logged)."""

    def tick(self) -> dict:
        """Periodic downstream work (assembly, reports); returns status fields, ideally
        ``total``/``accepted``/``failed`` for progress and ETA.  Runs after shipping and must
        stay short: put long downstream work on a thread pool."""
        return {}

    def finished(self) -> bool:
        return False


# One-time index bootstrap: adopt the legacy store into the content-addressed one by hard
# link (no upload), then list every blob the node holds.
SEED = r"""
import hashlib, os, sys
from concurrent.futures import ThreadPoolExecutor
legacy, cas = sys.argv[1], sys.argv[2]
def adopt(path):
    h = hashlib.sha256()
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            h.update(chunk)
    blob = os.path.join(cas, h.hexdigest()[:2], h.hexdigest())
    os.makedirs(os.path.dirname(blob), exist_ok=True)
    try:
        os.link(path, blob)
        os.chmod(blob, 0o444)
    except FileExistsError:
        pass
files = [os.path.join(d, n) for d, _, names in os.walk(legacy) for n in names if not n.endswith(".incoming")]
with ThreadPoolExecutor(8) as pool:
    list(pool.map(adopt, files))
for d, _, names in os.walk(cas):
    print("\n".join(names))
"""

PULL = r"""
import json, os, stat, sys, tarfile
request = json.load(sys.stdin)
limit = request["max_pull_bytes"]

def parts(value):
    if not isinstance(value, str) or any(c in value for c in ('\\', '\0')):
        raise ValueError("unsafe pull path: " + repr(value))
    result = value.split('/')
    if any(p in ('', '.', '..') for p in result):
        raise ValueError("unsafe pull path: " + repr(value))
    return result

def open_regular(pieces):
    directory = os.open(request["inbox"], os.O_RDONLY | os.O_DIRECTORY)
    try:
        for piece in pieces[:-1]:
            child = os.open(piece, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=directory)
            os.close(directory)
            directory = child
        descriptor = os.open(pieces[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=directory)
    finally:
        os.close(directory)
    stream = os.fdopen(descriptor, 'rb')
    if not stat.S_ISREG(os.fstat(stream.fileno()).st_mode):
        stream.close()
        raise ValueError("pull requires a regular file: " + '/'.join(pieces))
    return stream

def entry(pieces, name):
    with open_regular(pieces) as stream:
        state = os.fstat(stream.fileno())
    info = tarfile.TarInfo(name)
    info.size, info.mtime, info.mode = state.st_size, int(state.st_mtime), 0o600
    size = len(info.tobuf(tarfile.PAX_FORMAT)) + ((info.size + 511) // 512) * 512
    return pieces, info, size

def archive_size(payload):
    return ((payload + 1024 + tarfile.RECORDSIZE - 1) // tarfile.RECORDSIZE) * tarfile.RECORDSIZE

def pack(out):
    names = set()
    for job, have in request["jobs"].items():
        if len(parts(job)) != 1:
            raise ValueError("unsafe job name: " + repr(job))
        base = os.path.join(request["inbox"], job)
        recs, have = os.path.join(base, "records"), set(have)
        for n in sorted(os.listdir(recs) if os.path.isdir(recs) else []):
            if not n.endswith(".json") or n in have:
                continue
            if len(parts(n)) != 1:
                raise ValueError("unsafe receipt name: " + repr(n))
            receipt = entry([job, 'records', n], job + '/incoming/records/' + n)
            with open_regular(receipt[0]) as stream:
                record = json.load(stream)  # receipts are published by rename: never partial
            files = []
            if record.get("exit") == 0 or request["preserve_failed_outputs"]:
                for rel in record.get("files", {}):
                    files.append(entry([job, 'out', *parts(rel)], job + '/incoming/out/' + rel))
            unit = [*files, receipt]  # publish the receipt after all of its outputs
            cost = sum(item[2] for item in unit)
            required = archive_size(cost)
            if required > limit:
                if out.offset:
                    return  # finish prior units; next pass reports this unit before writing it
                raise ValueError(f"unit {job}/{record.get('id', n)} requires {required} tar bytes; "
                                 f"max_pull_bytes={limit}; increase max_pull_bytes explicitly")
            if archive_size(out.offset + cost) > limit:
                return
            for pieces, info, _ in unit:
                if info.name in names:
                    raise ValueError("conflicting output path: " + info.name)
                names.add(info.name)
                with open_regular(pieces) as stream:
                    if os.fstat(stream.fileno()).st_size != info.size:
                        raise RuntimeError("pull file changed size: " + info.name)
                    out.addfile(info, stream)

with tarfile.open(fileobj=sys.stdout.buffer, mode="w|", format=tarfile.PAX_FORMAT) as out:
    pack(out)
"""


def _pull_parts(value: str) -> list[str]:
    if not isinstance(value, str) or any(c in value for c in ("\\", "\0")):
        raise ValueError(f"unsafe pull path: {value!r}")
    parts = value.split("/")
    if any(part in ("", ".", "..") for part in parts):
        raise ValueError(f"unsafe pull path: {value!r}")
    return parts


class Node:
    def __init__(self, config: Config, state: Path):
        self.c = config
        self.state = state
        self.jobs = state / "jobs"
        self.failures = state / "failures.jsonl"
        # One index per node store, shared by every workload's state dir (locked updates).
        tag = hashlib.sha256(json.dumps(config.identity(), sort_keys=True).encode()).hexdigest()[:16]
        index_name = f"cas-index-{tag}.json" if config.native else "cas-index.json"
        metadata = Path(config.local_metadata_dir) if config.local_metadata_dir else state.parent / "local-metadata"
        self.metadata_dir = metadata
        self.closures = ClosureStore(metadata)
        self.index_path = Path(config.lib_index) if config.lib_index else state.parent / index_name
        self.hashes_path = state / "mac-hash-cache.json"
        self.last_progress: dict = {}
        self._last_transport_notice = None
        control = Path(config.transport_control_dir) if config.transport_control_dir else state.parent / "node-control"
        self.guard = TransportGuard(control, config.identity())
        self.ssh = ["ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=10",
                    "-o", "ServerAliveInterval=30", "-o", "ServerAliveCountMax=4", config.remote]
        # Legacy rsync consumers append '--', 'rsync' to this prefix; env supports the same native shape.
        self.wsl_prefix = (["env"] if config.native else
                           ["wsl", "-d", config.distro] + (["-u", config.wsl_user] if config.wsl_user else []))
        self.check_state()

    # ------------------------------------------------------------ transport

    def remote_argv(self, *argv: str) -> list[str]:
        command = [*self.wsl_prefix, "--", *argv]
        return [*self.ssh, shlex.join(command)] if self.c.native else [*self.ssh, *command]

    @contextlib.contextmanager
    def transport_session(self, *, allow_probe: bool = True):
        ticket = self.guard.acquire(allow_probe=allow_probe)
        if ticket.probe:
            try:
                evidence = self._probe_transport()
            except Exception as error:
                self.guard.failure(ticket, error)
                raise
            if not self.guard.success(ticket, evidence):
                raise TransportBlocked(self.guard.snapshot())
            ticket = self.guard.acquire(allow_probe=False)
        try:
            yield
        except Exception as error:
            if is_transport_failure(error):
                self.guard.failure(ticket, error)
            raise

    def _raw_remote(self, argv: list[str], **kwargs) -> subprocess.CompletedProcess:
        result = subprocess.run(argv, **kwargs)
        if result.returncode == 255:
            raise TransportFailure(f"SSH disconnected: {(result.stderr or b'').decode(errors='replace')[-400:]}")
        return result

    def _run_remote(self, argv: list[str], *, allow_probe: bool = True, **kwargs) -> subprocess.CompletedProcess:
        with self.transport_session(allow_probe=allow_probe):
            return self._raw_remote(argv, **kwargs)

    def _probe_transport(self, *, min_free_bytes: int | None = None) -> dict:
        if min_free_bytes is None:
            script = "printf 'PCNODE_TRANSPORT_OK\\n'\n"
        else:
            script = "python3 - <<'PCNODE_HEALTH'\n" + f"home = {self.c.remote_home!r}\n" + r"""
import json, os, platform, shutil, tempfile
from pathlib import Path
home = Path(home)
free = shutil.disk_usage(home).free
with tempfile.NamedTemporaryFile(prefix=".transport-probe-", dir=home) as probe:
    probe.write(b"pcnode writable\n")
    probe.flush()
    os.fsync(probe.fileno())
    probe.seek(0)
    assert probe.read() == b"pcnode writable\n"
print(json.dumps({"host": platform.node(), "free_bytes": free, "writable": True}))
""" + "\nPCNODE_HEALTH\n"
        result = self._raw_remote(self.remote_argv("bash", "-s"), input=script.encode(),
                                  capture_output=True, timeout=PROBE_TIMEOUT)
        if result.returncode:
            raise RuntimeError(f"health probe failed ({result.returncode}): {result.stderr.decode(errors='replace')[-400:]}")
        if min_free_bytes is None:
            if result.stdout.strip() != b"PCNODE_TRANSPORT_OK":
                raise ValueError("health probe returned an unexpected response")
            return {"connected": True}
        evidence = json.loads(result.stdout)
        if (evidence.get("host") != self.c.host or evidence.get("writable") is not True
                or type(evidence.get("free_bytes")) is not int or evidence["free_bytes"] < min_free_bytes):
            raise ValueError(f"recovery requires matching host, writable node home and {min_free_bytes} free bytes: {evidence}")
        return evidence

    def recover_transport(self, *, min_free_bytes: int = 1 << 30) -> dict:
        """Explicit recovery changes only this machine's guard; remote jobs stay intact."""
        if type(min_free_bytes) is not int or min_free_bytes < 0:
            raise ValueError("min_free_bytes must be a nonnegative integer")
        ticket = self.guard.acquire(force_probe=True)
        try:
            evidence = self._probe_transport(min_free_bytes=min_free_bytes)
        except Exception as error:
            self.guard.failure(ticket, error)
            raise
        if not self.guard.success(ticket, evidence):
            raise TransportBlocked(self.guard.snapshot())
        return evidence

    def wsl(self, script: str, timeout: int = 600, *, allow_probe: bool = True) -> bytes:
        """Run bash on the configured node; keep the legacy method name for workload adapters."""
        result = self._run_remote(self.remote_argv("bash", "-s"), allow_probe=allow_probe,
                                  input=script.encode(), capture_output=True, timeout=timeout)
        if result.returncode:
            raise RuntimeError(f"node script failed ({result.returncode}): {result.stderr.decode()[-400:]}")
        return result.stdout

    def deploy_and_heartbeat(self, needed: bool = True) -> dict:
        self.bind_state()
        home = self.c.remote_home
        files = {name: (NODE_DIR / name).read_bytes() for name in NODE_FILES}
        probe = (f"mkdir -p {shlex.quote(home + '/bin')} {shlex.quote(home + '/inbox')}\n"
                 f"exec 9>{shlex.quote(home + '/.deploy.lock')}; flock -s 9\n"
                 f"code={shlex.quote(home + '/bin')}; test ! -d \"$code/current\" || code=\"$code/current\"\n"
                 + "".join(f"printf '%s ' {n}; if test -f \"$code/{n}\"; then "
                           f"sha256sum \"$code/{n}\" | cut -c1-64; else echo none; fi\n"
                           for n in NODE_FILES)
                 # A loop on pre-generation code once overwrote the launchers with full files; republish then.
                 + f"g=0; test -d {shlex.quote(home + '/bin/current')} && g=1; l=1\n"
                 + "".join(f"grep -q runpy.run_path {shlex.quote(home + '/bin/' + n)} 2>/dev/null || l=0\n"
                           for n in NODE_FILES)
                 + "echo \"generation $g launchers $l\"\n"
                 + f"cat {home}/daemon.heartbeat.json 2>/dev/null || echo '{{}}'\n")
        out = self.wsl(probe, 60).decode().splitlines()
        remote = {line.split()[0]: (line.split() + ["none"])[1] for line in out[:len(NODE_FILES)]}
        published = len(out) > len(NODE_FILES) and out[len(NODE_FILES)] == "generation 1 launchers 1"
        beat = json.loads(out[len(NODE_FILES) + 1] or "{}") if len(out) > len(NODE_FILES) + 1 else {}
        changed = [n for n in NODE_FILES if remote.get(n) != hashlib.sha256(files[n]).hexdigest()]
        if changed or not published:
            staging = f"{home}/.deploy-{uuid.uuid4().hex}"
            buffer = io.BytesIO()
            with tarfile.open(fileobj=buffer, mode="w") as bundle:
                for name in NODE_FILES:
                    info = tarfile.TarInfo(name)
                    info.size, info.mode = len(files[name]), 0o644
                    bundle.addfile(info, io.BytesIO(files[name]))
            self.wsl(f"mkdir -p {shlex.quote(staging)}\n", 60)
            self._run_remote(self.remote_argv("tar", "-xf", "-", "-C", staging),
                           input=buffer.getvalue(), capture_output=True, check=True, timeout=120)
            expected = json.dumps({n: hashlib.sha256(raw).hexdigest() for n, raw in files.items()})
            self.wsl(f"python3 - {shlex.quote(staging)} {shlex.quote(home)} {shlex.quote(expected)} <<'PYEOF'\n"
                     f"{PUBLISH}\nPYEOF\n", 120)
            log(f"deployed {changed}")
        alive = bool(beat) and not beat.get("exited") and time.time() - beat.get("at", 0) < 120
        code = hashlib.sha256(b"".join(files[n] for n in DAEMON_CODE)).hexdigest()
        if alive and not beat.get("reload") and beat.get("running") and beat.get("code") != code:
            beat["upgrade_pending"] = True
        if alive and beat.get("code") != code and not beat.get("stopping"):
            if beat.get("reload"):  # re-exec in place; running units are adopted, nobody waits
                self.wsl(f"touch {home}/RELOAD\n", 60)
                log("asked node daemon to reload the deployed code")
            elif beat.get("running"):
                # Keep the old memory brake and frozen-unit policy while current work finishes.
                # STOP on old versions wakes every unit, so pause admission before draining.
                self.wsl(f"python3 - {shlex.quote(home)} begin <<'PYEOF'\n{DEFER}\nPYEOF\n", 60)
                beat["upgrade_pending"] = True
                log("pre-reload daemon keeps current units; new admission paused until upgrade")
            else:
                self.wsl(f"touch {home}/STOP\n", 60)
                log("asked pre-reload node daemon to drain for code update")
        # Start only with work to do: an idle daemon exits to free the desktop's memory.
        if not alive and self.c.start_daemon and needed:
            self.start_daemon()
            time.sleep(8)
            beat = json.loads(self.wsl(f"cat {home}/daemon.heartbeat.json 2>/dev/null || echo '{{}}'\n", 60)
                              .decode() or "{}")
            log(f"started node daemon (heartbeat pid {beat.get('pid')})")
        return beat

    def start_daemon(self) -> None:
        """Detach a native Linux daemon, or host WSL in a wsl.exe created through WMI.

        WSL shuts the distro down when its last wsl.exe client exits, killing
        processes started from an SSH session (even setsid/nohup ones); a
        Win32_Process created via WMI lives outside the SSH job object.
        """
        self.bind_state()
        home, lib = self.c.remote_home, self.c.remote_lib
        self.wsl(f"python3 - {shlex.quote(home)} finish <<'PYEOF'\n{DEFER}\nPYEOF\n", 60)
        self.wsl(f"rm -f {home}/STOP\n", 60)
        if self.c.native:
            command = shlex.join(["python3", f"{home}/bin/pcnode_daemon.py", "--home", home, "--lib", lib])
            # macOS ships no setsid(1); Python's os.setsid gives the same detached session.
            launcher, check = (("setsid", "command -v setsid >/dev/null\n") if self.c.transport == "linux" else
                               (shlex.join(["python3", "-c", MACOS_SETSID]), ""))
            self.wsl(f"set -eu\n{check}"
                     f"nohup {launcher} {command} </dev/null >>{shlex.quote(home + '/daemon.log')} 2>&1 &\n", 60)
            return
        user = f" -u {self.c.wsl_user}" if self.c.wsl_user else ""
        inner = (f"cd {home}/bin && exec python3 pcnode_daemon.py --home {home} --lib {lib}"
                 f" >> {home}/daemon.log 2>&1")
        script = (f"$cmd = 'wsl.exe -d {self.c.distro}{user} -- bash -lc \"{inner}\"'\n"
                  "$r = Invoke-CimMethod -ClassName Win32_Process -MethodName Create -Arguments @{CommandLine=$cmd}\n"
                  "\"$($r.ReturnValue) $($r.ProcessId)\"\n")
        result = self._run_remote([*self.ssh, "powershell", "-NoProfile", "-Command", "-"],
                                input=script.encode(), capture_output=True, timeout=60)
        if result.returncode or not result.stdout.decode().strip().startswith("0"):
            raise RuntimeError(f"WMI start failed: {result.stdout.decode()[-200:]} {result.stderr.decode()[-200:]}")

    # ------------------------------------------------------------ job bookkeeping

    def check_state(self) -> None:
        marker = self.state / "node.json"
        if marker.exists() and json.loads(marker.read_text()) != self.c.identity():
            raise ValueError("state belongs to another node; retain its ledger and use a new state")

    def bind_state(self) -> None:
        self.check_state()
        marker = self.state / "node.json"
        if marker.exists():
            return
        if self.c.native and any(self.jobs.glob("*/queue.jsonl")):
            raise ValueError("unbound jobs cannot be adopted by a Linux node; use a new state")
        self.state.mkdir(parents=True, exist_ok=True)
        temporary = self.state / f".node-{uuid.uuid4().hex}.json"
        temporary.write_text(json.dumps(self.c.identity(), sort_keys=True) + "\n")
        temporary.replace(marker)

    def remote_dir(self, name: str) -> str:
        return f"{self.c.remote_home}/inbox/{name}"

    def committed(self) -> list[Path]:
        return sorted(p.parent for p in self.jobs.glob("*/job.json"))

    def unsettled(self) -> list[Path]:
        return sorted(p for p in self.jobs.glob("*")
                      if p.is_dir() and not (p / "job.json").exists())

    def shipped_ids(self) -> set[str]:
        ids = set()
        # An unacknowledged READY may already be running; reserve its ids until reconciliation.
        for queue in self.jobs.glob("*/queue.jsonl"):
            ids |= {u["id"] for u in read_jsonl(queue)}
        return ids

    def processed(self, job: Path) -> set[str]:
        marker = job / "incoming" / "processed.txt"
        return set(marker.read_text().split()) if marker.exists() else set()

    def reconcile(self) -> None:
        """Settle job dirs a crash left without job.json: commit if READY, else unship."""
        self.bind_state()
        open_jobs = self.unsettled()
        if not open_jobs:
            return
        probe = "".join(f"test -f {self.remote_dir(p.name)}/READY && echo {p.name}\n" for p in open_jobs)
        ready = set(self.wsl(probe + "true\n", 120).decode().split())
        for job in open_jobs:
            if job.name in ready:
                queue = read_jsonl(job / "queue.jsonl")
                if not queue:
                    raise RuntimeError(f"READY job {job.name} has no local queue")
                (job / "job.json").write_text(json.dumps({"job": job.name, "units": len(queue),
                                                          "recovered": True, "at": time.time()}) + "\n")
                if (job / "blobs.json").exists():
                    self.update_index(json.loads((job / "blobs.json").read_text()))
                    (job / "blobs.json").unlink()
                (job / "job.tar.gz").unlink(missing_ok=True)
                log(f"recovered shipped job {job.name} ({len(queue)} units)")
            else:
                self.wsl(f"rm -rf {self.remote_dir(job.name)}.part {self.remote_dir(job.name)}\n", 60)
                shutil.rmtree(job, ignore_errors=True)
                log(f"unshipped interrupted job {job.name}")

    # ------------------------------------------------------------ shipping

    def _index_locked(self, change) -> set[str]:
        self.index_path.parent.mkdir(parents=True, exist_ok=True)
        with open(self.index_path.with_suffix(".lock"), "w") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            if self.c.native:
                owner = self.index_path.with_suffix(".node.json")
                if owner.exists():
                    if json.loads(owner.read_text()) != self.c.identity():
                        raise ValueError("CAS index belongs to another node")
                elif self.index_path.exists():
                    raise ValueError("unbound CAS index cannot be reused by a Linux node")
                else:
                    temporary = owner.with_suffix(".json.tmp")
                    temporary.write_text(json.dumps(self.c.identity(), sort_keys=True) + "\n")
                    temporary.replace(owner)
            if not self.index_path.exists():
                script = (f"mkdir -p {self.c.remote_lib} {self.c.remote_home}/cas\nd=$(mktemp -d)\n"
                          f"cat > $d/seed.py <<'PYEOF'\n{SEED}\nPYEOF\n"
                          f"python3 $d/seed.py {self.c.remote_lib} {self.c.remote_home}/cas; "
                          "code=$?; rm -rf $d; exit $code\n")
                known = set(self.wsl(script, 3600).decode().split())
                log(f"indexed {len(known)} node closure blobs")
            else:
                known = set(json.loads(self.index_path.read_text()))
            additions = set(change) - known
            if additions or not self.index_path.exists():
                known |= additions
                staging = self.index_path.with_suffix(".json.tmp")
                staging.write_text(json.dumps(sorted(known)))
                staging.replace(self.index_path)
            return known

    def update_index(self, blobs) -> None:
        """Record resident blobs; coordinated eviction must invalidate every shared index first."""
        self._index_locked(blobs)

    def cas_index(self) -> set[str]:
        return self._index_locked(())

    def ship(self, workload: Workload, beat: dict) -> str | None:
        self.bind_state()
        self.reconcile()
        if queued(beat, workload.name) >= self.c.low_water:
            return None
        shipped = self.shipped_ids()
        units = [u for u in workload.candidates(shipped) if u["id"] not in shipped][: self.c.max_units]
        if not units:
            return None
        closure = workload.closure(units)
        if closure and not beat.get("cas"):
            log("node daemon predates closure views; closure jobs wait for its upgrade")
            return None
        name = f"{workload.name}-{dt.datetime.now():%Y%m%d-%H%M%S}-{uuid.uuid4().hex[:12]}"
        job = self.jobs / name
        job.mkdir(parents=True)
        (job / "queue.jsonl").write_text("".join(json.dumps(u) + "\n" for u in units))
        meta = {"workload": workload.name, "priority": workload.priority, "units": len(units),
                "created": time.time(), "state": str(self.state)}
        (job / "meta.json").write_text(json.dumps(meta) + "\n")
        payload = workload.payload(units)
        manifest: dict[str, str] = {}
        blobs: dict[str, Path] = {}
        if closure:
            known = self.cas_index()
            with HashCache(self.metadata_dir) as cache:
                cache.import_legacy(self.hashes_path)
                for path, rel in closure:
                    digest = cache.digest(path)
                    manifest[rel] = digest
                    if digest not in known:
                        blobs.setdefault(digest, path)
                cache.prune()
        wire_closure = (json.dumps(manifest, sort_keys=True) + "\n").encode()
        self.closures.reference(job / "closure.json", wire_closure)
        (job / "blobs.json").write_text(json.dumps(sorted(blobs)) + "\n")
        archive = job / "job.tar.gz"
        # Dereference: closure roots may be link overlays, and a symlink would arrive dangling.
        with tarfile.open(archive, "w:gz", dereference=True, compresslevel=self.c.ship_compresslevel) as bundle:
            for entry in ("queue.jsonl", "meta.json"):
                bundle.add(job / entry, arcname=entry)
            # The node protocol still receives ordinary JSON. The control machine
            # keeps a small reference; no full per-job JSON is written to disk.
            info = tarfile.TarInfo("closure.json")
            info.size, info.mode = len(wire_closure), 0o644
            bundle.addfile(info, io.BytesIO(wire_closure))
            for path, arc in dict((arc, (path, arc)) for path, arc in payload).values():
                bundle.add(path, arcname=f"src/{arc}")
            for digest, path in blobs.items():
                bundle.add(path, arcname=f"cas/{digest}")
        remote = self.remote_dir(name)
        try:
            self.wsl(f"rm -rf {remote}.part && mkdir -p {remote}.part\n", 60)
            with archive.open("rb") as stream:
                self._run_remote(self.remote_argv("tar", "-xzf", "-", "-C", f"{remote}.part"),
                               stdin=stream, capture_output=True, check=True, timeout=3600)
            self.wsl(f"mv {remote}.part {remote} && touch {remote}/READY\n", 60)
        except Exception:
            # SSH failure cannot tell us whether READY was committed. Keep both sides
            # intact and let the next successful reconciliation decide whether to retry.
            log(f"ship {name}: awaiting reconciliation")
            raise
        (job / "job.json").write_text(json.dumps({**meta, "job": name, "closure_files": len(manifest),
                                                  "closure_blobs": len(blobs)}) + "\n")
        if blobs:
            self.update_index(blobs)
        (job / "blobs.json").unlink()
        archive.unlink()
        log(f"shipped {name}: {len(units)} units, {len(manifest)} closure files ({len(blobs)} new)")
        return name

    # ------------------------------------------------------------ receipts

    def _pull_stream(self, script: str, archive: Path, errors: Path, timeout: float) -> None:
        with self.transport_session():
            self._pull_stream_unchecked(script, archive, errors, timeout)

    def _pull_stream_unchecked(self, script: str, archive: Path, errors: Path, timeout: float) -> None:
        deadline = time.monotonic() + timeout
        command = archive.with_suffix(".sh")
        command.write_text(script)
        with command.open("rb") as source, archive.open("wb") as target, errors.open("w+b") as stderr:
            with subprocess.Popen(self.remote_argv("bash", "-s"), stdin=source, stdout=subprocess.PIPE,
                                  stderr=stderr, bufsize=0) as process:
                try:
                    received = 0
                    with selectors.DefaultSelector() as selector:
                        selector.register(process.stdout, selectors.EVENT_READ)
                        while True:
                            remaining = deadline - time.monotonic()
                            if remaining <= 0:
                                raise subprocess.TimeoutExpired(process.args, timeout)
                            if not selector.select(remaining):
                                raise subprocess.TimeoutExpired(process.args, timeout)
                            data = os.read(process.stdout.fileno(), min(1 << 20, self.c.max_pull_bytes - received + 1))
                            if not data:
                                break
                            received += len(data)
                            if received > self.c.max_pull_bytes:
                                raise RuntimeError(f"pull stream exceeds max_pull_bytes={self.c.max_pull_bytes}")
                            target.write(data)
                    process.wait(timeout=max(0, deadline - time.monotonic()))
                except BaseException:
                    if process.poll() is None:
                        process.kill()
                    process.wait()
                    raise
                if process.returncode:
                    stderr.seek(0, os.SEEK_END)
                    stderr.seek(max(0, stderr.tell() - 800))
                    error = TransportFailure if process.returncode == 255 else RuntimeError
                    raise error(f"node pull failed ({process.returncode}): {stderr.read().decode(errors='replace')}")

    def pull_all(self, jobs: list[Path], *, timeout: float = 1800) -> dict[str, list[tuple[str, dict]]]:
        """Pull complete units up to max_pull_bytes; failed transfers publish nothing."""
        self.bind_state()
        if not jobs:
            return {}
        if timeout <= 0:
            raise ValueError("pull timeout must be positive")
        known = {job.name: sorted(self.processed(job)) for job in jobs}
        if any(len(_pull_parts(job.name)) != 1 or job.parent.resolve() != self.jobs.resolve() for job in jobs):
            raise ValueError("pull jobs must belong to this state's jobs directory")
        request = json.dumps({"inbox": f"{self.c.remote_home}/inbox", "jobs": known,
                              "max_pull_bytes": self.c.max_pull_bytes,
                              "preserve_failed_outputs": self.c.preserve_failed_outputs})
        script = f"python3 -c {shlex.quote(PULL)} <<'PCNODE_PULL_REQUEST'\n{request}\nPCNODE_PULL_REQUEST\n"
        with tempfile.TemporaryDirectory(prefix=".pull-", dir=self.state) as temporary:
            staging = Path(temporary)
            archive = staging / "incoming.tar"
            self._pull_stream(script, archive, staging / "stderr", timeout)
            size = archive.stat().st_size
            if size < tarfile.RECORDSIZE or size % tarfile.RECORDSIZE:
                raise tarfile.ReadError("incomplete pull archive")
            unpacked = staging / "files"
            fresh: dict[str, list[tuple[str, dict]]] = {}
            members: set[str] = set()
            with tarfile.open(archive, mode="r:") as bundle:
                for member in bundle:
                    parts = _pull_parts(member.name)
                    if (not member.isfile() or not 0 <= member.size <= size or len(parts) < 4 or parts[0] not in known
                            or parts[1] != "incoming" or parts[2] not in ("out", "records")
                            or (parts[2] == "records" and (len(parts) != 4 or not parts[3].endswith(".json")))
                            or member.name in members):
                        raise tarfile.ReadError(f"unexpected pull member: {member.name}")
                    members.add(member.name)
                    target = unpacked.joinpath(*parts)
                    target.parent.mkdir(parents=True, exist_ok=True)
                    with bundle.extractfile(member) as source, target.open("wb") as destination:
                        shutil.copyfileobj(source, destination, length=1 << 20)
                    if parts[2] == "records":
                        if parts[3] in known[parts[0]]:
                            raise tarfile.ReadError("pull repeated a processed receipt")
                        record = json.loads(target.read_text())
                        if not isinstance(record, dict):
                            raise tarfile.ReadError("pull receipt must be an object")
                        fresh.setdefault(parts[0], []).append((parts[3], record))
                end = bundle.offset
            expected_size = ((end + 1024 + tarfile.RECORDSIZE - 1) // tarfile.RECORDSIZE) * tarfile.RECORDSIZE
            with archive.open("rb") as stream:
                stream.seek(end)
                if size != expected_size or any(stream.read(min(1 << 20, size - end))):
                    raise tarfile.ReadError("invalid pull archive trailer")
                while stream.tell() < size:
                    if any(stream.read(min(1 << 20, size - stream.tell()))):
                        raise tarfile.ReadError("invalid pull archive trailer")
            expected = set()
            for job, receipts in fresh.items():
                for name, record in receipts:
                    expected.add(f"{job}/incoming/records/{name}")
                    files = record.get("files", {})
                    if not isinstance(files, dict):
                        raise tarfile.ReadError("pull receipt needs a files object")
                    for rel in files:
                        _pull_parts(rel)
                        if record.get("exit") == 0 or self.c.preserve_failed_outputs:
                            output = f"{job}/incoming/out/{rel}"
                            if output in expected:
                                raise tarfile.ReadError("pull receipts share an output path")
                            expected.add(output)
            if members != expected:
                raise tarfile.ReadError("pull receipt and output set disagree")
            # Check every destination before moving anything; tar links are never extracted.
            for name in members:
                parts = _pull_parts(name)
                target = self.jobs
                for part in parts[:-1]:
                    target /= part
                    if target.is_symlink() or (target.exists() and not target.is_dir()):
                        raise tarfile.ReadError(f"unsafe local pull destination: {name}")
                target /= parts[-1]
                if target.is_symlink() or (target.exists() and not target.is_file()):
                    raise tarfile.ReadError(f"unsafe local pull destination: {name}")
            for name in sorted(members, key=lambda name: _pull_parts(name)[2] == "records"):
                target = self.jobs / name
                target.parent.mkdir(parents=True, exist_ok=True)
                (unpacked / name).replace(target)
            return fresh

    def preserve_failure(self, job: Path, receipt: str, record: dict,
                         files: dict[str, Path], reasons: list[str]) -> Path | None:
        """Save rejected bytes before acknowledging or deleting their original outputs."""
        if not self.c.preserve_failed_outputs:
            return None
        if (len(_pull_parts(job.name)) != 1 or job.parent.resolve() != self.jobs.resolve()
                or len(_pull_parts(receipt)) != 1 or not receipt.endswith(".json")
                or len(_pull_parts(receipt.removesuffix(".json"))) != 1):
            raise ValueError("unsafe failed result identity")
        target = self.state / "failed-results" / job.name / receipt.removesuffix(".json")
        parent = self.state
        for part in target.relative_to(self.state).parts:
            parent /= part
            if parent.is_symlink() or (parent.exists() and not parent.is_dir()):
                raise ValueError("unsafe failed result destination")
        source = job / "incoming" / "records" / receipt
        original = source.read_bytes()
        checks = {}
        for rel, path in files.items():
            _pull_parts(rel)
            if path.is_symlink() or not path.is_file():
                raise ValueError(f"missing failed output: {rel}")
            actual = sha(path)
            checks[rel] = {"sha256": actual, "expected_sha256": record["files"][rel],
                           "matches_receipt": actual == record["files"][rel]}
        manifest = {"job": job.name, "id": record.get("id"), "node": self.c.identity(),
                    "transport_exit": record.get("exit"), "reasons": reasons, "files": checks,
                    "receipt_sha256": hashlib.sha256(original).hexdigest(), "accepted": False}
        if target.exists():
            for rel in ("receipt.json", "preservation.json", *("outputs/" + rel for rel in checks)):
                path = target
                for part in _pull_parts(rel):
                    path /= part
                    if path.is_symlink():
                        raise ValueError("unsafe preserved failed output")
            saved = json.loads((target / "preservation.json").read_text())
            if (saved != manifest or (target / "receipt.json").read_bytes() != original
                    or any(sha(target / "outputs" / rel) != row["sha256"]
                           for rel, row in checks.items())):
                raise ValueError("failed result conflicts with its preserved original")
            return target
        target.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
        with tempfile.TemporaryDirectory(prefix=".failed-", dir=target.parent) as temporary:
            staging = Path(temporary) / "result"
            staging.mkdir(mode=0o700)
            for rel, path in files.items():
                destination = staging / "outputs" / rel
                destination.parent.mkdir(parents=True, exist_ok=True)
                try:
                    os.link(path, destination)
                except OSError:
                    shutil.copyfile(path, destination)
            (staging / "receipt.json").write_bytes(original)
            (staging / "preservation.json").write_text(json.dumps(manifest, indent=2) + "\n")
            staging.rename(target)
        return target

    def report(self, job: Path, record: dict, reasons: list[str], workload: Workload,
               artifacts: Path | None = None) -> None:
        row = {"job": job.name, "id": record.get("id"), "exit": record.get("exit"),
               "reasons": reasons, "output": str(record.get("output", ""))[-1500:]}
        if artifacts is not None:
            row["artifacts"] = str(artifacts)
        append_jsonl(self.failures, row)
        workload.failed(record, reasons)

    def accept(self, workload: Workload, job: Path, fresh: list[tuple[str, dict]]) -> tuple[int, int]:
        self.bind_state()
        incoming = job / "incoming"
        promoted = failed = 0
        processed = self.processed(job)
        for receipt, record in fresh:
            if receipt in processed:
                continue
            try:
                reasons = []
                if record.get("exit") != 0:
                    reasons.append(f"exit {record.get('exit')}")
                if record.get("missing"):
                    reasons.append(f"missing outputs {record['missing']}")
                if record.get("host") != self.c.host:
                    reasons.append(f"host {record.get('host')}")
                if record.get("kind") == "lean" and self.c.githash and record.get("githash") != self.c.githash:
                    reasons.append(f"githash {record.get('githash')}")
                files = {rel: incoming / "out" / rel for rel in record.get("files", {})}
                if record.get("exit") == 0 or self.c.preserve_failed_outputs:
                    for rel, digest in record["files"].items():
                        if not files[rel].is_file() or sha(files[rel]) != digest:
                            reasons.append(f"file hash {rel}")
                if reasons:
                    artifacts = self.preserve_failure(job, receipt, record, files, reasons)
                    self.report(job, record, reasons, workload, artifacts)
                    outcome = "failed"
                else:
                    outcome = workload.accept(record, files)
                    if outcome == "failed":
                        self.preserve_failure(job, receipt, record, files, ["adapter rejected result"])
            except Exception as error:  # leave unprocessed: pulled again next loop
                log(f"accept {record.get('id')} deferred: {error!r}"[:300])
                continue
            promoted += outcome == "promoted"
            failed += outcome == "failed"
            with (incoming / "processed.txt").open("a") as stream:
                stream.write(receipt + "\n")
            processed.add(receipt)
            for path in files.values():
                path.unlink(missing_ok=True)
        return promoted, failed

    def tidy_all(self, jobs: list[Path]) -> None:
        """Drop processed job payloads and the remote copy of a verified local closure."""
        self.bind_state()
        ready = []
        for job in jobs:
            queue = read_jsonl(job / "queue.jsonl")
            expected = {re.sub(r"[^A-Za-z0-9._-]", "_", u["id"]) + ".json" for u in queue}
            if queue and len(expected) == len(queue) and expected <= self.processed(job):
                ready.append(job)
        if not ready:
            return
        # DONE appears on the daemon's next queue scan (<= 15 s); until then retry next loop.
        requests = [{"path": self.remote_dir(j.name),
                     "closure_sha256": closure_sha256(j / "closure.json")
                     if (j / "closure.json").is_file() and not (j / "closure.json").is_symlink() else None}
                    for j in ready]
        # Completed jobs are skipped by the daemon. Keep the original local manifest,
        # rather than thousands of redundant multi-megabyte copies in the remote inbox.
        script = "python3 - <<'TIDYPY'\nrequests = " + repr(requests) + "\n" + r"""
import hashlib, os, shutil, stat
from pathlib import Path
for request in requests:
    job = Path(request['path'])
    if job.is_symlink() or not (job / 'DONE').is_file() or (job / 'DONE').is_symlink():
        continue
    for name in ('src', 'lib', 'cas', 'out', 'run'):
        path = job / name
        if path.is_symlink() or path.is_file():
            path.unlink()
        elif path.is_dir():
            shutil.rmtree(path)
    path = job / 'closure.json'
    if request['closure_sha256'] and path.exists() and not path.is_symlink():
        with os.fdopen(os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK), 'rb') as stream:
            before = os.fstat(stream.fileno())
            digest = hashlib.file_digest(stream, 'sha256').hexdigest() if stat.S_ISREG(before.st_mode) else None
        after = path.lstat()
        key = lambda s: (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
        if digest == request['closure_sha256'] and key(before) == key(after):
            path.unlink()
    print('cleaned', job.name)
""" + "\nTIDYPY\n"
        cleaned = {line.split()[1] for line in self.wsl(script, 120).decode().splitlines()
                   if line.startswith("cleaned ")}
        for job in ready:
            if job.name in cleaned:
                shutil.rmtree(job / "incoming" / "out", ignore_errors=True)
                (job / "incoming" / "remote-cleaned").write_text(f"{time.time()}\n")

    def cancel_queued(self, unit_ids: list[str]) -> list[dict]:
        """Request only named queued units; running siblings and the reader continue."""
        self.bind_state()
        if (not unit_ids or any(not isinstance(uid, str) or not uid for uid in unit_ids)
                or len(set(unit_ids)) != len(unit_ids)):
            raise ValueError("distinct queued unit ids are required")
        requests = []
        for uid in unit_ids:
            matches = [(j, u) for j in self.committed()
                       for u in read_jsonl(j / "queue.jsonl") if u.get("id") == uid]
            if len(matches) != 1:
                raise ValueError("queued id must identify one committed same-state unit: " + uid)
            job, unit = matches[0]
            requests.append({"job": self.remote_dir(job.name), "id": uid})
        script = "python3 - <<'CANCELPY'\n" + "requests = " + repr(requests) + "\n" + r"""
import hashlib, json, time
from pathlib import Path
for request in requests:
    job = Path(request["job"])
    queue = [json.loads(line) for line in (job / "queue.jsonl").read_text().splitlines() if line.strip()]
    if not (job / "READY").exists() or not any(u.get("id") == request["id"] for u in queue):
        raise RuntimeError("queued cancellation must identify a READY unit")
for request in requests:
    job = Path(request["job"])
    target = job / "CANCEL_QUEUED" / (hashlib.sha256(request["id"].encode()).hexdigest() + ".json")
    target.parent.mkdir(exist_ok=True)
    temporary = target.with_suffix(".tmp")
    temporary.write_text(json.dumps({"id": request["id"], "requested_unix": time.time()}) + "\n")
    temporary.replace(target)
""" + "\nCANCELPY\n"
        self.wsl(script, 60)
        return requests

    def cancel(self) -> list[str]:
        """Write CANCEL into every open job of this state on the node; returns their names."""
        self.reconcile()
        jobs = [j for j in self.committed() if not (j / "incoming" / "remote-cleaned").exists()]
        if jobs:
            self.wsl("".join(f"d={shlex.quote(self.remote_dir(j.name))}; test -d $d && touch $d/CANCEL\n"
                             for j in jobs) + "true\n", 120)
        return [j.name for j in jobs]

    # ------------------------------------------------------------ loop

    def once(self, workload: Workload) -> dict:
        self.bind_state()
        status: dict = {"at": time.time()}
        try:
            with self.transport_session():
                self._once_remote(workload, status)
        except Exception as error:
            status.setdefault("node_error", repr(error)[:300])
            transport = self.guard.snapshot()
            notice = (transport["epoch"], repr(error) if transport["phase"] == "healthy" else transport["phase"])
            if notice != self._last_transport_notice:
                log(f"node transport suspended: {error!r}"[:300])
                self._last_transport_notice = notice
        status["transport"] = self.guard.snapshot()
        if status["transport"]["phase"] == "healthy":
            self._last_transport_notice = None
        try:
            status["workload"] = workload.tick()
        except Exception:
            log("workload tick error\n" + traceback.format_exc()[-800:])
        (self.state / "status.json").write_text(json.dumps(status, indent=2) + "\n")
        progress = {k: (status.get("workload") or {}).get(k) for k in ("total", "accepted", "failed")}
        if progress["accepted"] is not None and progress != self.last_progress:
            append_jsonl(self.state / "progress.jsonl", {"at": status["at"], **progress})
            self.last_progress = progress
        return status

    def _once_remote(self, workload: Workload, status: dict) -> None:
        beat = None
        open_jobs = [j for j in self.committed() if not (j / "incoming" / "remote-cleaned").exists()]
        try:
            beat = self.deploy_and_heartbeat(needed=bool(open_jobs) or bool(self.unsettled())
                                            or not workload.finished())
            status["node"] = {k: v for k, v in beat.items() if k != "units"}
        except Exception as error:
            status["node_error"] = repr(error)[:300]
            if is_transport_failure(error) or isinstance(error, TransportBlocked):
                raise
            log(f"node unreachable: {error!r}"[:300])
        if beat is not None:
            try:
                self.reconcile()
            except Exception as error:
                status["reconcile_error"] = repr(error)[:300]
                if is_transport_failure(error) or isinstance(error, TransportBlocked):
                    raise
                log(f"reconcile failed: {error!r}"[:300])
            try:  # Refill independent work before a large pull can hold up the queue.
                if "reconcile_error" not in status:
                    status["shipped"] = self.ship(workload, beat)
            except Exception as error:
                status["ship_error"] = repr(error)[:300]
                if is_transport_failure(error) or isinstance(error, TransportBlocked):
                    raise
                log("ship error\n" + traceback.format_exc()[-800:])
            open_jobs = [j for j in self.committed() if not (j / "incoming" / "remote-cleaned").exists()]
            totals = [0, 0]
            try:  # settled jobs (remote-cleaned) cannot receive receipts any more
                fresh = self.pull_all(open_jobs)
                for job in open_jobs:
                    if fresh.get(job.name):
                        promoted, failed = self.accept(workload, job, fresh[job.name])
                        totals[0] += promoted
                        totals[1] += failed
                        log(f"{job.name}: pulled {len(fresh[job.name])}, promoted {promoted}, failed {failed}")
                self.tidy_all(open_jobs)
            except Exception as error:
                status["pull_error"] = repr(error)[:1200]
                status["promoted"], status["failed"] = totals
                if is_transport_failure(error) or isinstance(error, TransportBlocked):
                    raise
                log(f"pull failed: {error!r}"[:300])
            status["promoted"], status["failed"] = totals
            try:  # A just-accepted dependency may be the first ready work of this pass.
                if status.get("shipped", "not-attempted") is None and totals[0]:
                    status["shipped"] = self.ship(workload, beat)
            except Exception as error:
                status["ship_error"] = repr(error)[:300]
                if is_transport_failure(error) or isinstance(error, TransportBlocked):
                    raise
                log("ship error\n" + traceback.format_exc()[-800:])


def main_exit(reason: str) -> None:
    sys.exit(RELOAD_EXIT if reason == "reload" else 0)


def code_digest(workload: Workload) -> str:
    paths = {Path(__file__).resolve(), Path(inspect.getfile(type(workload))).resolve(),
             Path(sys.argv[0]).resolve(), Path(__file__).resolve().with_name("transport_guard.py"),
             Path(__file__).resolve().with_name("local_metadata.py")}
    return "".join(sha(p) for p in sorted(paths) if p.is_file())


RELOAD_EXIT = 75  # run_supervisor.sh restarts at once on this code, stops on 0, retries on crashes


def run(workload: Workload, config: Config, state: Path, *, once: bool = False,
        until_done: bool = False) -> str:
    """Drive one workload; returns why it stopped: finished | stop | once | reload | locked."""
    state.mkdir(parents=True, exist_ok=True)
    node = Node(config, state)
    node.jobs.mkdir(exist_ok=True)
    lock = open(state / "loop.lock", "w")
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        log(f"another loop holds {state}/loop.lock; exiting")
        return "locked"
    code = code_digest(workload)
    (state / "FINISHED").unlink(missing_ok=True)
    while True:
        started = time.time()
        node.once(workload)
        open_jobs = [j for j in node.committed() if not (j / "incoming" / "remote-cleaned").exists()]
        if until_done and workload.finished() and not open_jobs and not node.unsettled():
            log("workload finished")
            (state / "FINISHED").write_text(f"{time.time()}\n")  # resume.sh skips it at login
            return "finished"
        if once:
            return "once"
        if (state / "STOP").exists():
            return "stop"
        if code_digest(workload) != code:
            log("code changed; exiting for restart")
            return "reload"
        time.sleep(max(5, config.interval - (time.time() - started)))
