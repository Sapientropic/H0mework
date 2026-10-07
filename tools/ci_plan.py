"""Partition the default Lake module closure and transport its checked artifacts."""

from __future__ import annotations

import argparse
import collections
from collections import defaultdict, deque
from dataclasses import dataclass
import hashlib
import json
import math
import io
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import statistics
import subprocess
import sys
import tarfile
import tempfile
import time
import tomllib
import urllib.error
import urllib.parse
import urllib.request

from first_release import build_environment


CACHE_VERSION = "lean-parts-v1"
# Changing these re-runs the complete-selection check; part caches stay valid.
CI_FILES = ("tools/ci_plan.py", ".github/workflows/ci.yml", ".github/workflows/lean-part.yml")
# Seconds per module on a hosted runner, refreshed from CI logs with `ci_plan.py times`.
TIMES = "tools/ci_times.tsv"
# Committed module -> shard placement; `plan --rebalance` rewrites it from scratch.
LAYOUT = "tools/ci_layout.tsv"
DEFAULT_SECONDS = 10.0


def without_comments(text: str) -> str:
    # Lean block comments nest. Keep newlines so import declarations remain separate.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            out.extend("  ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            out.extend("  ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end == -1 else end
        elif text[i] == '"':
            start = i
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append(text[start:i])
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError("Unclosed Lean block comment")
    return "".join(out)


def imports(text: str) -> list[str]:
    # Only the header can declare imports; proof strings and examples are irrelevant.
    result = []
    for line in without_comments(text).splitlines():
        line = line.strip()
        if not line or line in {"module", "prelude"}:
            continue
        match = re.fullmatch(r"(?:(?:public|private|meta)\s+)*import\s+(.+)", line)
        if not match:
            break
        result.extend(n for n in match[1].split() if n not in {"all", "meta"})
    return result


def matches(name: str, glob: str) -> bool:
    if glob.endswith(".+"):
        return name.startswith(glob[:-1])
    if glob.endswith(".*"):
        return name == glob[:-2] or name.startswith(glob[:-1])
    return name == glob


def closure(roots, dependencies):
    seen, pending = set(roots), deque(roots)
    while pending:
        for dep in dependencies[pending.popleft()]:
            if dep not in seen:
                seen.add(dep)
                pending.append(dep)
    return seen


@dataclass(frozen=True)
class Layout:
    """Stage geometry in seconds of one hosted runner thread."""
    window: float = 2.75 * 3600       # dependency chain one stage may advance
    workers: int = 4
    fill: float = 0.9                 # share of a runner's window given to one shard's work
    shared_users: int = 3             # shards that would each rebuild a module
    shared_chain: float = 0.5 * 3600  # longest chain worth a short stage of its own
    max_shards: int = 20              # concurrent jobs on a free account
    max_stages: int = 8               # stage jobs defined in ci.yml
    copy_share: float = 0.05          # rebuilt same-stage imports a new module may cost a shard

    @property
    def capacity(self) -> float:
        return self.workers * self.window * self.fill


def read_times(path: Path) -> dict[str, float]:
    if not path.is_file():
        return {}
    times = {}
    for line in path.read_text().splitlines():
        seconds, name = line.split("\t")
        times[name] = float(seconds)
    return times


def estimate_costs(modules, times: dict[str, float]) -> dict[str, float]:
    # An unmeasured module takes the median of its nearest namespace with enough measurements.
    samples = defaultdict(list)
    for name, seconds in times.items():
        parts = name.split(".")
        for k in range(1, len(parts)):
            samples[".".join(parts[:k])].append(seconds)
    medians = {k: statistics.median(v) for k, v in samples.items() if len(v) >= 5}
    fallback = statistics.median(times.values()) if times else DEFAULT_SECONDS
    costs = {}
    for name in modules:
        parts = name.split(".")
        prefixes = (".".join(parts[:k]) for k in range(len(parts) - 1, 0, -1))
        estimate = times[name] if name in times else next((medians[p] for p in prefixes if p in medians), fallback)
        costs[name] = max(estimate, 0.01)
    return costs


def ancestors_within(starts, dependencies, members):
    seen, pending = set(starts), list(starts)
    while pending:
        for dep in dependencies[pending.pop()]:
            if dep in members and dep not in seen:
                seen.add(dep)
                pending.append(dep)
    return seen


def sinks_of(members, dependencies):
    imported = {d for n in members for d in dependencies[n] if d in members}
    return sorted(members - imported)


def pack_shards(members, dependencies, cost, capacity, layout):
    """Group the sinks of one stage so that each shard builds the closure it needs.

    A shard also rebuilds same-stage modules owned by another shard; packing keeps those
    copies small by placing each sink where its closure is mostly built already.
    """
    sinks = sinks_of(members, dependencies)
    closures = {s: ancestors_within([s], dependencies, members) for s in sinks}
    work = {s: sum(cost[n] for n in closures[s]) for s in sinks}
    shards = []
    for sink in sorted(sinks, key=lambda s: (-work[s], s)):
        best, best_load = None, None
        for shard in shards:
            extra = sum(cost[n] for n in closures[sink] - shard["build"])
            load = shard["work"] + extra
            if (load <= capacity or len(shards) >= layout.max_shards) and (best is None or load < best_load):
                best, best_load = shard, load
        if best is None:
            best = {"sinks": [], "build": set(), "work": 0.0}
            shards.append(best)
            best_load = work[sink]
        best["sinks"].append(sink)
        best["build"] |= closures[sink]
        best["work"] = best_load
    return sorted(shards, key=lambda shard: min(shard["sinks"]))


def stage_plan(dependencies, cost, layout: Layout = Layout()):
    """Assign modules to stages of parallel shards.

    Stages follow the dependency chain in windows of `layout.window`. Inside a stage, a
    module needed by several shards is published first in a short stage when its chain is
    short; a sink whose closure cannot fit one shard waits for the next stage.
    """
    order = dependency_order(dependencies)
    finish = {}
    for name in order:
        finish[name] = cost[name] + max((finish[d] for d in dependencies[name]), default=0.0)
    window = {n: max(0, math.ceil(finish[n] / layout.window) - 1) for n in order}
    position = {n: i for i, n in enumerate(order)}
    stages, pending, current_window = [], set(order), 0
    while pending:
        members = {n for n in pending if window[n] <= current_window}
        while members:
            local = {}
            for name in sorted(members, key=position.get):
                local[name] = cost[name] + max((local[d] for d in dependencies[name] if d in members), default=0.0)
            waiting = [s for s in sinks_of(members, dependencies)
                       if any(d in members for d in dependencies[s])
                       and (local[s] > layout.window
                            or sum(cost[n] for n in ancestors_within([s], dependencies, members)) > layout.capacity)]
            if not waiting:
                break
            for sink in waiting:
                window[sink] = current_window + 1
                members.discard(sink)
        if members:
            users = defaultdict(int)
            for sink in sinks_of(members, dependencies):
                for name in ancestors_within([sink], dependencies, members):
                    users[name] += 1
            shared = [n for n in members if users[n] >= layout.shared_users and local[n] <= layout.shared_chain]
            early = ancestors_within(shared, dependencies, members)
            if early and early != members:
                short = layout.workers * max(layout.shared_chain, max(local[n] for n in early)) * layout.fill
                stages.append(pack_shards(early, dependencies, cost, short, layout))
                pending -= early
                members -= early
            stages.append(pack_shards(members, dependencies, cost, layout.capacity, layout))
            pending -= members
        current_window += 1
    if len(stages) > layout.max_stages:
        raise ValueError(f"{len(stages)} stages exceed the {layout.max_stages} stage jobs in ci.yml")
    return stages


def dependency_order(dependencies):
    order, seen = [], set()
    for start in sorted(dependencies):
        if start in seen:
            continue
        seen.add(start)
        stack = [(start, iter(dependencies[start]))]
        while stack:
            name, pending = stack[-1]
            for dep in pending:
                if dep not in seen:
                    seen.add(dep)
                    stack.append((dep, iter(dependencies[dep])))
                    break
            else:
                stack.pop()
                order.append(name)
    return order


def digest(records) -> str:
    return hashlib.sha256(json.dumps(records, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def make_plan(root: Path, layout: Layout = Layout(), rebalance: bool = False) -> dict:
    lean = root / "Lean"
    config = tomllib.loads((lean / "lakefile.toml").read_text())
    libraries = config["lean_lib"]
    defaults = set(config["defaultTargets"])
    by_name = {lib["name"]: lib for lib in libraries}
    if not defaults <= by_name.keys():
        raise ValueError("CI partition requires module libraries as default targets")
    files = {".".join(p.relative_to(lean).with_suffix("").parts): p
             for p in sorted((lean / "H0mework").rglob("*.lean"))}
    files["H0mework"] = lean / "H0mework.lean"
    owners, selected = {}, set()
    source_hashes, all_imports = {}, {}
    for name, path in files.items():
        owners_for_module = [lib for lib in libraries if any(matches(name, g) for g in lib["globs"])]
        if len(owners_for_module) != 1:
            raise ValueError(f"Expected one owning library for {name}")
        owners[name] = owners_for_module[0]
        if owners[name]["name"] in defaults:
            selected.add(name)
        source = path.read_bytes()
        source_hashes[name] = hashlib.sha256(source).hexdigest()
        all_imports[name] = imports(source.decode())
    for name, deps in all_imports.items():
        missing = [n for n in deps if (n == "H0mework" or n.startswith("H0mework.")) and n not in files]
        if missing:
            raise ValueError(f"Missing local imports in {name}: {missing}")
    local = {n: [d for d in ds if d in files] for n, ds in all_imports.items()}
    selected = closure(selected, local)
    if any(owners[n]["name"] not in defaults for n in selected):
        raise ValueError("A default module imports a non-default library")
    dependencies = {n: local[n] for n in selected}
    cost = estimate_costs(dependencies, read_times(root / TIMES))
    previous = {} if rebalance else read_layout(root / LAYOUT)
    if previous:
        assignment = sticky_assignment(dependencies, cost, previous, layout)
    else:
        assignment = full_assignment(dependencies, cost, layout)
    shards = shards_from(assignment, dependencies, cost)
    slots = sorted({shard["stage"] for shard in shards.values()})
    if len(slots) > layout.max_stages:
        raise ValueError(f"{len(slots)} stages exceed the {layout.max_stages} stage jobs in ci.yml; rebalance")

    resources = {r["name"]: r for r in config.get("input_file", [])}
    resource_hashes = {
        n: hashlib.sha256((lean / r["path"]).read_bytes()).hexdigest() for n, r in resources.items()
    }
    toolchain = (lean / "lean-toolchain").read_text().strip()
    manifest = (lean / "lake-manifest.json").read_bytes()
    compatibility = digest([toolchain, hashlib.sha256(manifest).hexdigest()])[:24]
    # New globs or paper targets do not change an existing module's compiler settings.
    # Lake excludes weakLeanArgs from build traces, so budget changes reuse artifacts in either scope.
    package_options = {k: v for k, v in config.items()
                       if k not in {"defaultTargets", "lean_lib", "input_file", "weakLeanArgs"}}
    position = {n: i for i, n in enumerate(dependency_order(dependencies))}
    parts = {}
    for name, shard in sorted(shards.items(), key=lambda item: (item[1]["stage"], item[0])):
        inputs = closure(shard["owned"], dependencies)
        upstream = sorted({assignment[n] for n in inputs - shard["build"]})
        if any(shards[u]["stage"] >= shard["stage"] for u in upstream):
            raise ValueError(f"{name} imports from its own or a later stage")
        needed = sorted({r for n in inputs for r in owners[n].get("needs", [])})
        if any(n not in resources for n in needed):
            raise ValueError(f"Unknown resource input in {name}")
        module_options = {
            n: {k: v for k, v in owners[n].items() if k not in {"globs", "roots", "weakLeanArgs"}}
            for n in inputs
        }
        targets = ["+" + n for n in shard["targets"]]
        fingerprint = digest({
            "modules": {n: source_hashes[n] for n in sorted(inputs)},
            "owned": shard["owned"], "targets": targets, "options": module_options,
            "package": package_options,
            "resources": {n: [resources[n], resource_hashes[n]] for n in needed},
        })
        chain = {}
        for n in sorted(shard["build"], key=position.get):
            chain[n] = cost[n] + max((chain[d] for d in dependencies[n] if d in chain), default=0.0)
        parts[name] = {
            "stage": shard["stage"], "modules": shard["owned"], "targets": targets,
            "progress_modules": sorted(shard["build"]),
            "upstream": upstream, "fingerprint": fingerprint, "module_count": len(shard["owned"]),
            "hours": round(max(shard["work"] / layout.workers, max(chain.values())) / 3600, 2),
        }
    # The verified-selection record exists only after every part of exactly this
    # content passed together, so a run decides from content, not from its diff.
    ci_files = {p: hashlib.sha256((root / p).read_bytes()).hexdigest()
                for p in CI_FILES if (root / p).is_file()}
    selection = digest({"version": CACHE_VERSION, "compatibility": compatibility, "ci": ci_files,
                        "parts": {g: p["fingerprint"] for g, p in parts.items()}})
    # Stage numbers stay in shard names so that caches survive; jobs run them in order.
    stages = [[n for n, p in parts.items() if p["stage"] == stage] for stage in slots]
    parts["complete"] = {"stage": slots[-1] + 1, "modules": [], "targets": [], "upstream": sorted(parts),
                         "progress_modules": [], "fingerprint": selection, "module_count": 0, "hours": 0.0}
    return {"version": CACHE_VERSION, "compatibility": compatibility, "selection": selection,
            "module_count": len(selected), "libraries": sorted(defaults), "stages": stages,
            "parts": parts, "assignment": assignment, "placed": len(set(assignment) - set(previous))}


def stage_number(shard: str) -> int:
    return int(shard[1:shard.index("-")])


def family(name: str) -> str:
    parts = name.split(".")
    return ".".join(parts[:5] if parts[1:2] == ["Versions"] else parts[:3])


def read_layout(path: Path) -> dict[str, str]:
    if not path.is_file():
        return {}
    return dict(reversed(line.split("\t")) for line in path.read_text().splitlines())


def write_layout(path: Path, assignment: dict[str, str]):
    path.write_text("".join(f"{shard}\t{name}\n" for name, shard in sorted(assignment.items())))


def full_assignment(dependencies, cost, layout: Layout) -> dict[str, str]:
    # A shard owns the modules it builds first; a later shard of the same stage that also
    # needs them builds a private copy and leaves them out of its archive.
    assignment = {}
    for k, shards in enumerate(stage_plan(dependencies, cost, layout), 1):
        for j, shard in enumerate(shards, 1):
            for name in sorted(shard["build"]):
                assignment.setdefault(name, f"s{k}-{j:02d}")
    return assignment


def sticky_assignment(dependencies, cost, previous: dict[str, str], layout: Layout) -> dict[str, str]:
    """Keep committed placements and put new or displaced modules beside their imports.

    Existing shards then change only by gaining modules, so a migration rebuilds little
    more than what it adds. A module whose same-stage imports live in other shards would
    have to rebuild them; when those copies cost more than a small share of a shard, it
    waits one stage instead.
    """
    assignment, load = {}, defaultdict(float)
    by_stage, families = defaultdict(set), defaultdict(collections.Counter)
    members = defaultdict(set)
    for shard in previous.values():
        by_stage[stage_number(shard)].add(shard)

    def place(name):
        imports_ = dependencies[name]
        stage = max((stage_number(assignment[d]) for d in imports_), default=1)
        same = [d for d in imports_ if stage_number(assignment[d]) == stage]
        home = collections.Counter(assignment[d] for d in same).most_common(1)[0][0] if same else None
        if home is not None and load[home] + cost[name] > layout.capacity:
            home = None
        others = [d for d in same if assignment[d] != home]
        copies = sum(cost[n] for n in ancestors_within(others, dependencies, members[stage])
                     if assignment[n] != home)
        if copies > layout.capacity * layout.copy_share:
            stage, home = stage + 1, None
        if home is not None:
            return home
        room = [s for s in by_stage[stage] if load[s] + cost[name] <= layout.capacity]
        if room:
            return max(room, key=lambda s: (families[s][family(name)], -load[s], s))
        taken = [int(s.split("-")[1]) for s in by_stage[stage]]
        return f"s{stage}-{max(taken, default=0) + 1:02d}"

    for name in dependency_order(dependencies):
        shard = previous.get(name)
        if shard is None or any(stage_number(assignment[d]) > stage_number(shard) for d in dependencies[name]):
            shard = place(name)
        assignment[name] = shard
        load[shard] += cost[name]
        families[shard][family(name)] += 1
        members[stage_number(shard)].add(name)
        by_stage[stage_number(shard)].add(shard)
    return assignment


def shards_from(assignment: dict[str, str], dependencies, cost) -> dict[str, dict]:
    owned, members = defaultdict(list), defaultdict(set)
    for name, shard in assignment.items():
        owned[shard].append(name)
        members[stage_number(shard)].add(name)
    shards = {}
    for shard, names in owned.items():
        names = set(names)
        imported = {d for n in names for d in dependencies[n] if d in names}
        targets = sorted(names - imported)
        build = ancestors_within(targets, dependencies, members[stage_number(shard)])
        shards[shard] = {"stage": stage_number(shard), "owned": sorted(names), "targets": targets,
                         "build": build, "work": sum(cost[n] for n in build)}
    return shards


def artifact_pattern(upstream: list[str]) -> str:
    if not upstream:
        return ""
    names = upstream[0] if len(upstream) == 1 else "{" + ",".join(upstream) + "}"
    return f"lean-part-{names}"


def completed_setup_files(build: Path) -> int:
    count = 0
    for setup in (build / "ir").rglob("*.setup.json"):
        relative = setup.relative_to(build / "ir")
        trace = build / "lib/lean" / str(relative).removesuffix(".setup.json")
        trace = trace.with_name(trace.name + ".trace")
        try:
            if trace.stat().st_mtime_ns >= setup.stat().st_mtime_ns:
                setup.unlink()
                count += 1
        except FileNotFoundError:
            continue
    return count


def append_outputs(path, values: dict):
    if path:
        with open(path, "a") as stream:
            for key, value in values.items():
                stream.write(f"{key}={value}\n")


def built_since(build: Path, modules: list[str], since_ns: int) -> int:
    count = 0
    for name in modules:
        trace = build / "lib/lean" / (str(Path(*name.split("."))) + ".trace")
        try:
            count += trace.stat().st_mtime_ns >= since_ns
        except FileNotFoundError:
            continue
    return count


def stop_group(process: subprocess.Popen, grace: float):
    # Lake runs in its own session, so its process group also holds every lean it started.
    for sig, wait in ((signal.SIGINT, grace), (signal.SIGTERM, 5.0), (signal.SIGKILL, 5.0)):
        try:
            os.killpg(process.pid, sig)
        except ProcessLookupError:
            return
        end = time.monotonic() + wait
        while time.monotonic() < end:
            process.poll()
            try:
                os.killpg(process.pid, 0)
            except ProcessLookupError:
                return
            time.sleep(0.1)


def build_part(root: Path, part: dict, check_only: bool = False, output: Path | None = None,
               deadline: float | None = None, checkpoint=None, checkpoint_interval: float = 300) -> int:
    append_outputs(output, {"started": "true"})
    if not part["targets"]:
        append_outputs(output, {"current": "true", "status": "complete", "built": 0})
        return 0
    command = ["lake", "--no-build", "build", *part["targets"]]
    environment = build_environment()
    # The cache client uses the token; Lake and its compiler children do not.
    environment.pop("GH_TOKEN", None)
    print(f"Lean runtime: LEAN_NUM_THREADS={environment['LEAN_NUM_THREADS']}", flush=True)
    probe = subprocess.run(command, cwd=root / "Lean", capture_output=True, text=True, env=environment)
    append_outputs(output, {"current": str(probe.returncode == 0).lower()})
    if probe.returncode == 0:
        print(f"All {part['module_count']} module artifacts are current")
        append_outputs(output, {"status": "complete", "built": 0})
        return 0
    if check_only or probe.returncode != 3:
        print(probe.stdout + probe.stderr, file=sys.stderr)
        append_outputs(output, {"status": "failed", "built": 0})
        return probe.returncode
    build = root / "Lean/.lake/build"
    started = time.time_ns()
    stopped = None
    progress_modules = part.get("progress_modules", part["modules"])
    checkpoint_built = 0

    def interrupted(signum, frame):
        nonlocal stopped
        stopped = stopped or "cancelled"

    previous = {sig: signal.signal(sig, interrupted) for sig in (signal.SIGINT, signal.SIGTERM)}
    try:
        # Lake decides freshness; a cache hit never bypasses resource/hash checks.
        process = subprocess.Popen(["lake", "build", *part["targets"]], cwd=root / "Lean",
                                   start_new_session=True, env=environment)
        swept = time.monotonic()
        checkpointed = swept
        while process.poll() is None and not stopped:
            if deadline is not None and time.time() >= deadline:
                stopped = "incomplete"
            elif checkpoint and time.monotonic() - checkpointed >= checkpoint_interval:
                built = built_since(build, progress_modules, started)
                if built > checkpoint_built and checkpoint():
                    checkpoint_built = built
                    print(f"Saved live progress after {built} completed modules", flush=True)
                checkpointed = time.monotonic()
            elif time.monotonic() - swept >= 5:
                completed_setup_files(build)
                swept = time.monotonic()
            else:
                time.sleep(0.5)
        if stopped:
            # Lake writes a module's trace only after its outputs, so stopping keeps every
            # finished module reusable and rebuilds the interrupted ones next time.
            stop_group(process, 30.0 if stopped == "incomplete" else 3.0)
    finally:
        for sig, handler in previous.items():
            signal.signal(sig, handler)
        completed_setup_files(build)
    code = {"incomplete": 75, "cancelled": 130}.get(stopped, process.returncode)
    status = stopped or ("complete" if code == 0 else "failed")
    # Same-stage imports may be owned by another shard but are useful progress here.
    built = built_since(build, progress_modules, started)
    append_outputs(output, {"status": status, "built": built})
    print(f"{status}: {built} of {len(progress_modules)} build-scope modules built in this job")
    return code


def artifact_files(build: Path, modules: list[str]):
    for name in modules:
        relative = Path(*name.split("."))
        for directory in ["lib/lean", "ir"]:
            stem = build / directory / relative
            for file in sorted(stem.parent.glob(stem.name + ".*")):
                if file.is_file() and not file.name.endswith(".setup.json"):
                    yield file


def pack(root: Path, modules: list[str], archive: Path):
    build = root / "Lean/.lake/build"
    archive.parent.mkdir(parents=True, exist_ok=True)
    temporary = archive.with_suffix(archive.suffix + ".tmp")
    try:
        with temporary.open("wb") as output:
            compressor = subprocess.Popen(["zstd", "-q", "-3", "-T0", "-c"], stdin=subprocess.PIPE, stdout=output)
            try:
                with tarfile.open(fileobj=compressor.stdin, mode="w|") as tar:
                    for file in artifact_files(build, modules):
                        tar.add(file, arcname=str(file.relative_to(build)), recursive=False)
            finally:
                compressor.stdin.close()
            if compressor.wait() != 0:
                raise RuntimeError("Artifact compression failed")
        temporary.replace(archive)
    finally:
        temporary.unlink(missing_ok=True)


def pack_checkpoint(root: Path, modules: list[str], archive: Path) -> int:
    """Snapshot settled module outputs while Lake continues compiling."""
    build = root / "Lean/.lake/build"
    archive.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=archive.parent) as temporary:
        snapshot = Path(temporary)
        copied = []
        for name in modules:
            files = list(artifact_files(build, [name]))
            stem = build / "lib/lean" / Path(*name.split("."))
            trace, olean = stem.with_suffix(".trace"), stem.with_suffix(".olean")
            destinations = []
            try:
                before = {p: (p.stat().st_size, p.stat().st_mtime_ns) for p in files}
                if trace not in before or olean not in before:
                    continue
                # Lake writes the compilation trace after the module's outputs.
                if any(stamp[1] > before[trace][1] for stamp in before.values()):
                    continue
                for source in files:
                    target = snapshot / "Lean/.lake/build" / source.relative_to(build)
                    target.parent.mkdir(parents=True, exist_ok=True)
                    destinations.append(target)
                    shutil.copy2(source, target)
                after = {p: (p.stat().st_size, p.stat().st_mtime_ns) for p in files}
                unchanged = before == after and files == list(artifact_files(build, [name]))
            except FileNotFoundError:
                unchanged = False
            if unchanged:
                copied.append(name)
            else:
                for target in destinations:
                    target.unlink(missing_ok=True)
        if copied:
            pack(snapshot, copied, archive)
        return len(copied)


def unpack(root: Path, archive: Path):
    build = root / "Lean/.lake/build"
    build.mkdir(parents=True, exist_ok=True)
    decompressor = subprocess.Popen(["zstd", "-q", "-d", "-c", str(archive)], stdout=subprocess.PIPE)
    try:
        with tarfile.open(fileobj=decompressor.stdout, mode="r|") as tar:
            for member in tar:
                path = Path(member.name)
                if not member.isfile() or path.is_absolute() or ".." in path.parts:
                    raise ValueError(f"Invalid artifact archive entry: {member.name}")
                if not (member.name.startswith("lib/lean/") or member.name.startswith("ir/")):
                    raise ValueError(f"Unexpected artifact archive entry: {member.name}")
                tar.extract(member, build, filter="data")
        # tar stops at its end marker before zstd has necessarily emitted the padding.
        while decompressor.stdout.read(1 << 20):
            pass
    except BaseException:
        decompressor.terminate()
        raise
    finally:
        decompressor.stdout.close()
        code = decompressor.wait()
    if code != 0:
        raise RuntimeError("Artifact decompression failed")


def update_times(path: Path, logs, scale: float) -> int:
    times = read_times(path)
    measured = {}
    for log in logs:
        for line in log.read_text(errors="replace").splitlines():
            match = re.search(r" Built (H0mework\S*) \(([0-9.]+)(m?s)\)", line)
            if match:
                measured[match[1]] = round(float(match[2]) / (1000 if match[3] == "ms" else 1) * scale, 1)
    times.update(measured)
    path.write_text("".join(f"{seconds:g}\t{name}\n" for name, seconds in sorted(times.items())))
    return len(measured)


STORE_TAG = "proof-cache"
ASSET_LIMIT = 1900 * 2**20  # GitHub rejects release assets of 2 GiB or more


def platform_tag() -> str:
    return f"{os.environ.get('RUNNER_OS', platform.system())}-{os.environ.get('RUNNER_ARCH', platform.machine())}"


def part_prefix(plan: dict, name: str) -> str:
    return f"{platform_tag()}-{plan['version']}-{plan['compatibility']}-{name}-"


def part_key(plan: dict, name: str) -> str:
    return part_prefix(plan, name) + plan["parts"][name]["fingerprint"]


def seal_name(plan: dict) -> str:
    return f"{platform_tag()}-lean-selection-{plan['selection']}.json"


def restore_choice(entries: dict[str, str], key: str, prefix: str):
    """Exact archive, else the newest progress for this content, else the newest of this part."""
    exact = key + ".tar.zst"
    if exact in entries:
        return exact, True
    for start in (key + "-", prefix):
        found = [n for n in entries if n.startswith(start) and n.endswith(".tar.zst")]
        if found:
            return max(found, key=lambda n: (entries[n], n)), False
    return None, False


def superseded(entries: dict[str, str], keep: set[str]) -> list[str]:
    ours = (f"{platform_tag()}-{CACHE_VERSION}-", f"{platform_tag()}-lean-selection-")
    return sorted(n for n in entries if n.startswith(ours) and n not in keep)


class ReleaseStore:
    """Checked part archives kept as assets of one draft release of this repository.

    Release assets have no total size limit and never expire, unlike Actions caches. A
    draft stays out of public view but is visible only to tokens with push access, so a
    job that uses the store needs `contents: write`. Archives over the asset limit are
    split; their `.parts` record is uploaded last, so an interrupted upload stays invisible.
    """

    def __init__(self, repo: str, token: str):
        self.repo, self.token = repo, token
        self.release_id, self.assets = None, None

    def request(self, method, url, data=None, headers=None):
        request = urllib.request.Request(url, data=data, method=method)
        # Asset downloads redirect to storage that rejects a second credential.
        request.add_unredirected_header("Authorization", f"Bearer {self.token}")
        for key, value in {"Accept": "application/vnd.github+json", "X-GitHub-Api-Version": "2022-11-28",
                           **(headers or {})}.items():
            request.add_header(key, value)
        return urllib.request.urlopen(request, timeout=900)

    def api(self, method, path, body=None):
        data = None if body is None else json.dumps(body).encode()
        headers = {"Content-Type": "application/json"} if data else None
        with self.request(method, f"https://api.github.com/repos/{self.repo}/{path}", data, headers) as response:
            payload = response.read()
        return json.loads(payload) if payload else None

    def pages(self, path):
        page = 1
        while True:
            items = self.api("GET", f"{path}?per_page=100&page={page}")
            yield from items
            if len(items) < 100:
                return
            page += 1

    def open(self, create=False) -> bool:
        if self.release_id is None:
            self.release_id = next((r["id"] for r in self.pages("releases") if r["tag_name"] == STORE_TAG), None)
        if self.release_id is None and create:
            self.release_id = self.api("POST", "releases", {
                "tag_name": STORE_TAG, "name": "CI proof cache", "draft": True,
                "body": "Checked Lean build outputs kept between CI runs by tools/ci_plan.py. Not a release."})["id"]
        if self.release_id is not None and self.assets is None:
            self.assets = {a["name"]: a for a in self.pages(f"releases/{self.release_id}/assets")
                           if a["state"] == "uploaded"}
        return self.release_id is not None

    def dump(self, path: Path):
        path.write_text(json.dumps({"release": self.release_id, "assets": self.assets or {}}))

    def load(self, path: Path):
        # A listing taken once by the plan job saves every part from listing the store again.
        snapshot = json.loads(path.read_text())
        self.release_id, self.assets = snapshot["release"], snapshot["assets"]

    def entries(self) -> dict[str, str]:
        """Complete archives by name, with upload times; a split archive counts once."""
        if not self.open():
            return {}
        return {n.removesuffix(".parts"): a["created_at"] for n, a in self.assets.items()
                if not re.search(r"\.\d{3}$", n)}

    def download(self, asset, output):
        with self.request("GET", asset["url"], headers={"Accept": "application/octet-stream"}) as response:
            shutil.copyfileobj(response, output, 1 << 20)

    def fetch(self, name: str, path: Path) -> bool:
        if name not in self.entries():
            return False
        pieces = [name]
        if name not in self.assets:
            record = io.BytesIO()
            self.download(self.assets[name + ".parts"], record)
            pieces = [f"{name}.{i:03d}" for i in range(int(record.getvalue()))]
        path.parent.mkdir(parents=True, exist_ok=True)
        temporary = path.with_name(path.name + ".download")
        with temporary.open("wb") as output:
            for piece in pieces:
                self.download(self.assets[piece], output)
        temporary.replace(path)
        return True

    def upload(self, name: str, source: Path):
        if name in self.assets:
            self.api("DELETE", f"releases/assets/{self.assets.pop(name)['id']}")
        url = (f"https://uploads.github.com/repos/{self.repo}/releases/{self.release_id}/assets"
               f"?name={urllib.parse.quote(name)}")
        headers = {"Content-Type": "application/octet-stream", "Content-Length": str(source.stat().st_size)}
        with source.open("rb") as body, self.request("POST", url, body, headers) as response:
            self.assets[name] = json.loads(response.read())

    def put(self, name: str, path: Path):
        self.open(create=True)
        size = path.stat().st_size
        if size <= ASSET_LIMIT:
            self.upload(name, path)
            return
        count = math.ceil(size / ASSET_LIMIT)
        with tempfile.TemporaryDirectory() as temporary, path.open("rb") as source:
            for i in range(count):
                piece = Path(temporary) / f"{i:03d}"
                with piece.open("wb") as output:
                    output.write(source.read(ASSET_LIMIT))
                self.upload(f"{name}.{i:03d}", piece)
                piece.unlink()
            record = Path(temporary) / "parts"
            record.write_text(str(count))
            self.upload(name + ".parts", record)

    def remove(self, names):
        self.open()
        for name in names:
            for asset in [n for n in self.assets if n == name or n.startswith(name + ".")]:
                self.api("DELETE", f"releases/assets/{self.assets.pop(asset)['id']}")


def open_store() -> ReleaseStore | None:
    repo, token = os.environ.get("GITHUB_REPOSITORY"), os.environ.get("GH_TOKEN")
    return ReleaseStore(repo, token) if repo and token else None


def store_call(action, fallback=None):
    # The store only saves time; when it is unreachable a run rebuilds instead of failing.
    try:
        return action()
    except (urllib.error.URLError, OSError, ValueError) as error:
        print(f"::warning::Proof store unavailable: {error}")
        return fallback


def save_archive(store: ReleaseStore, key: str, archive: Path, progress: str | None = None):
    name = f"{key}-{progress}.tar.zst" if progress else key + ".tar.zst"
    store.put(name, archive)
    # Older progress for this content is superseded by the newer progress or the full archive.
    store.remove([n for n in store.entries() if n.startswith(key + "-") and n != name])


def live_checkpoint(root: Path, plan: dict, name: str, store: ReleaseStore, run: str, attempt: str):
    archive = root / ".local/ci/cache" / f"{name}.checkpoint.tar.zst"
    archive.parent.mkdir(parents=True, exist_ok=True)
    modules = plan["parts"][name].get("progress_modules", plan["parts"][name]["modules"])

    def save():
        def upload():
            if not pack_checkpoint(root, modules, archive):
                return False
            progress = f"{run}-{attempt}-checkpoint-{time.time_ns()}"
            save_archive(store, part_key(plan, name), archive, progress)
            return True
        try:
            return store_call(upload, False)
        finally:
            archive.unlink(missing_ok=True)

    return save


def continuation_parts(store: ReleaseStore, plan: dict, run: str, attempt: str) -> list[str]:
    def items(kind):
        page = 1
        while True:
            query = f"per_page=100&page={page}" + ("&filter=latest" if kind == "jobs" else "")
            batch = store.api("GET", f"actions/runs/{run}/{kind}?{query}")[kind]
            yield from batch
            if len(batch) < 100:
                return
            page += 1

    markers = {a["name"] for a in items("artifacts") if not a["expired"]}
    interrupted = set()
    for job in items("jobs"):
        match = re.search(r"\((s[1-8]-[0-9]+)\) / build$", job["name"])
        if job["conclusion"] != "failure":
            continue
        # A real compiler/setup/evidence failure must stop the whole continuation.
        if not match:
            return []
        name = match[1]
        if (any(s["conclusion"] == "failure" for s in job["steps"])
                and f"lean-incomplete-{name}-{attempt}" not in markers):
            return []
        if any(
                s["name"] == "Build part using Lake freshness checks" and s["conclusion"] == "cancelled"
                for s in job["steps"]):
            interrupted.add(name)
    entries = store.entries()
    resumable = []
    for name in plan["parts"]:
        if name not in interrupted and f"lean-incomplete-{name}-{attempt}" not in markers:
            continue
        progress = part_key(plan, name) + f"-{run}-{attempt}"
        if progress + ".tar.zst" in entries or any(n.startswith(progress + "-checkpoint-") for n in entries):
            resumable.append(name)
    return sorted(resumable)


def prune_store(store: ReleaseStore, keep: set[str]) -> list[str]:
    entries = store.entries()
    # Older versions stay as fallbacks until every current archive is stored.
    if not keep <= entries.keys():
        return []
    stale = superseded(entries, keep)
    store.remove(stale)
    return stale


def coverage(root: Path, plan: dict) -> tuple[set[str], set[str]]:
    """Default modules as Lake enumerates them, against the modules the parts own."""
    targets = [f"{lib}:modules" for lib in plan["libraries"]]
    result = subprocess.run(["lake", "--no-build", "query", "--json", *targets], cwd=root / "Lean",
                            capture_output=True, text=True)
    if result.returncode != 0:
        raise RuntimeError(result.stdout + result.stderr)
    listed = {m for line in result.stdout.splitlines() if line.strip() for m in json.loads(line)}
    owned = {m for part in plan["parts"].values() for m in part["modules"]}
    return listed - owned, owned - listed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["plan", "part", "build", "pack", "unpack", "times",
                                            "fetch", "save", "sealed", "seal", "prune", "coverage", "continuation"])
    parser.add_argument("logs", nargs="*", type=Path, help="Lake build logs read by `times`")
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--plan", type=Path, default=Path(".local/ci/plan.json"))
    parser.add_argument("--part")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--archive", type=Path)
    parser.add_argument("--deadline", type=float, help="Unix time at which a build stops and keeps its progress")
    parser.add_argument("--scale", type=float, default=1.0, help="runner seconds per logged second, for `times`")
    parser.add_argument("--rebalance", action="store_true", help="plan from scratch and rewrite the layout")
    parser.add_argument("--update-layout", action="store_true", help="record where new modules were placed")
    parser.add_argument("--progress", help="save the archive as progress under this run tag")
    parser.add_argument("--checkpoint", action="store_true",
                        help="include same-stage build dependencies in a resumable archive")
    args = parser.parse_args()
    root = args.root.resolve()
    if args.command == "times":
        print(f"Recorded {update_times(root / TIMES, args.logs, args.scale)} module times in {TIMES}")
        return
    if args.command == "plan":
        layout = Layout()
        plan = make_plan(root, layout, rebalance=args.rebalance)
        assignment = plan.pop("assignment")
        if args.rebalance or args.update_layout:
            write_layout(root / LAYOUT, assignment)
        args.plan.parent.mkdir(parents=True, exist_ok=True)
        args.plan.write_text(json.dumps(plan, indent=2) + "\n")
        outputs = {"stages": len(plan["stages"]), "selection": plan["selection"]}
        for k in range(1, layout.max_stages + 1):
            names = plan["stages"][k - 1] if k <= len(plan["stages"]) else ["unused"]
            outputs[f"s{k}"] = json.dumps({"include": [{"part": n} for n in names]}, separators=(",", ":"))
        append_outputs(os.environ.get("GITHUB_OUTPUT"), outputs)
        print(f"{plan['module_count']} modules in {len(plan['stages'])} stages; selection {plan['selection']}")
        for k, names in enumerate(plan["stages"], 1):
            shards = [plan["parts"][n] for n in names]
            print(f"stage {k}: {len(names)} shards, {sum(p['module_count'] for p in shards)} modules,"
                  f" longest estimate {max(p['hours'] for p in shards):.2f} h")
        if plan["placed"] and not (args.rebalance or args.update_layout):
            print(f"::notice::{plan['placed']} modules are not in {LAYOUT};"
                  " `python3 tools/ci_plan.py plan --update-layout` keeps their placement")
        for name, part in plan["parts"].items():
            if part["hours"] > 1.3 * layout.window / 3600:
                print(f"::warning::{name} is estimated at {part['hours']} h;"
                      " `python3 tools/ci_plan.py plan --rebalance` spreads the stages again")
        return
    if args.command == "unpack":
        unpack(root, args.archive)
        return
    plan = json.loads(args.plan.read_text())
    store = open_store()
    snapshot = args.plan.with_name("store.json")
    if args.command == "sealed":
        entries = store_call(store.entries, {}) if store else {}
        if store and store.release_id:
            store.dump(snapshot)
        print(f"Proof store holds {len(entries)} archives" if entries or (store and store.release_id)
              else "No proof store found")
        append_outputs(args.output, {"verified": str(seal_name(plan) in entries).lower()})
        return
    if args.command == "seal":
        record = Path(tempfile.mkdtemp()) / "selection.json"
        record.write_text(json.dumps({"commit": os.environ.get("GITHUB_SHA"), "run": os.environ.get("GITHUB_RUN_ID")}))
        if store:
            store_call(lambda: store.put(seal_name(plan), record))
        return
    if args.command == "prune":
        keep = {part_key(plan, n) + ".tar.zst" for n in plan["parts"] if n != "complete"} | {seal_name(plan)}
        stale = store_call(lambda: prune_store(store, keep), []) if store else []
        print(f"Removed {len(stale)} superseded archives from the proof store")
        return
    if args.command == "coverage":
        unowned, unlisted = coverage(root, plan)
        for label, names in (("not built by any part", unowned), ("not a default module", unlisted)):
            if names:
                print(f"{len(names)} modules {label}: {sorted(names)[:20]}", file=sys.stderr)
        raise SystemExit(1 if unowned or unlisted else 0)
    if args.command == "continuation":
        parts = continuation_parts(store, plan, os.environ["GITHUB_RUN_ID"], os.environ["GITHUB_RUN_ATTEMPT"])
        append_outputs(args.output, {"resume": str(bool(parts)).lower()})
        print(f"Resumable parts: {', '.join(parts)}" if parts else "No interrupted part has saved new progress")
        return
    part = plan["parts"][args.part]
    archive = args.archive or root / ".local/ci/cache" / f"{args.part}.tar.zst"
    if store and snapshot.is_file() and args.command == "fetch":
        store.load(snapshot)
    if args.command == "part":
        outputs = {"prefix": f"{plan['version']}-{plan['compatibility']}-{args.part}-",
                   "fingerprint": part["fingerprint"], "modules": part["module_count"],
                   "upstream": artifact_pattern(part["upstream"])}
        append_outputs(args.output, outputs)
        print(json.dumps(outputs))
    elif args.command == "fetch":
        entries = store_call(store.entries, {}) if store else {}
        name, exact = restore_choice(entries, part_key(plan, args.part), part_prefix(plan, args.part))
        if name and not store_call(lambda: store.fetch(name, archive), False):
            name, exact = None, False
        print(f"Restored {name}" if name else f"No stored outputs for this part among {len(entries)} archives")
        append_outputs(args.output, {"hit": str(exact).lower(), "matched": name or ""})
    elif args.command == "save":
        if store:
            store_call(lambda: save_archive(store, part_key(plan, args.part), archive, args.progress))
    elif args.command == "build":
        checkpoint = None
        if store and os.environ.get("STORE_WRITES") == "true" and not args.check_only:
            checkpoint = live_checkpoint(root, plan, args.part, store,
                                         os.environ["GITHUB_RUN_ID"], os.environ["GITHUB_RUN_ATTEMPT"])
        raise SystemExit(build_part(root, part, args.check_only, args.output, args.deadline, checkpoint))
    else:
        modules = part.get("progress_modules", part["modules"]) if args.checkpoint else part["modules"]
        pack(root, modules, archive)


if __name__ == "__main__":
    main()
