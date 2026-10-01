"""Partition the default Lake module closure and transport its checked artifacts."""

from __future__ import annotations

import argparse
from collections import defaultdict, deque
from dataclasses import dataclass
import hashlib
import json
import math
import os
from pathlib import Path
import re
import signal
import statistics
import subprocess
import sys
import tarfile
import time
import tomllib


CACHE_VERSION = "lean-parts-v1"
# Changing these re-runs the complete-selection check; part caches stay valid.
CI_FILES = ("tools/ci_plan.py", ".github/workflows/ci.yml", ".github/workflows/lean-part.yml")
# Seconds per module on a hosted runner, refreshed from CI logs with `ci_plan.py times`.
TIMES = "tools/ci_times.tsv"
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


def make_plan(root: Path, layout: Layout = Layout()) -> dict:
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
    stages = stage_plan(dependencies, cost, layout)

    resources = {r["name"]: r for r in config.get("input_file", [])}
    resource_hashes = {
        n: hashlib.sha256((lean / r["path"]).read_bytes()).hexdigest() for n, r in resources.items()
    }
    toolchain = (lean / "lean-toolchain").read_text().strip()
    manifest = (lean / "lake-manifest.json").read_bytes()
    compatibility = digest([toolchain, hashlib.sha256(manifest).hexdigest()])[:24]
    # New globs or paper targets do not change an existing module's compiler settings.
    package_options = {k: v for k, v in config.items() if k not in {"defaultTargets", "lean_lib", "input_file"}}
    # A shard owns the modules it builds first; a later shard of the same stage that also
    # needs them builds a private copy and leaves them out of its archive.
    owner, stage_of = {}, {}
    for k, shards in enumerate(stages, 1):
        for j, shard in enumerate(shards, 1):
            shard["name"], shard["stage"] = f"s{k}-{j:02d}", k
            shard["owned"] = sorted(n for n in shard["build"] if n not in owner)
            owner.update(dict.fromkeys(shard["owned"], shard["name"]))
            stage_of[shard["name"]] = k
    if owner.keys() != dependencies.keys():
        raise ValueError("Every default module needs exactly one owning shard")
    position = {n: i for i, n in enumerate(dependency_order(dependencies))}
    parts = {}
    for shard in (shard for shards in stages for shard in shards):
        inputs = closure(shard["owned"], dependencies)
        upstream = sorted({owner[n] for n in inputs - shard["build"]})
        if any(stage_of[u] >= shard["stage"] for u in upstream):
            raise ValueError(f"{shard['name']} imports from its own or a later stage")
        needed = sorted({r for n in inputs for r in owners[n].get("needs", [])})
        if any(n not in resources for n in needed):
            raise ValueError(f"Unknown resource input in {shard['name']}")
        module_options = {
            n: {k: v for k, v in owners[n].items() if k not in {"globs", "roots"}}
            for n in inputs
        }
        targets = ["+" + n for n in sorted(shard["sinks"])]
        fingerprint = digest({
            "modules": {n: source_hashes[n] for n in sorted(inputs)},
            "owned": shard["owned"], "targets": targets, "options": module_options,
            "package": package_options,
            "resources": {n: [resources[n], resource_hashes[n]] for n in needed},
        })
        chain = {}
        for n in sorted(shard["build"], key=position.get):
            chain[n] = cost[n] + max((chain[d] for d in dependencies[n] if d in chain), default=0.0)
        parts[shard["name"]] = {
            "stage": shard["stage"], "modules": shard["owned"], "targets": targets,
            "upstream": upstream, "fingerprint": fingerprint, "module_count": len(shard["owned"]),
            "hours": round(max(shard["work"] / layout.workers, max(chain.values())) / 3600, 2),
        }
    # The verified-selection record exists only after every part of exactly this
    # content passed together, so a run decides from content, not from its diff.
    ci_files = {p: hashlib.sha256((root / p).read_bytes()).hexdigest()
                for p in CI_FILES if (root / p).is_file()}
    selection = digest({"version": CACHE_VERSION, "compatibility": compatibility, "ci": ci_files,
                        "parts": {g: p["fingerprint"] for g, p in parts.items()}})
    matrices = {
        str(k): {"include": [{"part": s["name"], "dependencies": artifact_pattern(parts[s["name"]]["upstream"])}
                             for s in shards]}
        for k, shards in enumerate(stages, 1)
    }
    parts["complete"] = {"stage": len(stages) + 1, "modules": [], "targets": [], "upstream": sorted(stage_of),
                         "fingerprint": selection, "module_count": 0, "hours": 0.0}
    return {"version": CACHE_VERSION, "compatibility": compatibility, "selection": selection,
            "module_count": len(selected), "stages": [[s["name"] for s in shards] for shards in stages],
            "parts": parts, "matrices": matrices}


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
               deadline: float | None = None) -> int:
    append_outputs(output, {"started": "true"})
    if not part["targets"]:
        append_outputs(output, {"current": "true", "status": "complete", "built": 0})
        return 0
    command = ["lake", "--no-build", "build", *part["targets"]]
    probe = subprocess.run(command, cwd=root / "Lean", capture_output=True, text=True)
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

    def interrupted(signum, frame):
        nonlocal stopped
        stopped = stopped or "cancelled"

    previous = {sig: signal.signal(sig, interrupted) for sig in (signal.SIGINT, signal.SIGTERM)}
    try:
        # Lake decides freshness; a cache hit never bypasses resource/hash checks.
        process = subprocess.Popen(["lake", "build", *part["targets"]], cwd=root / "Lean",
                                   start_new_session=True)
        swept = time.monotonic()
        while process.poll() is None and not stopped:
            if deadline is not None and time.time() >= deadline:
                stopped = "incomplete"
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
    built = built_since(build, part["modules"], started)
    append_outputs(output, {"status": status, "built": built})
    print(f"{status}: {built} of {part['module_count']} modules built in this job")
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["plan", "part", "build", "pack", "unpack", "times"])
    parser.add_argument("logs", nargs="*", type=Path, help="Lake build logs read by `times`")
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--plan", type=Path, default=Path(".local/ci/plan.json"))
    parser.add_argument("--part")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--archive", type=Path)
    parser.add_argument("--deadline", type=float, help="Unix time at which a build stops and keeps its progress")
    parser.add_argument("--scale", type=float, default=1.0, help="runner seconds per logged second, for `times`")
    args = parser.parse_args()
    root = args.root.resolve()
    if args.command == "times":
        print(f"Recorded {update_times(root / TIMES, args.logs, args.scale)} module times in {TIMES}")
        return
    if args.command == "plan":
        plan = make_plan(root)
        args.plan.parent.mkdir(parents=True, exist_ok=True)
        args.plan.write_text(json.dumps(plan, indent=2) + "\n")
        outputs = {"stages": len(plan["stages"]), "selection": plan["selection"]}
        unused = {"include": [{"part": "unused", "dependencies": ""}]}
        for k in range(1, Layout().max_stages + 1):
            outputs[f"s{k}"] = json.dumps(plan["matrices"].get(str(k), unused), separators=(",", ":"))
        append_outputs(os.environ.get("GITHUB_OUTPUT"), outputs)
        print(f"{plan['module_count']} modules in {len(plan['stages'])} stages; selection {plan['selection']}")
        for k, names in enumerate(plan["stages"], 1):
            shards = [plan["parts"][n] for n in names]
            print(f"stage {k}: {len(names)} shards, {sum(p['module_count'] for p in shards)} modules,"
                  f" longest estimate {max(p['hours'] for p in shards):.2f} h")
        return
    if args.command == "unpack":
        unpack(root, args.archive)
        return
    plan = json.loads(args.plan.read_text())
    part = plan["parts"][args.part]
    if args.command == "part":
        outputs = {"prefix": f"{plan['version']}-{plan['compatibility']}-{args.part}-",
                   "fingerprint": part["fingerprint"], "modules": part["module_count"],
                   "upstream": artifact_pattern(part["upstream"])}
        append_outputs(args.output, outputs)
        print(json.dumps(outputs))
    elif args.command == "build":
        raise SystemExit(build_part(root, part, args.check_only, args.output, args.deadline))
    else:
        pack(root, part["modules"], args.archive)


if __name__ == "__main__":
    main()
