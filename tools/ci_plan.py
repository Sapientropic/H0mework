"""Partition the default Lake module closure and transport its checked artifacts."""

from __future__ import annotations

import argparse
from collections import defaultdict, deque
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import threading
import tomllib


CACHE_VERSION = "lean-parts-v1"


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


def domain(name: str) -> str:
    parts = name.split(".")
    if parts[1:2] == ["Versions"]:
        return parts[3]
    return parts[1] if len(parts) > 1 else "root"


def partition(dependencies):
    reverse = defaultdict(set)
    for name, deps in dependencies.items():
        for dep in deps:
            reverse[dep].add(name)
    chemical = {n for n in dependencies if domain(n) == "Chemistry"}
    chemical_consumers = closure(chemical, reverse)

    def initial(name):
        area = domain(name)
        if area == "Chemistry":
            match = re.match(
                r"H0mework\.Chemistry\.(?:LAlanineBandCall|LAlanineCellField|LAlanineBandTaylor)(\d+)",
                name,
            )
            return f"chemistry-{int(match[1]) % 4}" if match else "integration"
        if name in chemical_consumers or area in {"Papers", "root"}:
            return "integration"
        return {
            "Arithmetic": "arithmetic", "NavierStokes": "navier-stokes", "Physics": "physics",
        }.get(area, "structures")

    groups = {n: initial(n) for n in dependencies}
    # Dependencies used across parallel parts are built once, before the matrix.
    shared = {
        dep for name, deps in dependencies.items() if groups[name] != "integration"
        for dep in deps if groups[name] != groups[dep]
    }
    for name in closure(shared, dependencies):
        groups[name] = "base"
    return groups


def digest(records) -> str:
    return hashlib.sha256(json.dumps(records, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def make_plan(root: Path) -> dict:
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
    groups = partition(dependencies)
    modules = defaultdict(list)
    imported = defaultdict(set)
    for name, group in groups.items():
        modules[group].append(name)
        for dep in dependencies[name]:
            if groups[dep] == group:
                imported[group].add(dep)
            elif group == "base" or (group != "integration" and groups[dep] != "base"):
                raise ValueError(f"Invalid shard ordering: {name} imports {dep}")

    resources = {r["name"]: r for r in config.get("input_file", [])}
    resource_hashes = {
        n: hashlib.sha256((lean / r["path"]).read_bytes()).hexdigest() for n, r in resources.items()
    }
    toolchain = (lean / "lean-toolchain").read_text().strip()
    manifest = (lean / "lake-manifest.json").read_bytes()
    compatibility = digest([toolchain, hashlib.sha256(manifest).hexdigest()])[:24]
    # New globs or paper targets do not change an existing module's compiler settings.
    package_options = {k: v for k, v in config.items() if k not in {"defaultTargets", "lean_lib", "input_file"}}
    parts = {}
    for group, owned in sorted(modules.items()):
        owned = sorted(owned)
        roots = sorted(set(owned) - imported[group])
        if closure(roots, dependencies) & set(owned) != set(owned):
            raise ValueError(f"Module cycle or incomplete roots in {group}")
        inputs = closure(owned, dependencies)
        needed = sorted({r for n in inputs for r in owners[n].get("needs", [])})
        if any(n not in resources for n in needed):
            raise ValueError(f"Unknown resource input in {group}")
        module_options = {
            n: {k: v for k, v in owners[n].items() if k not in {"globs", "roots"}}
            for n in inputs
        }
        fingerprint = digest({
            "modules": {n: source_hashes[n] for n in sorted(inputs)},
            "owned": owned, "options": module_options, "package": package_options,
            "resources": {n: [resources[n], resource_hashes[n]] for n in needed},
        })
        parts[group] = {
            "modules": owned, "targets": ["+" + n for n in roots],
            "fingerprint": fingerprint, "module_count": len(owned),
        }
    matrix = {"include": [{"part": p} for p in parts if p not in {"base", "integration"}]}
    return {"version": CACHE_VERSION, "compatibility": compatibility,
            "module_count": len(selected), "parts": parts, "matrix": matrix}


def changed_paths(root: Path, event_name: str, event: dict) -> list[str] | None:
    if event_name not in {"push", "pull_request"}:
        return None
    try:
        if event_name == "pull_request":
            base, head = event["pull_request"]["base"]["sha"], event["pull_request"]["head"]["sha"]
            base = subprocess.check_output(["git", "merge-base", base, head], cwd=root, text=True, stderr=subprocess.PIPE).strip()
        else:
            base, head = event.get("before"), event.get("after")
        if not base or not head or set(base) == {"0"}:
            return None
        output = subprocess.check_output(["git", "diff", "--name-only", "-z", base, head], cwd=root, stderr=subprocess.PIPE)
    except subprocess.CalledProcessError:
        # A force-push can make the previous head unavailable in a fresh checkout.
        print("Changed-file range unavailable; checking the complete selection", file=sys.stderr)
        return None
    return [p.decode() for p in output.split(b"\0") if p]


def requires_lean(paths: list[str] | None) -> bool:
    return paths is None or any(p.startswith(("Lean/", "evidence/", ".github/"))
        or p == "Makefile" or p.startswith("tools/ci_") for p in paths)


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


def build_part(root: Path, part: dict, check_only: bool = False, output: Path | None = None) -> int:
    if not part["targets"]:
        return 0
    command = ["lake", "--no-build", "build", *part["targets"]]
    probe = subprocess.run(command, cwd=root / "Lean", capture_output=True, text=True)
    if output:
        with output.open("a") as stream:
            stream.write(f"current={str(probe.returncode == 0).lower()}\n")
    if probe.returncode == 0:
        print(f"All {part['module_count']} module artifacts are current")
        return 0
    if check_only or probe.returncode != 3:
        print(probe.stdout + probe.stderr, file=sys.stderr)
        return probe.returncode
    stop = threading.Event()

    def janitor():
        while not stop.wait(5):
            completed_setup_files(root / "Lean/.lake/build")

    thread = threading.Thread(target=janitor, daemon=True)
    thread.start()
    try:
        # Lake decides freshness; a cache hit never bypasses resource/hash checks.
        return subprocess.run(["lake", "build", *part["targets"]], cwd=root / "Lean").returncode
    finally:
        stop.set()
        thread.join()
        completed_setup_files(root / "Lean/.lake/build")


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
            compressor = subprocess.Popen(["zstd", "-q", "-3", "-T2", "-c"], stdin=subprocess.PIPE, stdout=output)
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["plan", "part", "build", "pack", "unpack"])
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--plan", type=Path, default=Path(".local/ci/plan.json"))
    parser.add_argument("--part")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--archive", type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    if args.command == "plan":
        plan = make_plan(root)
        args.plan.parent.mkdir(parents=True, exist_ok=True)
        args.plan.write_text(json.dumps(plan, indent=2) + "\n")
        paths = changed_paths(root, os.environ.get("GITHUB_EVENT_NAME", "workflow_dispatch"),
            json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text()) if "GITHUB_EVENT_PATH" in os.environ else {})
        outputs = {"matrix": json.dumps(plan["matrix"], separators=(",", ":")),
                   "lean": str(requires_lean(paths)).lower()}
        if path := os.environ.get("GITHUB_OUTPUT"):
            with open(path, "a") as stream:
                for key, value in outputs.items():
                    stream.write(f"{key}={value}\n")
        print(json.dumps({"modules": plan["module_count"],
            "parts": {n: p["module_count"] for n, p in plan["parts"].items()}, **outputs}, indent=2))
        return
    if args.command == "unpack":
        unpack(root, args.archive)
        return
    plan = json.loads(args.plan.read_text())
    part = plan["parts"][args.part]
    if args.command == "part":
        outputs = {"prefix": f"{plan['version']}-{plan['compatibility']}-{args.part}-",
                   "fingerprint": part["fingerprint"]}
        if args.output:
            with args.output.open("a") as stream:
                for key, value in outputs.items():
                    stream.write(f"{key}={value}\n")
        print(json.dumps(outputs))
    elif args.command == "build":
        raise SystemExit(build_part(root, part, args.check_only, args.output))
    else:
        pack(root, part["modules"], args.archive)


if __name__ == "__main__":
    main()
