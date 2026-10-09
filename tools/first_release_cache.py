#!/usr/bin/env python3
"""Locate and verify reusable first-release scientific replay artifacts.

The report must bind the producing commit's export map. Reuse then follows the
actual configured scientific views, so unrelated new exports preserve the result
while changed or newly selected inputs require another replay.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import types
import urllib.error
import urllib.request

import source_view
import first_release_replay
from first_release_replay import ReplayError


ROOT = Path(__file__).resolve().parents[1]
API = "https://api.github.com"
ARTIFACTS = {"bell": "first-release-bell-replay", "quantum": "first-release-quantum-replay"}
CONFIGS = {"bell": "checks/first-release-runtime.json", "quantum": "checks/first-release-quantum.json"}
EXPECTED_CHECKS = {"bell": 14, "quantum": 18}

# These files define the scientific execution algorithm and external inputs.
# CI files and ordinary documentation are deliberately absent: changing them
# must not invalidate a scientific result.
SCIENCE_PATHS = (
    "checks/first-release-runtime.json",
    "checks/first-release-quantum.json",
    "tools/first_release_replay.py",
    "tools/first_release_quantum.py",
    "Makefile",
    "evidence/first-release/bell-inputs",
)
VIEW_ENGINES = ("tools/publication.py", "tools/source_view.py", "tools/first_release_replay.py")


def sha(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def api(path: str, token: str):
    request = urllib.request.Request(API + path, headers={
        "Accept": "application/vnd.github+json",
        "Authorization": f"Bearer {token}",
        "X-GitHub-Api-Version": "2022-11-28",
        "User-Agent": "H0mework-first-release-cache",
    })
    with urllib.request.urlopen(request, timeout=60) as response:
        return json.loads(response.read())


def output(path: str | None, values: dict[str, str]):
    if path:
        with open(path, "a", encoding="utf-8") as stream:
            for key, value in values.items():
                stream.write(f"{key}={value}\n")


def find(kind: str, destination: str | None):
    token = os.environ.get("GH_TOKEN")
    repository = os.environ.get("GITHUB_REPOSITORY")
    current_run = os.environ.get("GITHUB_RUN_ID")
    current_sha = os.environ.get("GITHUB_SHA")
    if not token or not repository:
        output(destination, {"found": "false"})
        return
    # The overall workflow may be red because a separate Lean shard was
    # interrupted even though this replay job completed successfully. The
    # report and its artifact are the authoritative status for this scope.
    workflow = api(f"/repos/{repository}/actions/workflows/ci.yml/runs?branch=main&per_page=50", token)
    for run in workflow.get("workflow_runs", []):
        run_id = str(run["id"])
        if run_id == current_run or run.get("head_sha") == current_sha:
            continue
        assets = api(f"/repos/{repository}/actions/runs/{run_id}/artifacts?per_page=100", token).get("artifacts", [])
        artifact = next((row for row in assets if row.get("name") == ARTIFACTS[kind] and not row.get("expired")), None)
        if artifact:
            output(destination, {"found": "true", "run_id": run_id, "artifact_id": str(artifact["id"]),
                                  "source_sha": run["head_sha"], "source_run_url": run.get("html_url", "")})
            return
    output(destination, {"found": "false"})


def unchanged_since(commit: str) -> bool:
    if subprocess.run(["git", "cat-file", "-e", commit], cwd=ROOT,
                      stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode != 0:
        return False
    return subprocess.run(["git", "diff", "--quiet", commit, "--", *SCIENCE_PATHS], cwd=ROOT,
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0


def original_file(commit: str, path: str) -> bytes:
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("Artifact source must be a full commit SHA")
    return subprocess.check_output(["git", "show", f"{commit}:{path}"], cwd=ROOT,
                                   stderr=subprocess.DEVNULL)


def original_map(commit: str) -> bytes:
    return original_file(commit, "tools/export-map.json")


def load_view_engines(blobs: dict[str, bytes], workspace: Path):
    """Load independent source-view implementations with their own dependencies."""
    previous = {Path(path).stem: sys.modules.get(Path(path).stem) for path in VIEW_ENGINES}
    modules = {}
    try:
        for path in VIEW_ENGINES:
            name = Path(path).stem
            module = types.ModuleType(name)
            module.__file__ = str(workspace / path)
            sys.modules[name] = module
            exec(compile(blobs[path], module.__file__, "exec"), module.__dict__)
            module.ROOT = ROOT
            modules[name] = module
    finally:
        for name, module in previous.items():
            if module is None:
                sys.modules.pop(name, None)
            else:
                sys.modules[name] = module
    return modules["source_view"], modules["first_release_replay"]


def scientific_inputs(kind: str, export_map: Path, workspace: Path, engines=None) -> dict:
    """Resolve the replay's real selectors and verify every selected file's bytes."""
    config = json.loads((ROOT / CONFIGS[kind]).read_bytes())
    inputs = {"views": {}, "files": {}}
    view_engine, replay_engine = engines or (source_view, first_release_replay)

    def repository_input(path):
        view_engine.source_path(path)
        inputs["files"][path] = sha(ROOT / path)

    def identity(row, raw):
        return {"view_sha256": hashlib.sha256(raw).hexdigest(),
                "source_sha256": row["source_sha256"], "source_revision": row["source_revision"],
                "publication": row.get("publication")}

    if kind == "bell":
        checks = replay_engine.select_checks(config, "bell")
        views = {check["view"] for check in checks if "view" in check}
        views.update(name for check in checks for name in check.get("historical_views", []))
        for name in sorted(views):
            omitted = [check["output"] for check in checks if check.get("view") == name
                       and check["kind"] == "exact-source-controls"]
            view = replay_engine.prepare_view(ROOT, workspace / name, config["views"][name], omitted, export_map)
            # Adding labels for the same byte version does not change an input.
            inputs["views"][name] = {"source_revision": view["source_revision"], "bindings": {
                path: {key: value for key, value in binding.items() if key != "source_revisions"}
                for path, binding in view["bindings"].items()}}
        for check in checks:
            for row in check.get("inputs", []):
                repository_input(row["path"])
            if check.get("frozen"):
                repository_input(check["frozen"])
    else:
        with replay_engine.map_root(ROOT, export_map):
            data, modules, artifacts, inverse = view_engine.load_map()
            for check in config["checks"]:
                bindings = {}
                for name, digest in check["expected_source_sha256"].items():
                    if name == check["output"]:
                        continue
                    rows = modules.get(name, []) + artifacts.get(name, [])
                    row = view_engine.pick(rows, name, {digest}, check["ref"])
                    raw = view_engine.module_views(row, inverse)[1] if name in modules \
                        else view_engine.artifact_views(row)[0]
                    if hashlib.sha256(raw).hexdigest() != digest:
                        raise ValueError(f"Original quantum input differs: {name}")
                    bindings[name] = identity(row, raw)
                frozen = [row for row in data["artifacts"] if row["path"] == check["frozen"]
                          and row["source"] == check["output"] and view_engine.row_at(row, check["ref"])]
                if len(frozen) != 1 or frozen[0]["source_sha256"] != check["frozen_source_sha256"]:
                    raise ValueError("Frozen quantum comparison identity differs")
                repository_input(check["frozen"])
                if inputs["files"][check["frozen"]] != check["frozen_sha256"] \
                        or frozen[0]["target_sha256"] != check["frozen_sha256"]:
                    raise ValueError("Frozen quantum comparison bytes differ")
                inputs["views"][check["id"]] = {"source_revision": check["ref"], "bindings": bindings}
    return inputs


def scientific_inputs_match(kind: str, document: dict, source_sha: str, evidence=None) -> bool:
    original = original_map(source_sha)
    if document.get("map_sha256") != hashlib.sha256(original).hexdigest():
        return False
    with tempfile.TemporaryDirectory() as directory:
        workspace = Path(directory)
        snapshot = workspace / "export-map.json"
        snapshot.write_bytes(original)
        historical = {path: original_file(source_sha, path) for path in VIEW_ENGINES}
        current = {path: (ROOT / path).read_bytes() for path in VIEW_ENGINES}
        old_engines = load_view_engines(historical, workspace / "historical")
        new_engines = load_view_engines(current, workspace / "current")
        # Both implementations run: a new reconstruction algorithm cannot certify
        # its own interpretation of the historical map by repeating that algorithm.
        try:
            before = scientific_inputs(kind, snapshot, workspace / "original-views", old_engines)
            after = scientific_inputs(kind, ROOT / "tools/export-map.json", workspace / "current-views", new_engines)
        except (old_engines[0].ViewError, old_engines[1].ReplayError,
                new_engines[0].ViewError, new_engines[1].ReplayError) as error:
            raise ValueError(f"Incompatible scientific source view: {error}") from error
        if evidence is not None:
            evidence.update({"view_engine_comparison": "historical-source-vs-current-source",
                             "historical_source_view_sha256": hashlib.sha256(historical["tools/source_view.py"]).hexdigest(),
                             "current_source_view_sha256": hashlib.sha256(current["tools/source_view.py"]).hexdigest(),
                             "historical_view_inputs_sha256": hashlib.sha256(json.dumps(before, sort_keys=True).encode()).hexdigest(),
                             "current_view_inputs_sha256": hashlib.sha256(json.dumps(after, sort_keys=True).encode()).hexdigest()})
        if before != after:
            return False
        for path, digest in before["files"].items():
            raw = original_file(source_sha, path)
            if hashlib.sha256(raw).hexdigest() != digest:
                return False
    return True


def report_path(directory: Path, kind: str) -> Path | None:
    names = list(directory.rglob("report.json"))
    expected = "/bell/report.json" if kind == "bell" else "/quantum/report.json"
    matches = [path for path in names if path.as_posix().endswith(expected)]
    return matches[0] if len(matches) == 1 else None


def current_archives_match(report: dict) -> bool:
    base = ROOT / "evidence/first-release/bell-inputs"
    expected = {}
    for check in report.get("checks", []):
        result = check.get("result", {})
        if not isinstance(result, dict):
            return False
        if isinstance(result.get("archive"), dict):
            expected[result["archive"].get("name")] = result["archive"].get("sha256")
        for archive in result.get("archives", []):
            if isinstance(archive, dict):
                expected[archive.get("name")] = archive.get("sha256")
    for name, digest in expected.items():
        if not isinstance(name, str) or not isinstance(digest, str):
            return False
        path = base / name
        if not path.is_file() or sha(path) != digest:
            return False
    return bool(expected)


def verify(kind: str, artifact_directory: str, source_sha: str, destination: str | None):
    directory = Path(artifact_directory).resolve()
    report = report_path(directory, kind)
    reason = "artifact report not found"
    passed = False
    details = {}
    if report:
        try:
            document = json.loads(report.read_text())
            if not isinstance(document, dict):
                raise ValueError("Artifact report must be an object")
            config = ROOT / CONFIGS[kind]
            checks = document.get("checks", [])
            comparison = {}
            passed = (document.get("status") == "passed" and isinstance(checks, list)
                      and len(checks) == EXPECTED_CHECKS[kind]
                      and all(isinstance(row, dict) and row.get("status") == "passed"
                              and row.get("exit_code") == 0 for row in checks)
                      and document.get("config_sha256") == sha(config)
                      and unchanged_since(source_sha)
                      and scientific_inputs_match(kind, document, source_sha, comparison)
                      and (kind != "bell" or current_archives_match(document)))
            reason = "validated against current source, configuration and inputs" if passed else "artifact inputs changed"
            details = {"report_sha256": sha(report), "checks": len(checks), "config_sha256": document.get("config_sha256"),
                       "map_sha256": document.get("map_sha256"),
                       "current_map_sha256": sha(ROOT / "tools/export-map.json"), **comparison}
        except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError,
                source_view.ViewError, ReplayError, SyntaxError) as error:
            reason = f"invalid report: {error}"
    receipt = {"schema": "h0mework/first-release-cache@1", "kind": kind, "status": "reused" if passed else "miss",
               "source_commit": source_sha, "source_run": os.environ.get("SOURCE_RUN_URL", ""),
               "reason": reason, **details}
    destination_path = Path(destination) if destination else None
    if destination_path:
        destination_path.mkdir(parents=True, exist_ok=True)
        (destination_path / "reuse.json").write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n")
    output(os.environ.get("GITHUB_OUTPUT"), {"reused": str(passed).lower(), "reason": reason})
    print(json.dumps(receipt, ensure_ascii=False))


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("find", "verify"))
    parser.add_argument("--kind", choices=tuple(ARTIFACTS))
    parser.add_argument("--output")
    parser.add_argument("--artifact-directory")
    parser.add_argument("--source-sha")
    args = parser.parse_args(argv)
    if args.command == "find":
        find(args.kind, args.output)
    else:
        verify(args.kind, args.artifact_directory, args.source_sha, args.output)


if __name__ == "__main__":
    main()
