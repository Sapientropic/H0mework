#!/usr/bin/env python3
"""Locate and verify reusable first-release scientific replay artifacts.

The artifact is accepted only when its report passed, its declared runtime and
export-map bytes still match, all relevant repository paths are unchanged since
the producing commit, and every declared Bell archive has the same bytes.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import urllib.error
import urllib.request


ROOT = Path(__file__).resolve().parents[1]
API = "https://api.github.com"
ARTIFACTS = {"bell": "first-release-bell-replay", "quantum": "first-release-quantum-replay"}
CONFIGS = {"bell": "checks/first-release-runtime.json", "quantum": "checks/first-release-quantum.json"}
EXPECTED_CHECKS = {"bell": 14, "quantum": 18}

# These files define the replay algorithm, source binding and external inputs.
# CI files and ordinary documentation are deliberately absent: changing them
# must not invalidate a scientific result.
SCIENCE_PATHS = (
    "checks/first-release-runtime.json",
    "checks/first-release-quantum.json",
    "tools/first_release_replay.py",
    "tools/first_release_quantum.py",
    "tools/source_view.py",
    "tools/export-map.json",
    "Makefile",
    "evidence/first-release/bell-inputs",
)


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
            config = ROOT / CONFIGS[kind]
            export_map = ROOT / "tools/export-map.json"
            checks = document.get("checks", [])
            passed = (document.get("status") == "passed" and len(checks) == EXPECTED_CHECKS[kind]
                      and all(row.get("status") == "passed" and row.get("exit_code") == 0 for row in checks)
                      and document.get("config_sha256") == sha(config)
                      and document.get("map_sha256") == sha(export_map)
                      and unchanged_since(source_sha)
                      and (kind != "bell" or current_archives_match(document)))
            reason = "validated against current source, configuration and inputs" if passed else "artifact inputs changed"
            details = {"report_sha256": sha(report), "checks": len(checks), "config_sha256": document.get("config_sha256"),
                       "map_sha256": document.get("map_sha256")}
        except (OSError, ValueError, KeyError) as error:
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
