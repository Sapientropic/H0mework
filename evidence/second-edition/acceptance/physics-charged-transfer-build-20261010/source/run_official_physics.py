from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
import subprocess

ROOT = Path(__file__).resolve().parents[2]
BASE = Path(__file__).resolve().parent


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("action", choices=("build", "trust"))
    parser.add_argument("--package", action="append", required=True)
    parser.add_argument("--label", required=True)
    args = parser.parse_args()
    freeze_path = ROOT / ".local/acceptance-execution-20261010/cohort-freeze.json"
    freeze = json.loads(freeze_path.read_bytes())
    plan = json.loads((BASE / "physics-runtime-overlap-plan.json").read_bytes())
    packets = {p["id"]: p for p in plan["packages"]}
    selected = [packets[key] for key in args.package]
    output = BASE / args.label
    provenance = BASE / (args.label + "-provenance")
    assert not output.exists() and not provenance.exists()
    provenance.mkdir()
    sources = {path: digest for p in selected for path, digest in p["source_files"].items()}

    def capture():
        current_head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        assert current_head == freeze["head"]
        global_inputs = {path: sha((ROOT / path).read_bytes()) for path in freeze["files"]}
        assert global_inputs == freeze["files"]
        actual = {path: sha((ROOT / path).read_bytes()) for path in sources}
        assert actual == sources
        scopes = {}
        for p in selected:
            files = {path: actual[path] for path in p["source_files"]}
            scopes[p["id"]] = {"files": files, "digest": sha(json.dumps(files, sort_keys=True).encode()),
                               "modules": len(files)}
            assert scopes[p["id"]]["digest"] == p["source_scope_sha256"]
        return {"head": current_head, "global_inputs": global_inputs,
                "cohort_freeze_sha256": sha(freeze_path.read_bytes()), "package_inputs": scopes,
                "tools": {path: sha((ROOT / path).read_bytes()) for path in
                          ("tools/first_release.py", "tools/edition_release.py", "tools/source_view.py", "tools/publication.py")}}

    before = capture()
    write(provenance / "before.json", before)
    command = ["python3", "tools/edition_release.py", "--edition", "second", args.action,
               *[item for key in args.package for item in ("--package", key)],
               "--output", output.relative_to(ROOT).as_posix()]
    environment = dict(os.environ)
    assert environment.get("LEAN_NUM_THREADS") == "2"
    write(provenance / "argv.json", {"command": command, "cwd": ".", "LEAN_NUM_THREADS": "2",
                                    "controller_pid": os.getpid(), "started_at": datetime.now(timezone.utc).isoformat()})
    print(json.dumps({"stage": args.action, "packages": args.package, "controller_pid": os.getpid(),
                      "output": output.relative_to(ROOT).as_posix()}), flush=True)
    with (provenance / "cli.json").open("w") as stream:
        run = subprocess.run(command, cwd=ROOT, env=environment, stdout=stream, stderr=subprocess.STDOUT)
    after = capture()
    write(provenance / "after.json", after)
    result_path = output / "result.json"
    official = json.loads(result_path.read_bytes()) if result_path.exists() else None
    if official is not None:
        expected = {key: scope["digest"] for key, scope in before["package_inputs"].items()}
        assert official["input_identity"]["package_inputs"] == expected
        assert official.get("input_identity_after", {}).get("package_inputs") == expected
    summary = {"schema": "h0mework/physics-official-invocation-provenance@1",
               "exit_code": run.returncode, "packages": args.package, "head": before["head"],
               "actual_official_result": result_path.relative_to(ROOT).as_posix(),
               "actual_official_result_sha256": sha(result_path.read_bytes()) if official is not None else None,
               "inputs_unchanged": before == after,
               "ok": run.returncode == 0 and official is not None and official["ok"] and before == after}
    write(provenance / "result.json", summary)
    print(json.dumps(summary), flush=True)
    return 0 if summary["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
