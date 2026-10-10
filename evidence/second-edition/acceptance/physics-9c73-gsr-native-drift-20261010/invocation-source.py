from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "tools"))
import first_release as fr
import source_view as sv


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--target", required=True)
    parser.add_argument("--label", required=True)
    args = parser.parse_args()
    freeze_path = ROOT / ".local/acceptance-execution-20261010/cohort-freeze.json"
    freeze_raw = freeze_path.read_bytes()
    freeze = json.loads(freeze_raw)
    configured, environment = fr.settings(ROOT), fr.build_environment()
    assert environment["LEAN_NUM_THREADS"] == "2"
    exported, _, _, _ = sv.load_map()
    parse_cache = {}

    def capture():
        head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        controls = {name: sha((ROOT / name).read_bytes()) for name in freeze["files"]}
        scope = fr.package_inputs(ROOT, exported, {"lean_target": args.target, "id": args.target}, [],
                                  parse_cache=parse_cache)
        identity = fr.snapshot(ROOT, "docs/second-edition-map.json", {args.target: scope})
        identity.update(head=head, controls=controls, cohort_freeze_sha256=sha(freeze_path.read_bytes()))
        return identity, scope

    before, scope_before = capture()
    assert before["head"] == freeze["head"]
    assert before["controls"] == freeze["files"]
    assert before["cohort_freeze_sha256"] == sha(freeze_raw)
    output = fr.new_output(ROOT, BASE / args.label)
    command = ["lake", "build", "+" + args.target]
    write(output / "argv.json", {"command": command, "cwd": "Lean", "LEAN_NUM_THREADS": "2",
                                "settings": configured})
    write(output / "source-scope-before.json", scope_before)
    write(output / "provenance-before.json", before)
    (output / "invocation-source.py").write_bytes(Path(__file__).read_bytes())
    result = {"schema": "h0mework/physics-single-native-focused-build@1", "ok": False,
              "formal_package_acceptance": False, "targets": [args.target], "input_identity": before,
              "settings": configured, "compiled_targets_before": fr.compiled_targets(ROOT, [args.target]),
              "source_scope_before": "source-scope-before.json", "source_scope_after": "source-scope-after.json"}
    started_at = datetime.now(timezone.utc).isoformat()
    begin = time.monotonic()
    with (output / "build.log").open("w") as stream:
        process = subprocess.Popen(command, cwd=ROOT / "Lean", env=environment,
                                   stdout=stream, stderr=subprocess.STDOUT)
        write(output / "handles.json", {"controller_pid": os.getpid(), "lake_pid": process.pid,
                                        "started_at": started_at, "build_log": "build.log"})
        print(json.dumps({"stage": "single-native-focused-build", "controller_pid": os.getpid(),
                          "lake_pid": process.pid, "target": args.target,
                          "output": output.relative_to(ROOT).as_posix()}), flush=True)
        code = process.wait()
    result["build"] = {"command": command, "cwd": "Lean", "started_at": started_at,
                       "finished_at": datetime.now(timezone.utc).isoformat(),
                       "elapsed_seconds": round(time.monotonic() - begin, 3), "exit_code": code,
                       "error": None, "log": (output / "build.log").relative_to(ROOT).as_posix()}
    after, scope_after = capture()
    write(output / "source-scope-after.json", scope_after)
    write(output / "provenance-after.json", after)
    result["input_identity_after"] = after
    result["inputs_unchanged"] = before == after and scope_before == scope_after
    result["compiled_targets_after"] = fr.compiled_targets(ROOT, [args.target])
    result["ok"] = code == 0 and result["inputs_unchanged"] and all(result["compiled_targets_after"].values())
    result["result_path"] = (output / "result.json").relative_to(ROOT).as_posix()
    write(output / "result.json", result)
    print(json.dumps({"ok": result["ok"], "exit_code": code, "inputs_unchanged": result["inputs_unchanged"],
                      "result": result["result_path"]}), flush=True)
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
