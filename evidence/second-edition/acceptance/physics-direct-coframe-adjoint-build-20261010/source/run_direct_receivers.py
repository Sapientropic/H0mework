from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "tools"))
import first_release as fr
import source_view as sv


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def write(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")


def main():
    freeze_path = ROOT / ".local/acceptance-execution-20261010/cohort-freeze.json"
    freeze = json.loads(freeze_path.read_bytes())
    expected_head = "5c627eb4783af2c39e4c22d2c48a11637e3bdd88"
    assert freeze["head"] == expected_head
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip() == expected_head
    for name, digest in freeze["files"].items():
        assert sha((ROOT / name).read_bytes()) == digest, name
    output = fr.new_output(ROOT, BASE / "direct-coframe-adjoint-build-5c627eb4")
    prefix = "H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology."
    targets = [
        prefix + "ExternalCompositeDecay.SourceActualCandidateBraLeftCoframe",
        prefix + "AlphaSource.CanonicalSourcePropagationCoframeInverseJets",
        prefix + "AlphaSource.CanonicalSourcePropagationNativeGravityScalarReturn",
    ]
    exported, _, _, _ = sv.load_map()
    parse_cache = {}

    def scopes():
        return {target: fr.package_inputs(ROOT, exported, {"lean_target": target, "id": target}, [],
                                          parse_cache=parse_cache) for target in targets}

    before_scopes = scopes()
    before = fr.snapshot(ROOT, "docs/second-edition-map.json", before_scopes)
    probe = BASE / "R71eCoframeGravityAdjointConsumer.lean"
    before["head"] = expected_head
    before["consumer_sha256"] = sha(probe.read_bytes())
    before["cohort_freeze_sha256"] = sha(freeze_path.read_bytes())
    configured, environment = fr.settings(ROOT), fr.build_environment()
    assert environment["LEAN_NUM_THREADS"] == "2"
    flags = list(dict.fromkeys(configured["package_moreLeanArgs"] + configured["package_weakLeanArgs"] +
                               ["--trust=0", "-DwarningAsError=true"]))
    build_command = ["lake", "build", *["+" + target for target in targets]]
    consumer_command = ["lake", "env", "lean", "--root=..", *flags,
                        "../" + probe.relative_to(ROOT).as_posix(), "-o",
                        "../" + (output / "adjoint-consumer.olean").relative_to(ROOT).as_posix()]
    write(output / "argv.json", {"build": build_command, "consumer": consumer_command,
                                "cwd": "Lean", "LEAN_NUM_THREADS": "2", "settings": configured})
    write(output / "source-scope-before.json", before_scopes)
    write(output / "provenance-before.json", before)
    write(output / "handles.json", {"controller_pid": os.getpid(), "build_log": "build.log",
                                    "consumer_log": "adjoint-consumer.log", "started_at": datetime.now(timezone.utc).isoformat()})
    print(json.dumps({"stage": "native-focused-build", "controller_pid": os.getpid(),
                      "output": output.relative_to(ROOT).as_posix(), "targets": targets}), flush=True)
    result = {"schema": "h0mework/physics-direct-consumers-focused-build@1",
              "formal_package_acceptance": False, "ok": False, "targets": targets,
              "input_identity": before, "settings": configured,
              "source_scope_before": "source-scope-before.json", "source_scope_after": "source-scope-after.json",
              "compiled_targets_before": fr.compiled_targets(ROOT, targets)}
    build = fr.run_process(build_command, ROOT, output / "build.log", environment)
    result["build"] = build
    if build["exit_code"] == 0:
        print(json.dumps({"stage": "adjoint-independent-consumer", "build_exit_code": 0}), flush=True)
        result["consumer"] = fr.run_process(consumer_command, ROOT, output / "adjoint-consumer.log", environment)
    after_scopes = scopes()
    after = fr.snapshot(ROOT, "docs/second-edition-map.json", after_scopes)
    after["head"] = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    after["consumer_sha256"] = sha(probe.read_bytes())
    after["cohort_freeze_sha256"] = sha(freeze_path.read_bytes())
    write(output / "source-scope-after.json", after_scopes)
    write(output / "provenance-after.json", after)
    result["input_identity_after"] = after
    result["inputs_unchanged"] = before == after
    result["compiled_targets_after"] = fr.compiled_targets(ROOT, targets)
    result["ok"] = (build["exit_code"] == 0 and result.get("consumer", {}).get("exit_code") == 0
                    and result["inputs_unchanged"] and all(result["compiled_targets_after"].values()))
    result["result_path"] = (output / "result.json").relative_to(ROOT).as_posix()
    write(output / "result.json", result)
    print(json.dumps({"ok": result["ok"], "inputs_unchanged": result["inputs_unchanged"],
                      "build_exit_code": build["exit_code"], "consumer_exit_code": result.get("consumer", {}).get("exit_code"),
                      "result": result["result_path"]}), flush=True)
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
