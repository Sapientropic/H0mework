#!/usr/bin/env python3
"""Recompute the fixed source-carrier consumers of first-release P26.

Each original nullary independent main runs in a fresh verified source view.
Its coefficient constructors and comparisons are unchanged. Only the recorded
top-level wall-clock field is excluded from the frozen-result comparison.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import inspect
import json
from pathlib import Path
import subprocess
import sys
import sysconfig
import time
import traceback
import uuid

import source_view
from first_release_replay import (PublicInputs, ReplayError, RuntimeInputs, inside,
                                  map_root, python_executable, read_json,
                                  require, sha, write_json)

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "h0mework/first-release-quantum@1"
REPORT_SCHEMA = "h0mework/first-release-quantum-replay@1"
ECD = "Verification/physics/low-energy-phenomenology/external-composite-decay"
REVISIONS = {
    "T": "85cb5386ca132818f74d90470d87a252e4a27ea7",
    "T3": "f9b733928fb5078ac82430b164dabb8696542e64",
    "V": "6726f385356cb327e7c158687e6e37f5f086fe71",
    "X": "eec031c489f37459742e62a59a26b9866a21caed",
}
CASES = {
    "k3-scalar-gauss": ("T", "scalar_gauss_reduction"),
    "k4-joint-domain": ("T", "joint_local_quantum"),
    "k6-stabilizer": ("T3", "quantum_stabilizer"),
    "k7-phase-chart": ("T3", "stabilizer_phase_reduction"),
    "k8-local-section": ("V", "quantum_gauss_section"),
    "k8-measure": ("V", "gauss_section_measure"),
    "k8-full-gauss": ("V", "full_gauss_section"),
    "k9-filtration": ("V", "quantum_grade_structure"),
    "k9-reducing-carrier": ("V", "yukawa_reducing_carrier"),
    "k9-coframe-metric": ("V", "reducing_coframe_metric"),
    "k9-joint-form": ("V", "joint_form_hamiltonian"),
    "k9-full-adjoint": ("V", "full_quantum_adjoint"),
    "k9-antiunitary": ("V", "quantum_antiunitary"),
    "k10-coframe-weyl": ("V", "coframe_weyl_symbol"),
    "k10-scalar-weyl": ("V", "scalar_weyl_symbol"),
    "k10-common-weyl": ("V", "common_weyl_symbol"),
    "k10-common-temporal": ("V", "common_temporal_form"),
    "k12-ccr-car-ports": ("X", "joint_ccr_car_ports"),
}


def compare_results(frozen, actual, pointer=""):
    """Preserve physical time, signs, source bindings, verdicts and false fields."""
    require(type(frozen) is type(actual), f"Result type differs at {pointer or '/'}")
    if isinstance(frozen, dict):
        omitted = {"elapsed_seconds"} if not pointer else set()
        expected, observed = set(frozen) - omitted, set(actual) - omitted
        require(expected == observed, f"Result fields differ at {pointer or '/'}")
        for key in sorted(expected):
            escaped = key.replace("~", "~0").replace("/", "~1")
            compare_results(frozen[key], actual[key], pointer + "/" + escaped)
    elif isinstance(frozen, list):
        require(len(frozen) == len(actual), f"Result array length differs at {pointer}")
        for index, (old, new) in enumerate(zip(frozen, actual, strict=True)):
            compare_results(old, new, pointer + "/" + str(index))
    else:
        require(frozen == actual, f"Scientific result differs at {pointer or '/'}")


def load_config(path):
    config = read_json(path)
    require(config.get("schema") == SCHEMA, f"Quantum configuration must use {SCHEMA}")
    require(config.get("ignored_result_pointers") == ["/elapsed_seconds"],
            "Only the original top-level wall-clock field may be omitted")
    checks = config.get("checks")
    require(isinstance(checks, list) and checks, "Quantum checks must be a nonempty array")
    seen = set()
    for check in checks:
        name = check.get("id")
        require(name in CASES and name not in seen, "Unknown or duplicate quantum check")
        seen.add(name)
        tag, stem = CASES[name]
        expected_program = ECD + "/independent_source_" + stem + ".py"
        require(check.get("ref") == REVISIONS[tag], "Original source revision differs")
        require(check.get("program") == expected_program and check.get("function") == "main",
                "Original independent entry differs")
        require(check.get("output") == expected_program[:-3] + ".json",
                "Original independent output differs")
        require(check.get("producer", {}).get("program") == ECD + "/source_" + stem + ".py",
                "Original producer differs")
        require(isinstance(check.get("paths"), list) and check["paths"],
                "Quantum source-view inputs are missing")
        require(set(check.get("expected_source_sha256", {})) == set(check["paths"]),
                "Every source-view input needs its original identity")
    require(seen == set(CASES) and set(config.get("required", [])) == seen,
            "The configured carrier scope must contain all eighteen checks")
    return config


def execute_original(inputs, check, output, frozen):
    """Call the byte-verified main; its original output stays in the new view."""
    inputs.verify_all()
    program = inputs.path(check["program"])
    require(inputs.bindings[check["program"]]["source_sha256"] == check["program_sha256"],
            "Independent mathematical program identity differs")
    producer = check["producer"]["program"]
    require(inputs.bindings[producer]["source_sha256"] == check["producer"]["source_sha256"],
            "Original mathematical producer identity differs")
    destination = inside(inputs.root, check["output"])
    require(not destination.exists(), "A fresh result would overwrite a frozen input")
    module = inputs.load(check["program"], "_h0_quantum_" + check["id"].replace("-", "_"))
    require(callable(getattr(module, "main", None)) and not inspect.signature(module.main).parameters,
            "Original independent main must be nullary")
    module.main()
    require(destination.is_file(), "Original independent main produced no result")
    actual = read_json(destination)
    require(actual.get("verdict") == check["expected_verdict"], "Original independent verdict changed")
    compare_results(frozen, actual)
    inputs.verify_all()
    scope = {key: actual[key] for key in check["scope_fields"]}
    output_result = output / "result.json"
    output_result.write_bytes(destination.read_bytes())
    return {"source_commit": check["ref"], "subclaim": check["subclaim"],
            "mathematical_program": {"path": check["program"], "function": "main",
                                     "sha256": check["program_sha256"]},
            "producer": check["producer"], "original_independent_main_executed": True,
            "actual_verdict": actual["verdict"], "actual_scope": scope,
            "fresh_output": "result.json", "fresh_sha256": sha(output_result.read_bytes()),
            "frozen_sha256": check["frozen_sha256"],
            "compared_all_fields_except": ["/elapsed_seconds"],
            "all_verified_source_inputs_preserved": True}


def prepare_quantum_view(check, destination, map_snapshot):
    """Restore receipt-bound data bytes without inventing a compiled epoch.

The mathematical programs are pinned at their own revision. Older receipts
also identify unchanged Lean/data inputs by digest; they are restored from an
already exported byte version and recorded with that provider's actual epoch.
These data bindings create no new Lean build obligation.
"""
    require(not destination.exists(), "A quantum source view must be new")
    bindings, outputs = {}, {}
    with map_root(ROOT, map_snapshot):
        _, modules, artifacts, inverse = source_view.load_map()
        for name, digest in check["expected_source_sha256"].items():
            if name == check["output"]:
                continue
            rows = modules.get(name, []) + artifacts.get(name, [])
            require(rows, "Original quantum input is not exported: " + name)
            row = source_view.pick(rows, name, {digest}, check["ref"])
            if name in modules:
                _, raw = source_view.module_views(row, inverse)
            else:
                raw, _ = source_view.artifact_views(row)
            require(sha(raw) == digest, "Original quantum data bytes differ: " + name)
            outputs[name] = raw
            bindings[name] = {"view_sha256": digest, "source_sha256": digest,
                              "source_revision": row["source_revision"],
                              "source_revisions": row.get("source_revisions", [row["source_revision"]]),
                              "requested_program_revision": check["ref"],
                              "selection_basis": "recorded original SHA256",
                              "publication": row.get("publication")}
    destination.mkdir(parents=True)
    for name, raw in outputs.items():
        path = inside(destination, name)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
    return {"source_revision": check["ref"], "bindings": bindings,
            "omitted_fresh_outputs": [check["output"]]}


def worker(spec_path):
    spec = read_json(spec_path)
    check, output = spec["check"], Path(spec["output"])
    output.mkdir(parents=True)
    receipt = {"id": check["id"], "schema": REPORT_SCHEMA, "status": "failed", "exit_code": 1}
    started = time.monotonic()
    try:
        require(sha(Path(spec["map_snapshot"]).read_bytes()) == spec["map_sha256"],
                "Export identity snapshot changed")
        inputs = PublicInputs(Path(spec["view"]["root"]), spec["view"]["bindings"])
        frozen_path = Path(spec["frozen_snapshot"])
        require(sha(frozen_path.read_bytes()) == check["frozen_sha256"], "Frozen comparison changed")
        frozen = read_json(frozen_path)
        libraries = [sysconfig.get_path(key) for key in ("stdlib", "platstdlib", "purelib", "platlib")]
        scope = RuntimeInputs([Path(spec_path).parent, ROOT / "tools",
                               *[path for path in libraries if path]])
        sys.addaudithook(scope.audit)
        receipt["result"] = execute_original(inputs, check, output, frozen)
        receipt.update(status="passed", exit_code=0)
    except Exception as error:
        receipt["error"] = f"{type(error).__name__}: {error}"
        (output / "failure.log").write_text(traceback.format_exc())
    receipt["elapsed_seconds"] = time.monotonic() - started
    write_json(output / "execution.json", receipt)
    return receipt["exit_code"]


def run(config_path, output=None, python=sys.executable, ids=None):
    config_path = Path(config_path)
    require(config_path.resolve().is_relative_to(ROOT), "Quantum config must be in this repository")
    config = load_config(config_path)
    selected = set(ids) if ids is not None else set(CASES)
    require(selected and selected <= set(CASES), "Selected quantum scope contains an unknown id")
    checks = [check for check in config["checks"] if check["id"] in selected]
    executable = python_executable(python)
    directory = Path(output or ROOT / ".local/first-release-quantum" / uuid.uuid4().hex).resolve()
    require(directory.is_relative_to((ROOT / ".local").resolve()) and not directory.exists(),
            "Quantum output must be a new directory under .local")
    directory.mkdir(parents=True)
    map_raw = (ROOT / "tools/export-map.json").read_bytes()
    map_snapshot = directory / "export-map.snapshot.json"
    map_snapshot.write_bytes(map_raw)
    report = {"schema": REPORT_SCHEMA, "status": "running", "claim_id": "phys.P26",
              "started_at": datetime.now(timezone.utc).isoformat(),
              "config_sha256": sha(config_path.read_bytes()), "map_sha256": sha(map_raw),
              "required": list(CASES), "selected": [check["id"] for check in checks],
              "Lean_build_executed": False, "original_scientific_records_overwritten": False,
              "checks": []}
    started = time.monotonic()
    report_path = directory / "report.json"
    for check in checks:
        result_dir = directory / "checks" / check["id"]
        try:
            print("START", check["id"], flush=True)
            metadata = prepare_quantum_view(check, directory / "views" / check["id"], map_snapshot)
            for name, identity in metadata["bindings"].items():
                require(identity["source_sha256"] == check["expected_source_sha256"][name],
                        "Original source-view identity differs: " + name)
            export = read_json(map_snapshot)
            frozen_rows = [row for row in export["artifacts"]
                           if row["path"] == check["frozen"] and row["source"] == check["output"] and
                           check["ref"] in row.get("source_revisions", [row["source_revision"]])]
            require(len(frozen_rows) == 1 and frozen_rows[0]["source_sha256"] == check["frozen_source_sha256"],
                    "Frozen receipt is not the original declared independent output")
            frozen_raw = inside(ROOT, check["frozen"]).read_bytes()
            require(sha(frozen_raw) == check["frozen_sha256"] == frozen_rows[0]["target_sha256"],
                    "Published frozen comparison differs")
            frozen_snapshot = directory / (check["id"] + ".frozen.json")
            frozen_snapshot.write_bytes(frozen_raw)
            spec = {"check": check, "output": str(result_dir),
                    "view": {**metadata, "root": str(directory / "views" / check["id"])},
                    "map_snapshot": str(map_snapshot), "map_sha256": sha(map_raw),
                    "frozen_snapshot": str(frozen_snapshot)}
            spec_path = directory / (check["id"] + ".worker.json")
            write_json(spec_path, spec)
            completed = subprocess.run([executable, str(Path(__file__).resolve()), "_worker", str(spec_path)],
                                       cwd=ROOT, capture_output=True, text=True, check=False,
                                       timeout=check.get("timeout_seconds", 21600))
            result_dir.mkdir(parents=True, exist_ok=True)
            (result_dir / "worker.stdout.log").write_text(completed.stdout)
            (result_dir / "worker.stderr.log").write_text(completed.stderr)
            receipt = read_json(result_dir / "execution.json")
            require(receipt["id"] == check["id"] and receipt["exit_code"] == completed.returncode,
                    "Worker receipt and actual process exit differ")
            receipt["actual_process_exit_code"] = completed.returncode
            receipt["output_directory"] = str(result_dir.relative_to(directory))
        except Exception as error:
            result_dir.mkdir(parents=True, exist_ok=True)
            (result_dir / "failure.log").write_text(traceback.format_exc())
            receipt = {"id": check["id"], "status": "failed", "exit_code": 1,
                       "error": f"{type(error).__name__}: {error}"}
        report["checks"].append(receipt)
        print(receipt["status"].upper(), check["id"], flush=True)
        report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2, allow_nan=False) + "\n")
    report["elapsed_seconds"] = time.monotonic() - started
    report["passed"] = all(row["status"] == "passed" for row in report["checks"])
    report["complete_carrier_scope"] = report["passed"] and selected == set(CASES)
    report["status"] = "passed" if report["passed"] else "failed"
    report["exit_code"] = 0 if report["passed"] else 1
    report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2, allow_nan=False) + "\n")
    return report, report_path


def main(argv=None):
    argv = list(argv if argv is not None else sys.argv[1:])
    if argv and argv[0] == "_worker":
        require(len(argv) == 2, "Worker needs one declared specification")
        return worker(argv[1])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", default="checks/first-release-quantum.json")
    parser.add_argument("--output")
    parser.add_argument("--python", default=sys.executable)
    parser.add_argument("--ids", action="append", nargs="+")
    args = parser.parse_args(argv)
    try:
        ids = [name for group in args.ids for name in group] if args.ids is not None else None
        report, path = run(args.config, args.output, args.python, ids)
        print(json.dumps({"status": report["status"], "checks": len(report["checks"]),
                          "complete_carrier_scope": report["complete_carrier_scope"],
                          "report": str(path.relative_to(ROOT))}))
        return report["exit_code"]
    except (ReplayError, OSError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
