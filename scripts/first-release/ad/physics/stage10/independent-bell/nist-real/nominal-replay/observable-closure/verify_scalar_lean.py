#!/usr/bin/env python3
"""Certify source generation on the frozen scalar physical domain."""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

import verify_lean as base

HERE = Path(__file__).resolve().parent
ROOT = base.ROOT
CRITERION_FREEZE = "e71683e0bf961a5221579f0d36bf9bb9f711b0b6"
CANDIDATE_FREEZE = "0d34a2a0e61680568adec69be401777ce7dba9b4"
CHAIN = [HERE.parent/"gaussian-window/GaussianSource.lean",
         *[HERE/name for name in ("ObservableClosure.lean", "ClosureConsumer.lean", "ScalarFiber.lean",
                                  "ScalarFiberConsumer.lean", "ScalarFiberCertification.lean")]]


def main() -> int:
    for name in ("criterion-ef0002.md", "sources-ef0002.json"):
        base.frozen(HERE/name, CRITERION_FREEZE)
    for name in ("ScalarFiber.lean", "ScalarFiberConsumer.lean"):
        base.frozen(HERE/name, CANDIDATE_FREEZE)
    source = json.loads((HERE/"sources-ef0002.json").read_text())
    if source["schema"] != "p23-observable-closure-sources/v2" or source["version"] != "p23-observable-closure-ef0002":
        raise ValueError("unexpected scalar source contract")
    if source["bell_event_files_read"] != 0 or source["retrospective"] is not True:
        raise ValueError("scalar source access or statistical scope differs")
    bindings = {row["path"]: row["sha256"] for row in source["inputs"]}
    for name, expected in bindings.items():
        path = (ROOT/name).resolve()
        if not path.is_relative_to(ROOT) or base.digest(path) != expected:
            raise ValueError("scalar source upstream binding differs: "+name)
    owned = [*CHAIN, Path(__file__).resolve(), HERE/"criterion-ef0002.md", HERE/"sources-ef0002.json",
             HERE/"verify_lean.py", HERE/"ClosureCertification.lean", HERE/"certification.json",
             ROOT/"Lean/lean-toolchain", ROOT/"Lean/lake-manifest.json", base.LSP_HELPER, base.LSP_INPUT]
    freezes = {base.relative(path): base.committed(path) for path in owned}
    bindings.update({name: row["sha256"] for name, row in freezes.items()})
    project = ROOT/"Lean"
    env = json.loads(subprocess.check_output(
        ["lake", "env", "python3", "-c", "import json,os;print(json.dumps(dict(os.environ)))"], cwd=project, text=True))
    checks = []
    with tempfile.TemporaryDirectory(prefix="p23-scalar-independent-certify-") as fresh:
        env["LEAN_PATH"] = fresh+os.pathsep+env.get("LEAN_PATH", "")
        for path in CHAIN:
            argv = ["lean", "--trust=0", "-DwarningAsError=true", "--root="+os.path.relpath(path.parent, project),
                    "-o", str(Path(fresh)/(path.stem+".olean")), os.path.relpath(path, project)]
            run = subprocess.run(argv, cwd=project, env=env, capture_output=True, text=True, timeout=180)
            shown = argv.copy()
            shown[5] = "${fresh_olean}/"+path.stem+".olean"
            checks.append({"source": base.relative(path), "command": shown, "exit_code": run.returncode,
                           "stdout": run.stdout, "stderr": run.stderr})
            print(path.name+" fresh trust0/werror exit="+str(run.returncode), flush=True)
            if run.returncode:
                print(run.stdout+run.stderr, flush=True)
                raise RuntimeError("focused scalar source certification failed")
        base.CHAIN = CHAIN
        diagnostics = base.lsp(project, env)
    for name, expected in bindings.items():
        if base.digest(ROOT/name) != expected:
            raise ValueError("source changed during scalar source certification: "+name)
    log = checks[-1]["stdout"]
    match = re.search(r"SCALAR_SOURCE_CERTIFIED declarations=(\d+) main_nodes=(\d+) bundle_nodes=(\d+) required=(\d+) primitive=(\d+)", log)
    independent = re.search(r"SCALAR_SOURCE_INDEPENDENT_AXIOMS declarations=(\d+)", log)
    if match is None or independent is None:
        raise ValueError("scalar source primitive or independent axiom audit missing")
    counts = dict(zip(("candidate_declarations", "main_dependency_nodes", "bundle_dependency_nodes",
                       "required_main_nodes", "primitive_nodes"), map(int, match.groups())))
    counts["independent_declarations"] = int(independent.group(1))
    report = {
        "schema": "p23-scalar-source-lean-certification/v1", "version": "p23-observable-closure-ef0002",
        "status": "certified", "criterion_preexecution_freeze": CRITERION_FREEZE,
        "candidate_precompile_freeze": CANDIDATE_FREEZE,
        "public_mouth": "P23.ObservableClosure.ScalarFiber.Consumer.source_fiber_generates_seed_and_windows",
        "bindings": bindings, "execution_source_freezes": freezes,
        "authorized_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "focused_verification": {"fresh_source_compilation": True, "trust_level": 0, "warning_as_error": True,
                                 "commands": checks, "lsp": diagnostics},
        "source_audit": {**counts, "primitive": "scaled h>v>0, ratio>0, delta, legal scalar loss, seed w and computed phase square inequality",
            "completed_seed_readback_target_snapshot_or_actual_source_identity_in_primitive": False,
            "lambda_legality_T_positive_and_actual_seed_readback_generated": True,
            "same_source_means_cells_and_N5_recipe_consumer_in_main_closure": True,
            "numeric_signs_to_generated_training_pulse_interval_in_bundle": True,
            "countPGF_fullBorn_or_native_kernel_in_main_closure": False,
            "root_or_probability_authority_in_bundle": False},
        "kernel_claims": {"pointwise_legal_scalar_domain_generates_physical_Snapshot": True,
            "generated_strictly_positive_T_and_legal_coherence_lambda": True,
            "generated_actual_named_pulse_seed_readback": True,
            "generated_scaled_source_loss_readback": True, "all_angle_means_independent_of_scalar_loss": True,
            "same_source_all_cell_and_N5_OR_recipe_readback": True,
            "two_computed_signs_transport_to_generated_training_pulse_interval": True,
            "nonempty_phase_domain_and_illegal_phase_zero_loss_controls": True,
            "new_full_Gaussian_Born_identity": False, "public_four_single_inverse": False,
            "all_outcome_nonnegative_distribution": False, "scalar_partition_cover_completeness": False,
            "statistical_confidence_or_Ville": False, "full_six_dimensional_statistical_fiber": False,
            "actual_source_identified": False},
        "scope": {"source": "h>v>0, ratio>0 and legal free loss generate one named Gaussian source from the seed scalar domain",
            "loss": "fiber index; no actual parameter identification or interval partition completeness",
            "training": "computed source-free polynomial sign conditions transport to actual generated pulse intervals",
            "consumer": "same generated source and phase for all cells; N5 OR recipes as arithmetic",
            "background": "formal consumer has arbitrary real background arguments; probability qualification remains separate",
            "statistics": "five centers plus original joint11 CI define a named slice; neither statistical coverage nor public-data inverse is a new kernel claim",
            "actual_NIST_configuration_identified": False, "hardware_operated": False, "production_admitted": False,
            "full_statistical_fiber_certified": False, "apparatus_optimum_verified": False,
            "global_optimum_proved": False, "controller_advance": False},
        "numerical_access": {"new_ef0002_science_program_or_receipt_files_read": False,
            "prior_ef0001_science_files": "hash bindings checked only", "prior_center_outcome_summary_received": True},
        "retrospective": True, "bell_event_files_read": 0,
    }
    output = HERE/"scalar-certification.json"
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False, allow_nan=False)+"\n")
    capsule = {"schema": "p23-scalar-source-certify-capsule/v1", "phase": "certify", "verdict": "certified",
               "public_mouth": report["public_mouth"], "candidate_precompile_freeze": CANDIDATE_FREEZE,
               "certification_sha256": base.digest(output), "source_audit": report["source_audit"],
               "kernel_claims": report["kernel_claims"], "scope": report["scope"], "bindings": bindings}
    Path("/tmp/p23-ef2-certify-capsule.json").write_text(json.dumps(capsule, indent=2, ensure_ascii=False))
    print(json.dumps({"status": report["status"], "source_audit": report["source_audit"],
                      "certification_sha256": capsule["certification_sha256"]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
