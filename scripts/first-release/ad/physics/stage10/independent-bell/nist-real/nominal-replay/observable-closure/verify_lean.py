#!/usr/bin/env python3
"""Independent certification of the frozen source-forward elimination candidate."""
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
NOMINAL = HERE.parent
CRITERION_FREEZE = "fde5c14df36b6064c87064acd20830d3df0500bb"
CANDIDATE_FREEZE = "d95c4ff3f0614eb098bd5d83cb929c1b97ab3857"
CHAIN = [NOMINAL/"gaussian-window/GaussianSource.lean",
         *[HERE/name for name in ("ObservableClosure.lean", "ClosureConsumer.lean", "ClosureCertification.lean")]]
LSP_HELPER = NOMINAL/"investigation/collected-source/certify.py"
LSP_INPUT = LSP_HELPER.parent/"verify.py"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def frozen(path: Path, commit: str) -> None:
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=True)
    original = subprocess.check_output(["git", "show", commit+":"+relative(path)], cwd=ROOT)
    if original != path.read_bytes():
        raise ValueError("observable closure source differs from its preexecution freeze: "+relative(path))


def committed(path: Path) -> dict:
    commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", relative(path)],
                                     cwd=ROOT, text=True).strip()
    if not commit:
        raise ValueError("observable closure execution source has no precompile freeze")
    frozen(path, commit)
    return {"commit": commit, "sha256": digest(path)}


def lsp(project: Path, env: dict) -> list:
    old_verify = sys.modules.pop("verify", None)
    sys.path.insert(0, str(LSP_HELPER.parent))
    try:
        spec = importlib.util.spec_from_file_location("p23_ef_independent_LSP", LSP_HELPER)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        return module.lsp_check(project, env, CHAIN)
    finally:
        sys.path.remove(str(LSP_HELPER.parent))
        sys.modules.pop("verify", None)
        if old_verify is not None:
            sys.modules["verify"] = old_verify


def main() -> int:
    for name in ("criterion.md", "sources.json"):
        frozen(HERE/name, CRITERION_FREEZE)
    for name in ("ObservableClosure.lean", "ClosureConsumer.lean"):
        frozen(HERE/name, CANDIDATE_FREEZE)
    source = json.loads((HERE/"sources.json").read_text())
    if source["schema"] != "p23-observable-closure-sources/v1" or source["version"] != "p23-observable-closure-ef0001":
        raise ValueError("unexpected observable closure source contract")
    if source["bell_event_files_read"] != 0 or source["retrospective"] is not True:
        raise ValueError("observable closure source access or statistical scope differs")
    bindings = {row["path"]: row["sha256"] for row in source["inputs"]}
    for name, expected in bindings.items():
        path = (ROOT/name).resolve()
        if not path.is_relative_to(ROOT) or digest(path) != expected:
            raise ValueError("observable closure upstream binding differs: "+name)
    owned = [*CHAIN, Path(__file__).resolve(), HERE/"criterion.md", HERE/"sources.json",
             ROOT/"Lean/lean-toolchain", ROOT/"Lean/lake-manifest.json", LSP_HELPER, LSP_INPUT]
    freezes = {relative(path): committed(path) for path in owned}
    bindings.update({name: row["sha256"] for name, row in freezes.items()})
    project = ROOT/"Lean"
    env = json.loads(subprocess.check_output(
        ["lake", "env", "python3", "-c", "import json,os;print(json.dumps(dict(os.environ)))"], cwd=project, text=True))
    checks = []
    with tempfile.TemporaryDirectory(prefix="p23-ef-independent-certify-") as fresh:
        env["LEAN_PATH"] = fresh+os.pathsep+env.get("LEAN_PATH", "")
        for path in CHAIN:
            argv = ["lean", "--trust=0", "-DwarningAsError=true", "--root="+os.path.relpath(path.parent, project),
                    "-o", str(Path(fresh)/(path.stem+".olean")), os.path.relpath(path, project)]
            run = subprocess.run(argv, cwd=project, env=env, capture_output=True, text=True, timeout=180)
            shown = argv.copy()
            shown[5] = "${fresh_olean}/"+path.stem+".olean"
            checks.append({"source": relative(path), "command": shown, "exit_code": run.returncode,
                           "stdout": run.stdout, "stderr": run.stderr})
            print(path.name+" fresh trust0/werror exit="+str(run.returncode), flush=True)
            if run.returncode:
                print(run.stdout+run.stderr, flush=True)
                raise RuntimeError("focused observable closure certification failed")
        diagnostics = lsp(project, env)
    for name, expected in bindings.items():
        if digest(ROOT/name) != expected:
            raise ValueError("source changed during observable closure certification: "+name)
    log = checks[-1]["stdout"]
    match = re.search(r"OBSERVABLE_CLOSURE_CERTIFIED declarations=(\d+) main_nodes=(\d+) bundle_nodes=(\d+) required=(\d+) primitive=(\d+)", log)
    independent = re.search(r"OBSERVABLE_CLOSURE_INDEPENDENT_AXIOMS declarations=(\d+)", log)
    if match is None or independent is None:
        raise ValueError("observable closure dependency or independent axiom audit missing")
    counts = dict(zip(("candidate_declarations", "main_dependency_nodes", "bundle_dependency_nodes",
                       "required_main_nodes", "primitive_nodes"), map(int, match.groups())))
    counts["independent_declarations"] = int(independent.group(1))
    report = {
        "schema": "p23-observable-closure-lean-certification/v1", "version": "p23-observable-closure-ef0001",
        "status": "certified", "criterion_preexecution_freeze": CRITERION_FREEZE,
        "candidate_precompile_freeze": CANDIDATE_FREEZE,
        "public_mouth": "P23.ObservableClosure.Consumer.shared_training_root_and_heldout",
        "bindings": bindings, "execution_source_freezes": freezes,
        "authorized_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "focused_verification": {"fresh_source_compilation": True, "trust_level": 0, "warning_as_error": True,
                                 "commands": checks, "lsp": diagnostics},
        "source_audit": {**counts,
            "primitive": "nH/nV, two positive scalar transmissions, one delta and lambda, physical order/bounds only",
            "target_H_F_root_or_coverage_in_primitive": False,
            "named_phase_denominators_generated_positive": True,
            "source_H_degree_common_root_and_shared_consumer_in_main_closure": True,
            "native_RawKernel_and_mean_readback_certified_separately": True,
            "native_kernel_or_countPGF_or_fullBorn_in_main_closure": False,
            "root_or_statistical_authority_in_main_closure": False},
        "kernel_claims": {"legal_native_source_mapping_and_mean_readback": True,
            "named_Gaussian_phase_denominator_positivity": True,
            "actual_source_generates_H_equals_coherence_gT": True,
            "generated_polynomial_degree_at_most_two": True,
            "actual_absolute_loss_is_common_training_and_cell_root": True,
            "first_informative_mirror_seed_and_zero_fallback": True,
            "same_source_all_cell_N5_OR_recipe_equality": True, "four_outcome_recipe_sum_one": True,
            "source_generated_necessary_Sylvester_determinants_zero": True,
            "nonempty_source_negative_coherence_fallback_and_nonsufficiency_controls": True,
            "resultant_sufficiency": False, "full_Gaussian_Born_vacuum_identity": False,
            "full_outcome_nonnegative_distribution": False, "public_six_count_inverse": False,
            "all_real_inverse_roots_enumerated": False, "finite_count_Ville_kernel": False,
            "full_statistical_training_fiber_certified": False},
        "scope": {"source": "forward arithmetic of the named two-polarization Gaussian pulse law",
            "source_mapping": "legal original RawKernel generated separately from the same finite source occupations",
            "consumer": "one Snapshot, actual loss/root and phase generates all cells; N5 OR formulas as arithmetic recipes",
            "background": "formal consumer accepts arbitrary real background arguments; probability qualification is separate",
            "statistics": "frozen po0003 confidence is external; no stationary source identity or coverage inferred from public centers",
            "native_fullBorn_identity_newly_proved": False, "actual_NIST_configuration_identified": False,
            "hardware_operated": False, "production_admitted": False, "full_statistical_fiber_certified": False,
            "global_optimum_proved": False, "controller_advance": False, "nominal_optimum_verdict_changed": False},
        "numerical_access": {"new_science_program_files_read": False, "science_receipt_files_read": False,
            "parent_center_outcome_summary_received": True,
            "summary_scope": "illegal exact-center roots were communicated before route review; the mathematical candidate was not modified"},
        "retrospective": True, "bell_event_files_read": 0,
    }
    output = HERE/"certification.json"
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False, allow_nan=False)+"\n")
    capsule = {"schema": "p23-observable-closure-certify-capsule/v1", "phase": "certify", "verdict": "certified",
               "public_mouth": report["public_mouth"], "candidate_precompile_freeze": CANDIDATE_FREEZE,
               "certification_sha256": digest(output), "source_audit": report["source_audit"],
               "kernel_claims": report["kernel_claims"], "scope": report["scope"], "bindings": bindings}
    Path("/tmp/p23-ef-certify-capsule.json").write_text(json.dumps(capsule, indent=2, ensure_ascii=False))
    print(json.dumps({"status": report["status"], "source_audit": report["source_audit"],
                      "certification_sha256": capsule["certification_sha256"]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
