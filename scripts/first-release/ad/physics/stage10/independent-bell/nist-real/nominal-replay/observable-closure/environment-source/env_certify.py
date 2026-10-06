#!/usr/bin/env python3
"""Independent finite-environment source, actual ports and all-sector trust audit."""
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
ROOT = HERE.parents[7]
NOMINAL = HERE.parents[1]
CRITERION_FREEZE = "0d1e6c22ee1b18a01e2755ee5e04a618a66cf157"
CANDIDATE_FREEZE = "ee4adfbc4a7d26e80d997a72db858811ed87d277"
CHAIN = [NOMINAL/"gaussian-window/GaussianSource.lean",
         NOMINAL/"gaussian-window/native-effects/DetectorGamma.lean",
         *[HERE/name for name in ("EnvironmentSource.lean", "EnvironmentConsumer.lean", "EnvironmentCertification.lean")]]
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
        raise ValueError("environment source differs from its preexecution freeze: "+relative(path))


def committed(path: Path) -> dict:
    commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", relative(path)],
                                     cwd=ROOT, text=True).strip()
    if not commit:
        raise ValueError("environment audit source has no precompile freeze")
    frozen(path, commit)
    return {"commit": commit, "sha256": digest(path)}


def lsp(project: Path, env: dict) -> list:
    old_verify = sys.modules.pop("verify", None)
    sys.path.insert(0, str(LSP_HELPER.parent))
    try:
        spec = importlib.util.spec_from_file_location("p23_ev_independent_LSP", LSP_HELPER)
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
    for name in ("EnvironmentSource.lean", "EnvironmentConsumer.lean"):
        frozen(HERE/name, CANDIDATE_FREEZE)
    text = (HERE/"criterion.md").read_text()
    block = text.split("<!-- ENV-FROZEN-BEGIN -->")[1].split("<!-- ENV-FROZEN-END -->")[0]
    config = json.loads(block.split("```json")[1].split("```")[0])
    if config["version"] != "p23-fixed-environment-ev0001" or config["environment_dimension_per_party"] != 2 or config["output_ports_per_party"] != 6:
        raise ValueError("unexpected physical environment contract")
    for name in ("completed_Gram_or_PSD_as_primitive", "old_rank_one_gain_inverse_admitted_for_new_source",
                 "new_full_Born_kernel_claim", "actual_source_identity_verified", "apparatus_optimum_verified", "controller_advance"):
        if config[name] is not False:
            raise ValueError("environment source scope changed: "+name)
    if config["all_number_sectors_required"] is not True or config["rank_one_limit_required"] is not True or config["retrospective"] is not True or type(config["event_files_read"]) is not int or config["event_files_read"] != 0:
        raise ValueError("environment source access or consumer scope changed")
    source = json.loads((HERE/"sources.json").read_text())
    if source["schema"] != "p23-fixed-environment-sources/v1" or source["version"] != config["version"]:
        raise ValueError("unexpected environment source manifest")
    if source["retrospective"] is not True or source["archive_code_executed"] is not False or type(source["event_files_read"]) is not int or source["event_files_read"] != 0:
        raise ValueError("environment source execution or empirical identity changed")
    bindings = {row["path"]: row["sha256"] for row in source["inputs"]}
    for name, expected in bindings.items():
        path = (ROOT/name).resolve()
        if not path.is_relative_to(ROOT) or digest(path) != expected:
            raise ValueError("environment source upstream binding differs: "+name)
    owned = [*CHAIN, Path(__file__).resolve(), HERE/"criterion.md", HERE/"sources.json",
             ROOT/"Lean/lean-toolchain", ROOT/"Lean/lake-manifest.json", LSP_HELPER, LSP_INPUT]
    freezes = {relative(path): committed(path) for path in owned}
    bindings.update({name: row["sha256"] for name, row in freezes.items()})
    project = ROOT/"Lean"
    env = json.loads(subprocess.check_output(
        ["lake", "env", "python3", "-c", "import json,os;print(json.dumps(dict(os.environ)))"], cwd=project, text=True))
    checks = []
    with tempfile.TemporaryDirectory(prefix="p23-ev-independent-certify-") as fresh:
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
                raise RuntimeError("focused environment source certification failed")
        diagnostics = lsp(project, env)
    for name, expected in bindings.items():
        if digest(ROOT/name) != expected:
            raise ValueError("source changed during environment certification: "+name)
    log = checks[-1]["stdout"]
    match = re.search(r"ENVIRONMENT_SOURCE_CERTIFIED declarations=(\d+) main_nodes=(\d+) bundle_nodes=(\d+) required=(\d+) bundle_required=(\d+) primitive=(\d+) source_body=(\d+)", log)
    independent = re.search(r"ENVIRONMENT_SOURCE_INDEPENDENT_AXIOMS declarations=(\d+)", log)
    if match is None or independent is None:
        raise ValueError("environment primitive, source body or independent axiom audit missing")
    counts = dict(zip(("candidate_declarations", "main_dependency_nodes", "bundle_dependency_nodes",
                       "required_main_nodes", "required_bundle_nodes", "primitive_nodes", "source_body_nodes"), map(int, match.groups())))
    counts["independent_declarations"] = int(independent.group(1))
    report = {
        "schema": "p23-environment-source-lean-certification/v1", "version": "p23-fixed-environment-ev0001",
        "status": "certified", "criterion_preexecution_freeze": CRITERION_FREEZE, "candidate_precompile_freeze": CANDIDATE_FREEZE,
        "public_mouth": "P23.EnvironmentSource.Consumer.environment_source_consumer",
        "rank_one_limit_mouth": "P23.EnvironmentSource.Consumer.rankOne_limit_consumer",
        "bindings": bindings, "execution_source_freezes": freezes,
        "authorized_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "focused_verification": {"fresh_source_compilation": True, "trust_level": 0, "warning_as_error": True,
                                 "commands": checks, "lsp": diagnostics},
        "source_audit": {**counts, "primitive": "original legal DetectorPrim plus complex xi with normSq<=1",
            "completed_Gram_PSD_source_certificate_in_primitive_or_port_body": False,
            "occupied_and_six_port_isometries_in_main_closure": True,
            "actual_Pol_times_Env_rotation_and_source_columns_in_bundle": True,
            "actual_all_number_port_Gram_bounds_and_occupation_in_main_closure": True,
            "old_gamma_is_alias_of_general_environment_main": False,
            "full_infinite_Born_or_Gaussian_determinant_in_main_closure": False,
            "root_or_statistical_authority_in_bundle": False},
        "kernel_claims": {"physical_environment_columns_generated_isometric": True,
            "physical_Pol_Env_action_then_analyzer_generated_rows": True,
            "explicit_complete_six_port_Gram_identity": True,
            "generated_clicked_Gram_formula_and_no_click_complement": True,
            "generated_one_photon_and_every_number_sector_positive_contraction": True,
            "actual_numberPorts_Gram_and_complete_number_port_isometry": True,
            "generic_complex_density_and_finite_vector_same_effect_consumers": True,
            "generated_rank_defect_and_conditional_not_rank_one": True,
            "xi_equals_one_exact_original_onePhoton_and_all_gamma_limit": True,
            "xi_zero_one_complex_i_loss_boundary_and_carrier_alias_controls": True,
            "new_full_infinite_Born_kernel": False, "new_Gaussian_determinant_kernel": False,
            "old_rank_one_inverse_admitted": False, "public_calibration_fiber_inverse": False,
            "actual_hardware_or_source_identity": False, "argmax_or_original_gate_pass": False,
            "statistical_model_or_Ville_qualification": False, "root_activation": False},
        "declaration_classification": {
            "producer": ["occupiedColumns", "physicalClickedRows_generated", "sixPorts_gram", "onePhoton_bounds", "gamma_port_born", "allPorts_number_isometry", "gamma_bounds"],
            "readout": ["clickedGram_formula", "onePhoton_density_generated", "onePhoton_finitePhi_generated", "number_density_generated", "number_finitePhi_generated"],
            "transporter": ["rankOne_noClick", "rankOne_gamma", "rankOne_limit_consumer"],
            "diagnostic": ["clickedGram_determinant", "clickedGram_not_rankOne"],
            "direct_consumer": ["environment_source_consumer"]},
        "scope": {"source": "named two-dimensional local environment and physical six-port passive source constructor",
            "rotation": "Pol x Env action precedes analyzer; it acts on transmitted physical columns",
            "rank_defect": "positive TH/TV, nonzero sin/cos and normSq(xi)<1 exclude every vector outer product",
            "old_limit": "xi=1 gives the original real-angle detector gamma; arbitrary unit complex xi is not silently identified with that old limit",
            "Born": "all finite number-sector matrices and vector port Grams; arbitrary complex density trace identity without supplied state positivity",
            "infinite_source": "no new full infinite-state Born, Gaussian determinant or calibration inverse identity",
            "actual_NIST_source_identified": False, "actual_hardware_verified": False, "calibration_inverse_verified": False,
            "new_full_infinite_Born_kernel": False, "new_Gaussian_determinant_kernel": False,
            "production_admitted": False, "apparatus_optimum_verified": False, "controller_advance": False},
        "source_access": {"new_scientific_model_or_DAQ_execution": False, "event_files_read": 0},
        "retrospective": True,
    }
    output = HERE/"certification.json"
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False, allow_nan=False)+"\n")
    capsule = {"schema": "p23-fixed-environment-certify-capsule/v1", "phase": "certify", "verdict": "certified",
               "public_mouth": report["public_mouth"], "candidate_precompile_freeze": CANDIDATE_FREEZE,
               "certification_sha256": digest(output), "source_audit": report["source_audit"],
               "kernel_claims": report["kernel_claims"], "scope": report["scope"], "bindings": bindings}
    Path("/tmp/p23-ev-certify-capsule.json").write_text(json.dumps(capsule, indent=2, ensure_ascii=False))
    print(json.dumps({"status": report["status"], "source_audit": report["source_audit"],
                      "certification_sha256": capsule["certification_sha256"]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
