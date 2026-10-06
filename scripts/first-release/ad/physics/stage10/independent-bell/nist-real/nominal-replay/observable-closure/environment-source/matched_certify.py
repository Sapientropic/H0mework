#!/usr/bin/env python3
"""Certify actual matched EV infinite-Born calibration and necessary raw cubic."""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

import env_certify as base

HERE = Path(__file__).resolve().parent
ROOT = base.ROOT
CRITERION_FREEZE = "af0c821c6aa0e5bb700eb7ec822f63976e86bd00"
CANDIDATE_FREEZE = "64cc6efa6cfacb4d0938908393dc0b7d6c9bd490"
CHAIN = [base.NOMINAL/"gaussian-window/GaussianSource.lean",
         base.NOMINAL/"gaussian-window/native-effects/DetectorGamma.lean",
         *[HERE/name for name in ("EnvironmentSource.lean", "SectorSource.lean", "SectorConsumer.lean",
                                  "MatchedSource.lean", "MatchedConsumer.lean", "MatchedCertification.lean")]]


def main() -> int:
    for name in ("matched-criterion.md", "matched-sources.json"):
        base.frozen(HERE/name, CRITERION_FREEZE)
    for name in ("MatchedSource.lean", "MatchedConsumer.lean"):
        base.frozen(HERE/name, CANDIDATE_FREEZE)
    text = (HERE/"matched-criterion.md").read_text()
    block = text.split("<!-- MATCHED-FROZEN-BEGIN -->")[1].split("<!-- MATCHED-FROZEN-END -->")[0]
    config = json.loads(block.split("```json")[1].split("```")[0])
    if config["version"] != "p23-environment-matched-mc0001" or config["matched_angles"] != [0,0]:
        raise ValueError("unexpected actual matched contract")
    for name in ("arbitrary_legal_environment_overlap", "arbitrary_unit_source_phase", "actual_EV_fullBorn_required", "background_raw_K_required"):
        if config[name] is not True:
            raise ValueError("matched source consumer contract changed: "+name)
    for name in ("completed_Born_or_calibration_as_primitive", "numerical_inverse_or_general_angle_determinant_claim",
                 "controller_advance", "new_numeric_programs_or_outputs_read"):
        if config[name] is not False:
            raise ValueError("matched source scope changed: "+name)
    source = json.loads((HERE/"matched-sources.json").read_text())
    if source["schema"] != "p23-environment-matched-sources/v1" or source["version"] != config["version"]:
        raise ValueError("unexpected matched source manifest")
    if source["new_numeric_programs_or_outputs_read"] is not False or source["controller_advance"] is not False:
        raise ValueError("matched source access or authority changed")
    bindings = {row["path"]: row["sha256"] for row in source["inputs"]}
    for name, expected in bindings.items():
        path = (ROOT/name).resolve()
        if not path.is_relative_to(ROOT) or base.digest(path) != expected:
            raise ValueError("matched source upstream binding differs: "+name)
    owned = [*CHAIN, Path(__file__).resolve(), HERE/"env_certify.py", HERE/"matched-criterion.md", HERE/"matched-sources.json",
             ROOT/"Lean/lean-toolchain", ROOT/"Lean/lake-manifest.json", base.LSP_HELPER, base.LSP_INPUT]
    freezes = {base.relative(path): base.committed(path) for path in owned}
    bindings.update({name: row["sha256"] for name, row in freezes.items()})
    project = ROOT/"Lean"
    env = json.loads(subprocess.check_output(
        ["lake", "env", "python3", "-c", "import json,os;print(json.dumps(dict(os.environ)))"], cwd=project, text=True))
    checks = []
    with tempfile.TemporaryDirectory(prefix="p23-mc-independent-certify-") as fresh:
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
                raise RuntimeError("focused actual matched certification failed")
        base.CHAIN = CHAIN
        diagnostics = base.lsp(project, env)
    for name, expected in bindings.items():
        if base.digest(ROOT/name) != expected:
            raise ValueError("source changed during matched certification: "+name)
    log = checks[-1]["stdout"]
    match = re.search(r"ACTUAL_MATCHED_CERTIFIED declarations=(\d+) main_nodes=(\d+) bundle_nodes=(\d+) required=(\d+) bundle_required=(\d+) primitive=(\d+) source_body=(\d+)", log)
    independent = re.search(r"ACTUAL_MATCHED_INDEPENDENT_AXIOMS declarations=(\d+)", log)
    if match is None or independent is None:
        raise ValueError("actual matched primitive or independent axiom audit missing")
    counts = dict(zip(("candidate_declarations", "main_dependency_nodes", "bundle_dependency_nodes",
                       "required_main_nodes", "required_bundle_nodes", "primitive_nodes", "source_body_nodes"), map(int, match.groups())))
    counts["independent_declarations"] = int(independent.group(1))
    report = {
        "schema": "p23-environment-matched-lean-certification/v1", "version": "p23-environment-matched-mc0001",
        "status": "certified", "criterion_preexecution_freeze": CRITERION_FREEZE,
        "candidate_precompile_freeze": CANDIDATE_FREEZE,
        "unconditional_public_mouth": "P23.EnvironmentSource.Matched.Consumer.actual_matched_calibration_consumer",
        "known_source_inverse_mouth": "P23.EnvironmentSource.Matched.Consumer.generated_loss_inverse_consumer",
        "positive_raw_cubic_mouth": "P23.EnvironmentSource.Matched.Consumer.actual_matched_rawK_cubic_consumer",
        "bindings": bindings, "execution_source_freezes": freezes,
        "authorized_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "focused_verification": {"fresh_source_compilation": True, "trust_level": 0, "warning_as_error": True,
                                 "commands": checks, "lsp": diagnostics},
        "source_audit": {**counts, "primitive": "original RawKernel, two EnvironmentPrim and independent-OR bA/bB in [0,1)",
            "completed_Born_normalizer_PSD_or_calibration_in_primitive": False,
            "actual_EV_gamma_weighted_numberMass_geometric_Cauchy_fullBorn_in_main_closure": True,
            "internally_generated_silent_local_readouts_same_RawKernel": True,
            "generated_positive_heralds_joint_known_mean_inverse_and_cubic_in_bundle": True,
            "abstract_CalibrationLaw_or_root_or_statistical_authority_in_bundle": False},
        "kernel_claims": {"actual_matched_EV_infinite_fullBorn_identity": True,
            "arbitrary_unit_phase_and_legal_xi_eliminated_at_matched_ports": True,
            "internally_generated_silent_detector_local_QA_QB": True,
            "same_source_named_OR_background_singles_joint_and_raw_Option_K": True,
            "raw_source_background_herald_iff_and_positive_joint_guards": True,
            "same_RawKernel_mean_generates_known_mean_TV_readback": True,
            "positive_source_branch_generates_necessary_cubic": True,
            "phase_xi_zero_BG_herald_party_divisor_inverse_cubic_controls": True,
            "unknown_mean_or_loss_inverse_existence_uniqueness": False,
            "Sturm_grid_or_environment_fringe_coherence_inverse": False,
            "general_angle_infinite_Gaussian_determinant_identity": False,
            "actual_hardware_or_source_identity": False, "argmax_or_original_gate_pass": False, "root_activation": False},
        "declaration_classification": {
            "producer": ["matched_gamma", "matched_sector_mass", "weighted_number_cauchy", "matched_fullBorn", "silent"],
            "readout": ["matched_mean_form", "localA_mean_form", "localB_mean_form", "herald_A_iff", "herald_B_iff", "raw_K_generated", "lossA_inverse", "lossB_inverse", "generated_cubic"],
            "direct_consumer": ["actual_matched_calibration_consumer", "generated_loss_inverse_consumer", "actual_matched_rawK_cubic_consumer"]},
        "scope": {"source": "actual EV no-click port effects on the same original normalized RawKernel; a=b=0",
            "infinite_identity": "matched actual fullBorn from all-n weighted numberMass and internally justified geometric/Cauchy summation",
            "local_readouts": "source-generated TV=0 silent detector with the same RawKernel; arbitrary tH/unit phase and legal xi cancel internally",
            "background": "named independent local OR background law; actual noise qualification is separate",
            "herald": "KA=J/SB, KB=J/SA with physical guards; zero herald remains None",
            "inverse": "same-source known mean n=meanNumber(tV) and tV>0; no unknown parameter identification",
            "cubic": "necessary forward P(SA)=0 from raw tV>0 and two positive TV values; not a sufficient inverse certificate",
            "general_angle_infinite_determinant_claim": False, "unknown_inverse_or_numerical_solver_claim": False,
            "calibration_epoch_or_hardware_verified": False, "actual_NIST_source_identified": False,
            "production_admitted": False, "apparatus_optimum_verified": False, "controller_advance": False},
        "new_numeric_programs_or_outputs_read": False,
    }
    output = HERE/"matched-certification.json"
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False, allow_nan=False)+"\n")
    capsule = {"schema": "p23-environment-matched-certify-capsule/v1", "phase": "certify", "verdict": "certified",
               "unconditional_public_mouth": report["unconditional_public_mouth"], "candidate_precompile_freeze": CANDIDATE_FREEZE,
               "certification_sha256": base.digest(output), "source_audit": report["source_audit"],
               "kernel_claims": report["kernel_claims"], "scope": report["scope"], "bindings": bindings}
    Path("/tmp/p23-mc-certify-capsule.json").write_text(json.dumps(capsule, indent=2, ensure_ascii=False))
    print(json.dumps({"status": report["status"], "source_audit": report["source_audit"],
                      "certification_sha256": capsule["certification_sha256"]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
