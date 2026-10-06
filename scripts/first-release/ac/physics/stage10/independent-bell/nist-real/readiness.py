"""Fail-closed theory-readiness assessment; no dataset paths or data-reader API."""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
sys.path.insert(0, str(HERE.parent))
import real_family as rf
from checks import control_loop

PRODUCTION = "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/RealFamily.lean"
CERTIFICATION = "Lean/docs/audits/physics/stage10-bell/RealFamilyCertification.lean"
REGISTRY_KEYS = {"preparation", "angles_and_pulses", "eta", "assignment", "background",
                 "pair_probability", "visibility", "model_tv", "epoch_and_drift",
                 "trial_format", "joint_coverage", "nominal_optimum"}
GEOMETRY_KEYS = ("matrix_matches_all_cells", "mirror_geometry", "real_shape",
                 "rare_vertical_transmission", "primed_destructive_structure",
                 "wrong_basis_rejected", "wrong_bob_sign_rejected")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_lean():
    path = HERE / "evidence/lean-certification.json"
    initial = {p: digest(ROOT / p) for p in (PRODUCTION, CERTIFICATION)}
    path.write_text(json.dumps({"status": "running", "source_sha256": initial}) + "\n")
    commands = [
        ["lake", "build", "SaturationMonoid.PhysicsCore.Stage10.Bell.RealFamily"],
        ["lake", "env", "lean", "--trust=0", "-DwarningAsError=true", PRODUCTION[5:]],
        ["lake", "env", "lean", "--trust=0", "-DwarningAsError=true", CERTIFICATION[5:]],
    ]
    results = []
    for command in commands:
        start = time.monotonic()
        try:
            run = subprocess.run(command, cwd=ROOT / "Lean", text=True,
                                 capture_output=True, timeout=180)
            results.append({"command": command, "returncode": run.returncode,
                            "seconds": round(time.monotonic()-start, 3),
                            "output": (run.stdout+run.stderr)[-6000:]})
        except subprocess.TimeoutExpired:
            results.append({"command": command, "returncode": -1, "output": "timeout"})
        if results[-1]["returncode"] != 0:
            break
    unchanged = initial == {p: digest(ROOT / p) for p in initial}
    passed = unchanged and len(results) == 3 and all(r["returncode"] == 0 for r in results)
    path.write_text(json.dumps({"status": "passed" if passed else "failed",
                               "source_sha256": initial, "commands": results}, indent=2)+"\n")


def visibility_investigation():
    directory = HERE / "nominal-replay/investigation"
    if not (directory / "verification.json").exists():
        return {"status": "not_available", "evidence_valid": False, "production_admitted": False}
    try:
        run = subprocess.run([sys.executable, str(directory / "verify.py"), "--check-only"],
                             text=True, capture_output=True, timeout=30)
        result = json.loads(run.stdout)
        if (run.returncode != 0 or result.get("status") != "verified"
                or result.get("production_admitted") is not False
                or result.get("source_mapping_identified") is not False):
            return {"status": "invalid_research_evidence", "evidence_valid": False,
                    "production_admitted": False, "reason": result.get("reason", "verification failed")}
        result["evidence_valid"] = True
        result["status"] = "verified_research_with_unidentified_source_mapping"
        return result
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        return {"status": "invalid_research_evidence", "evidence_valid": False,
                "production_admitted": False, "reason": str(error)}

def source_code_investigation(*, report_dir=None, enabled=True):
    directory = HERE / "nominal-replay/source-code"
    rejected = {"evidence_valid": False, "model_source_identified": False,
                "publication_configuration_identified": False, "production_admitted": False}
    if not enabled:
        return {**rejected, "status": "disabled_by_override"}
    if not (directory / "verification.json").is_file():
        return {**rejected, "status": "not_available"}
    command = [sys.executable, str(directory / "verify.py"), "--check-only"]
    if report_dir is not None:
        command.extend(("--directory", str(report_dir)))
    try:
        run = subprocess.run(command, text=True, capture_output=True, timeout=30)
        result = json.loads(run.stdout)
        if (run.returncode != 0 or result.get("status") != "verified"
                or result.get("model_source_identified") is not True
                or result.get("publication_configuration_identified") is not False
                or result.get("production_admitted") is not False):
            return {**rejected, "status": "invalid_source_code_evidence",
                    "reason": result.get("reason", "verification failed")}
        result["evidence_valid"] = True
        result["status"] = "verified_research_source_model_recovered"
        return result
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        return {**rejected, "status": "invalid_source_code_evidence", "reason": str(error)}


def response_investigation(*, report_dir=None, enabled=True):
    directory = HERE / "nominal-replay/response"
    rejected = {"evidence_valid": False, "source_mapping_identified": False,
                "production_admitted": False}
    if not enabled:
        return {**rejected, "status": "disabled_by_override"}
    receipt_dir = directory if report_dir is None else Path(report_dir)
    if not (receipt_dir / "verification.json").is_file():
        return {**rejected, "status": "not_available"}
    command = [sys.executable, str(directory / "verify.py"), "--check-only"]
    if report_dir is not None:
        command.extend(("--directory", str(report_dir)))
    try:
        run = subprocess.run(command, text=True, capture_output=True, timeout=60)
        result = json.loads(run.stdout)
        if (run.returncode != 0 or result.get("schema") != "nist-response-verification/v1"
                or result.get("status") != "verified"
                or result.get("criterion_version") != "nominal-response-r0006"
                or result.get("source_mapping_identified") is not False
                or result.get("production_admitted") is not False):
            return {**rejected, "status": "invalid_response_evidence",
                    "reason": result.get("reason", "verification failed")}
        # A conditional improving update supplies research evidence, not an optimum receipt.
        result["evidence_valid"] = True
        result["status"] = "verified_research_continuous_response_and_update"
        return result
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        return {**rejected, "status": "invalid_response_evidence", "reason": str(error)}


def collected_response_investigation(*, report_dir=None, enabled=True):
    directory = HERE / "nominal-replay/collected-response"
    rejected = {"evidence_valid": False, "source_mapping_identified": False,
                "publication_configuration_identified": False, "production_admitted": False}
    if not enabled:
        return {**rejected, "status": "disabled_by_override"}
    receipt_dir = directory if report_dir is None else Path(report_dir)
    if not (receipt_dir / "verification.json").is_file():
        return {**rejected, "status": "not_available"}
    command = [sys.executable, str(directory / "verify.py"), "--check-only"]
    if report_dir is not None:
        command.extend(("--directory", str(report_dir)))
    try:
        run = subprocess.run(command, text=True, capture_output=True, timeout=60)
        result = json.loads(run.stdout)
        if (run.returncode != 0 or result.get("schema") != "p23-collected-response-verification/v1"
                or result.get("status") != "verified"
                or result.get("version") != "p23-collected-response-cr0001.1"
                or any(result.get(k) is not False for k in ("source_mapping_identified",
                           "publication_configuration_identified", "production_admitted"))):
            return {**rejected, "status": "invalid_collected_response_evidence",
                    "reason": result.get("reason", "verification failed")}
        # The intake preserves the conditional calibration contract and the original optimum gate.
        result["evidence_valid"] = True
        result["status"] = "verified_research_collected_source_response"
        return result
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        return {**rejected, "status": "invalid_collected_response_evidence", "reason": str(error)}


def observable_prediction_investigation(*, report_dir=None, enabled=True, public=False):
    directory = HERE / "nominal-replay/observable-prediction"
    rejected = {"evidence_valid": False, "source_mapping_identified": False,
                "publication_configuration_identified": False, "production_admitted": False}
    if not enabled:
        return {**rejected, "status": "disabled_by_override"}
    receipt_dir = directory if report_dir is None else Path(report_dir)
    verifier = "public_verify.py" if public else "verify.py"
    receipt = "public-verification.json" if public else "verification.json"
    if not (receipt_dir / receipt).is_file():
        return {**rejected, "status": "not_available"}
    command = [sys.executable, str(directory / verifier), "--check-only"]
    if report_dir is not None:
        command.extend(("--directory", str(report_dir)))
    schema = "p23-public-observable-verification/v1" if public else "p23-observable-prediction-verification/v1"
    version = "p23-public-observables-po0003" if public else "p23-observable-prediction-op0001"
    try:
        run = subprocess.run(command, text=True, capture_output=True, timeout=60)
        result = json.loads(run.stdout)
        if (run.returncode != 0 or result.get("schema") != schema or result.get("version") != version
                or result.get("status") != "verified" or result.get("evidence_valid") is not True
                or any(result.get(k) is not False for k in ("source_mapping_identified",
                           "publication_configuration_identified", "production_admitted"))):
            return {**rejected, "status": "invalid_observable_prediction_evidence",
                    "reason": result.get("reason", "verification failed")}
        # Public compatibility consumes its own contract and cannot replace the design optimum.
        result["status"] = ("verified_research_public_observable_family" if public
                            else "verified_research_source_observable_prediction")
        return result
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        return {**rejected, "status": "invalid_observable_prediction_evidence", "reason": str(error)}


def gaussian_window_investigation(*, report_dir=None, enabled=True):
    directory = HERE / "nominal-replay/gaussian-window"
    rejected = {"evidence_valid": False, "source_mapping_identified": False,
                "publication_configuration_identified": False, "production_admitted": False,
                "actual_window_model_identified": False, "compatible_member_verified": False}
    if not enabled:
        return {**rejected, "status": "disabled_by_override"}
    receipt_dir = directory if report_dir is None else Path(report_dir)
    if not (receipt_dir / "verification.json").is_file():
        return {**rejected, "status": "not_available"}
    command = [sys.executable, str(directory / "verify.py"), "--check-only"]
    if report_dir is not None:
        command.extend(("--directory", str(report_dir)))
    try:
        run = subprocess.run(command, text=True, capture_output=True, timeout=60)
        result = json.loads(run.stdout)
        if (run.returncode != 0 or result.get("schema") != "p23-gaussian-window-verification/v1"
                or result.get("version") != "p23-gaussian-window-gw0001"
                or result.get("status") != "verified" or result.get("evidence_valid") is not True
                or any(result.get(k) is not False for k in ("source_mapping_identified",
                           "publication_configuration_identified", "production_admitted",
                           "actual_window_model_identified"))):
            return {**rejected, "status": "invalid_gaussian_window_evidence",
                    "reason": result.get("reason", "verification failed")}
        # A valid negative receipt remains evidence without becoming a compatible member.
        positive = (result.get("outcome") == "EXHIBITED_FULL_FOCK_WINDOW_MEMBER"
                    and result.get("all_public_enclosures_contained") is True)
        result["compatible_member_verified"] = positive
        result["status"] = ("verified_research_full_fock_window_member" if positive
                            else "verified_research_full_fock_window_not_certified")
        return result
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        return {**rejected, "status": "invalid_gaussian_window_evidence", "reason": str(error)}


def source_readout_investigation(directory_name, schema, version, flags, *, report_dir=None,
                                enabled=True, kernel_truth=None, calibration=False):
    directory = HERE / "nominal-replay" / directory_name
    rejected = {"evidence_valid": False, **{name: False for name in flags}}
    if not enabled:
        return {**rejected, "status": "disabled_by_override"}
    receipt_dir = directory if report_dir is None else Path(report_dir)
    if not (receipt_dir / "verification.json").is_file():
        return {**rejected, "status": "not_available"}
    command = [sys.executable, str(directory / "verify.py"), "--check-only"]
    if report_dir is not None:
        command.extend(("--directory", str(report_dir)))
    try:
        run = subprocess.run(command, text=True, capture_output=True, timeout=60)
        result = json.loads(run.stdout)
        valid = (run.returncode == 0 and result.get("schema") == schema
                 and result.get("version") == version and result.get("status") == "verified"
                 and result.get("evidence_valid") is True
                 and all(result.get(name) is False for name in flags))
        if kernel_truth is not None:
            truth = result.get("kernel_claims", {})
            valid = valid and set(truth) == set(kernel_truth) and all(
                truth.get(name) is value for name, value in kernel_truth.items())
        if calibration:
            valid = (valid and result.get("actual_calibration_failure_claimed") is False
                     and result.get("no_calibration_branch_selected") is True)
        if not valid:
            return {**rejected, "status": "invalid_source_readout_evidence",
                    "reason": result.get("reason", "source readout verification failed")}
        # These source consumers record their own scope; the optimum consumes control_loop.
        result["status"] = ("verified_research_source_calibration_readout" if calibration
                            else "verified_research_source_native_fock_effects")
        return result
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        return {**rejected, "status": "invalid_source_readout_evidence", "reason": str(error)}


def native_effects_investigation(*, report_dir=None, enabled=True):
    return source_readout_investigation(
        "gaussian-window/native-effects", "p23-native-effects-verification/v1", "p23-native-effects-ge0001",
        ("source_mapping_identified", "publication_configuration_identified", "production_admitted",
         "actual_window_model_identified"), report_dir=report_dir, enabled=enabled,
        kernel_truth={"native_ports_generated": True, "native_occupation_isometry_generated": True,
                      "all_n_tensor_port_Born_identity": True, "all_n_Gamma_positive_contraction": True,
                      "native_three_paired_effects_to_source_tail": True,
                      "gaussian_vacuum_kernel_proof": False, "whole_window_Born_kernel_proof": False})


def calibration_readout_investigation(*, report_dir=None, enabled=True):
    return source_readout_investigation(
        "calibration-readout", "p23-calibration-readout-verification/v1", "p23-calibration-readout-cal0001",
        ("calibration_preparation_identified", "calibration_ports_identified", "calibration_pump_identified",
         "background_subtraction_identified", "source_mapping_identified",
         "publication_configuration_identified", "production_admitted"),
        report_dir=report_dir, enabled=enabled, calibration=True)


def structured_contrast_investigation(*, report_dir=None, enabled=True):
    flags = ("source_mapping_identified", "publication_configuration_identified",
             "production_admitted", "calibration_protocol_identified", "actual_source_failure_claimed")
    result = source_readout_investigation(
        "structured-contrast", "p23-structured-contrast-verification/v1", "p23-structured-contrast-sc0001.1",
        flags, report_dir=report_dir, enabled=enabled)
    if result.get("evidence_valid") is not True:
        return result
    if (result.get("fullBorn_source_dominance_kernel") is not True
            or result.get("kernel_closed_form_Born_identity") is not False
            or result.get("nominal_optimum_verdict_changed") is not False
            or type(result.get("all_named_mappings_rejected")) is not bool):
        return {"evidence_valid": False, **{name: False for name in flags},
                "status": "invalid_source_readout_evidence", "reason": "invalid source contrast scope"}
    result["status"] = ("verified_research_aligned_scalar_mapping_rejected"
                        if result["all_named_mappings_rejected"]
                        else "verified_research_aligned_scalar_mapping_not_rejected")
    return result


def frame_window_investigation(*, report_dir=None, enabled=True):
    flags = ("source_mapping_identified", "publication_configuration_identified", "production_admitted",
             "actual_window_model_identified", "calibration_protocol_identified", "noise_channel_identified",
             "source_pair_rate_reference_identified", "common_Jones_map_identified",
             "equal_branch_conversion_identified", "actual_pump_actuator_identified")
    result = source_readout_investigation(
        "frame-window", "p23-frame-window-verification/v1", "p23-frame-window-fw0001",
        flags, report_dir=report_dir, enabled=enabled)
    if result.get("evidence_valid") is not True:
        return result
    required = ("both_public_members_verified", "all_nine_numeric_replays_verified",
                "full_printed_five_control_gain_verified", "source_calibration_inverse_kernel")
    if (any(result.get(name) is not True for name in required)
            or result.get("global_optimum_kernel_proof") is not False
            or result.get("numeric_outcome") not in ("NUMERICAL_DEVIATION_EXCEEDS_DECLARED_BAND",
                                                    "NUMERICAL_BAND_CONTAINS_ALL_PRINTED_COMPONENTS")):
        return {"evidence_valid": False, **{name: False for name in flags},
                "status": "invalid_source_readout_evidence", "reason": "invalid frame source scope"}
    result["status"] = "verified_research_calibrated_frame_source_and_numeric_replay"
    return result


def assess(*, nominal_replay_dir=None, nominal_replay_enabled=True,
           source_code_report_dir=None, source_code_enabled=True,
           response_report_dir=None, response_enabled=True,
           collected_response_report_dir=None, collected_response_enabled=True,
           observable_prediction_report_dir=None, observable_prediction_enabled=True,
           public_observable_report_dir=None, public_observable_enabled=True,
           gaussian_window_report_dir=None, gaussian_window_enabled=True,
           native_effects_report_dir=None, native_effects_enabled=True,
           calibration_readout_report_dir=None, calibration_readout_enabled=True,
           structured_contrast_report_dir=None, structured_contrast_enabled=True,
           frame_window_report_dir=None, frame_window_enabled=True):
    instrument = json.loads((HERE / "instrument.json").read_text())
    request = json.loads((HERE / "request.json").read_text())
    registry = json.loads((HERE / "calibration-registry.json").read_text())["entries"]
    proof_path = HERE / "evidence/lean-certification.json"
    proof = json.loads(proof_path.read_text()) if proof_path.exists() else {}
    expected = {p: digest(ROOT / p) for p in (PRODUCTION, CERTIFICATION)}
    commands = proof.get("commands", [])
    proof_ok = (proof.get("status") == "passed" and proof.get("source_sha256") == expected
                and len(commands) == 3 and all(c.get("returncode") == 0 for c in commands)
                and "REAL_FAMILY_CERTIFIED" in commands[-1].get("output", ""))
    tests = subprocess.run([sys.executable, str(HERE / "test_real_family.py"), "-v"],
                           text=True, capture_output=True, timeout=60)
    loop = control_loop(instrument, nominal_replay_dir=nominal_replay_dir,
                        nominal_replay_enabled=nominal_replay_enabled)
    registered = set(registry) == REGISTRY_KEYS and all(
        row.get("responsible_role") and row.get("required_evidence") for row in registry.values())
    budget = rf.error_budget(request["error_budget"])
    protocol = all((HERE / name).is_file() for name in
                   ("protocol.md", "controller-capsule.md", "access-record.md"))
    components = {"lean_family_and_certification": proof_ok,
                  "predictor_and_synthetic_regressions": tests.returncode == 0,
                  "nominal_control_geometry": all(loop[k] for k in GEOMETRY_KEYS),
                  "no_click_and_calibration_responsibilities": bool(registered),
                  "protocol_and_budget_draft": protocol,
                  "nominal_apparatus_optimum": loop["apparatus_optimum_verified"]}
    return {"schema": "nist-real-readiness/v1", "components": components,
            "nominal_replay": loop["nominal_replay"],
            "nominal_investigation": visibility_investigation(),
            "nominal_source_code": source_code_investigation(report_dir=source_code_report_dir,
                                                            enabled=source_code_enabled),
            "nominal_response": response_investigation(report_dir=response_report_dir,
                                                       enabled=response_enabled),
            "nominal_collected_response": collected_response_investigation(
                report_dir=collected_response_report_dir, enabled=collected_response_enabled),
            "nominal_observable_prediction": observable_prediction_investigation(
                report_dir=observable_prediction_report_dir, enabled=observable_prediction_enabled),
            "public_observable_family": observable_prediction_investigation(
                report_dir=public_observable_report_dir, enabled=public_observable_enabled, public=True),
            "gaussian_window_family": gaussian_window_investigation(
                report_dir=gaussian_window_report_dir, enabled=gaussian_window_enabled),
            "source_native_fock_effects": native_effects_investigation(
                report_dir=native_effects_report_dir, enabled=native_effects_enabled),
            "source_calibration_readout": calibration_readout_investigation(
                report_dir=calibration_readout_report_dir, enabled=calibration_readout_enabled),
            "aligned_scalar_source_constraint": structured_contrast_investigation(
                report_dir=structured_contrast_report_dir, enabled=structured_contrast_enabled),
            "calibrated_frame_source_family": frame_window_investigation(
                report_dir=frame_window_report_dir, enabled=frame_window_enabled),
            "r0003_nist_ready": all(components.values()),
            "status": "ready" if all(components.values()) else "blocked_at_nominal_optimum_gate"}


def main():
    parser = argparse.ArgumentParser(
        description="Fail-closed theory-readiness assessment; exit 1 unless fully ready.")
    parser.add_argument("--reuse-lean-receipt", action="store_true",
                        help="skip fresh Lean verification and reuse evidence/lean-certification.json")
    parser.add_argument("--disable-nominal-replay", action="store_true",
                        help="explicitly keep the nominal optimum gate closed, even for a valid pass receipt")
    parser.add_argument("--disable-source-code-study", action="store_true",
                        help="explicitly disable the recovered source-code study readout")
    parser.add_argument("--disable-response-study", action="store_true",
                        help="explicitly disable the continuous conditional response readout")
    parser.add_argument("--disable-collected-response-study", action="store_true",
                        help="explicitly disable the collected-source conditional response readout")
    parser.add_argument("--disable-observable-prediction-study", action="store_true",
                        help="explicitly disable the source-generated observable prediction readout")
    parser.add_argument("--disable-public-observable-study", action="store_true",
                        help="explicitly disable the public source-family compatibility readout")
    parser.add_argument("--disable-gaussian-window-study", action="store_true",
                        help="explicitly disable the generated full-Fock window readout")
    parser.add_argument("--disable-native-effects-study", action="store_true",
                        help="explicitly disable the source-native detector-effect readout")
    parser.add_argument("--disable-calibration-readout-study", action="store_true",
                        help="explicitly disable the generated source calibration readout")
    parser.add_argument("--disable-structured-contrast-study", action="store_true",
                        help="explicitly disable the aligned source constraint readout")
    parser.add_argument("--disable-frame-window-study", action="store_true",
                        help="explicitly disable the calibrated Jones-frame source readout")
    args = parser.parse_args()
    if not args.reuse_lean_receipt:
        verify_lean()
    result = assess(nominal_replay_enabled=not args.disable_nominal_replay,
                    source_code_enabled=not args.disable_source_code_study,
                    response_enabled=not args.disable_response_study,
                    collected_response_enabled=not args.disable_collected_response_study,
                    observable_prediction_enabled=not args.disable_observable_prediction_study,
                    public_observable_enabled=not args.disable_public_observable_study,
                    gaussian_window_enabled=not args.disable_gaussian_window_study,
                    native_effects_enabled=not args.disable_native_effects_study,
                    calibration_readout_enabled=not args.disable_calibration_readout_study,
                    structured_contrast_enabled=not args.disable_structured_contrast_study,
                    frame_window_enabled=not args.disable_frame_window_study)
    (HERE / "evidence").mkdir(exist_ok=True)
    (HERE / "evidence/readiness.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    return 0 if result["r0003_nist_ready"] else 1


if __name__ == "__main__":
    sys.exit(main())
