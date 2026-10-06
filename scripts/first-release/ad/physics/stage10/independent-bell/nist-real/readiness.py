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
from nominal_environment_optimum import REVISIONS, VERSION

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


def public_statistical_fiber_investigation(*, report_dir=None, enabled=True):
    directory = HERE / "nominal-replay/observable-closure/full-statistical-fiber"
    rejected = {"evidence_valid": False, "production_eligible": False, "readout_certified": False,
                "full_training_fiber_outer_cover_verified": False,
                "nonempty_training_fiber_verified": False,
                "certified_training_fiber_readout_disagreement": False,
                "same_source_shared_phase_and_no_signaling_verified": False,
                "apparatus_optimum_verified": False}
    if not enabled:
        return {**rejected, "status": "disabled_by_override"}
    receipt = directory / "cross-verification.json" if report_dir is None else Path(report_dir) / "cross-verification.json"
    if not receipt.is_file():
        return {**rejected, "status": "not_available"}
    command = [sys.executable, str(directory / "verify_fiber.py"), "--check-only", "--certificate", str(receipt)]
    try:
        run = subprocess.run(command, text=True, capture_output=True, timeout=60)
        result = json.loads(run.stdout)
        required = ("evidence_valid", "production_eligible", "readout_certified",
                    "full_training_fiber_outer_cover_verified", "nonempty_training_fiber_verified",
                    "certified_training_fiber_readout_disagreement",
                    "same_source_shared_phase_and_no_signaling_verified")
        if (run.returncode != 0 or any(result.get(name) is not True for name in required)
                or result.get("uniform_heldout_contained") is not False
                or result.get("apparatus_optimum_verified") is not False):
            return {**rejected, "status": "invalid_public_statistical_fiber_evidence",
                    "reason": result.get("reason", "full fibre certificate verification failed")}
        # The certificate consumes the complete conditional fibre and its explicit counterexample.
        result["status"] = "verified_public_full_training_fiber_and_prediction_disagreement"
        return result
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        return {**rejected, "status": "invalid_public_statistical_fiber_evidence", "reason": str(error)}


def public_all_data_fiber_investigation(*, report_dir=None, enabled=True):
    directory = HERE / "nominal-replay/observable-closure/full-statistical-fiber"
    rejected = {"evidence_valid": False, "production_eligible": False, "readout_certified": False,
                "full_all_data_fiber_outer_cover_verified": False,
                "nonempty_all_data_fiber_verified": False,
                "same_source_shared_phase_and_no_signaling_verified": False,
                "apparatus_optimum_verified": False, "heldout_prediction_claimed": False}
    if not enabled:
        return {**rejected, "status": "disabled_by_override"}
    receipt = directory / "all-data-sign-certification.json" if report_dir is None else Path(report_dir) / "all-data-sign-certification.json"
    if not receipt.is_file():
        return {**rejected, "status": "not_available"}
    command = [sys.executable, str(directory / "all_data_signs.py"), "--check-only", "--certificate", str(receipt)]
    try:
        run = subprocess.run(command, text=True, capture_output=True, timeout=60)
        result = json.loads(run.stdout)
        required = ("evidence_valid", "production_eligible", "readout_certified",
                    "full_all_data_fiber_outer_cover_verified", "nonempty_all_data_fiber_verified",
                    "same_source_shared_phase_and_no_signaling_verified", "retrospective",
                    "complete_public_CI_fibre_opposite_CH_signs_verified",
                    "uniform_CH_N5_strictly_positive_refuted", "uniform_CH_N5_strictly_negative_refuted")
        if (run.returncode != 0 or any(result.get(name) is not True for name in required)
                or result.get("statistical_role") != "retrospective_all_public_CI_intersection"
                or any(result.get(name) is not False for name in
                       ("apparatus_optimum_verified", "heldout_prediction_claimed",
                        "old_training_uniform_prediction_counterexample_retracted"))
                or type(result.get("all_data_fibre_has_certified_source_ambiguity")) is not bool
                or result.get("uniform_CH_N5_strictly_positive") is not False
                or result.get("uniform_CH_N5_strictly_negative") is not False
                or result.get("uniform_CH_N5_sign") != "mixed_certified"):
            return {**rejected, "status": "invalid_public_all_data_fiber_evidence",
                    "reason": result.get("reason", "all-data fibre certificate verification failed")}
        result["status"] = "verified_retrospective_public_all_data_fiber_and_same_source_readouts"
        return result
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        return {**rejected, "status": "invalid_public_all_data_fiber_evidence", "reason": str(error)}


def covariance_source_realization_investigation(*, report_dir=None, enabled=True):
    directory = HERE / "nominal-replay/observable-closure/full-statistical-fiber"
    rejected = {"evidence_valid": False, "source_realization_kernel_certified": False,
                "all_legal_regular_coordinate_tuples_realizable_as_source": False,
                "five_covariance_coordinates_read_back": False,
                "source_generated_all_cells_and_N5": False, "apparatus_optimum_verified": False}
    if not enabled:
        return {**rejected, "status": "disabled_by_override"}
    receipt = (directory if report_dir is None else Path(report_dir)) / "covariance-source-certification.json"
    if not receipt.is_file():
        return {**rejected, "status": "not_available"}
    command = [sys.executable, str(directory / "covariance_source_certify.py"), "--check-only", "--certificate", str(receipt)]
    try:
        run = subprocess.run(command, text=True, capture_output=True, timeout=60)
        result = json.loads(run.stdout)
        required = ("evidence_valid", "source_realization_kernel_certified",
                    "all_legal_regular_coordinate_tuples_realizable_as_source",
                    "five_covariance_coordinates_read_back", "source_generated_all_cells_and_N5")
        if (run.returncode != 0 or result.get("schema") != "p23-covariance-source-evidence/v1"
                or any(result.get(name) is not True for name in required)
                or result.get("nominal_optimum_verified") is not False):
            return {**rejected, "status": "invalid_covariance_source_realization_evidence",
                    "reason": result.get("reason", "covariance source realization verification failed")}
        result["apparatus_optimum_verified"] = False
        result["status"] = "verified_kernel_covariance_source_generation_and_readback"
        return result
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        return {**rejected, "status": "invalid_covariance_source_realization_evidence", "reason": str(error)}


def public_experiment_review_investigation(*, report_dir=None, enabled=True):
    rejected = {"evidence_valid": False, "public_review_completed": False,
                "public_statistical_source_signature_certified": False,
                "apparatus_optimum_verified": False}
    if not enabled:
        return {**rejected, "status": "disabled_by_override"}
    directory = HERE / "nominal-replay/public-review"
    receipt = (directory if report_dir is None else Path(report_dir)) / "complete-review-final.json"
    if not receipt.is_file():
        return {**rejected, "status": "not_available"}
    command = [sys.executable, str(HERE / "public_experiment_review_compatibility.py"),
               "--check-only", "--certificate", str(receipt)]
    try:
        run = subprocess.run(command, text=True, capture_output=True, timeout=180)
        result = json.loads(run.stdout)
        if (run.returncode != 0 or result.get("schema") != "p23-complete-public-experiment-review-evidence/v1"
                or any(result.get(key) is not True for key in ("evidence_valid", "public_review_completed",
                    "public_statistical_source_signature_certified"))
                or any(result.get(key) is not False for key in ("apparatus_optimum_verified",
                    "new_external_data_dependency", "actual_hardware_identity_claimed", "original_CI_modified",
                    "hidden_cut_log_required_for_public_signature"))
                or result.get("decision") != "COMPLETED_WITH_NOMINAL_MODEL_REJECTION"):
            return {**rejected, "status": "invalid_public_experiment_review_evidence",
                    "reason": result.get("reason", "public claim review did not verify")}
        result["status"] = "completed_public_review_with_certified_nominal_model_rejection"
        return result
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        return {**rejected, "status": "invalid_public_experiment_review_evidence", "reason": str(error)}


def public_source_compression_investigation(*, report_dir=None, enabled=True):
    positive = ("public_source_domain_compressed", "joint_95_source_domain_certified",
                "joint_95_source_domain_nonempty", "joint_95_source_domain_CH_N5_positive",
                "complete_continuous_source_outer_cover_certified")
    negative = ("apparatus_optimum_verified", "original_CI_modified", "actual_hardware_identity_claimed",
                "calibration_sigma_inserted_as_CI", "global_all_mask_family_rejected",
                "new_external_data_dependency", "controller_advance", "new_stochastic_process_or_Ville_kernel")
    rejected = {"evidence_valid": False, **{name: False for name in (*positive, *negative)}}
    if enabled is False:
        return {**rejected, "status": "disabled_by_override"}
    if enabled is not True:
        return {**rejected, "status": "invalid_source_compression_selection"}
    directory = HERE / "nominal-replay/public-review/source-compression"
    receipt = (directory if report_dir is None else Path(report_dir)) / "source-compression-verification.json"
    if not receipt.is_file():
        return {**rejected, "status": "not_available"}
    # Overrides relocate certificates; the source law and executable consumer stay fixed.
    command = [sys.executable, str(directory / "verify.py"), "--check-only", "--certificate", str(receipt)]
    try:
        run = subprocess.run(command, text=True, capture_output=True, timeout=60)
        result = json.loads(run.stdout)
        if (run.returncode != 0 or result.get("schema") != "p23-public-source-compression-evidence/v1"
                or result.get("evidence_valid") is not True
                or any(result.get(name) is not True for name in positive)
                or any(result.get(name) is not False for name in negative)
                or result.get("conditional_source_law_required") is not True
                or type(result.get("spacelike_public_family_size")) is not int
                or result["spacelike_public_family_size"] != 24
                or any(type(result.get(name)) is not int or result[name] != 0
                       for name in ("bell_event_files_read", "new_science_executed_at_intake"))):
            return {**rejected, "status": "invalid_public_source_compression_evidence"}
        return result
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        return {**rejected, "status": "invalid_public_source_compression_evidence", "reason": str(error)}


def theory_blind_investigation(*, report_dir=None, enabled=True):
    positive = ("blind_by_construction_certified", "blind_theory_prediction_certified",
                "complete_Born_probability_family_certified", "same_original_source_current_next_certified",
                "uniform_XZ_Tsirelson_bound_certified", "fixed_theory_settings_saturate_Tsirelson",
                "exact_full_source_matrix_cross_certified", "exact_Qsqrt2_export_bridge_certified")
    negative = ("empirical_parameters_used", "human_outcome_unexposed_claimed",
                "real_instrument_empirical_verdict_executed", "actual_hardware_identity_claimed",
                "apparatus_optimum_verified", "controller_advance")
    counts = ("constructor_empirical_argument_count", "constructor_external_resource_count",
              "public_statistical_dependency_count", "new_public_statistical_tables_read",
              "trial_event_files_read", "new_science_executed_at_intake")
    rejected = {"evidence_valid": False, **{name: False for name in (*positive, *negative)}}
    if enabled is False:
        return {**rejected, "status": "disabled_by_override"}
    if enabled is not True:
        return {**rejected, "status": "invalid_theory_blind_selection"}
    directory = HERE.parent / "theory-blind"
    receipt = (directory if report_dir is None else Path(report_dir)) / "verification.json"
    if not receipt.is_file():
        return {**rejected, "status": "not_available"}
    # Data-independent prediction is a separate gate; it cannot admit a nominal instrument.
    command = [sys.executable, str(directory / "verify.py"), "--check-only", "--certificate", str(receipt)]
    try:
        run = subprocess.run(command, text=True, capture_output=True, timeout=90)
        result = json.loads(run.stdout)
        if (run.returncode != 0 or result.get("schema") != "stage10-theory-blind-evidence/v1"
                or result.get("status") != "certified_blind_by_construction_theory_prediction"
                or result.get("evidence_valid") is not True
                or any(result.get(name) is not True for name in positive)
                or any(result.get(name) is not False for name in negative)
                or any(type(result.get(name)) is not int or result[name] != 0 for name in counts)
                or any(type(result.get(name)) is not int or result[name] != 32
                       for name in ("raw_probability_records_checked", "aligned_probability_records_checked"))):
            return {**rejected, "status": "invalid_theory_blind_evidence"}
        return result
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        return {**rejected, "status": "invalid_theory_blind_evidence", "reason": str(error)}


def assess_theory_blind_only(*, report_dir=None, enabled=True):
    theory = theory_blind_investigation(report_dir=report_dir, enabled=enabled)
    passed = theory.get("blind_theory_prediction_certified") is True
    return {"schema": "stage10-theory-blind-readiness/v1",
            "status": "theory_blind_prediction_certified" if passed else "theory_blind_evidence_not_admitted",
            "theory_construction_gate_passed": passed, "blind_theory_prediction_certified": passed,
            "theory_blind_prediction": theory,
            "real_instrument_empirical_verdict_executed": False,
            "new_public_statistical_tables_read": 0, "trial_event_files_read": 0,
            "readiness_program_sha256": digest(Path(__file__).resolve())}


def munich_instrument_adjudication(*, report_dir=None, enabled=True):
    positive = ("public_instrument_adjudication_completed",
                "real_instrument_empirical_verdict_executed",
                "continuous_XZ_geometry_eliminated", "independent_archive_cross_certified")
    negative = ("encoding_selected_by_outcomes", "full_joint_model_certified",
                "source_theorem_changed", "actual_hardware_identity_claimed",
                "apparatus_optimum_verified", "controller_advance")
    rejected = {"evidence_valid": False, **{name: False for name in (*positive, *negative)}}
    if enabled is False:
        return {**rejected, "status": "disabled_by_override"}
    if enabled is not True:
        return {**rejected, "status": "invalid_munich_selection"}
    directory = HERE.parent / "munich"
    receipt = (directory if report_dir is None else Path(report_dir)) / "verification.json"
    if not receipt.is_file():
        return {**rejected, "status": "not_available"}
    # A completed rejection is an admitted adjudication, with its own model verdict.
    command = [sys.executable, str(directory / "verify.py"), "--check-only", "--certificate", str(receipt)]
    try:
        run = subprocess.run(command, text=True, capture_output=True, timeout=60)
        result = json.loads(run.stdout)
        if (run.returncode != 0 or result.get("schema") != "stage10-munich-adjudication-evidence/v1"
                or result.get("evidence_valid") is not True
                or any(result.get(name) is not True for name in positive)
                or any(result.get(name) is not False for name in negative)
                or result.get("verdict") not in ("rejected", "not_rejected")
                or type(result.get("run_count")) is not int or result["run_count"] != 2
                or result.get("familywise_alpha") != "1/20"
                or any(type(result.get(name)) is not int or result[name] != 0
                       for name in ("trial_event_files_read_at_intake", "new_science_executed_at_intake"))):
            return {**rejected, "status": "invalid_munich_adjudication_evidence"}
        return result
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        return {**rejected, "status": "invalid_munich_adjudication_evidence", "reason": str(error)}


def assess_munich_adjudication_only(*, report_dir=None, enabled=True):
    empirical = munich_instrument_adjudication(report_dir=report_dir, enabled=enabled)
    completed = empirical.get("public_instrument_adjudication_completed") is True
    return {"schema": "stage10-munich-adjudication-readiness/v1",
            "status": "empirical_adjudication_completed" if completed else "empirical_evidence_not_admitted",
            "public_instrument_adjudication_completed": completed,
            "real_instrument_empirical_verdict_executed": completed,
            "balanced_instrument_contract_not_rejected": completed and empirical.get("verdict") == "not_rejected",
            "public_instrument_adjudication": empirical,
            "apparatus_optimum_verified": False,
            "trial_event_files_read_at_intake": 0, "new_science_executed_at_intake": 0,
            "readiness_program_sha256": digest(Path(__file__).resolve())}


def munich_readout_domain(*, report_dir=None, enabled=True):
    positive = ("public_readout_domain_adjudication_completed", "full_joint_source_model_certified",
                "same_occurrence_source_bound", "independent_8D_Born_cross_certified",
                "all_original_prefixes_certified", "continuous_carrier_image_complete")
    negative = ("source_theorem_changed", "actual_hardware_identity_claimed",
                "apparatus_optimum_verified", "controller_advance", "human_outcome_unexposed_claimed")
    rejected = {"evidence_valid": False, **{name: False for name in (*positive, *negative)}}
    if enabled is False:
        return {**rejected, "status": "disabled_by_override"}
    if enabled is not True:
        return {**rejected, "status": "invalid_readout_selection"}
    directory = HERE.parent / "munich/readout-domain"
    receipt = (directory if report_dir is None else Path(report_dir)) / "verification.json"
    if not receipt.is_file():
        return {**rejected, "status": "not_available"}
    command = [sys.executable, str(directory / "verify.py"), "--check-only", "--certificate", str(receipt)]
    try:
        run = subprocess.run(command, text=True, capture_output=True, timeout=60)
        result = json.loads(run.stdout)
        if (run.returncode != 0 or result.get("schema") != "stage10-munich-readout-domain-evidence/v1"
                or result.get("evidence_valid") is not True
                or any(result.get(name) is not True for name in positive)
                or any(result.get(name) is not False for name in negative)
                or result.get("verdict") != "source_confidence_domain_nonempty"
                or type(result.get("run_count")) is not int or result["run_count"] != 2
                or type(result.get("pair_records_scored")) is not int or result["pair_records_scored"] != 20403
                or result.get("familywise_alpha") != "1/20"
                or result.get("conditional_selected_fixed_run_source_contract_required") is not True
                or result.get("original_zero_error_face_rejected") is not True
                or any(type(result.get(name)) is not int or result[name] != 0
                       for name in ("trial_event_files_read_at_intake", "new_science_executed_at_intake"))):
            return {**rejected, "status": "invalid_munich_readout_evidence"}
        return result
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        return {**rejected, "status": "invalid_munich_readout_evidence", "reason": str(error)}


def assess_munich_readout_only(*, report_dir=None, enabled=True):
    empirical = munich_readout_domain(report_dir=report_dir, enabled=enabled)
    completed = empirical.get("public_readout_domain_adjudication_completed") is True
    return {"schema": "stage10-munich-readout-readiness/v1",
            "status": "complete_joint_source_contract_compatible" if completed else "empirical_evidence_not_admitted",
            "public_readout_domain_adjudication_completed": completed,
            "full_joint_source_model_certified": completed,
            "joint_confidence_domain_nonempty": completed,
            "public_readout_domain": empirical, "apparatus_optimum_verified": False,
            "trial_event_files_read_at_intake": 0, "new_science_executed_at_intake": 0,
            "readiness_program_sha256": digest(Path(__file__).resolve())}


def munich_parameter_identification(*, report_dir=None, enabled=True):
    positive = ("parameter_identification_completed", "maximal_observable_quotient_certified",
                "registered_regular_law_fibers_complete", "continuous_equivalent_hardware_certified",
                "parent_confidence_bias_envelopes_certified", "isotropic_nonuniqueness_preserves_axes",
                "parent_joint_adjudication_preserved")
    negative = ("hardware_parameter_uniqueness_certified", "new_confidence_budget_spent",
                "controller_advance", "actual_hardware_identity_claimed")
    rejected = {"evidence_valid": False, **{name: False for name in (*positive, *negative)}}
    if enabled is False:
        return {**rejected, "status": "disabled_by_override"}
    if enabled is not True:
        return {**rejected, "status": "invalid_identification_selection"}
    directory = HERE.parent / "munich/readout-domain"
    receipt = (directory if report_dir is None else Path(report_dir)) / "identification-verification.json"
    if not receipt.is_file():
        return {**rejected, "status": "not_available"}
    command = [sys.executable, str(directory / "identify_verify.py"), "--check-only", "--certificate", str(receipt)]
    try:
        run = subprocess.run(command, text=True, capture_output=True, timeout=60)
        result = json.loads(run.stdout)
        if (run.returncode != 0 or result.get("schema") != "stage10-munich-readout-identification-evidence/v1"
                or result.get("evidence_valid") is not True
                or any(result.get(name) is not True for name in positive)
                or any(result.get(name) is not False for name in negative)
                or result.get("parent_confidence_budget") != "1/20"
                or len(result.get("runs", [])) != 2
                or any(type(result.get(name)) is not int or result[name] != 0
                       for name in ("trial_event_files_read_at_intake", "new_science_executed_at_intake"))):
            return {**rejected, "status": "invalid_identification_evidence"}
        return result
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        return {**rejected, "status": "invalid_identification_evidence", "reason": str(error)}


def assess_munich_identification_only(*, report_dir=None, enabled=True):
    result = munich_parameter_identification(report_dir=report_dir, enabled=enabled)
    return {"schema": "stage10-munich-identification-readiness/v1",
            "status": "parameter_identification_completed" if result.get("evidence_valid") is True else "evidence_not_admitted",
            "parameter_identification_completed": result.get("parameter_identification_completed") is True,
            "public_parameter_identification": result, "hardware_parameter_uniqueness_certified": False,
            "trial_event_files_read_at_intake": 0, "new_science_executed_at_intake": 0,
            "readiness_program_sha256": digest(Path(__file__).resolve())}


def munich_hardware_fiber_ranges(*, report_dir=None, enabled=True):
    positive = ("complete_fixed_law_hardware_ranges_certified", "uniform_continuous_fiber_bounds_certified",
                "near_attainable_extrema_certified", "parent_joint_adjudication_preserved")
    negative = ("hardware_parameter_uniqueness_certified", "whole_empirical_confidence_set_bounds",
                "new_confidence_budget_spent", "controller_advance")
    rejected = {"evidence_valid": False, **{name: False for name in (*positive, *negative)}}
    if enabled is False:
        return {**rejected, "status": "disabled_by_override"}
    if enabled is not True:
        return {**rejected, "status": "invalid_fiber_selection"}
    directory = HERE.parent / "munich/readout-domain"
    receipt = (directory if report_dir is None else Path(report_dir)) / "fiber-verification.json"
    if not receipt.is_file():
        return {**rejected, "status": "not_available"}
    command = [sys.executable, str(directory / "fiber_verify.py"), "--check-only", "--certificate", str(receipt)]
    try:
        run = subprocess.run(command, text=True, capture_output=True, timeout=60)
        result = json.loads(run.stdout)
        if (run.returncode != 0 or result.get("schema") != "stage10-munich-readout-fiber-evidence/v1"
                or result.get("evidence_valid") is not True
                or any(result.get(name) is not True for name in positive)
                or any(result.get(name) is not False for name in negative)
                or result.get("gain_squared_optimality_gap") != "1/100000000"
                or result.get("endpoints_checked") != 16 or result.get("hardware_ranges_checked") != 8
                or any(type(result.get(name)) is not int or result[name] != 0
                       for name in ("trial_event_files_read_at_intake", "new_science_executed_at_intake"))):
            return {**rejected, "status": "invalid_fiber_evidence"}
        return result
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        return {**rejected, "status": "invalid_fiber_evidence", "reason": str(error)}


def assess_munich_fiber_only(*, report_dir=None, enabled=True):
    result = munich_hardware_fiber_ranges(report_dir=report_dir, enabled=enabled)
    return {"schema": "stage10-munich-fiber-readiness/v1",
            "status": "complete_fixed_law_hardware_ranges_certified" if result.get("evidence_valid") is True else "evidence_not_admitted",
            "complete_fixed_law_hardware_ranges_certified": result.get("complete_fixed_law_hardware_ranges_certified") is True,
            "public_hardware_fiber_ranges": result, "hardware_parameter_uniqueness_certified": False,
            "whole_empirical_confidence_set_bounds": False, "trial_event_files_read_at_intake": 0,
            "new_science_executed_at_intake": 0, "readiness_program_sha256": digest(Path(__file__).resolve())}


def munich_response_confidence(*, report_dir=None, enabled=True):
    positive = ("parent_confidence_hardware_envelopes_certified", "simultaneous_necessary_outer_projections",
                "whole_empirical_confidence_set_bounds", "parent_joint_adjudication_preserved")
    negative = ("hardware_parameter_uniqueness_certified", "fixed_law_point_used_as_confidence_bound",
                "new_confidence_budget_spent", "controller_advance")
    rejected = {"evidence_valid": False, **{name: False for name in (*positive, *negative)}}
    if enabled is False:
        return {**rejected, "status": "disabled_by_override"}
    if enabled is not True:
        return {**rejected, "status": "invalid_response_projection_selection"}
    directory = HERE.parent / "munich/readout-domain"
    receipt = (directory if report_dir is None else Path(report_dir)) / "response-projection-verification.json"
    if not receipt.is_file():
        return {**rejected, "status": "not_available"}
    command = [sys.executable, str(directory / "response_projection_verify.py"), "--check-only", "--certificate", str(receipt)]
    try:
        run = subprocess.run(command, text=True, capture_output=True, timeout=60)
        result = json.loads(run.stdout)
        if (run.returncode != 0 or result.get("schema") != "stage10-munich-readout-response-projection-evidence/v1"
                or result.get("evidence_valid") is not True
                or any(result.get(name) is not True for name in positive)
                or any(result.get(name) is not False for name in negative)
                or result.get("parent_confidence_budget") != "1/20"
                or result.get("correlation_envelopes_checked") != 16 or result.get("response_envelopes_checked") != 8
                or any(type(result.get(name)) is not int or result[name] != 0
                       for name in ("trial_event_files_read_at_intake", "new_science_executed_at_intake"))):
            return {**rejected, "status": "invalid_response_projection_evidence"}
        return result
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        return {**rejected, "status": "invalid_response_projection_evidence", "reason": str(error)}


def assess_munich_response_projection_only(*, report_dir=None, enabled=True):
    result = munich_response_confidence(report_dir=report_dir, enabled=enabled)
    return {"schema": "stage10-munich-response-projection-readiness/v1",
            "status": "parent_confidence_hardware_envelopes_certified" if result.get("evidence_valid") is True else "evidence_not_admitted",
            "parent_confidence_hardware_envelopes_certified": result.get("parent_confidence_hardware_envelopes_certified") is True,
            "public_response_confidence_envelopes": result, "hardware_parameter_uniqueness_certified": False,
            "trial_event_files_read_at_intake": 0, "new_science_executed_at_intake": 0,
            "readiness_program_sha256": digest(Path(__file__).resolve())}


def munich_shared_response(*, report_dir=None, enabled=True):
    positive = ("shared_response_profile_certified", "parent_confidence_hardware_envelopes_certified",
                "whole_empirical_confidence_set_bounds", "parent_joint_adjudication_preserved",
                "old_cp0001_envelopes_preserved_or_tightened")
    negative = ("hardware_parameter_uniqueness_certified", "fixed_law_point_used_as_confidence_bound",
                "actual_gain_extremum_sharpness_claimed", "new_confidence_budget_spent", "controller_advance")
    rejected = {"evidence_valid": False, **{name: False for name in (*positive, *negative)}}
    if enabled is False:
        return {**rejected, "status": "disabled_by_override"}
    if enabled is not True:
        return {**rejected, "status": "invalid_shared_response_selection"}
    directory = HERE.parent / "munich/readout-domain"
    receipt = (directory if report_dir is None else Path(report_dir)) / "shared-response-verification.json"
    if not receipt.is_file():
        return {**rejected, "status": "not_available"}
    command = [sys.executable, str(directory / "shared_response_verify.py"), "--check-only", "--certificate", str(receipt)]
    try:
        # Shared intake consumes the frozen prior gate before checking its added bounds.
        run = subprocess.run(command, text=True, capture_output=True, timeout=120)
        result = json.loads(run.stdout)
        if (run.returncode != 0 or result.get("schema") != "stage10-munich-shared-response-evidence/v1"
                or result.get("evidence_valid") is not True
                or any(result.get(name) is not True for name in positive)
                or any(result.get(name) is not False for name in negative)
                or result.get("parent_confidence_budget") != "1/20"
                or result.get("shared_response_envelopes_checked") != 8
                or result.get("shared_response_endpoints_checked") != 16
                or result.get("context_likelihood_checks") != 64
                or any(type(result.get(name)) is not int or result[name] != 0
                       for name in ("trial_event_files_read_at_intake", "new_science_executed_at_intake"))):
            return {**rejected, "status": "invalid_shared_response_evidence"}
        return result
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        return {**rejected, "status": "invalid_shared_response_evidence", "reason": str(error)}


def assess_munich_shared_response_only(*, report_dir=None, enabled=True):
    result = munich_shared_response(report_dir=report_dir, enabled=enabled)
    return {"schema": "stage10-munich-shared-response-readiness/v1",
            "status": "shared_response_profile_certified" if result.get("evidence_valid") is True else "evidence_not_admitted",
            "shared_response_profile_certified": result.get("shared_response_profile_certified") is True,
            "public_shared_response_bounds": result, "hardware_parameter_uniqueness_certified": False,
            "trial_event_files_read_at_intake": 0, "new_science_executed_at_intake": 0,
            "readiness_program_sha256": digest(Path(__file__).resolve())}


def assess(*, nominal_replay_dir=None, nominal_replay_enabled=True,
           nominal_replay_revision=VERSION,
           source_code_report_dir=None, source_code_enabled=True,
           response_report_dir=None, response_enabled=True,
           collected_response_report_dir=None, collected_response_enabled=True,
           observable_prediction_report_dir=None, observable_prediction_enabled=True,
           public_observable_report_dir=None, public_observable_enabled=True,
           gaussian_window_report_dir=None, gaussian_window_enabled=True,
           native_effects_report_dir=None, native_effects_enabled=True,
           calibration_readout_report_dir=None, calibration_readout_enabled=True,
           structured_contrast_report_dir=None, structured_contrast_enabled=True,
           frame_window_report_dir=None, frame_window_enabled=True,
           public_statistical_fiber_report_dir=None, public_statistical_fiber_enabled=True,
           public_all_data_fiber_report_dir=None, public_all_data_fiber_enabled=True,
           covariance_source_realization_report_dir=None, covariance_source_realization_enabled=True,
           public_experiment_review_report_dir=None, public_experiment_review_enabled=True,
           public_source_compression_report_dir=None, public_source_compression_enabled=True,
           theory_blind_report_dir=None, theory_blind_enabled=True,
           munich_adjudication_report_dir=None, munich_adjudication_enabled=True,
           munich_readout_report_dir=None, munich_readout_enabled=True,
           munich_identification_report_dir=None, munich_identification_enabled=True,
           munich_fiber_report_dir=None, munich_fiber_enabled=True,
           munich_response_projection_report_dir=None, munich_response_projection_enabled=True,
           munich_shared_response_report_dir=None, munich_shared_response_enabled=True):
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
                        nominal_replay_enabled=nominal_replay_enabled,
                        nominal_replay_revision=nominal_replay_revision)
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
    full_training = public_statistical_fiber_investigation(
        report_dir=public_statistical_fiber_report_dir, enabled=public_statistical_fiber_enabled)
    all_data = public_all_data_fiber_investigation(
        report_dir=public_all_data_fiber_report_dir, enabled=public_all_data_fiber_enabled)
    source_realization = covariance_source_realization_investigation(
        report_dir=covariance_source_realization_report_dir, enabled=covariance_source_realization_enabled)
    public_review = public_experiment_review_investigation(
        report_dir=public_experiment_review_report_dir, enabled=public_experiment_review_enabled)
    compressed = public_source_compression_investigation(
        report_dir=public_source_compression_report_dir, enabled=public_source_compression_enabled)
    blind = theory_blind_investigation(report_dir=theory_blind_report_dir, enabled=theory_blind_enabled)
    empirical = munich_instrument_adjudication(report_dir=munich_adjudication_report_dir,
                                              enabled=munich_adjudication_enabled)
    readout = munich_readout_domain(report_dir=munich_readout_report_dir, enabled=munich_readout_enabled)
    identification = munich_parameter_identification(report_dir=munich_identification_report_dir,
                                                     enabled=munich_identification_enabled)
    fiber = munich_hardware_fiber_ranges(report_dir=munich_fiber_report_dir, enabled=munich_fiber_enabled)
    response_confidence = munich_response_confidence(report_dir=munich_response_projection_report_dir,
                                                    enabled=munich_response_projection_enabled)
    shared_response = munich_shared_response(report_dir=munich_shared_response_report_dir,
                                             enabled=munich_shared_response_enabled)
    reviewed_deviation = (public_review.get("public_review_completed") is True
                         and loop["nominal_replay"].get("evidence_valid") is True
                         and loop["nominal_replay"].get("status") == "certified_deviation_exceeds_predeclared_band")
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
            "public_statistical_fiber": full_training,
            "public_all_data_statistical_fiber": all_data,
            "covariance_source_realization": source_realization,
            "public_experiment_review": public_review,
            "public_source_compression": compressed,
            "theory_blind_prediction": blind,
            "public_instrument_adjudication": empirical,
            "public_readout_domain": readout,
            "public_parameter_identification": identification,
            "public_hardware_fiber_ranges": fiber,
            "public_response_confidence_envelopes": response_confidence,
            "public_shared_response_bounds": shared_response,
            "full_joint_source_model_certified": readout.get("full_joint_source_model_certified") is True,
            "public_instrument_adjudication_completed": empirical.get("public_instrument_adjudication_completed") is True,
            "blind_theory_prediction_certified": blind.get("blind_theory_prediction_certified") is True,
            "public_source_domain_compressed": compressed.get("public_source_domain_compressed") is True,
            "joint_95_source_domain_nonempty": compressed.get("joint_95_source_domain_nonempty") is True,
            "joint_95_source_domain_CH_N5_positive": compressed.get("joint_95_source_domain_CH_N5_positive") is True,
            "public_review_completed": public_review.get("public_review_completed") is True,
            "public_statistical_source_signature_certified": public_review.get("public_statistical_source_signature_certified") is True,
            "conditional_public_source_fiber_certified": all(value.get("evidence_valid") is True
                for value in (full_training, all_data, source_realization)),
            "r0003_nist_ready": all(components.values()),
            "status": "ready" if all(components.values()) else
                      "review_completed_with_nominal_deviation" if reviewed_deviation else "blocked_at_nominal_optimum_gate"}


def main():
    parser = argparse.ArgumentParser(
        description="Fail-closed theory-readiness assessment; exit 1 unless fully ready.")
    parser.add_argument("--reuse-lean-receipt", action="store_true",
                        help="skip fresh Lean verification and reuse evidence/lean-certification.json")
    parser.add_argument("--disable-nominal-replay", action="store_true",
                        help="explicitly keep the nominal optimum gate closed, even for a valid pass receipt")
    parser.add_argument("--nominal-replay-revision", choices=REVISIONS, default=VERSION,
                        help="named replay evaluator; historical R3 requires explicit selection")
    parser.add_argument("--nominal-replay-dir", type=Path,
                        help="receipt-location override; scientific code and criteria remain fixed")
    parser.add_argument("--output", type=Path,
                        help="new readiness receipt path; existing receipts are preserved")
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
    parser.add_argument("--disable-public-statistical-fiber-study", action="store_true",
                        help="explicitly disable the complete public training-fibre certificate")
    parser.add_argument("--public-statistical-fiber-dir", type=Path,
                        help="certificate-location override; source laws and verification code remain fixed")
    parser.add_argument("--disable-public-all-data-fiber-study", action="store_true",
                        help="explicitly disable the retrospective complete public-CI fibre certificate")
    parser.add_argument("--public-all-data-fiber-dir", type=Path,
                        help="all-data certificate-location override; science and verification code remain fixed")
    parser.add_argument("--disable-covariance-source-realization-study", action="store_true",
                        help="explicitly disable the kernel raw-coordinate source generation certificate")
    parser.add_argument("--covariance-source-realization-dir", type=Path,
                        help="source certificate-location override; Lean candidate and audit remain fixed")
    parser.add_argument("--disable-public-experiment-review", action="store_true",
                        help="explicitly disable the completed public experiment claim review")
    parser.add_argument("--public-experiment-review-dir", type=Path,
                        help="public review certificate-location override; all source laws and programs remain fixed")
    parser.add_argument("--disable-public-source-compression", action="store_true",
                        help="explicitly disable the joint 95-percent public source-domain certificate")
    parser.add_argument("--public-source-compression-dir", type=Path,
                        help="source compression certificate-location override; source laws and consumer stay fixed")
    parser.add_argument("--theory-blind-only", action="store_true",
                        help="consume only the theory-only prediction; no statistical or instrument inputs")
    parser.add_argument("--disable-theory-blind-study", action="store_true",
                        help="explicitly disable the data-independent theoretical prediction gate")
    parser.add_argument("--theory-blind-dir", type=Path,
                        help="theory certificate-location override; constructor and source remain fixed")
    parser.add_argument("--munich-adjudication-only", action="store_true",
                        help="consume only the frozen Munich empirical adjudication; no event replay")
    parser.add_argument("--disable-munich-adjudication", action="store_true",
                        help="explicitly disable the public Munich instrument adjudication")
    parser.add_argument("--munich-adjudication-dir", type=Path,
                        help="Munich certificate-location override; model and consumer remain fixed")
    parser.add_argument("--munich-readout-only", action="store_true",
                        help="consume the complete joint readout domain and both frozen prefix checks")
    parser.add_argument("--disable-munich-readout", action="store_true",
                        help="explicitly disable the complete Munich joint-domain assessment")
    parser.add_argument("--munich-readout-dir", type=Path,
                        help="joint-domain certificate-location override; source and consumer remain fixed")
    parser.add_argument("--munich-identification-only", action="store_true",
                        help="consume maximal observables, complete regular fibers and confidence projections")
    parser.add_argument("--disable-munich-identification", action="store_true",
                        help="explicitly disable the parameter-identification assessment")
    parser.add_argument("--munich-identification-dir", type=Path,
                        help="identification certificate-location override; source and consumer remain fixed")
    parser.add_argument("--munich-fiber-only", action="store_true",
                        help="consume complete generated-law hardware ranges without optimization")
    parser.add_argument("--disable-munich-fiber", action="store_true",
                        help="explicitly disable the fixed-law hardware-range assessment")
    parser.add_argument("--munich-fiber-dir", type=Path,
                        help="hardware-range certificate-location override; source and consumer remain fixed")
    parser.add_argument("--munich-response-projection-only", action="store_true",
                        help="consume response parameter envelopes of the entire original confidence set")
    parser.add_argument("--disable-munich-response-projection", action="store_true",
                        help="explicitly disable the entire-CS response parameter assessment")
    parser.add_argument("--munich-response-projection-dir", type=Path,
                        help="response projection certificate-location override; source and consumer remain fixed")
    parser.add_argument("--munich-shared-response-only", action="store_true",
                        help="consume four-context shared-response confidence bounds without generation")
    parser.add_argument("--disable-munich-shared-response", action="store_true",
                        help="explicitly disable the shared-response confidence assessment")
    parser.add_argument("--munich-shared-response-dir", type=Path,
                        help="shared-response receipt-location override; source and consumer remain fixed")
    args = parser.parse_args()
    if sum((args.theory_blind_only, args.munich_adjudication_only, args.munich_readout_only,
            args.munich_identification_only, args.munich_fiber_only, args.munich_response_projection_only,
            args.munich_shared_response_only)) > 1:
        parser.error("select exactly one dedicated assessment")
    if args.output is None:
        args.output = HERE / ("evidence/readiness-munich-shared-response-cp0002.json" if args.munich_shared_response_only else
                              "evidence/readiness-munich-response-projection-cp0001.json" if args.munich_response_projection_only else
                              "evidence/readiness-munich-fiber-fb0001.json" if args.munich_fiber_only else
                              "evidence/readiness-munich-identification-id0001.json" if args.munich_identification_only else
                              "evidence/readiness-munich-readout-rd0001.json" if args.munich_readout_only else
                              "evidence/readiness-munich-mu0001.1.json" if args.munich_adjudication_only else
                              "evidence/readiness-theory-blind-tb0001.json" if args.theory_blind_only else
                              "evidence/readiness-source-compression-sc0001.1.json")
    if args.output.exists():
        parser.error("existing_readiness_receipt: choose a new --output path")
    if args.munich_shared_response_only:
        result = assess_munich_shared_response_only(report_dir=args.munich_shared_response_dir,
                                                   enabled=not args.disable_munich_shared_response)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x", encoding="utf-8") as output:
            json.dump(result, output, indent=2)
            output.write("\n")
        print(json.dumps(result, indent=2))
        return 0 if result["shared_response_profile_certified"] else 1
    if args.munich_response_projection_only:
        result = assess_munich_response_projection_only(report_dir=args.munich_response_projection_dir,
                                                       enabled=not args.disable_munich_response_projection)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x", encoding="utf-8") as output:
            json.dump(result, output, indent=2)
            output.write("\n")
        print(json.dumps(result, indent=2))
        return 0 if result["parent_confidence_hardware_envelopes_certified"] else 1
    if args.munich_fiber_only:
        result = assess_munich_fiber_only(report_dir=args.munich_fiber_dir, enabled=not args.disable_munich_fiber)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x", encoding="utf-8") as output:
            json.dump(result, output, indent=2)
            output.write("\n")
        print(json.dumps(result, indent=2))
        return 0 if result["complete_fixed_law_hardware_ranges_certified"] else 1
    if args.munich_identification_only:
        result = assess_munich_identification_only(report_dir=args.munich_identification_dir,
                                                  enabled=not args.disable_munich_identification)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x", encoding="utf-8") as output:
            json.dump(result, output, indent=2)
            output.write("\n")
        print(json.dumps(result, indent=2))
        return 0 if result["parameter_identification_completed"] else 1
    if args.munich_readout_only:
        result = assess_munich_readout_only(report_dir=args.munich_readout_dir,
                                          enabled=not args.disable_munich_readout)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x", encoding="utf-8") as output:
            json.dump(result, output, indent=2)
            output.write("\n")
        print(json.dumps(result, indent=2))
        return 0 if result["public_readout_domain_adjudication_completed"] else 1
    if args.munich_adjudication_only:
        result = assess_munich_adjudication_only(report_dir=args.munich_adjudication_dir,
                                               enabled=not args.disable_munich_adjudication)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x", encoding="utf-8") as output:
            json.dump(result, output, indent=2)
            output.write("\n")
        print(json.dumps(result, indent=2))
        return 0 if result["public_instrument_adjudication_completed"] else 1
    if args.theory_blind_only:
        result = assess_theory_blind_only(report_dir=args.theory_blind_dir,
                                         enabled=not args.disable_theory_blind_study)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x", encoding="utf-8") as output:
            json.dump(result, output, indent=2)
            output.write("\n")
        print(json.dumps(result, indent=2))
        return 0 if result["theory_construction_gate_passed"] else 1
    if not args.reuse_lean_receipt:
        verify_lean()
    result = assess(nominal_replay_enabled=not args.disable_nominal_replay,
                    nominal_replay_revision=args.nominal_replay_revision,
                    nominal_replay_dir=args.nominal_replay_dir,
                    source_code_enabled=not args.disable_source_code_study,
                    response_enabled=not args.disable_response_study,
                    collected_response_enabled=not args.disable_collected_response_study,
                    observable_prediction_enabled=not args.disable_observable_prediction_study,
                    public_observable_enabled=not args.disable_public_observable_study,
                    gaussian_window_enabled=not args.disable_gaussian_window_study,
                    native_effects_enabled=not args.disable_native_effects_study,
                    calibration_readout_enabled=not args.disable_calibration_readout_study,
                    structured_contrast_enabled=not args.disable_structured_contrast_study,
                    frame_window_enabled=not args.disable_frame_window_study,
                    public_statistical_fiber_enabled=not args.disable_public_statistical_fiber_study,
                    public_statistical_fiber_report_dir=args.public_statistical_fiber_dir,
                    public_all_data_fiber_enabled=not args.disable_public_all_data_fiber_study,
                    public_all_data_fiber_report_dir=args.public_all_data_fiber_dir,
                    covariance_source_realization_enabled=not args.disable_covariance_source_realization_study,
                    covariance_source_realization_report_dir=args.covariance_source_realization_dir,
                    public_experiment_review_enabled=not args.disable_public_experiment_review,
                    public_experiment_review_report_dir=args.public_experiment_review_dir,
                    public_source_compression_enabled=not args.disable_public_source_compression,
                    public_source_compression_report_dir=args.public_source_compression_dir,
                    theory_blind_enabled=not args.disable_theory_blind_study,
                    theory_blind_report_dir=args.theory_blind_dir,
                    munich_adjudication_enabled=not args.disable_munich_adjudication,
                    munich_adjudication_report_dir=args.munich_adjudication_dir,
                    munich_readout_enabled=not args.disable_munich_readout,
                    munich_readout_report_dir=args.munich_readout_dir,
                    munich_identification_enabled=not args.disable_munich_identification,
                    munich_identification_report_dir=args.munich_identification_dir,
                    munich_fiber_enabled=not args.disable_munich_fiber,
                    munich_fiber_report_dir=args.munich_fiber_dir,
                    munich_response_projection_enabled=not args.disable_munich_response_projection,
                    munich_response_projection_report_dir=args.munich_response_projection_dir,
                    munich_shared_response_enabled=not args.disable_munich_shared_response,
                    munich_shared_response_report_dir=args.munich_shared_response_dir)
    (HERE / "evidence").mkdir(exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    return 0 if result["r0003_nist_ready"] else 1


if __name__ == "__main__":
    sys.exit(main())
