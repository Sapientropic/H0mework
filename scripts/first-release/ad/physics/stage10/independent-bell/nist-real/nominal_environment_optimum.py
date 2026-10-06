"""Consume the named public-calibration replay; retain R3 by explicit selection."""
from __future__ import annotations

from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ENVIRONMENT = HERE / "nominal-replay/observable-closure/environment-source"
VERSION = "nominal-environment-replay-r0006"
NUMERICAL_REVISION = VERSION + ".1"
LEGACY_VERSION = "nominal-replay-r0003"
REVISIONS = (VERSION, LEGACY_VERSION)
COMPONENTS = ("r", "a0", "a1", "b0", "b1")


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def load_verifier():
    # Only receipts may come from report_dir; executable code has one repository source.
    sys.path.insert(0, str(ENVIRONMENT))
    path = ENVIRONMENT / "verify_environment_replay.py"
    spec = importlib.util.spec_from_file_location("_nist_environment_verifier", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def documented_values(instrument):
    amplitudes = instrument["preparation"]["amplitudes"]
    return (Fraction(amplitudes["VV"]) / Fraction(amplitudes["HH"]),
            *(Fraction(x) for x in instrument["controls"]["alice"]),
            *(Fraction(x) for x in instrument["controls"]["bob"]))


def consume_verified_cross(result, instrument):
    require(result["schema"] == "p23-nominal-environment-replay-verification/v1"
            and result["scientific_model_id"] == VERSION
            and result["numerical_revision"] == NUMERICAL_REVISION,
            "unregistered_environment_replay_revision")
    require(result["status"] == "verified" and result["evidence_valid"] is True,
            "uncertified_environment_replay")
    require(result["default_box_points_verified"] == 17
            and result["total_source_points_verified"] == 19,
            "incomplete_environment_source_box")
    rows = result["default_comparison"]
    require(len(rows) == 5, "incomplete_environment_comparisons")
    for row, name, value in zip(rows, COMPONENTS, documented_values(instrument)):
        lo, hi = (Fraction(row["band"][k]) for k in ("exact_lower", "exact_upper"))
        require(row["name"] == name and Fraction(row["documented"]) == value and lo <= hi,
                "environment_documented_value_or_band_mismatch")
        require(row["inside"] is (lo <= value <= hi), "environment_incorrect_inside_flag")
    passed = all(row["inside"] for row in rows)
    require(result["default_verdict"] == ("CONSISTENT" if passed else "DEVIATION")
            and result["verified"] is passed
            and result["documented_values_in_band"] == sum(row["inside"] for row in rows),
            "environment_verdict_disagrees_with_default_band")
    return passed


def assess_nominal_replay(instrument, *, report_dir=None, enabled=True, revision=VERSION):
    """Valid negative evidence closes the gate; disable never admits a source.

    The named nominal model does not require an actual run identity or new measurements.
    R3 is an explicit historical selector, never a fallback for missing R6 evidence.
    """
    base = {"verified": False, "evidence_valid": False, "production_eligible": False,
            "criterion_version": revision, "scientific_model_id": revision}
    if enabled is False:
        return {**base, "status": "disabled_by_override"}
    if enabled is not True or revision not in REVISIONS:
        return {**base, "status": "invalid_replay_selection"}
    if revision == LEGACY_VERSION:
        from nominal_optimum import assess_nominal_replay as legacy
        return legacy(instrument, report_dir=report_dir, enabled=True)
    try:
        require(instrument == json.loads((HERE / "instrument.json").read_text()),
                "target_instrument_mismatch")
        result = load_verifier().verify(report_dir=report_dir, enabled=True)
        if result.get("evidence_valid") is not True:
            return {**base, "status": "invalid_environment_replay_evidence",
                    "reason": result.get("reason", result.get("status"))}
        passed = consume_verified_cross(result, instrument)
        require(result["production_eligible"] is (report_dir is None)
                and result["synthetic_receipt_used"] is False,
                "environment_receipt_location_identity_mismatch")
        keys = ("schema", "scientific_model_id", "numerical_revision", "evidence_valid",
                "production_eligible", "default_verdict", "numeric_outcome", "criterion_freeze",
                "default_box_points_verified", "total_source_points_verified", "documented_values_in_band",
                "default_comparison", "per_model_verdicts", "bindings", "completion_lineage",
                "shared_source_setting_cell_count", "complete_N1_and_N5_outcome_windows_recomputed",
                "actual_publication_configuration_identified", "global_argmax_kernel_proof",
                "new_full_Born_or_general_Gaussian_determinant_kernel_claim", "controller_advance",
                "event_files_read")
        return {**{key: result[key] for key in keys}, "verified": passed,
                "criterion_version": VERSION, "evidence_identity": "frozen_public_nominal_environment_replay",
                "status": "certified_consistent_within_predeclared_band" if passed
                          else "certified_deviation_exceeds_predeclared_band",
                "evaluator": {"path": "nominal_environment_optimum.py",
                              "sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}}
    except (ValueError, KeyError, TypeError, IndexError, OSError, ImportError,
            subprocess.SubprocessError) as error:
        return {**base, "status": "invalid_environment_replay_evidence", "reason": str(error)}
