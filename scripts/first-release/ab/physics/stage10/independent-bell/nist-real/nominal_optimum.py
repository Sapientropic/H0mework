"""Consume the frozen nominal replay without running an optimiser or reading event data."""
from __future__ import annotations

import hashlib
import importlib.util
import json
import math
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
NOMINAL = HERE / "nominal-replay"
VERSION = "nominal-replay-r0003"
PRIMARY = "replay-r0003.json"
INDEPENDENT = "independent_replay-r0003.json"
POINT_KEYS = ("label", "eta_a", "eta_b", "pair_probability", "visibility")
OPTIMUM_KEYS = ("r", "theta0_deg", "theta1_deg", "S")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_implementation(name):
    spec = importlib.util.spec_from_file_location("_nist_" + name, NOMINAL / (name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def close(actual, expected, tolerance):
    return (isinstance(actual, (int, float)) and not isinstance(actual, bool)
            and math.isfinite(actual) and abs(actual - expected) <= tolerance)


def derived_band(points, frozen):
    band = {}
    for key in OPTIMUM_KEYS[:3]:
        width = frozen["band"]["r_widen" if key == "r" else "angle_widen_deg"]
        values = [point["optimum"][key] for point in points]
        band[key] = [min(values) - width, max(values) + width]
    return band


def band_matches(actual, expected, tolerance):
    return (set(actual) == set(expected)
            and all(len(actual[k]) == 2 and all(close(x, y, tolerance["r" if k == "r" else "angle_deg"])
                                               for x, y in zip(actual[k], expected[k])) for k in expected))


def comparisons(band, instrument):
    a, b = instrument["controls"]["alice"], instrument["controls"]["bob"]
    amplitudes = instrument["preparation"]["amplitudes"]
    r = float(amplitudes["VV"]) / float(amplitudes["HH"])
    rows = [("r", r, band["r"]),
            ("angle_theta0A_deg", float(a[0]), band["theta0_deg"]),
            ("angle_theta0B_deg", float(b[0]), [-v for v in reversed(band["theta0_deg"])]),
            ("angle_theta1A_deg", float(a[1]), band["theta1_deg"]),
            ("angle_theta1B_deg", float(b[1]), [-v for v in reversed(band["theta1_deg"])])]
    return [{"name": name, "documented": value, "band": interval,
             "inside": interval[0] <= value <= interval[1]} for name, value, interval in rows]


def validate_comparisons(actual, expected, tolerance):
    require(len(actual) == len(expected) == 5, "incomplete_documented_comparisons")
    for row, target in zip(actual, expected):
        require(row["name"] == target["name"] and row["documented"] == target["documented"],
                "documented_value_mismatch")
        require(row["inside"] is target["inside"], "incorrect_inside_flag")
        tol = tolerance["r" if row["name"] == "r" else "angle_deg"]
        require(len(row["band"]) == 2 and all(close(x, y, tol) for x, y in zip(row["band"], target["band"])),
                "comparison_band_mismatch")


def validate_points(points, expected, frozen, implementation, independent=False):
    require(len(points) == len(expected) == 17, "incomplete_input_box")
    for point, target in zip(points, expected):
        require(all(point[key] == target[key] for key in POINT_KEYS), "criterion_input_box_mismatch")
        optimum = point["optimum"]
        require(all(close(optimum[key], optimum[key], 0) for key in OPTIMUM_KEYS), "nonfinite_optimum")
        require(frozen["model"]["r_domain"][0] <= optimum["r"] <= frozen["model"]["r_domain"][1],
                "optimum_outside_r_domain")
        require(all(frozen["model"]["angle_domain_deg"][0] <= optimum[k]
                    <= frozen["model"]["angle_domain_deg"][1] for k in OPTIMUM_KEYS[1:3]),
                "optimum_outside_angle_domain")
        require(optimum["theta0_deg"] >= 0 and (optimum["theta0_deg"] != 0 or optimum["theta1_deg"] >= 0),
                "noncanonical_optimum")
        if independent:
            context = implementation.context_for(frozen, point)
            objective = implementation.objective
        else:
            context = implementation.make_context(frozen, point["eta_a"], point["eta_b"], point["pair_probability"])
            objective = implementation.s_ch
        value = objective(context, optimum["r"], optimum["theta0_deg"], optimum["theta1_deg"])
        require(close(optimum["S"], value, frozen["tolerance"]["S_abs"]), "objective_value_mismatch")


def assess_nominal_replay(instrument, *, report_dir=None, enabled=True):
    """CERTIFIED_DEVIATION is valid negative evidence, so it cannot open the gate.

    report_dir is an explicit receipt-location override for isolated synthetic controls.
    Scientific inputs and implementations always come from the frozen production directory.
    enabled=False can disable the gate; there is no force-pass override.
    """
    if not enabled:
        return {"verified": False, "evidence_valid": False, "status": "disabled_by_override"}
    directory = NOMINAL if report_dir is None else Path(report_dir)
    try:
        primary_impl = load_implementation("replay")
        independent_impl = load_implementation("independent_replay")
        frozen = primary_impl.load_frozen()
        require(frozen == independent_impl.load_frozen(), "criterion_parser_disagreement")
        require(frozen["criterion_version"] == VERSION, "criterion_revision_mismatch")
        require(instrument == json.loads((HERE / "instrument.json").read_text()), "target_instrument_mismatch")
        freeze = primary_impl.criterion_freeze()
        primary = json.loads((directory / PRIMARY).read_text())
        independent = json.loads((directory / INDEPENDENT).read_text())
        fixture = primary.get("fixture_identity") or independent.get("fixture_identity")
        if fixture is not None:
            require(primary.get("fixture_identity") == independent.get("fixture_identity") == "synthetic-only",
                    "invalid_fixture_identity")
            require(report_dir is not None, "synthetic_receipt_in_production")
        source_names = ("criterion-r0003.md", "../instrument.json", "christensen-appendix-a.txt",
                        "shalm2015-channel-inputs.txt")
        common = {name: digest(NOMINAL / name) for name in source_names}
        require(primary["bindings"] == dict(common, **{"replay.py": digest(NOMINAL / "replay.py")}),
                "primary_source_binding_mismatch")
        require(independent["bindings"] == dict(common, **{
            "independent_replay.py": digest(NOMINAL / "independent_replay.py"),
            PRIMARY: digest(directory / PRIMARY)}), "independent_source_binding_mismatch")
        for report, schema in ((primary, "nominal-apparatus-replay/v1"),
                               (independent, "independent-nominal-apparatus-replay/v1")):
            require(report["schema"] == schema and report["criterion_version"] == VERSION,
                    "replay_revision_mismatch")
            require(report["criterion_freeze"] == freeze, "criterion_freeze_mismatch")
        choices = primary["fixed_choices"]
        require(choices["F14_band"] == frozen["band"] and choices["F15_tolerance"] == frozen["tolerance"]
                and choices["F16_verdicts"] == frozen["verdicts"]
                and choices["F2_delta_deg"] == frozen["model"]["delta_deg"]
                and choices["F6_background"]["b_A_per_trial"] == frozen["channel"]["background_A_per_trial"]
                and choices["F6_background"]["b_B_per_trial"] == frozen["channel"]["background_B_per_trial"],
                "criterion_choice_mismatch")
        tolerance = frozen["tolerance"]
        require(independent["tolerance"] == tolerance, "independent_tolerance_mismatch")
        expected = independent_impl.box_points(frozen)
        validate_points(primary["box_points"], expected, frozen, primary_impl)
        validate_points(independent["box_points"], expected, frozen, independent_impl, independent=True)
        primary_band = derived_band(primary["box_points"], frozen)
        independent_band = derived_band(independent["box_points"], frozen)
        require(band_matches(primary["band"]["widened"], primary_band, tolerance), "primary_band_mismatch")
        require(band_matches(independent["recomputed"]["band_widened"], independent_band, tolerance),
                "independent_band_mismatch")
        require(band_matches(primary_band, independent_band, tolerance), "band_disagreement")
        primary_comparisons = comparisons(primary_band, instrument)
        independent_comparisons = comparisons(independent_band, instrument)
        validate_comparisons(primary["comparison"], primary_comparisons, tolerance)
        validate_comparisons(independent["recomputed"]["comparison"], independent_comparisons, tolerance)
        require([r["inside"] for r in primary_comparisons] == [r["inside"] for r in independent_comparisons],
                "comparison_disagreement")
        require(len(independent["agreement"]) == 17, "incomplete_independent_agreement")
        for p, q, agreement in zip(primary["box_points"], independent["box_points"], independent["agreement"]):
            require(all(agreement[k] == p[k] for k in POINT_KEYS), "agreement_input_mismatch")
            for key in OPTIMUM_KEYS:
                tol = tolerance["r" if key == "r" else "S_abs" if key == "S" else "angle_deg"]
                delta = abs(p["optimum"][key] - q["optimum"][key])
                require(delta <= tol and close(agreement["delta_" + key], delta, 1e-15),
                        "box_optimum_disagreement")
            require(agreement["within_tolerance"] is True, "uncertified_box_point")
        require(all(close(independent["recomputed"]["centre_optimum"][k], independent["box_points"][0]["optimum"][k], 0)
                    for k in OPTIMUM_KEYS), "independent_centre_mismatch")
        require(all(independent[k] is True for k in ("source_agreement", "input_agreement", "comparison_agreement",
                                                   "verdict_agreement")), "independent_certification_failed")
        require(independent["band_agreement"]["within_tolerance"] is True, "uncertified_band")
        passed = all(row["inside"] for row in primary_comparisons)
        verdict = frozen["verdicts"]["pass" if passed else "fail"]
        require(primary["verdict"] == verdict and independent["recomputed"]["verdict"] == verdict
                and independent["verdict"] == "CERTIFIED_" + verdict, "incorrect_or_uncertified_verdict")
        return {"verified": passed, "evidence_valid": True,
                "evidence_identity": fixture or "frozen_nominal_replay",
                "production_eligible": fixture is None and report_dir is None,
                "status": "certified_consistent_within_predeclared_band" if passed else "certified_deviation_exceeds_predeclared_band",
                "criterion_version": VERSION, "criterion_freeze": freeze,
                "primary_verdict": primary["verdict"], "independent_verdict": independent["verdict"],
                "box_points_verified": 17, "documented_values_in_band": sum(r["inside"] for r in primary_comparisons),
                "bindings": {PRIMARY: digest(directory / PRIMARY), INDEPENDENT: digest(directory / INDEPENDENT)}}
    except FileNotFoundError as error:
        return {"verified": False, "evidence_valid": False, "status": "missing_replay_evidence", "reason": error.filename}
    except (ValueError, KeyError, TypeError, IndexError, OSError, subprocess.SubprocessError) as error:
        return {"verified": False, "evidence_valid": False, "status": "invalid_replay_evidence", "reason": str(error)}
