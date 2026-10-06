#!/usr/bin/env python3
"""Validate the frozen source-code studies without rerunning their searches."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import itertools
import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
COMPONENTS = ("r_one_pair", "a0_deg", "a1_deg", "b0_deg", "b1_deg")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def implementation():
    spec = importlib.util.spec_from_file_location("p23_source_code_primary", HERE / "replay.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def expected_points(study):
    historical = study["author_defaults"]
    points = [{"case": "author_defaults", "point_id": "author_defaults:center",
               "eta_A": historical["eta_A"], "eta_B": historical["eta_B"],
               "background_A": historical["darks_A_per_second"] * historical["coincidence_window_seconds"],
               "background_B": historical["darks_B_per_second"] * historical["coincidence_window_seconds"],
               "epsilon_squared": historical["balanced_HH_coincidences_per_second"] /
                   (historical["eta_A"] * historical["eta_B"] * historical["rep_rate_per_second"]),
               "pair_scale": None}]
    publication = study["published"]
    central = (publication["eta_A"]["center"], publication["eta_B"]["center"],
               publication["pair_scale"]["center"])
    axes = [(publication[side]["center"] - publication[side]["half_width"],
             publication[side]["center"] + publication[side]["half_width"])
            for side in ("eta_A", "eta_B")]
    axes.append((publication["pair_scale"]["box_low"], publication["pair_scale"]["box_high"]))
    for case in study["cases"][1:]:
        selections = [("center", central)] + [
            ("corner_" + "".join(map(str, bits)), tuple(axes[i][bit] for i, bit in enumerate(bits)))
            for bits in itertools.product((0, 1), repeat=3)]
        for name, (eta_a, eta_b, strength) in selections:
            points.append({"case": case, "point_id": case + ":" + name,
                           "eta_A": eta_a, "eta_B": eta_b,
                           "background_A": publication["background_A_per_trial"],
                           "background_B": publication["background_B_per_trial"],
                           "epsilon_squared": strength / 2 if case == "published_gain_half" else strength,
                           "pair_scale": strength})
    return points


def normalized_bindings(bindings):
    answer = {}
    for name, value in bindings.items():
        base = ROOT if name.startswith("Verification/") else HERE
        try:
            path = (base / name).resolve().relative_to(ROOT)
        except (ValueError, TypeError):
            raise ValueError("invalid_binding_path") from None
        require(str(path) not in answer, "duplicate_binding_path")
        answer[str(path)] = value
    return answer


def bindings_for(names):
    return {str((HERE / name).resolve().relative_to(ROOT)): digest(HERE / name) for name in names}


def case_band(rows, study):
    return {key: [min(row["optimum"][key] for row in rows) -
                  study["band"]["r_widen" if key == "r_one_pair" else "angle_widen_deg"],
                  max(row["optimum"][key] for row in rows) +
                  study["band"]["r_widen" if key == "r_one_pair" else "angle_widen_deg"]]
            for key in COMPONENTS}


def documented_values():
    instrument = json.loads((HERE / "../../instrument.json").read_text())
    preparation = instrument["preparation"]["amplitudes"]
    angles = instrument["controls"]
    return dict(zip(COMPONENTS, (float(preparation["VV"]) / float(preparation["HH"]),
                                *(float(v) for v in angles["alice"]),
                                *(float(v) for v in angles["bob"]))))


def assess(directory=None):
    directory = HERE if directory is None else Path(directory)
    primary = implementation()
    study = primary.load_frozen()
    freeze = primary.criterion_freeze()
    require(study["source"] == {"N": 4, "relative_phase_rad": 0.0, "detector_noise": "additive"},
            "incorrect_source_operator_contract")
    points = expected_points(study)
    require(len(points) == 19 and points == primary.input_points(study), "input_inventory_disagreement")
    reports = [json.loads((directory / name).read_text())
               for name in ("replay.json", "independent_replay.json")]
    documents = documented_values()
    tolerance = study["tolerance"]
    schemas = ("nist-source-code-replay/v1", "nist-source-code-independent/v1")
    summaries = []
    for index, report in enumerate(reports):
        require(report["schema"] == schemas[index] and report["criterion_version"] == study["criterion_version"],
                "incorrect_study_identity")
        require(report["criterion_freeze"] == freeze, "incorrect_criterion_freeze")
        require(report["model_source_identified"] is True and
                report["publication_configuration_identified"] is False and
                report["production_admitted"] is False, "unbound_configuration_cannot_be_admitted")
        names = ["criterion.md", "independent_replay.py" if index else "replay.py"] + study["input_sources"]
        expected = bindings_for(names)
        if index:
            expected[str((HERE / "replay.json").relative_to(ROOT))] = digest(directory / "replay.json")
        require(normalized_bindings(report["bindings"]) == expected, "source_binding_mismatch")
        require(len(report["results"]) == 19, "incomplete_input_inventory")
        for row, point in zip(report["results"], points):
            require(row["case"] == point["case"] and row["point"] == point, "source_input_identity_mismatch")
            optimum = row["optimum"]
            for key in (*COMPONENTS, "gamma_deg", "weak_r", "CH"):
                require(isinstance(optimum[key], (int, float)) and not isinstance(optimum[key], bool)
                        and math.isfinite(optimum[key]), "nonfinite_optimum")
            controls = [optimum["gamma_deg"], optimum["a0_deg"], optimum["a1_deg"]]
            require(study["domains"]["gamma_deg"][0] <= controls[0] <= study["domains"]["gamma_deg"][1]
                    and all(study["domains"]["angle_deg"][0] <= v <= study["domains"]["angle_deg"][1]
                            for v in controls[1:]), "optimum_outside_predeclared_domain")
            require(optimum["b0_deg"] == -controls[1] and optimum["b1_deg"] == -controls[2],
                    "incorrect_mirror_constraint")
            require(next((v for v in controls[1:] if abs(v) > 1e-12), 0) >= 0,
                    "incorrect_reflection_convention")
            model = primary.Model(point)
            require(abs(model.source_norm(controls[0]) - 1) <= 1e-12, "source_not_normalized")
            require(abs(model.r_one_pair(controls[0]) - optimum["r_one_pair"]) <= 1e-10,
                    "incorrect_single_pair_coordinate")
            require(abs(math.tan(math.radians(controls[0])) - optimum["weak_r"]) <= 1e-10,
                    "incorrect_weak_gain_coordinate")
            require(abs(model.score(controls) - optimum["CH"]) <= tolerance["CH_abs"],
                    "incorrect_source_ch_readout")
        require(set(report["cases"]) == set(study["cases"]), "incorrect_case_inventory")
        summary = {}
        for case in study["cases"]:
            rows = [row for row in report["results"] if row["case"] == case]
            require(len(rows) == (1 if case == "author_defaults" else 9), "incorrect_case_point_count")
            band = case_band(rows, study)
            actual = report["cases"][case]
            require(set(actual["band"]) == set(COMPONENTS), "incorrect_band_components")
            require(all(len(actual["band"][key]) == 2 and
                        all(abs(v - w) <= 1e-12 for v, w in zip(actual["band"][key], band[key]))
                        for key in COMPONENTS), "incorrect_case_band")
            checks = actual["comparisons"]
            require(len(checks) == 5, "incomplete_documented_controls")
            inside = []
            for key, check in zip(COMPONENTS, checks):
                expected_inside = band[key][0] <= documents[key] <= band[key][1]
                require(check["component"] == key and check["documented_value"] == documents[key]
                        and check["interval"] == actual["band"][key]
                        and check["inside"] is expected_inside, "incorrect_documented_comparison")
                inside.append(expected_inside)
            consistent = all(inside)
            legal = ("CONSISTENT", "REPLAY_CONSISTENT_WITH_PREDECLARED_BAND") if consistent else (
                "DEVIATION", "REPLAY_DEVIATION_EXCEEDS_PREDECLARED_BAND")
            require(actual["verdict"] in legal, "incorrect_case_verdict")
            summary[case] = {"verdict": "CONSISTENT" if consistent else "DEVIATION",
                             "documented_values_in_band": sum(inside), "band": band}
        summaries.append(summary)
    worst = {"r_one_pair": 0.0, "angle_deg": 0.0, "CH": 0.0}
    for first, second in zip(reports[0]["results"], reports[1]["results"]):
        for key in (*COMPONENTS, "CH"):
            kind = "r_one_pair" if key == "r_one_pair" else "CH" if key == "CH" else "angle_deg"
            delta = abs(first["optimum"][key] - second["optimum"][key])
            worst[kind] = max(worst[kind], delta)
            require(delta <= tolerance["r" if kind == "r_one_pair" else "CH_abs" if kind == "CH" else "angle_deg"],
                    "independent_numeric_disagreement")
    require(reports[1]["consistency"]["passed"] is True and not reports[1]["consistency"]["errors"],
            "independent_comparison_failed")
    require(all(summaries[0][case]["verdict"] == summaries[1][case]["verdict"] for case in study["cases"]),
            "independent_verdict_disagreement")
    sources = json.loads((HERE / "sources.json").read_text())
    require(sources["same_project_source_code_recovered"] is True and
            sources["model_source_identified"] is True and
            sources["publication_configuration_identified"] is False and
            sources["code_extraction_sha256"] == digest(HERE / "author-code.txt"), "incorrect_source_recovery")
    return {"schema": "nist-source-code-verification/v1", "status": "verified",
            "criterion_version": study["criterion_version"], "criterion_freeze": freeze,
            "model_source_identified": True, "publication_configuration_identified": False,
            "production_admitted": False, "input_points_verified": 19,
            "cases": summaries[0], "worst_deltas": worst,
            "required_source": ["same_final_design_efficiency_dark_and_brightness_configuration",
                                "publication_visibility_handling_or_approximation_binding"],
            "bindings": {name: digest(directory / name if name.endswith(".json") and
                         name in {"replay.json", "independent_replay.json"} else HERE / name)
                         for name in ("criterion.md", "replay.json", "independent_replay.json", "sources.json", "verify.py")},
            "bell_event_files_read": 0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--directory", type=Path, help="explicit report directory for focused controls")
    args = parser.parse_args()
    try:
        result = assess(args.directory)
    except (OSError, ValueError, KeyError, TypeError, ArithmeticError) as error:
        result = {"schema": "nist-source-code-verification/v1", "status": "failed", "reason": str(error),
                  "model_source_identified": False, "publication_configuration_identified": False,
                  "production_admitted": False}
    if not args.check_only:
        (HERE / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    return 0 if result["status"] == "verified" else 1


if __name__ == "__main__":
    raise SystemExit(main())
