#!/usr/bin/env python3
"""Source-owned calibrated ENV counts and a continuous nominal marginal bound."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import gzip
import importlib.util
import itertools
import json
from pathlib import Path
import re
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[7]
ENV = HERE.parents[1] / "observable-closure/environment-source"
MW = HERE.parent / "multi-window"
sys.path.insert(0, str(ENV))
import calibration_source as primary
import independent_calibration_source as independent
loader = importlib.util.spec_from_file_location("ncc_statistics", MW / "independent.py")
statistics = importlib.util.module_from_spec(loader)
sys.modules[loader.name] = statistics
loader.loader.exec_module(statistics)
VERSION = "p23-calibrated-environment-complete-count-review-ncc0001"
SCHEMA = "p23-calibrated-environment-complete-count-review/v1"
FALSE_SCOPE = ("calibration_sigma_inserted_as_95_percent_CI", "pair_box_claimed_as_public_uncertainty",
    "r6_optimum_parameters_used_as_source", "source_epoch_identified", "actual_hardware_identity_verified",
    "nominal_optimum_contract_replaced", "controller_advance")
CANONICAL_CI = MW / "independent.json.gz"


def require(value, reason):
    if not value:
        raise ValueError(reason)


def read_json(path):
    return json.loads(Path(path).read_text())


def interval(packet, I):
    return I(F(packet["exact_lower"]), F(packet["exact_upper"]))


def unpack_source(source, path):
    expected = {"G", "G_grid", "n_balanced", "n_grid", "t_balanced", "TA", "TB", "c", "c_descriptor", "xi_A", "xi_B", "u_A", "u_B", "source_phase", "allocation", "root_midpoints_used_as_source", "complete_Gram_supplied_by_caller"}
    require(set(source) == expected, "foreign_or_lookalike_ENV_source_fields")
    require(source["source_phase"] == ["1", "0"] and source["allocation"] in
            ("symmetric", "Alice_rank_one", "Bob_rank_one") and
            source["root_midpoints_used_as_source"] is False and source["complete_Gram_supplied_by_caller"] is False,
            "foreign_or_lookalike_calibrated_source")
    I = primary.I if path == "primary" else independent.I
    return {**{key: interval(source[key], I) for key in ("G", "TA", "TB", "c")}, "allocation": source["allocation"]}


def configuration():
    frozen = [statistics.frozen(HERE / name) for name in ("criterion.md", "sources.json", "review.py", "tests.py")]
    blocks = re.findall(r"<!-- NCC-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- NCC-FROZEN-END -->",
                        (HERE / "criterion.md").read_text(), re.S)
    require(len(blocks) == 1, "nonunique_calibrated_count_contract")
    spec = json.loads(blocks[0])
    require(spec["version"] == VERSION and spec["total_source_points"] == 19 and spec["default_source_points"] == 17 and
            spec["allocation_overrides"] == ["Alice_rank_one", "Bob_rank_one"] and spec["pulse_counts"] == [1, 3, 5, 7, 9] and
            spec["all_CI_count"] == 72 and spec["reference_beta_deg"] == "16" and
            spec["published_angles_deg"] == ["4.2", "-25.9", "-4.2", "25.9"] and
            all(spec[key] is False for key in FALSE_SCOPE) and spec["bell_event_files_read"] == 0,
            "calibrated_count_contract_or_scope_changed")
    manifest = read_json(HERE / "sources.json")
    for row in manifest["inputs"]:
        path = (ROOT / row["path"]).resolve()
        require(path.is_relative_to(ROOT) and statistics.sha(path.read_bytes()) == row["sha256"], "calibrated_count_source_binding_changed")
        statistics.frozen(path, row.get("commit"))
    calibration = read_json(ENV / "calibration-verification.json")
    require(calibration["status"] == "PUBLIC_RAW_CALIBRATION_ALL_ROOTS_AND_SHARED_SOURCE_FOCK_VERIFIED" and calibration["point_count"] == 19 and calibration["default_point_count"] == 17 and
            calibration["foreign_saved_source_gain_overlap_or_probabilities_used_as_forward_inputs"] is False and
            calibration["actual_source_or_hardware_identity_verified"] is False, "unqualified_original_calibration_source_chain")
    return spec, {"execution": frozen, "inputs": manifest["inputs"]}


def load_endpoints(ci_override=None):
    path = CANONICAL_CI if ci_override is None else Path(ci_override)
    require(path.read_bytes() == CANONICAL_CI.read_bytes(), "lookalike_or_changed_CI_override")
    report = json.loads(gzip.decompress(path.read_bytes()))
    require(report["schema"] == "p23-public-multi-window-independent/v1" and report["all_six_runs_and_thirty_windows_retained"] is True,
            "wrong_public_CI_kind")
    run = next(row for row in report["runs"] if row["run"] == "xor3")
    require(run["complete_trials"] == 182137032 and len(run["groups"]) == 5, "wrong_complete_XOR3_exposure")
    endpoints = [{"id": "full_N" + str(g["pulse_count"]), "N": g["pulse_count"], "exposure": g["complete_trials"],
                  "CI": g["common_Born_CI"], "spacelike_scope": g["spacelike_review_scope"]} for g in run["groups"]]
    old = read_json(HERE.parents[1] / "observable-prediction/public-comparison-po0003.json")
    require(old["complete_trials"] == 177358351, "wrong_original_stop_exposure")
    endpoints.append({"id": "old_stop_N5", "N": 5, "exposure": old["complete_trials"], "CI": old["common_mean_confidence"], "spacelike_scope": True})
    validate_endpoints(endpoints)
    return endpoints


def validate_endpoints(endpoints):
    require(len(endpoints) == 6 and [e["N"] for e in endpoints] == [1, 3, 5, 7, 9, 5] and
            len({e["id"] for e in endpoints}) == 6 and sum(len(e["CI"][field]) for e in endpoints for field in
            ("j", "sA_cell", "sB_cell")) == 72, "incomplete_or_lookalike_72_CI")
    for e in endpoints:
        require(e["exposure"] == (177358351 if e["id"] == "old_stop_N5" else 182137032), "source_endpoint_exposure_mapping_changed")
        require(set(e["CI"]) >= {"j", "sA_cell", "sB_cell"} and all(len(e["CI"][f]) == 4 for f in ("j", "sA_cell", "sB_cell")),
                "wrong_setting_mapping")
        for field in ("j", "sA_cell", "sB_cell"):
            for packet in e["CI"][field]:
                require(0 <= F(packet["exact_lower"]) <= F(packet["exact_upper"]) <= 1, "invalid_public_probability_CI")
    require(endpoints[4]["spacelike_scope"] is False, "N9_Bell_identity_inflated")


def source_inventory(spec):
    report = read_json((HERE / spec["source_report"]).resolve())
    require(report["status"] == "source_generated" and report["point_count"] == 19 and
            report["default_point_count"] == 17 and report["all_nineteen_source_points_generated"] is True and
            report["actual_source_or_hardware_identity_verified"] is False, "wrong_environment_source_report")
    points, branches = [], []
    for point in report["points"]:
        require(point["status"] == "source_generated", "unresolved_original_source_point")
        rows = [b for b in point["branches"] if b["status"] == "source_generated_with_complete_raw_fringe_certificates"]
        require(rows and all("source" in branch for branch in rows), "missing_original_source_branch")
        points.append({"id": point["id"], "input": point["input"], "included_in_default_source_box": point["included_in_default_source_box"]})
        for branch in rows:
            source = branch["source"]
            require(source["allocation"] == point["input"]["allocation"], "source_allocation_mapping_changed")
            unpack_source(source, "primary")
            branches.append({"point_id": point["id"], "root_index": branch["root_index"], "input": point["input"],
                "default": point["included_in_default_source_box"], "source": source})
    require(len(points) == 19 and sum(p["included_in_default_source_box"] for p in points) == 17,
            "source_point_or_default_override_inventory_changed")
    require({p["input"]["allocation"] for p in points if not p["included_in_default_source_box"]} == set(spec["allocation_overrides"]),
            "allocation_override_missing")
    return points, branches


def windows_from_no_click(no_click, pulses):
    a, b, ab = [no_click[k] ** pulses for k in ("A", "B", "AB")]
    return {"sA": 1 - a, "sB": 1 - b, "j": 1 - a - b + ab,
            "outcomes": [1 - a - b + ab, b - ab, a - ab, ab]}


def primary_forward(source, spec, endpoints):
    src = unpack_source(source, "primary")
    drive = primary.drive_source(src["G"], F(spec["reference_beta_deg"]))
    ba, bb = map(F, spec["background_per_pulse"])
    pulses = []
    angles = list(map(F, spec["published_angles_deg"]))
    for a, b in itertools.product(angles[:2], angles[2:]):
        no_click, _ = primary.native_forward(drive["tH"], drive["tV"], src["TA"], src["TB"], src["c"],
                                            src["allocation"], a, b, ba, bb)
        pulses.append(no_click)
    readings = [{"endpoint": e["id"], "N": e["N"], "cells": [windows_from_no_click(p, e["N"]) for p in pulses]} for e in endpoints]
    return readings, {"tH": drive["tH"], "tV": drive["tV"], "q": drive["q"], "same_source_full_gain_root_transported": True}


def independent_forward(source, spec, endpoints):
    src = unpack_source(source, "independent")
    packet = independent.source_packet(src, F(spec["reference_beta_deg"]))
    angles = list(map(F, spec["published_angles_deg"]))
    pulse_det, pulse_Born, probes = [], [], []
    for a, b in itertools.product(angles[:2], angles[2:]):
        effects = [independent.environment_effect(packet["TA"], packet["xiA"], a),
                   independent.environment_effect(packet["TB"], packet["xiB"], b)]
        determinant = independent.determinant_readout(packet, effects, spec["background_per_pulse"])
        actual = independent.independent_born(packet, effects, 6, spec["background_per_pulse"])
        za, zb = [1 - F(p) for p in spec["background_per_pulse"]]
        pulse_det.append(dict(zip(("A", "B", "AB"), [za * determinant["no_click"][0], zb * determinant["no_click"][1], za * zb * determinant["no_click"][2]])))
        pulse_Born.append(dict(zip(("A", "B", "AB"), [za * actual["no_click"][0], zb * actual["no_click"][1], za * zb * actual["no_click"][2]])))
        probes.append({"angles": [str(a), str(b)], "tail": actual["tail"], "prefix_renormalized": actual["prefix_renormalized"],
                       "Gamma_sector_dimensions": actual["Gamma_sector_dimensions"], "original_numberMass_tail": True})
    det = [{"endpoint": e["id"], "N": e["N"], "cells": [windows_from_no_click(p, e["N"]) for p in pulse_det]} for e in endpoints]
    actual = [{"endpoint": e["id"], "N": e["N"], "cells": [windows_from_no_click(p, e["N"]) for p in pulse_Born]} for e in endpoints]
    return det, actual, {"packet": packet, "actual_occupation_Born_probes": probes,
                        "foreign_EF_source_or_fields_used": False, "same_source_full_gain_root_transported": True}


def serialize(value):
    if isinstance(value, (primary.I, independent.I)):
        return value.packet()
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {k: serialize(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [serialize(v) for v in value]
    return value


def compare_readouts(paths, endpoints):
    certificate, contained, cross_count = [], True, 0
    for ei, e in enumerate(endpoints):
        for row in range(4):
            for field, name in (("sA_cell", "sA"), ("sB_cell", "sB"), ("j", "j")):
                values = [path[ei]["cells"][row][name] for path in paths]
                require(max(p.lo for p in values) <= min(p.hi for p in values), "same_ENV_source_forward_enclosures_disjoint")
                lo, hi = F(e["CI"][field][row]["exact_lower"]), F(e["CI"][field][row]["exact_upper"])
                contained &= all(lo <= value.lo <= value.hi <= hi for value in values)
                if all(value.hi < lo or hi < value.lo for value in values):
                    certificate.append({"endpoint": e["id"], "N": e["N"], "row": row, "field": field,
                        "original_CI": e["CI"][field][row], "primary": values[0], "independent": values[1], "actual_Born": values[2]})
                cross_count += 1
            for outcome in range(4):
                values = [path[ei]["cells"][row]["outcomes"][outcome] for path in paths]
                require(max(p.lo for p in values) <= min(p.hi for p in values), "same_ENV_source_outcome_enclosures_disjoint")
    return {"verdict": "SOURCE_REJECTED_BY_ORIGINAL_CI" if certificate else "ALL_72_CI_CONTAINED" if contained else "CI_OVERLAP_UNRESOLVED",
            "all_72_reads_and_96_outcomes_crossed": cross_count == 72, "all_72_CI_contained": bool(contained),
            "actual_strict_disjoint_certificates": certificate}


def continuum_bound(spec, endpoints):
    tol = F(spec["readout_tolerance"])
    qlo, qhi = F(spec["nominal_pair_input_box"][0]) - tol, F(spec["nominal_pair_input_box"][1]) + tol
    kahi, kblo = F(spec["nominal_K_A_box"][1]) + tol, F(spec["nominal_K_B_box"][0]) - tol
    ba, bb = map(F, spec["background_per_pulse"])
    nlo, nhi = qlo / 2, qhi / (2 * (1 - qhi))
    tblo = (kblo * (1 - ba) / (1 + nhi) - bb) / (1 + 2 * nhi)
    sblo = bb + (1 - bb) * tblo * nlo / (1 + tblo * nlo)
    require(0 < tblo < 1 and sblo > bb, "continuum_matched_K_herald_bound_not_qualified")
    tahi = (kahi - ba) / ((1 - ba) * (1 - bb / sblo))
    beta_s, _ = independent.born.trig(F(spec["reference_beta_deg"]))
    a_s, a_c = independent.born.trig(F(spec["published_angles_deg"][0]))
    require((a_c.square() - a_s.square()).lo > 0, "single_population_fraction_monotonicity_not_qualified")
    fraction = a_s.square() + beta_s.square() * (a_c.square() - a_s.square())
    population = qhi / (1 - qhi)
    upper = (independent.I(ba) + (1 - ba) * tahi * population * fraction).hi
    require(0 < upper < 1, "nonphysical_continuum_click_upper")
    bounds, witnesses = [], []
    for e in endpoints:
        high = 1 - (1 - upper) ** e["N"]
        target = e["CI"]["sA_cell"][0]
        bounds.append({"endpoint": e["id"], "N": e["N"], "single_upper": high, "original_CI": target})
        if high < F(target["exact_lower"]):
            witnesses.append({"endpoint": e["id"], "N": e["N"], "row": 0, "field": "sA_cell",
                "all_nominal_source_upper": high, "original_CI_lower": F(target["exact_lower"]),
                "strict_gap": F(target["exact_lower"]) - high, "spacelike_scope": e["spacelike_scope"]})
    return {"continuous_nominal_ENV_input_domain_rejected": bool(witnesses),
        "input_domain": {"q": [qlo, qhi], "K_A_upper": kahi, "K_B_lower": kblo},
        "balanced_n_domain": [nlo, nhi], "transmission_B_lower": tblo, "herald_B_lower": sblo,
        "transmission_A_upper": tahi, "total_reference_mean_upper": population,
        "V_population_fraction_upper": beta_s.square(), "receiver_weighted_fraction": fraction,
        "single_pulse_click_upper": upper, "all_N_transport": bounds, "strict_original_CI_witnesses": witnesses,
        "all_legal_environment_allocations_and_calibration_roots_covered": True,
        "calibration_k1_band_role": "nominal_condition_not_95_percent_coverage",
        "pair_interval_role": "old_self_chosen_nominal_box_not_public_uncertainty",
        "new_general_Born_kernel_claim": False, "more_point_scans_performed": False}


def science(ci_override=None):
    start = time.monotonic()
    spec, bindings = configuration()
    endpoints = load_endpoints(ci_override)
    points, branches = source_inventory(spec)
    result = []
    for branch in branches:
        a, a_source = primary_forward(branch["source"], spec, endpoints)
        b, actual, b_source = independent_forward(branch["source"], spec, endpoints)
        comparison = compare_readouts([a, b, actual], endpoints)
        result.append({**branch, "primary_source": a_source, "independent_source": b_source,
                       "primary_all_windows": a, "independent_all_windows": b, "actual_positive_Born_all_windows": actual,
                       "comparison": comparison})
        print(json.dumps({"calibrated_source_complete": branch["point_id"], "root": branch["root_index"], "verdict": comparison["verdict"]}), flush=True)
    continuous = continuum_bound(spec, endpoints)
    value = serialize({"schema": SCHEMA, "version": VERSION, "status": "complete", "source_point_inventory": points,
        "source_branches": result, "source_point_count": 19, "default_point_count": 17,
        "all_19_sources_rejected_by_original_CI": all(r["comparison"]["actual_strict_disjoint_certificates"] for r in result),
        "continuum_single_certificate": continuous, "all_original_72_CI": endpoints, "bindings": bindings,
        "finite_point_rejection_implies_continuum_rejection": False, **{key: False for key in FALSE_SCOPE},
        "statistical_role": "retrospective_named_calibrated_ENV_source_count_compatibility",
        "foreign_EF_source_or_fields_used": False, "r6_optimum_parameters_used_as_forward_inputs": False,
        "new_general_Born_or_statistical_coverage_kernel_claim": False, "bell_event_files_read": 0, "retrospective": True})
    value["source_stage_sha256"] = statistics.sha(json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False).encode())
    value["runtime_seconds"] = time.monotonic() - start
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--CI-report", type=Path)
    args = parser.parse_args()
    require(not args.output.exists(), "protected_existing_calibrated_count_first")
    value = science(args.CI_report)
    raw = (json.dumps(value, sort_keys=True, indent=2, allow_nan=False) + "\n").encode()
    args.output.write_bytes(raw)
    print(json.dumps({"output": str(args.output), "logical_sha256": statistics.sha(raw), "bytes": len(raw),
        "all_19_rejected": value["all_19_sources_rejected_by_original_CI"],
        "continuum_rejected": value["continuum_single_certificate"]["continuous_nominal_ENV_input_domain_rejected"],
        "runtime_seconds": value["runtime_seconds"]}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
