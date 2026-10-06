#!/usr/bin/env python3
"""Consume sealed r6 searches and r6.1 continuation on regenerated nominal sources."""
from __future__ import annotations

import argparse
import copy
from fractions import Fraction as F
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path
import re
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import environment_replay as primary
import independent_environment_replay as independent

HERE, ROOT, BASE = primary.HERE, primary.ROOT, primary.NOMINAL
CAL = primary.calibration
IND = independent.source
A = primary.ARITHMETIC
SCHEMA = "p23-nominal-environment-replay-verification/v1"
MODEL = "nominal-environment-replay-r0006"
REVISION = "nominal-environment-replay-r0006.1"
NUMERIC_FREEZE = "ffa38de226"
FIRST = {
    "replay-r0006.json": ("2dc881d0a6", "adde7242ff7522c67e209b76c5c518d3839412a277c9dfda420fcf10224edf0e", "replay-r0006-storage.json"),
    "independent-replay-r0006.json": ("4987380af3", "6356523599dffa91ef454b916ad251c343ac7d8e0dfa1c9d1012a56758d3881d", "independent-replay-r0006-storage.json"),
    "independent-replay-r0006.1.json": ("322efdc4dc", "8d57251760538c50dd1392f4f7950372e06abe16f322199895599db9a831cc53", "independent-replay-r0006.1-storage.json"),
}
COMPONENTS = ("r", "a0", "a1", "b0", "b1")
INDEPENDENT_COMPONENTS = ("r_one_pair", "a0_deg", "a1_deg", "b0_deg", "b1_deg")
SCOPE_FLAGS = ("actual_publication_configuration_identified", "global_argmax_kernel_proof", "controller_advance")
require = CAL.require


def parse(raw):
    return json.loads(raw, parse_constant=lambda value: (_ for _ in ()).throw(ValueError("nonfinite_JSON:" + value)))


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def logical_hash(value):
    return digest(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def ends(packet):
    lo, hi = F(packet["exact_lower"]), F(packet["exact_upper"])
    require(lo <= hi, "reversed_receipt_interval")
    return lo, hi


def distance(a, b):
    al, ah = ends(a); bl, bh = ends(b)
    return max(F(0), al - bh, bl - ah)


def close(a, b, tolerance, name):
    value = distance(a, b)
    require(value <= F(tolerance), name)
    return value


def point_packet(value):
    return {"exact_lower": str(F(value)), "exact_upper": str(F(value))}


def bind_tree(value):
    if isinstance(value, dict):
        if {"path", "commit", "sha256"} <= value.keys():
            path = (ROOT / value["path"]).resolve()
            require(path.is_relative_to(ROOT), "foreign_script_or_source_path")
            if not path.exists() and path.parent == HERE and path.name in FIRST:
                commit, expected, _ = FIRST[path.name]
                require(value["commit"] == commit and value["sha256"] == expected,
                        "different_original_logical_receipt_binding")
                raw = subprocess.check_output(["git", "show", commit + ":" + value["path"]], cwd=ROOT)
                require(digest(raw) == expected, "original_logical_receipt_binding_changed")
            else:
                bound = A.frozen(path, value["commit"])
                require(bound["sha256"] == value["sha256"], "execution_source_binding_changed:" + value["path"])
        for child in value.values():
            bind_tree(child)
    elif isinstance(value, list):
        for child in value:
            bind_tree(child)


def sealed(directory, name):
    commit, expected, storage_name = FIRST[name]
    relative = (HERE / name).relative_to(ROOT).as_posix()
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=True)
    blob = subprocess.check_output(["git", "show", commit + ":" + relative], cwd=ROOT)
    require(digest(blob) == expected, "original_logical_Git_blob_changed:" + name)
    metadata_path = HERE / storage_name
    A.frozen(metadata_path)
    metadata = parse(metadata_path.read_bytes())
    logical_sha = metadata.get("logical_json_sha256", metadata.get("logical_sha256"))
    first_commit = metadata.get("original_first_receipt_commit", metadata.get("original_first_result_commit"))
    require(logical_sha == expected and first_commit == commit and
            metadata.get("logical_scientific_receipt_changed", metadata.get("scientific_content_changed")) is False,
            "storage_logical_identity_changed:" + name)
    compressed_path = HERE / (name + ".gz")
    A.frozen(compressed_path)
    compressed = compressed_path.read_bytes()
    require(digest(compressed) == metadata["gzip_sha256"] and len(compressed) == metadata["gzip_bytes"] and
            metadata.get("gzip_mtime", metadata.get("compression_mtime")) == 0 and
            compressed[4:8] == b"\0\0\0\0", "storage_gzip_identity_changed:" + name)
    raw = gzip.decompress(compressed)
    require(raw == blob and len(raw) == metadata["raw_bytes"], "lossless_first_receipt_roundtrip_failed:" + name)
    if directory != HERE:
        plain_override = directory / name
        gzip_override = directory / (name + ".gz")
        require(plain_override.exists() or gzip_override.exists(), "missing_JSON_or_gzip_override:" + name)
        if plain_override.exists():
            require(plain_override.read_bytes() == blob, "conflicting_logical_JSON_override:" + name)
        if gzip_override.exists():
            require(gzip_override.read_bytes() == compressed, "conflicting_frozen_gzip_override:" + name)
        if (directory / storage_name).exists():
            require(parse((directory / storage_name).read_bytes()) == metadata, "conflicting_storage_metadata_override:" + name)
    receipt = parse(raw)
    return receipt, {"logical_path": relative, "original_commit": commit, "logical_sha256": expected,
                     "gzip_path": compressed_path.name, "gzip_sha256": digest(compressed),
            "logical_bytes": len(raw), "gzip_bytes": len(compressed), "logical_Git_blob_and_gzip_byte_equal": True}


def headers(p, first, completed):
    require(p["schema"] == "p23-nominal-environment-replay/v1" and p["criterion_version"] == MODEL and
            first["schema"] == "nist-nominal-environment-independent-replay/v1" and first["criterion_version"] == MODEL and
            completed["schema"] == "nist-nominal-environment-independent-replay-completion/v1" and
            completed["scientific_model_id"] == completed["criterion_version"] == MODEL and
            completed["numerical_revision"] == REVISION, "look_alike_replay_version")
    require(type(p["point_count"]) is int and p["point_count"] == len(p["points"]) ==
            len(first["results"]) == len(completed["results"]) == 19 and
            type(p["default_point_count"]) is int and p["default_point_count"] == 17, "incomplete_replay_point_inventory")
    for report in (p, first, completed):
        require(all(report[k] is False for k in SCOPE_FLAGS) and
                type(report["event_files_read"]) is int and report["event_files_read"] == 0 and
                type(report["objective_pulses"]) is int and report["objective_pulses"] == 1 and
                type(report["diagnostic_pulses"]) is int and report["diagnostic_pulses"] == 5,
                "replay_source_objective_or_authority_scope_changed")
        require(report.get("new_full_Born_or_Gaussian_determinant_kernel_claim",
                           report.get("new_full_Born_or_general_Gaussian_determinant_kernel_claim")) is False,
                "unpaid_general_infinite_kernel_claim")
    require(p["status"] == "complete" and p["comparison"]["documented_values_used_only_after_all_optimizations"] is True and
            first["documented_values_loaded_after_all_candidates"] is True and
            completed["documented_values_loaded_after_all_candidates"] is True and
            p["source_gain_update"] == "fixed_G_times_cos_sin_beta" and
            p["source_midpoints_used_only_for_candidate_search"] is True and
            p["entire_calibration_brackets_used_for_final_native_readout"] is True and
            all(value is False for key, value in p["independence"].items() if key.startswith("foreign_")),
            "forward_or_documented_input_role_changed")
    require(first["numerical_search_complete"] is False and completed["numerical_search_complete"] is True and
            completed["model_inputs_objective_bands_or_acceptance_changed"] is False and
            completed["source_or_seed_from_primary_used"] is False and
            completed["new_scientific_blind_first_run_claim"] is False, "completion_history_or_scope_changed")


def completion_lineage(first, completed, numeric):
    old = {row["source_id"]: row for row in first["results"]}
    new = {row["source_id"]: row for row in completed["results"]}
    require(len(old) == len(new) == 19 and old.keys() == new.keys(), "completion_source_inventory_changed")
    unresolved = [row for row in first["results"] if row["status"] != "NUMERICAL_SEARCH_COMPLETE"]
    require([row["point_id"] for row in unresolved] == numeric["unresolved_points"] and
            completed["original_unresolved_records"] == unresolved, "original_cap_receipt_not_preserved")
    reused = completed["reused_completed_record_bindings"]
    require(len(reused) == 18 and len({row["source_id"] for row in reused}) == 18, "lost_reused_completed_point")
    for binding in reused:
        source_id = binding["source_id"]
        require(old[source_id] == new[source_id] and logical_hash(old[source_id]) == binding["original_record_sha256"],
                "completed_point_record_was_recomputed_or_changed")
    for previous in unresolved:
        current = new[previous["source_id"]]
        require(len(current["candidates"]) == len(previous["candidates"]) == 8 and
                current["source_parameters"] == previous["source_parameters"] and
                current["coarse_grid"] == previous["coarse_grid"], "completion_lost_own_source_or_start")
        for candidate, origin in zip(current["candidates"], previous["candidates"]):
            require(candidate["original_candidate"] == origin and candidate["continuation_start_deg"] == origin["coordinates_deg"] and
                    candidate["line_stop_deg"] == numeric["line_stop_deg"] and
                    candidate["whole_cycle_stop_deg"] == numeric["whole_cycle_stop_deg"], "continuation_seed_or_precision_changed")
            cycles = candidate["continuation_cycles"]
            require(1 <= len(cycles) <= numeric["additional_cycles_per_candidate"] and
                    all(len(row["axis_searches"]) == 5 for row in cycles), "incomplete_continuation_axis_trace")
            require(type(candidate["complete"]) is bool, "numeric_completion_boolean")
            if candidate["complete"]:
                require(candidate["termination"] == "whole_cycle_stop" and
                        F(str(cycles[-1]["movement_deg"])) <= F(numeric["whole_cycle_stop_deg"]), "cycle_stop_not_satisfied")
            else:
                require(candidate["termination"] == "additional_coordinate_cycle_cap" and
                        len(cycles) == numeric["additional_cycles_per_candidate"], "false_continuation_stop")
            for axis, row in enumerate(candidate["final_axis_searches"]):
                require(row["axis"] == axis and row["scan_count"] == (9 if axis == 0 else 30) and
                        row["golden_steps"] <= numeric["golden_steps"], "continuation_axis_scan_changed")
                if candidate["complete"]:
                    lo, hi = map(lambda x: F(str(x)), row["final_bracket_deg"])
                    require(row["termination"] == "width_stop" and hi - lo <= F(numeric["line_stop_deg"]),
                            "continuation_line_stop_not_satisfied")
    require(completed["completion_method"] == {
        "line_stop_deg": numeric["line_stop_deg"], "whole_cycle_stop_deg": numeric["whole_cycle_stop_deg"],
        "additional_cycles_per_candidate": numeric["additional_cycles_per_candidate"],
        "all_own_eight_candidates_continued": True, "lower_converged_candidate_substitution_used": False},
        "completion_method_changed")
    return {"reused_completed_points": 18, "continued_points": len(unresolved), "continued_candidates": 8,
            "original_unresolved_first_logical_bytes_preserved": True,
            "same_science_inputs_bands_and_acceptance": True, "new_blind_first_run_claim": False}


def primary_search(branch, source, background, spec):
    controls = branch["selected_control_degrees"]
    require(len(controls) == 5 and 0 <= controls[0] <= 45 and controls[1] >= 0 and
            all(-90 <= a < 90 for a in controls[1:]), "primary_control_role_or_canonicalization_changed")
    history = branch["search"]
    require(history["grid_count"] == 1024 and history["completed_prescribed_search"] is True and
            len(history["neighbor_levels"]) == 20 and len(history["all_optimized_start_candidates"]) in (8, 9),
            "primary_search_incomplete")
    for candidate in history["all_optimized_start_candidates"]:
        receipt = candidate["simplex"]
        require(receipt["stop_reason"] == "simplex_diameter" and receipt["iterations"] <= 5000 and
                F(str(receipt["final_diameter_deg"])) <= F("1e-7"), "primary_simplex_not_stopped")
        vertices = receipt["final_simplex"]
        require(len(vertices) == 6 and all(len(row[0]) == 5 and row[1] is not None for row in vertices),
                "primary_final_simplex_incomplete")
        diameter = max(abs(a - b) for row in vertices for a, b in zip(row[0], vertices[0][0]))
        require(abs(diameter - receipt["final_diameter_deg"]) <= 1e-12, "primary_simplex_diameter_mismatch")
    for level, row in enumerate(history["neighbor_levels"]):
        require(row["level"] == level and row["step_deg"] == .05 / 2 ** level and
                type(row["accepted_moves"]) is int and 0 <= row["accepted_moves"] <= 16,
                "primary_ten_neighbor_schedule_changed")
    grid = [row for row in history["all_candidate_scores"] if row[0] == "grid"]
    method = spec["primary_optimizer"]
    expected = list(itertools.product(method["pump_grid_deg"], method["angle0_grid_deg"], method["angle1_grid_deg"],
                                      method["angle0_grid_deg"], method["angle1_grid_deg"]))
    require(len(expected) == 1024 and len(grid) in (1024, 1025), "primary_grid_trace_lost")
    extra = grid[1024:]
    require(len(history["grid_seeds"]) == 8 + len(extra) and
            len(history["all_optimized_start_candidates"]) == 8 + len(extra), "primary_extra_start_inventory_changed")
    if extra:
        require(extra[0][1:6] == history["grid_seeds"][-1][0] and
                extra[0][6] == history["grid_seeds"][-1][1], "primary_own_center_extra_start_changed")
    objective = primary.Objective(source, background)
    grid_gap = 0.0
    for row, point in zip(grid[:1024], expected):
        require(tuple(row[1:6]) == tuple(point) and type(row[6]) is float and math.isfinite(row[6]),
                "primary_grid_coordinate_or_score_changed")
        grid_gap = max(grid_gap, abs(objective(point) - row[6]))
    for row in extra:
        grid_gap = max(grid_gap, abs(objective(row[1:6]) - row[6]))
    require(grid_gap <= float(F(spec["source_readout_tolerance"])), "primary_grid_score_not_rebuilt")
    return {"grid_points_recomputed": 1024, "own_center_extra_starts_recomputed": len(extra),
            "grid_score_max_absolute_difference": grid_gap,
            "all_start_simplex_stops_verified": True, "ten_neighbor_halving_schedule_verified": True}


def independent_search(row, packet, background, spec, original):
    require(row["status"] == "NUMERICAL_SEARCH_COMPLETE" and len(row["candidates"]) == 8,
            "independent_point_not_completed")
    model = independent.Model(packet, background)
    _, coarse = independent.coarse_grid(model, spec["independent_optimizer"])
    require(coarse == row["coarse_grid"] == original["coarse_grid"], "independent_coarse_scores_not_rebuilt")
    best = min(row["candidates"], key=lambda c: (-F(c["CH_decimal"]), tuple(c["coordinates_deg"])))
    require(best["complete"] is True and best["termination"] == "whole_cycle_stop", "highest_independent_candidate_not_stopped")
    optimum = row["optimum"]
    controls = [optimum[k] for k in ("beta_deg", "a0_deg", "a1_deg", "b0_deg", "b1_deg")]
    require(controls == best["coordinates_deg"] and 0 <= controls[0] <= 45 and controls[1] >= 0 and
            all(-90 <= a < 90 for a in controls[1:]), "independent_optimum_not_highest_or_role_changed")
    lines = best["final_axis_searches"]
    tolerance = F("1e-9" if "continuation_cycles" in best else "1e-7")
    require(len(lines) == 5 and all(r["termination"] == "width_stop" and
            F(str(r["final_bracket_deg"][1])) - F(str(r["final_bracket_deg"][0])) <= tolerance for r in lines),
            "independent_line_stop_not_satisfied")
    cycles = best.get("continuation_cycles", best.get("cycles"))
    require(cycles and F(str(cycles[-1]["movement_deg"])) <= F("1e-7"), "independent_whole_cycle_stop_not_satisfied")
    require(F(str(model.score(controls))) == F(optimum["CH_decimal"]) and
            F(str(model.r_one_pair(controls[0]))) == F(optimum["r_one_pair"]), "independent_final_score_not_rebuilt")
    return model, controls, {"coarse_grid_points_recomputed": 1280, "coarse_score_hash_reproduced": True,
                             "highest_candidate_stopped": True, "final_axis_and_cycle_stops_verified": True}


def convert_ind(packet):
    return IND.I(*ends(packet))


def shared_source(source):
    return {"G": convert_ind(source["G"]), "TA": convert_ind(source["TA"]), "TB": convert_ind(source["TB"]),
            "c": convert_ind(source["c"]), "allocation": source["allocation"]}


def born_readout(source, controls, background):
    packet = IND.source_packet(source, F(str(controls[0])))
    rows, zero, values = [], [], []
    for a, b in itertools.product(controls[1:3], controls[3:5]):
        effects = [IND.environment_effect(packet["TA"], packet["xiA"], F(str(a))),
                   IND.environment_effect(packet["TB"], packet["xiB"], F(str(b)))]
        result = IND.independent_born(packet, effects, 6, background)
        n1 = result["observed_outcomes"]
        za, zb = (1 - F(x) for x in background)
        n5_zero = [result["no_click"][0] * za, result["no_click"][1] * zb, result["no_click"][2] * za * zb]
        n5 = IND.born.outcomes_from_no_click([x ** 5 for x in n5_zero])
        rows.append({"windows": {"1": {k: v.packet() for k, v in n1.items()},
                                 "5": {k: v.packet() for k, v in n5.items()}},
                     "prefix_mass": result["prefix_mass"].packet(), "original_tail": result["tail"].packet(),
                     "total_pair_prefix": 6, "prefix_renormalized": False})
        values.append(n1); zero.append(n5)
    ch = {}
    for n, cells in (("1", values), ("5", zero)):
        ch[n] = cells[0]["++"] + cells[1]["++"] + cells[2]["++"] - cells[3]["++"] -\
                cells[0]["++"] - cells[0]["+0"] - cells[0]["++"] - cells[0]["0+"]
    return {"r_one_pair": (packet["tV"] / packet["tH"]).sqrt().packet(),
            "native_CH_N1": ch["1"].packet(), "diagnostic_CH_N5": ch["5"].packet(), "cells": rows}


def probability_cross(native, born, tol):
    require(len(native["cells"]) == len(born["cells"]) == 4, "lost_receiver_setting_cell")
    maximum = F(0)
    for p, q in zip(native["cells"], born["cells"]):
        require(set(p["windows"]) == set(q["windows"]) == {"1", "5"}, "window_objective_diagnostic_role_changed")
        for n in ("1", "5"):
            require(set(p["windows"][n]) == set(q["windows"][n]) == {"++", "+0", "0+", "00"}, "incomplete_four_outcomes")
            maximum = max(maximum, *(close(p["windows"][n][k], q["windows"][n][k], tol,
                                          "shared_source_complete_outcomes_disagree") for k in ("++", "+0", "0+", "00")))
    for key in ("r_one_pair", "native_CH_N1", "diagnostic_CH_N5"):
        maximum = max(maximum, close(native[key], born[key], tol, "shared_source_CH_or_ratio_disagree"))
    return maximum


def calibration_certificates():
    bindings = {}
    for name in ("calibration-verification.json", "matched-certification.json"):
        binding = A.frozen(HERE / name)
        packet = parse((HERE / name).read_bytes())
        if name == "calibration-verification.json":
            require(packet["schema"] == "p23-nominal-environment-calibration-verification/v1" and
                    packet["status"] == "PUBLIC_RAW_CALIBRATION_ALL_ROOTS_AND_SHARED_SOURCE_FOCK_VERIFIED" and
                    packet["point_count"] == 19 and packet["default_point_count"] == 17 and
                    packet["foreign_saved_source_gain_overlap_or_probabilities_used_as_forward_inputs"] is False,
                    "calibration_cross_not_signed")
            bind_tree(packet["program_freeze"])
        else:
            require(packet["schema"] == "p23-environment-matched-lean-certification/v1" and packet["status"] == "certified" and
                    packet["unconditional_public_mouth"] == "P23.EnvironmentSource.Matched.Consumer.actual_matched_calibration_consumer",
                    "matched_source_kernel_not_signed")
            for relative, expected in packet["bindings"].items():
                require(A.digest(ROOT / relative) == expected, "matched_source_dependency_changed:" + relative)
        bindings[name] = binding
    return bindings


def band_verdict(comparisons):
    require(len(comparisons) == 5 and [row["name"] for row in comparisons] == list(COMPONENTS) and
            all(type(row["inside"]) is bool for row in comparisons), "incomplete_or_numeric_band_comparison")
    for row in comparisons:
        lo, hi = ends(row["band"])
        require(row["inside"] is (lo <= F(row["documented"]) <= hi), "forged_inside_band")
    return "CONSISTENT" if all(row["inside"] for row in comparisons) else "DEVIATION"


def _verify(directory, production):
    start = time.monotonic()
    program = A.frozen(Path(__file__))
    spec, _, background, bindings = primary.inputs()
    completion_path = BASE / "criterion-r0006.1.md"
    numeric_binding = A.frozen(completion_path, NUMERIC_FREEZE)
    blocks = re.findall(r"```json\s*(.*?)\s*```", completion_path.read_text(), re.S)
    require(len(blocks) == 1, "ambiguous_numeric_completion_contract")
    numeric = parse(blocks[0])
    require(numeric["scientific_model_id"] == MODEL and numeric["numerical_revision"] == REVISION and
            numeric["model_inputs_objective_bands_or_acceptance_changed"] is False and
            numeric["source_or_seed_from_primary_used"] is False, "completion_science_scope_changed")
    original, pbind = sealed(directory, "replay-r0006.json")
    first, ibind = sealed(directory, "independent-replay-r0006.json")
    completed, cbind = sealed(directory, "independent-replay-r0006.1.json")
    headers(original, first, completed)
    for report in (original, first, completed):
        bind_tree(report.get("freeze", report.get("bindings")))
    lineage = completion_lineage(first, completed, numeric)
    certificates = calibration_certificates()
    freshp = CAL.run()
    require(freshp["status"] == "source_generated" and len(freshp["points"]) == 19, "public_primary_source_regeneration_incomplete")
    cal_spec, _, _ = IND.load_frozen()
    inventory = IND.input_points(cal_spec)
    symbolic = IND.generate_native_fringe_polynomials()
    gains = {}
    original_i = {r["source_id"]: r for r in first["results"]}
    completed_i = {r["source_id"]: r for r in completed["results"]}
    verified_p, verified_i, rows = copy.deepcopy(original["points"]), copy.deepcopy(completed["results"]), []
    independent_rebuilt = {r["source_id"]: r for r in verified_i}
    for number, (fresh, saved, canonical_point, checked_p) in enumerate(zip(freshp["points"], original["points"], inventory, verified_p)):
        require(saved["id"] == fresh["id"] and saved["input"] == fresh["input"] and
                saved["included_in_default_source_box"] is (number < 17) and
                saved["calibration_all_roots"] == fresh["K_cubic_all_roots"] and saved["status"] == "optimized" and
                len(saved["branches"]) == len(fresh["branches"]), "primary_source_inventory_or_complete_root_cover_changed")
        for key in cal_spec["four_box_axes_order"]:
            require(F(fresh["input"][key]) == F(canonical_point["inputs"][key]), "public_tuple_roles_disagree")
        require(fresh["input"]["allocation"] == canonical_point["allocation"], "allocation_or_override_role_changed")
        q = F(canonical_point["inputs"]["pair_probability"])
        if q not in gains:
            gains[q] = IND.gain_from_pair_probability(q, cal_spec["reference_pump_beta_deg"])
        gain = gains[q]
        roots, root_certificate = IND.k_inverse(gain["n_grid"], canonical_point["inputs"]["K_A"],
                                               canonical_point["inputs"]["K_B"], cal_spec["background_per_pulse"])
        require(root_certificate["all_real_root_count"] == fresh["K_cubic_all_roots"]["all_real_distinct_root_count"] and
                root_certificate["physical_root_count"] == fresh["K_cubic_all_roots"]["legal_root_count"], "independent_complete_root_cover_disagrees")
        require([F(x) for x in root_certificate["polynomial"]] ==
                [F(x) for x in fresh["K_cubic_all_roots"]["polynomial"]] and
                all(distance(a["interval"], b) == 0 for a, b in
                    zip(fresh["K_cubic_all_roots"]["roots"], root_certificate["root_intervals"])),
                "same_input_complete_cubic_roots_disagree")
        regenerated_i = {}
        for root in roots:
            current = {**gain, "TA": root["TA"], "TB": root["TB"], "allocation": canonical_point["allocation"],
                       "source_id": canonical_point["point_id"] + "/root" + str(root["root_index"])}
            current["c"], _ = IND.coherence_inverse(symbolic, gain["n"], current["TA"], current["TB"],
                canonical_point["inputs"]["DA_raw_visibility"], canonical_point["allocation"], cal_spec)
            regenerated_i[root["root_index"]] = current
        branch_rows = []
        for fresh_branch, saved_branch, rebuilt_branch in zip(fresh["branches"], saved["branches"], checked_p["branches"]):
            index = fresh_branch["root_index"]
            require(saved_branch["root_index"] == index and saved_branch["calibration_branch_status"] == fresh_branch["status"],
                    "calibration_branch_identity_changed")
            if fresh_branch["status"] == "outside_physical_domain":
                require(saved_branch["status"] == "outside_physical_domain", "discarded_or_admitted_illegal_root")
                continue
            require(fresh_branch["status"] == "source_generated_with_complete_raw_fringe_certificates" and
                    saved_branch["status"] == "optimized" and index in regenerated_i, "legal_source_branch_not_completed")
            own = fresh_branch["source"]
            require(saved_branch["source"] == own, "saved_primary_forward_source_changed")
            require(F(own["G_grid"]) == gain["G"] and F(own["n_grid"]) == gain["n_grid"],
                    "different_unique_gain_or_balanced_number_grid")
            generated = regenerated_i[index]
            packet = IND.source_as_json(generated)
            foreign = completed_i[generated["source_id"]]
            require(foreign["source_parameters"] == packet and foreign["point_id"] == canonical_point["point_id"] and
                    foreign["inputs"] == canonical_point["inputs"] and foreign["allocation"] == canonical_point["allocation"] and
                    foreign["calibration_root_branch"] == "root" + str(index), "saved_independent_forward_source_changed")
            psearch = primary_search(saved_branch, own, background, spec)
            model, icontrol, isearch = independent_search(foreign, packet, cal_spec["background_per_pulse"], spec,
                                                         original_i[generated["source_id"]])
            pcontrol = saved_branch["selected_control_degrees"]
            native = primary.native_readout(own, pcontrol, background)
            require(native == saved_branch["native_final_readout"] and saved_branch["five_components"] ==
                    {"r": native["r_one_pair"], "angles_deg": pcontrol[1:]}, "primary_final_native_readout_not_rebuilt")
            require(CAL.close_to(primary.interval(native["native_CH_N1"]), F(str(saved_branch["stable_raw_CH_N1"]))),
                    "primary_final_stable_score_wrong")
            own_ind_readback = independent.source_validation(packet, icontrol, model, spec, cal_spec)
            require(own_ind_readback == foreign["source_validation"], "independent_coherent_Born_final_readout_not_rebuilt")
            independent_rebuilt[generated["source_id"]]["optimum"]["r_one_pair"] = str(model.r_one_pair(icontrol[0]))
            delta = {"r": close(native["r_one_pair"], point_packet(model.r_one_pair(icontrol[0])), spec["tolerance"]["r"],
                                 "independent_pair_ratio_disagrees"),
                     "CH": close(native["native_CH_N1"], point_packet(model.score(icontrol)), spec["tolerance"]["CH_abs"],
                                  "independent_objective_disagrees")}
            for key, a, b in zip(COMPONENTS[1:], pcontrol[1:], icontrol[1:]):
                d = F(str(abs(independent.wrap(a - b))))
                require(d <= F(spec["tolerance"]["angle_deg"]), "independent_receiver_angle_disagrees:" + key)
                delta[key] = d
            shared_rows = []
            same_source = shared_source(own)
            for producer, controls in (("primary", pcontrol), ("independent", icontrol)):
                same_native = native if producer == "primary" else primary.native_readout(own, controls, background)
                same_born = born_readout(same_source, controls, cal_spec["background_per_pulse"])
                outer = probability_cross(same_native, same_born, spec["source_readout_tolerance"])
                require(outer == 0, "same_regenerated_source_native_and_Fock_enclosures_disjoint")
                shared_rows.append({"controls_from": producer, "controls_deg": controls,
                                    "whole_source_brackets_transported": True, "outcome_CH_ratio_outer_distance": str(outer),
                                    "native_CH_N1": same_native["native_CH_N1"], "Fock_CH_N1": same_born["native_CH_N1"],
                                    "native_CH_N5": same_native["diagnostic_CH_N5"], "Fock_CH_N5": same_born["diagnostic_CH_N5"],
                                    "cells": same_born["cells"]})
            rebuilt_branch["native_final_readout"] = native
            rebuilt_branch["five_components"]["r"] = native["r_one_pair"]
            gain_difference = distance(own["G"], point_packet(gain["G"]))
            branch_rows.append({"root_index": index, "independent_source_id": generated["source_id"],
                "primary_search": psearch, "independent_search": isearch,
                "source_forward_coordinates": {"primary_G": own["G"], "independent_G_grid15": str(gain["G"]),
                    "grid_gain_outer_distance": str(gain_difference), "same_exact_G_coordinate_claimed": False,
                    "primary_c": own["c"], "independent_c": packet["c"]},
                "optimum_component_absolute_differences": {k: str(v) for k, v in delta.items()},
                "native_and_independent_Born_saved_readbacks_reproduced": True, "shared_source_readbacks": shared_rows})
        require(len(branch_rows) == len(roots), "legal_source_branch_lost_in_cross_consumer")
        rows.append({"primary_id": fresh["id"], "independent_id": canonical_point["point_id"],
                     "allocation": canonical_point["allocation"], "default_source": number < 17,
                     "all_real_root_count": root_certificate["all_real_root_count"],
                     "all_legal_root_count": len(roots), "source_branches": branch_rows})
        print(json.dumps({"verified_point": fresh["id"], "legal_branches": len(branch_rows)}), flush=True)
    require(set(completed_i) == {b["independent_source_id"] for row in rows for b in row["source_branches"]},
            "extra_or_missing_independent_source_branch")
    # Printed controls are consumed after all regenerated source and probability computations.
    comparison = primary.comparisons(verified_p, spec)
    require(comparison == original["comparison"], "primary_five_component_band_not_rebuilt")
    instrument, instrument_binding = independent.read_documented(spec)
    cases = independent.bands_and_comparisons(verified_i, independent.documented_values(instrument), spec)
    require(cases == completed["cases"], "independent_five_component_band_not_rebuilt")
    model_verdicts, default_comparisons = {}, []
    for row in comparison["models_and_branches"]:
        key = row["allocation"] + "/root" + str(row["root_index"])
        require(key in cases and cases[key]["point_count"] == row["point_count"], "model_or_override_band_identity_changed")
        foreign = cases[key]
        checks = []
        for index, (check, other) in enumerate(zip(row["comparisons"], foreign["comparisons"])):
            band = row["bands"][index]
            require(check["inside"] is other["inside"] and F(check["documented_value"]) == F(other["documented_value"]),
                    "five_component_verdicts_disagree")
            close(band, foreign["band"][INDEPENDENT_COMPONENTS[index]],
                  spec["tolerance"]["r" if index == 0 else "angle_deg"], "optimum_bands_disagree")
            checks.append({"name": COMPONENTS[index], "documented": check["documented_value"], "band": band,
                           "inside": check["inside"]})
        verdict = band_verdict(checks)
        require(verdict == row["status"] and foreign["verdict"] == "REPLAY_" +
                ("CONSISTENT_WITH_PREDECLARED_BAND" if verdict == "CONSISTENT" else "DEVIATION_EXCEEDS_PREDECLARED_BAND"),
                "forged_default_or_override_verdict")
        model_verdicts[key] = {"verdict": verdict, "point_count": row["point_count"],
                               "included_in_default_band": row["included_in_default_band"], "comparison": checks}
        if row["included_in_default_band"]:
            require(not default_comparisons, "multiple_default_branches_require_explicit_disposition")
            default_comparisons = checks
    require(default_comparisons and len(model_verdicts) == 3, "missing_default_or_override_model")
    verdict = band_verdict(default_comparisons)
    require(comparison["default_verdict"] == verdict, "default_verdict_changed")
    return {"schema": SCHEMA, "scientific_model_id": MODEL, "numerical_revision": REVISION,
        "status": "verified", "evidence_valid": True, "verified": verdict == "CONSISTENT", "default_verdict": verdict,
        "numeric_outcome": "REPLAY_" + ("CONSISTENT_WITH_PREDECLARED_BAND" if verdict == "CONSISTENT" else "DEVIATION_EXCEEDS_PREDECLARED_BAND"),
        "default_box_points_verified": 17, "total_source_points_verified": 19,
        "documented_values_in_band": sum(row["inside"] for row in default_comparisons),
        "default_comparison": default_comparisons, "per_model_verdicts": model_verdicts,
        "bindings": {**bindings, "verification_program": program, "numeric_criterion": numeric_binding,
                     "original_primary_first": pbind, "original_independent_first": ibind,
                     "independent_completion_first": cbind, "calibration_certificates": certificates,
                     "documented_values": instrument_binding},
        "criterion_freeze": primary.CONTRACT_COMMIT, "completion_lineage": lineage, "source_rows": rows,
        "primary_native_and_independent_Born_final_points_recomputed": 19,
        "shared_source_four_cell_readouts": 38, "shared_source_setting_cell_count": 152,
        "complete_N1_and_N5_outcome_windows_recomputed": 304,
        "frozen_public_inputs_regenerated_before_comparing_saved_source_fields": True,
        "foreign_saved_source_parameters_or_probabilities_used_as_forward_inputs": False,
        "native_unrounded_G_and_independent_G_grid_kept_distinct": True,
        "override_bands_combined_with_default": False, "original_unresolved_first_preserved": True,
        "actual_matched_calibration_Born_kernel_certification_consumed": True,
        "production_eligible": production, "synthetic_receipt_used": False,
        "actual_publication_configuration_identified": False, "global_argmax_kernel_proof": False,
        "new_full_Born_or_general_Gaussian_determinant_kernel_claim": False,
        "controller_advance": False, "event_files_read": 0, "retrospective": True,
        "runtime_seconds": time.monotonic() - start}


def verify(report_dir=None, enabled=True):
    production = report_dir is None
    base = {"schema": SCHEMA, "scientific_model_id": MODEL, "numerical_revision": REVISION,
            "evidence_valid": False, "verified": False, "production_eligible": False,
            "actual_publication_configuration_identified": False, "global_argmax_kernel_proof": False,
            "new_full_Born_or_general_Gaussian_determinant_kernel_claim": False, "controller_advance": False,
            "event_files_read": 0}
    if enabled is False:
        return {**base, "status": "disabled_by_override", "reason": "nominal_environment_replay_disabled"}
    if enabled is not True:
        return {**base, "status": "rejected", "reason": "numeric_enable_boolean"}
    try:
        return _verify(HERE if report_dir is None else Path(report_dir).resolve(), production)
    except (ValueError, KeyError, TypeError, OSError, subprocess.SubprocessError) as error:
        return {**base, "status": "rejected", "reason": str(error)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report-dir", type=Path)
    parser.add_argument("--disable", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    require(not args.output.exists(), "protected_existing_r6_verification_receipt")
    result = verify(args.report_dir, enabled=not args.disable)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True, allow_nan=False) + "\n")
    print(json.dumps({"status": result["status"], "evidence_valid": result["evidence_valid"],
                      "verified": result["verified"], "default_verdict": result.get("default_verdict"),
                      "output": str(args.output), "sha256": A.digest(args.output)}))
    return 0 if result["evidence_valid"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
