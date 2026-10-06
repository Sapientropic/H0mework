#!/usr/bin/env python3
"""Frozen-source five-control nominal CH replay; comparisons follow all searches."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import itertools
import json
import math
from pathlib import Path
import re
import subprocess
import time

import calibration_source as calibration
import stable_counts

HERE, ROOT = calibration.HERE, calibration.ROOT
NOMINAL = HERE.parents[1]
ARITHMETIC = calibration.arithmetic
I, C, require = calibration.I, calibration.C, calibration.require
VERSION = "nominal-environment-replay-r0006"
CONTRACT_COMMIT = "026102bf0c"
TOL = F("1e-12")
FALSE_FLAGS = ("actual_publication_configuration_identified", "global_argmax_kernel_proof",
               "new_full_Born_or_Gaussian_determinant_kernel_claim", "controller_advance")


def interval(packet):
    return I(F(packet["exact_lower"]), F(packet["exact_upper"]))


def midpoint(packet):
    bounds = interval(packet)
    return float((bounds.lo + bounds.hi) / 2)


def wrap_angle(value):
    return (value + 90.0) % 180.0 - 90.0


def wrapped(control):
    return (control[0], *(wrap_angle(v) for v in control[1:]))


def canonical(control):
    control = wrapped(control)
    return (control[0], *(-v for v in control[1:])) if control[1] < 0 else control


def inputs():
    program = ARITHMETIC.frozen(__file__)
    criterion_path = NOMINAL / "criterion-r0006.md"
    criterion = ARITHMETIC.frozen(criterion_path, CONTRACT_COMMIT)
    subprocess.run(["git", "merge-base", "--is-ancestor", CONTRACT_COMMIT, program["commit"]],
                   cwd=ROOT, check=True)
    text = criterion_path.read_text()
    blocks = re.findall(r"```json\s*(.*?)\s*```", text, re.S)
    require(len(blocks) == 1, "nonunique_r0006_criterion")
    config = json.loads(blocks[0])
    require(config["criterion_version"] == VERSION and config["status"] == "frozen_before_execution" and
            config["objective"] == "raw_CH_LHS_minus_RHS" and config["objective_pulses"] == 1 and
            config["source_gain_update"] == "fixed_G_times_cos_sin_beta" and
            config["receiver_angle_degrees_of_freedom"] == 4 and
            all(config[k] is False for k in FALSE_FLAGS), "r0006_source_or_objective_scope_changed")
    bindings = {}
    for relative in config["input_sources"]:
        path = NOMINAL / relative
        bindings[relative] = ARITHMETIC.frozen(path)
    for name in ("calibration_source.py", "counts.py", "stable_counts.py", "calibration-primary.json"):
        bindings[name] = ARITHMETIC.frozen(HERE / name)
    source = json.loads((HERE / "calibration-primary.json").read_text())
    require(source["version"] == config["calibration_version"] and len(source["points"]) == 19 and
            source["default_point_count"] == 17 and source["all_branches_and_unresolved_points_retained"] is True,
            "incomplete_primary_calibration_inventory")
    require(source["old_scalar_inverse_gain_or_published_controls_admitted"] is False and
            source["CH_optimization_executed"] is False, "calibration_source_uses_forbidden_controls")
    source_config, _, _, _ = calibration.inputs()
    background = tuple(float(F(x)) for x in source_config["background_per_pulse"])
    return config, source, background, {"criterion": criterion, "program": program, "inputs": bindings}


class Objective:
    def __init__(self, source, background):
        self.source, self.background = source, background
        self.gain, self.ta, self.tb, self.c = (midpoint(source[k]) for k in ("G", "TA", "TB", "c"))
        self.allocation = source["allocation"]
        self.trace = []
        self.stage = ""

    def __call__(self, proposed):
        control = wrapped(proposed)
        if not 0 <= control[0] <= 45:
            self.trace.append([self.stage, *control, None])
            return -math.inf
        source = stable_counts.nominal(self.gain, self.ta, self.tb, self.c, control[0],
                                       allocation=self.allocation, background=self.background)
        score = stable_counts.raw_ch(source, control[1:], 1)
        self.trace.append([self.stage, *control, score])
        return score


def ranked(entries):
    return sorted(entries, key=lambda item: (-item[1], tuple(item[0])))


def simplex_search(objective, seed, config):
    step = float(F(config["simplex_step_deg"]))
    points = [wrapped(seed)]
    for axis in range(5):
        point = list(seed); point[axis] += step
        if axis == 0 and point[axis] > 45:
            point[axis] = seed[axis] - step
        points.append(wrapped(point))
    entries = [(point, objective(point)) for point in points]
    stop = "iteration_cap"
    for iteration in range(config["iterations"]):
        entries = ranked(entries)
        best, worst = entries[0], entries[-1]
        diameter = max(abs(a - b) for point, _ in entries for a, b in zip(point, best[0]))
        if diameter <= float(F(config["diameter_stop_deg"])):
            stop = "simplex_diameter"; break
        centroid = tuple(sum(point[i] for point, _ in entries[:-1]) / 5 for i in range(5))
        reflection = wrapped(tuple(2 * a - b for a, b in zip(centroid, worst[0])))
        reflected = objective(reflection)
        if reflected > best[1]:
            expansion = wrapped(tuple(a + 2 * (b - a) for a, b in zip(centroid, reflection)))
            expanded = objective(expansion)
            entries[-1] = (expansion, expanded) if expanded > reflected else (reflection, reflected)
        elif reflected > entries[-2][1]:
            entries[-1] = (reflection, reflected)
        else:
            outside = reflected > worst[1]
            target = reflection if outside else worst[0]
            contraction = wrapped(tuple(a + .5 * (b - a) for a, b in zip(centroid, target)))
            contracted = objective(contraction)
            if contracted > (reflected if outside else worst[1]):
                entries[-1] = (contraction, contracted)
            else:
                entries = [best] + [(wrapped(tuple(a + .5 * (b - a) for a, b in zip(best[0], p))), 0)
                                  for p, _ in entries[1:]]
                entries = [best] + [(point, objective(point)) for point, _ in entries[1:]]
    entries = ranked(entries)
    best = entries[0]
    diameter = max(abs(a - b) for point, _ in entries for a, b in zip(point, best[0]))
    return best[0], best[1], {"seed": list(seed), "iterations": iteration + 1,
        "stop_reason": stop, "final_diameter_deg": diameter,
        "final_simplex": [[list(p), s if math.isfinite(s) else None] for p, s in entries]}


def neighbor_refine(objective, control, score, config):
    levels = []
    for level in range(config["halving_levels"]):
        step = float(F(config["neighbor_step_deg"])) / (2 ** level)
        accepted = 0
        for _ in range(config["accepted_moves_per_level"]):
            neighbors = []
            for axis in range(5):
                for sign in (-1, 1):
                    point = list(control); point[axis] += sign * step
                    point = wrapped(point)
                    neighbors.append((point, objective(point)))
            candidate, value = ranked(neighbors)[0]
            if value > score:
                control, score = candidate, value; accepted += 1
            else:
                break
        levels.append({"level": level, "step_deg": step, "accepted_moves": accepted,
                       "stop_reason": "accepted_move_cap" if accepted == config["accepted_moves_per_level"]
                                      else "no_strictly_improving_neighbor"})
    return control, score, levels


def search(source, background, config, center_seed=None):
    objective = Objective(source, background)
    spec = config["primary_optimizer"]
    objective.stage = "grid"
    grid = list(itertools.product(spec["pump_grid_deg"], spec["angle0_grid_deg"],
                 spec["angle1_grid_deg"], spec["angle0_grid_deg"], spec["angle1_grid_deg"]))
    require(len(grid) == 1024, "r0006_grid_cardinality_changed")
    seeds = ranked([(wrapped(point), objective(point)) for point in grid])[:spec["keep"]]
    if center_seed is not None:
        seeds.append((tuple(center_seed), objective(center_seed)))
    candidates = []
    for index, (seed, _) in enumerate(seeds):
        objective.stage = "Nelder_Mead_%d" % index
        control, score, stop = simplex_search(objective, seed, spec)
        candidates.append({"control": list(control), "raw_CH": score, "simplex": stop})
    best = min(candidates, key=lambda row: (-row["raw_CH"], tuple(row["control"])))
    objective.stage = "ten_neighbors"
    control, score, levels = neighbor_refine(objective, tuple(best["control"]), best["raw_CH"], spec)
    result = canonical(control)
    objective.stage = "canonical_readback"
    canonical_score = objective(result)
    require(abs(canonical_score - score) <= float(F(config["tolerance"]["CH_abs"])),
            "simultaneous_sign_canonicalization_changed_CH")
    completed = all(c["simplex"]["stop_reason"] == "simplex_diameter" for c in candidates)
    return result, canonical_score, {"grid_count": len(grid), "grid_seeds": [[list(p), s] for p, s in seeds],
        "all_optimized_start_candidates": candidates, "neighbor_levels": levels,
        "all_candidate_scores": objective.trace, "score_trace_coordinate_order": ["stage", "beta", "a0", "a1", "b0", "b1", "raw_CH"],
        "completed_prescribed_search": completed, "published_controls_read_before_search": False}


def native_readout(source, control, background):
    gain, ta, tb, c = (interval(source[k]) for k in ("G", "TA", "TB", "c"))
    beta = F(str(control[0]))
    physical = calibration.drive_source(gain, beta)
    ba, bb = (F(str(v)) for v in background)
    angles = tuple(F(str(v)) for v in control[1:])
    cells = []
    for a, b in itertools.product(angles[:2], angles[2:]):
        pulse, outcomes = calibration.native_forward(physical["tH"], physical["tV"], ta, tb, c,
                            source["allocation"], a, b, ba, bb)
        row = {"angles_deg": [str(a), str(b)], "pulse_no_click": {k: v.packet() for k, v in pulse.items()},
               "windows": {"1": {k: v.packet() for k, v in outcomes.items()}}}
        n5 = ARITHMETIC.window(pulse, 5)
        row["windows"]["5"] = {k: v.packet() for k, v in n5.items()}
        row["_N1"], row["_N5"] = outcomes, n5
        cells.append(row)
    ch = {}
    for n, key in ((1, "_N1"), (5, "_N5")):
        values = [row[key] for row in cells]
        sa = values[0]["++"] + values[0]["+0"]
        sb = values[0]["++"] + values[0]["0+"]
        ch[str(n)] = values[0]["++"] + values[1]["++"] + values[2]["++"] - values[3]["++"] - sa - sb
    for row in cells:
        del row["_N1"], row["_N5"]
    r = calibration.hyperbolic(physical["gV"]) / calibration.hyperbolic(physical["gH"])
    require(r.width <= TOL and ch["1"].width <= TOL, "native_final_interval_width_unresolved")
    return {"source_control": {"beta_deg": str(beta), "G": gain.packet(),
                "gH": physical["gH"].packet(), "gV": physical["gV"].packet(),
                "tH": physical["tH"].packet(), "tV": physical["tV"].packet(), "Z": physical["Z"].packet(),
                "source_phase": ["1", "0"], "G_environment_and_losses_held_fixed": True},
            "r_one_pair": r.packet(), "native_CH_N1": ch["1"].packet(), "diagnostic_CH_N5": ch["5"].packet(),
            "cells": cells, "complete_source_root_brackets_transported": True,
            "N5_entered_search_objective": False}


def optimize_points(source_report, background, config):
    result, centers = [], {}
    for point in source_report["points"]:
        row = {"id": point["id"], "input": point["input"],
               "included_in_default_source_box": point["included_in_default_source_box"],
               "calibration_status": point["status"], "branches": [],
               "calibration_all_roots": point.get("K_cubic_all_roots")}
        for branch in point["branches"]:
            outcome = {"root_index": branch["root_index"], "calibration_branch_status": branch["status"],
                       "calibration_a_root_interval": branch.get("a")}
            row["branches"].append(outcome)
            if branch["status"] == "outside_physical_domain":
                outcome["status"] = "outside_physical_domain"; continue
            if branch["status"] != "source_generated_with_complete_raw_fringe_certificates":
                outcome["status"] = "UNRESOLVED"; continue
            source = branch["source"]
            outcome["source"] = source
            warm = centers.get(source["allocation"]) if point["id"] != "center" else None
            control, score, history = search(source, background, config, warm)
            outcome.update(selected_control_degrees=list(control), stable_raw_CH_N1=score, search=history)
            try:
                native = native_readout(source, control, background)
                ch = interval(native["native_CH_N1"])
                require(calibration.close_to(ch, F(str(score))), "stable_candidate_native_readout_disagrees")
                stable = stable_counts.nominal(*(midpoint(source[k]) for k in ("G", "TA", "TB", "c")),
                    control[0], allocation=source["allocation"], background=background)
                largest = 0.0
                for cell, (a, b) in zip(native["cells"], itertools.product(control[1:3], control[3:5])):
                    for n in (1, 5):
                        fast = stable.probabilities(a, b, n)
                        for label, packet in cell["windows"][str(n)].items():
                            value = interval(packet)
                            largest = max(largest, float(value.lo) - fast["outcomes"][label],
                                          fast["outcomes"][label] - float(value.hi))
                require(largest <= float(TOL), "stable_final_complete_outcomes_disagree_with_native")
            except (ValueError, ArithmeticError) as error:
                outcome.update(status="UNRESOLVED", reason=str(error),
                               mathematical_details=getattr(error, "details", None))
                continue
            outcome.update(status="optimized" if history["completed_prescribed_search"] else "UNRESOLVED",
                source=source, selected_control_degrees=list(control), stable_raw_CH_N1=score,
                native_final_readout=native, search=history,
                stable_native_probability_max_distance=largest,
                five_components={"r": native["r_one_pair"], "angles_deg": list(control[1:])})
            if point["id"] == "center":
                centers[source["allocation"]] = control
        row["status"] = "optimized" if point["status"] == "source_generated" and row["branches"] and all(
            b["status"] in ("optimized", "outside_physical_domain") for b in row["branches"]) else "UNRESOLVED"
        result.append(row)
        print(json.dumps({"point": point["id"], "status": row["status"],
                          "searches": sum(b["status"] == "optimized" for b in row["branches"])}), flush=True)
    return result


def documented(config):
    path = (NOMINAL / config["documented_values_source"]).resolve()
    freeze = ARITHMETIC.frozen(path)
    instrument = json.loads(path.read_text())
    return instrument, freeze


def comparisons(points, config):
    instrument, instrument_freeze = documented(config)
    # The original instrument is parsed only after every optimization and native readback.
    require(instrument["revision"] == "r0003-NIST-design" and
            instrument["preparation"]["normalization"] == "radial" and
            instrument["preparation"]["basis_order"] == ["V", "H"] and
            instrument["controls"]["angle_reference"] == "vertical_polarizer_degrees" and
            instrument["controls"]["setting_bits"] == {"0": "unprimed", "1": "primed"},
            "instrument_preparation_or_setting_role_changed")
    amplitudes = instrument["preparation"]["amplitudes"]
    require(set(amplitudes) == {"HH", "VV"} and all(type(x) is str for x in amplitudes.values()),
            "instrument_HH_VV_role_missing")
    documented_r = F(amplitudes["VV"]) / F(amplitudes["HH"])
    alice, bob = instrument["controls"]["alice"], instrument["controls"]["bob"]
    require(type(alice) is list and type(bob) is list and len(alice) == len(bob) == 2 and
            all(type(x) is str for x in (*alice, *bob)), "instrument_receiver_role_missing")
    targets = [documented_r, *map(F, (*alice, *bob))]
    rows = []
    for allocation in (config["production_allocation"], *config["center_allocation_overrides"]):
        eligible = [p for p in points if p["input"]["allocation"] == allocation and
                    (p["included_in_default_source_box"] if allocation == config["production_allocation"] else True)]
        root_indices = sorted({b["root_index"] for p in eligible for b in p["branches"] if b["status"] == "optimized"})
        expected = 17 if allocation == config["production_allocation"] else 1
        for root_index in root_indices:
            members = [b for p in eligible for b in p["branches"] if b["root_index"] == root_index and b["status"] == "optimized"]
            if len(members) != expected or any(p["status"] != "optimized" for p in eligible):
                rows.append({"allocation": allocation, "root_index": root_index, "status": "UNRESOLVED"}); continue
            bands, checks = [], []
            for index, target in enumerate(targets):
                values = ([interval(m["five_components"]["r"]) for m in members] if index == 0 else
                          [I(F(str(m["five_components"]["angles_deg"][index - 1]))) for m in members])
                widen = F(config["band"]["r_widen"] if index == 0 else config["band"]["angle_widen_deg"])
                band = I(min(x.lo for x in values) - widen, max(x.hi for x in values) + widen)
                bands.append(band.packet())
                checks.append({"component": ("r", "a0", "a1", "b0", "b1")[index],
                               "documented_value": str(target), "inside": band.contains(target)})
            rows.append({"allocation": allocation, "root_index": root_index,
                "included_in_default_band": allocation == config["production_allocation"],
                "point_count": len(members), "bands": bands, "comparisons": checks,
                "status": "CONSISTENT" if all(c["inside"] for c in checks) else "DEVIATION"})
    default_rows = [r for r in rows if r.get("included_in_default_band")]
    status = ("UNRESOLVED" if len(points) != 19 or any(p["status"] != "optimized" for p in points) or not default_rows else
              "CONSISTENT" if any(r["status"] == "CONSISTENT" for r in default_rows) else "DEVIATION")
    return {"documented_values": [str(x) for x in targets], "instrument_freeze": instrument_freeze,
            "models_and_branches": rows, "default_verdict": status,
            "override_bands_combined_with_default": False, "documented_values_used_only_after_all_optimizations": True}


def run():
    start = time.monotonic()
    config, source, background, freeze = inputs()
    points = optimize_points(source, background, config)
    comparison = comparisons(points, config)
    return {"schema": "p23-nominal-environment-replay/v1", "criterion_version": VERSION,
        "status": "complete" if comparison["default_verdict"] != "UNRESOLVED" else "UNRESOLVED",
        "freeze": freeze, "calibration_source_sha256": ARITHMETIC.digest(HERE / "calibration-primary.json"),
        "points": points, "point_count": len(points), "default_point_count": 17,
        "source_gain_update": "fixed_G_times_cos_sin_beta", "objective": "raw_CH_LHS_minus_RHS",
        "objective_pulses": 1, "diagnostic_pulses": 5, "comparison": comparison,
        "independence": {"foreign_new_replay_program_read": False, "foreign_new_replay_output_read": False,
                         "foreign_calibration_fields_used_as_forward_inputs": False, "first_receipt_protected": True},
        **{k: False for k in FALSE_FLAGS}, "apparatus_optimum_verified": False,
        "source_midpoints_used_only_for_candidate_search": True,
        "entire_calibration_brackets_used_for_final_native_readout": True,
        "event_files_read": 0, "retrospective": True, "runtime_seconds": time.monotonic() - start}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=HERE / "replay-r0006.json")
    args = parser.parse_args()
    require(not args.output.exists(), "protected_existing_r0006_first_receipt")
    report = run()
    args.output.write_text(json.dumps(report, separators=(",", ":"), ensure_ascii=False, allow_nan=False) + "\n")
    print(json.dumps({"status": report["status"], "default_verdict": report["comparison"]["default_verdict"],
                      "output": str(args.output), "sha256": ARITHMETIC.digest(args.output)}))


if __name__ == "__main__":
    main()
