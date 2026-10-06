#!/usr/bin/env python3
"""Independent five-coordinate fixed-source search and coherent occupation replay."""
from __future__ import annotations

import argparse
from decimal import Decimal as D, getcontext
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import itertools
import json
import math
from pathlib import Path
import re
import sys
import time

import independent_calibration_source as source

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[1]
ROOT = source.ROOT
FREEZE = "026102bf0c67d25b919e5bca5b2496bd0080f00f"
CALIBRATION_RESULTS = "7de2651e11"
CALIBRATION_PROGRAM = "46eb6cbb22"
CALIBRATION_SHA = "d6ad02e1bdd6e8e19cbf7d46316ef116e1eaab3dafabc022a8011db1022a6325"
PROGRAM_SHA = "65c980d754326cc36eaa2ef5e01bc330efdc67956840f9bb9fe0238eb6262725"
VERSION = "nominal-environment-replay-r0006"
SCHEMA = "nist-nominal-environment-independent-replay/v1"
getcontext().prec = 40


def dec(x):
    if isinstance(x, D):
        return x
    if isinstance(x, F):
        return D(x.numerator) / D(x.denominator)
    return D(str(x))


def interval(packet):
    return source.I(packet["exact_lower"], packet["exact_upper"])


def wrap(degrees):
    return (float(degrees) + 90) % 180 - 90


def canonical(parameters):
    beta, *angles = parameters
    angles = [wrap(x) for x in angles]
    if angles[0] < 0:
        angles = [wrap(-x) for x in angles]
    return [beta, *angles]


def movement(a, b):
    return max(abs(a[0] - b[0]), *(abs(wrap(x - y)) for x, y in zip(a[1:], b[1:])))


@lru_cache(maxsize=16384)
def trig(degrees):
    degrees = dec(degrees)
    pi = dec((source.born.PI[0] + source.born.PI[1]) / 2)
    x = degrees * pi / 180
    xx, sine, cosine, sn, cs = x * x, D(0), D(0), x, D(1)
    for k in range(14):
        sine, cosine = sine + sn, cosine + cs
        sn = -sn * xx / ((2 * k + 2) * (2 * k + 3))
        cs = -cs * xx / ((2 * k + 1) * (2 * k + 2))
    return sine, cosine


class Model:
    def __init__(self, packet, background):
        self.packet = packet
        self.gain = dec(F(packet["G_grid15"]))
        self.ta = dec(interval(packet["transmission_A"]).midpoint())
        self.tb = dec(interval(packet["transmission_B"]).midpoint())
        self.c = dec(interval(packet["c"]).midpoint())
        self.allocation = packet["allocation"]
        if self.allocation == "symmetric":
            self.xa = self.xb = self.c.sqrt()
        elif self.allocation == "Alice_rank_one":
            self.xa, self.xb = D(1), self.c
        else:
            self.xa, self.xb = self.c, D(1)
        self.background = [dec(F(x)) for x in background]
        self.evaluations = 0
        self._geometry = lru_cache(maxsize=4096)(self._geometry_uncached)
        self._effect = lru_cache(maxsize=8192)(self._effect_uncached)

    def _geometry_uncached(self, beta):
        sine, cosine = trig(beta)
        gh, gv = self.gain * cosine, self.gain * sine
        sh = ((gh).exp() - (-gh).exp()) / 2
        sv = ((gv).exp() - (-gv).exp()) / 2
        nh, nv = sh * sh, sv * sv
        paired = (nh * nv * (1 + nh) * (1 + nv)).sqrt()
        return nh, nv, paired

    def _effect_uncached(self, side, degrees):
        sine, cosine = trig(degrees)
        transmission, xi = (self.ta, self.xa) if side == "alice" else (self.tb, self.xb)
        hh = transmission * sine * sine
        vv = transmission * cosine * cosine
        hv = transmission * xi * sine * cosine
        determinant = hh * vv - hv * hv
        return hh, vv, hv, determinant

    @staticmethod
    def local_delta(nh, nv, effect):
        hh, vv, _, determinant = effect
        return nh * hh + nv * vv + nh * nv * determinant

    @staticmethod
    def joint_delta(nh, nv, paired, ea, eb):
        ah, av, ax, ad = ea
        bh, bv, bx, bd = eb
        h = ah + bh - ah * bh
        v = av + bv - av * bv
        da, db = 1 - ah - av + ad, 1 - bh - bv + bd
        return nh * h + nv * v - 2 * paired * ax * bx + nh * nv * (h + v + da * db - 1)

    def rates(self, beta, alice, bob):
        nh, nv, paired = self._geometry(beta)
        ea, eb = self._effect("alice", alice), self._effect("bob", bob)
        a, b = self.local_delta(nh, nv, ea), self.local_delta(nh, nv, eb)
        ab = self.joint_delta(nh, nv, paired, ea, eb)
        sa, sb = a / (1 + a), b / (1 + b)
        # This expansion removes the four unit vacuum terms before rounding.
        joint = (a + b - ab + a * b * (2 + ab)) / ((1 + a) * (1 + b) * (1 + ab))
        ba, bb = self.background
        za, zb = 1 - ba, 1 - bb
        return {"S_A": sa + ba * (1 - sa), "S_B": sb + bb * (1 - sb),
                "J": za * zb * joint + ba * zb * sb + bb * za * sa + ba * bb,
                "signal_J": joint, "signal_S_A": sa, "signal_S_B": sb}

    def score(self, parameters):
        beta, a0, a1, b0, b1 = parameters
        source.require(0 <= beta <= 45, "pump_search_outside_domain")
        self.evaluations += 1
        j00, j01, j10, j11 = [self.rates(beta, a, b) for a, b in ((a0, b0), (a0, b1), (a1, b0), (a1, b1))]
        return j00["J"] + j01["J"] + j10["J"] - j11["J"] - j00["S_A"] - j00["S_B"]

    def r_one_pair(self, beta):
        sine, cosine = trig(beta)
        gh, gv = self.gain * cosine, self.gain * sine
        eh, ev = (2 * gh).exp(), (2 * gv).exp()
        return ((ev - 1) / (ev + 1)) / ((eh - 1) / (eh + 1))


def load_frozen():
    criterion = BASE / "criterion-r0006.md"
    bindings = {"criterion": source.frozen(criterion, FREEZE), "program": source.frozen(Path(__file__)),
                "calibration_program": source.frozen(HERE / "independent_calibration_source.py", CALIBRATION_PROGRAM),
                "calibration_receipt": source.frozen(HERE / "calibration-independent-r0002.json", CALIBRATION_RESULTS),
                "input_sources": []}
    source.require(bindings["calibration_program"]["sha256"] == PROGRAM_SHA and
                   bindings["calibration_receipt"]["sha256"] == CALIBRATION_SHA, "independent_calibration_binding_changed")
    blocks = re.findall(r"<!-- NOMINAL-ENVIRONMENT-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- NOMINAL-ENVIRONMENT-FROZEN-END -->",
                        criterion.read_text(), re.S)
    source.require(len(blocks) == 1, "ambiguous_environment_replay_contract")
    spec = json.loads(blocks[0])
    source.require(spec["criterion_version"] == VERSION and spec["objective_pulses"] == 1 and spec["diagnostic_pulses"] == 5 and
                   spec["pump_domain_deg"] == ["0", "45"] and spec["receiver_coordinate_order"] == ["a0", "a1", "b0", "b1"] and
                   spec["prefix_renormalized"] is False and spec["total_pair_prefix"] == 6, "environment_replay_method_changed")
    method = spec["independent_optimizer"]
    source.require(method == {"pump_grid_deg": [8,16,24,32,40], "angle0_grid_deg": [-10,-2,2,10],
                               "angle1_grid_deg": [-34,-22,22,34], "keep": 8, "axis_grid_step_deg": "6",
                               "coordinate_cycles": 80, "golden_steps": 80, "coordinate_stop_deg": "1e-7"},
                   "independent_optimizer_contract_changed")
    for flag in ("actual_publication_configuration_identified", "global_argmax_kernel_proof",
                 "new_full_Born_or_Gaussian_determinant_kernel_claim", "controller_advance"):
        source.require(spec[flag] is False, "replay_authority_changed")
    for path in spec["input_sources"]:
        bindings["input_sources"].append(source.frozen(BASE / path, FREEZE))
    cal_spec, cal_bindings, units = source.load_frozen()
    bindings["calibration_source_inputs"] = cal_bindings
    calibration = json.loads((HERE / "calibration-independent-r0002.json").read_text())
    source.require(calibration["passed"] is True and calibration["version"] == spec["calibration_version"] and
                   len(calibration["rows"]) == spec["total_points_with_overrides"] == 19, "independent_calibration_incomplete")
    return spec, cal_spec, calibration, bindings, units


def coarse_grid(model, method):
    grid = itertools.product(method["pump_grid_deg"], method["angle0_grid_deg"], method["angle1_grid_deg"],
                             method["angle0_grid_deg"], method["angle1_grid_deg"])
    scored = [(model.score(list(point)), list(point)) for point in grid]
    source.require(len(scored) == 1280, "incomplete_independent_coarse_grid")
    scored.sort(key=lambda row: (-row[0], tuple(row[1])))
    logical = [[str(score), point] for score, point in scored]
    return scored[:method["keep"]], {"point_count": len(scored),
                                    "all_scores_sha256": hashlib.sha256(json.dumps(logical, separators=(",", ":")).encode()).hexdigest(),
                                    "retained": [{"coordinates_deg": point, "CH_decimal": str(score)} for score, point in scored[:method["keep"]]]}


def axis_optimize(model, parameters, axis, method):
    step = float(method["axis_grid_step_deg"])
    if axis == 0:
        grid = [step * k for k in range(int(45 // step) + 1)]
        if grid[-1] != 45:
            grid.append(45.0)
    else:
        grid = [-90 + step * k for k in range(int(180 / step))]
    def value(position):
        point = list(parameters)
        point[axis] = position if axis == 0 else wrap(position)
        return model.score(point)
    samples = [(value(position), position, index) for index, position in enumerate(grid)]
    best_score, best_position, best_index = min(samples, key=lambda row: (-row[0], row[1]))
    if axis == 0:
        lo = grid[max(0, best_index - 1)]
        hi = grid[min(len(grid) - 1, best_index + 1)]
    else:
        lo, hi = best_position - step, best_position + step
    initial = [lo, hi]
    phi = float((D(5).sqrt() - 1) / 2)
    left, right = hi - phi * (hi - lo), lo + phi * (hi - lo)
    lv, rv = value(left), value(right)
    steps = 0
    tolerance = float(method["coordinate_stop_deg"])
    for steps in range(method["golden_steps"]):
        if hi - lo <= tolerance:
            break
        if lv >= rv:
            hi, right, rv = right, left, lv
            left = hi - phi * (hi - lo)
            lv = value(left)
        else:
            lo, left, lv = left, right, rv
            right = lo + phi * (hi - lo)
            rv = value(right)
    options = [(value(parameters[axis]), parameters[axis]), (best_score, best_position),
               (lv, left), (rv, right), (value((lo + hi) / 2), (lo + hi) / 2)]
    score, position = min(options, key=lambda row: (-row[0], row[1]))
    position = position if axis == 0 else wrap(position)
    return position, {"axis": axis, "scan_count": len(grid), "best_grid_deg": best_position,
                      "initial_bracket_deg": initial, "final_bracket_deg": [lo, hi],
                      "golden_steps": steps + 1, "golden_width_deg": hi - lo,
                      "termination": "width_stop" if hi - lo <= tolerance else "golden_step_cap",
                      "chosen_deg": position, "CH_decimal": str(score)}


def coordinate_candidate(model, seed, method):
    parameters = list(seed)
    cycles = []
    complete = False
    for cycle in range(method["coordinate_cycles"]):
        before, axes = list(parameters), []
        for axis in range(5):
            parameters[axis], receipt = axis_optimize(model, parameters, axis, method)
            axes.append(receipt)
        changed = movement(before, parameters)
        cycles.append({"cycle": cycle + 1, "coordinates_deg": list(parameters), "movement_deg": changed,
                       "CH_decimal": str(model.score(parameters)),
                       "axis_scan_counts": [row["scan_count"] for row in axes],
                       "axis_golden_steps": [row["golden_steps"] for row in axes],
                       "axis_terminations": [row["termination"] for row in axes]})
        if changed <= float(method["coordinate_stop_deg"]):
            complete = all(row["termination"] == "width_stop" for row in axes)
            break
    parameters = canonical(parameters)
    return {"seed_deg": seed, "coordinates_deg": parameters, "CH_decimal": str(model.score(parameters)),
            "cycles": cycles, "final_axis_searches": axes,
            "termination": "whole_cycle_stop" if complete else "coordinate_cycle_cap",
            "complete": complete}


def source_from_packet(packet):
    return {"G": F(packet["G_grid15"]), "TA": interval(packet["transmission_A"]), "TB": interval(packet["transmission_B"]),
            "c": interval(packet["c"]), "allocation": packet["allocation"], "source_id": packet["source_id"]}


def source_validation(packet, parameters, model, spec, cal_spec):
    beta, a0, a1, b0, b1 = parameters
    actual = source_from_packet(packet)
    raw_packet = source.source_packet(actual, F(str(beta)))
    rows, cells, noclick = [], [], []
    for cell, alice, bob in (("00", a0, b0), ("01", a0, b1), ("10", a1, b0), ("11", a1, b1)):
        effects = [source.environment_effect(raw_packet["T" + side], raw_packet["xi" + side], F(str(angle)))
                   for side, angle in (("A", alice), ("B", bob))]
        actual_born = source.independent_born(raw_packet, effects, spec["total_pair_prefix"], cal_spec["background_per_pulse"])
        actual_det = source.determinant_readout(raw_packet, effects, cal_spec["background_per_pulse"])
        search = model.rates(beta, alice, bob)
        gaps = {key: source.endpoint_gap(actual_born["observed"][key], F(search[key])) for key in ("S_A", "S_B", "J")}
        det_gaps = {key: source.overlap_gap(actual_born["observed"][key], actual_det["observed"][key]) for key in ("S_A", "S_B", "J")}
        source.require(all(value <= F(spec["source_readout_tolerance"]) for value in (*gaps.values(), *det_gaps.values())),
                       "actual_occupation_Born_search_readout_failed")
        cells.append(actual_born["observed"])
        noclick.append(actual_born["no_click"])
        rows.append({"cell": cell, "angles_deg": [alice, bob], "pulse_count": 1,
                     "search_stable_readout": {key: str(search[key]) for key in ("S_A", "S_B", "J")},
                     "actual_Born_observed": {key: value.packet() for key, value in actual_born["observed"].items()},
                     "actual_Born_signal": {key: value.packet() for key, value in actual_born["signal"].items()},
                     "actual_Born_signal_outcomes": {key: value.packet() for key, value in actual_born["signal_outcomes"].items()},
                     "actual_Born_observed_outcomes": {key: value.packet() for key, value in actual_born["observed_outcomes"].items()},
                     "prefix_mass": actual_born["prefix_mass"].packet(), "original_tail": actual_born["tail"].packet(),
                     "total_pair_prefix": 6, "prefix_renormalized": False, "sector_readout": actual_born["sectors"],
                     "search_gap": {key: str(value) for key, value in gaps.items()},
                     "native_determinant_gap": {key: str(value) for key, value in det_gaps.items()}, "passed": True})
    born_ch = cells[0]["J"] + cells[1]["J"] + cells[2]["J"] - cells[3]["J"] - cells[0]["S_A"] - cells[0]["S_B"]
    search_ch = model.score(parameters)
    source.require(source.endpoint_gap(born_ch, F(search_ch)) <= F(spec["tolerance"]["CH_abs"]), "actual_Born_CH_failed")
    ba, bb = [F(value) for value in cal_spec["background_per_pulse"]]
    n5 = [[(zero[0] * (1 - ba)) ** 5, (zero[1] * (1 - bb)) ** 5,
           (zero[2] * (1 - ba) * (1 - bb)) ** 5] for zero in noclick]
    n5_joint = [source.born.outcomes_from_no_click(zero)["++"] for zero in n5]
    n5_ch = n5_joint[0] + n5_joint[1] + n5_joint[2] - n5_joint[3] - (1 - n5[0][0]) - (1 - n5[0][1])
    r = (raw_packet["tV"] / raw_packet["tH"]).sqrt()
    source.require(source.endpoint_gap(r, F(model.r_one_pair(beta))) <= F(spec["tolerance"]["r"]), "one_pair_amplitude_ratio_failed")
    return {"passed": True, "beta_deg": beta, "tH": raw_packet["tH"].packet(), "tV": raw_packet["tV"].packet(),
            "r_one_pair": r.packet(), "source_gain_fixed": str(actual["G"]),
            "CH_Born_enclosure": born_ch.packet(), "CH_search_decimal": str(search_ch),
            "CH_gap": str(source.endpoint_gap(born_ch, F(search_ch))), "cells": rows,
            "N5_diagnostic_rawCH": n5_ch.packet(), "N5_used_for_optimization": False,
            "full_source_coherent_Born_prefix_and_original_tail": True}


def read_documented(spec):
    path = (BASE / spec["documented_values_source"]).resolve()
    binding = source.frozen(path, FREEZE)
    return json.loads(path.read_text()), binding


def documented_values(instrument):
    # Read the physical role structure after every search; no instrument enters the Model.
    state, controls = instrument["preparation"], instrument["controls"]
    source.require(instrument["revision"] == "r0003-NIST-design" and state["normalization"] == "radial" and
                   state["basis_order"] == ["V", "H"] and
                   controls["angle_reference"] == "vertical_polarizer_degrees" and
                   controls["setting_bits"] == {"0": "unprimed", "1": "primed"} and
                   len(controls["alice"]) == len(controls["bob"]) == 2, "instrument_physical_roles_changed")
    amplitudes = state["amplitudes"]
    source.require(F(amplitudes["HH"]) != 0, "zero_documented_HH_amplitude")
    return {"r_one_pair": F(amplitudes["VV"]) / F(amplitudes["HH"]),
            "a0_deg": F(controls["alice"][0]), "a1_deg": F(controls["alice"][1]),
            "b0_deg": F(controls["bob"][0]), "b1_deg": F(controls["bob"][1])}


def bands_and_comparisons(results, documented, spec):
    components = ["r_one_pair", "a0_deg", "a1_deg", "b0_deg", "b1_deg"]
    groups = {}
    for row in results:
        key = row["allocation"] + "/" + row["calibration_root_branch"]
        groups.setdefault(key, []).append(row)
    cases = {}
    for key, rows in groups.items():
        expected = 17 if key.startswith("symmetric/") else 1
        complete = len(rows) == expected and all(row["status"] == "NUMERICAL_SEARCH_COMPLETE" for row in rows)
        if not complete:
            cases[key] = {"verdict": "UNRESOLVED", "point_count": len(rows), "expected_point_count": expected,
                          "point_ids": [row["point_id"] for row in rows], "band": None, "comparisons": []}
            continue
        band, comparisons = {}, []
        for component in components:
            values = [F(str(row["optimum"][component])) for row in rows]
            widen = F(spec["band"]["r_widen"] if component == "r_one_pair" else spec["band"]["angle_widen_deg"])
            lo, hi = min(values) - widen, max(values) + widen
            band[component] = {"exact_lower": str(lo), "exact_upper": str(hi), "lower": float(lo), "upper": float(hi)}
            comparisons.append({"component": component, "documented_value": str(documented[component]),
                                "interval": [str(lo), str(hi)], "inside": lo <= documented[component] <= hi})
        consistent = all(row["inside"] for row in comparisons)
        cases[key] = {"verdict": "REPLAY_CONSISTENT_WITH_PREDECLARED_BAND" if consistent else "REPLAY_DEVIATION_EXCEEDS_PREDECLARED_BAND",
                      "point_count": len(rows), "expected_point_count": expected, "point_ids": [row["point_id"] for row in rows],
                      "band": band, "comparisons": comparisons}
    return cases


def run():
    started = time.time()
    spec, cal_spec, calibration, bindings, units = load_frozen()
    results = []
    for point in calibration["rows"]:
        if point["status"] != "SOURCE_GENERATED":
            results.append({"point_id": point["point_id"], "allocation": point["allocation"], "inputs": point["inputs"],
                            "calibration_root_branch": "unresolved", "status": "UNRESOLVED", "reason": "calibration_incomplete"})
            continue
        for branch in point["sources"]:
            point_started = time.time()
            packet = branch["source"]
            model = Model(packet, cal_spec["background_per_pulse"])
            seeds, coarse = coarse_grid(model, spec["independent_optimizer"])
            candidates = []
            for index, (_, seed) in enumerate(seeds):
                candidate = coordinate_candidate(model, seed, spec["independent_optimizer"])
                candidates.append(candidate)
                print("independent five-axis " + packet["source_id"] + " seed " + str(index + 1) + "/8 " + candidate["termination"],
                      file=sys.stderr, flush=True)
            best = min(candidates, key=lambda row: (-D(row["CH_decimal"]), tuple(row["coordinates_deg"])))
            parameters = best["coordinates_deg"]
            row = {"point_id": point["point_id"], "allocation": point["allocation"], "inputs": point["inputs"],
                   "calibration_root_branch": packet["source_id"].split("/")[-1], "source_id": packet["source_id"],
                   "source_parameters": packet, "coarse_grid": coarse, "candidates": candidates,
                   "optimum": {"beta_deg": parameters[0], "r_one_pair": str(model.r_one_pair(parameters[0])),
                               "a0_deg": parameters[1], "a1_deg": parameters[2], "b0_deg": parameters[3], "b1_deg": parameters[4],
                               "CH": float(D(best["CH_decimal"])), "CH_decimal": best["CH_decimal"]},
                   "elapsed_seconds": time.time() - point_started, "score_evaluations": model.evaluations}
            try:
                row["source_validation"] = source_validation(packet, parameters, model, spec, cal_spec)
                row["status"] = "NUMERICAL_SEARCH_COMPLETE" if best["complete"] else "UNRESOLVED"
                if not best["complete"]:
                    row["reason"] = best["termination"]
            except ValueError as error:
                row["status"] = "UNRESOLVED"
                row["reason"] = str(error)
            results.append(row)
            row["score_evaluations"] = model.evaluations
            print("independent replay " + packet["source_id"] + " " + row["status"], file=sys.stderr, flush=True)
    # The instrument is deliberately loaded only after all point candidates and Born receipts exist.
    instrument, instrument_binding = read_documented(spec)
    bindings["documented_values_source"] = instrument_binding
    documented = documented_values(instrument)
    cases = bands_and_comparisons(results, documented, spec)
    complete = bool(cases) and all(row["verdict"] != "UNRESOLVED" for row in cases.values())
    return {"schema": SCHEMA, "criterion_version": VERSION, "criterion_freeze": FREEZE, "bindings": bindings,
            "calibration_version": cal_spec["version"], "efficiency_unit_readback": units,
            "decimal_precision_digits": 40, "source_readout_tolerance": spec["source_readout_tolerance"],
            "independent_optimizer": spec["independent_optimizer"], "results": results, "cases": cases,
            "numerical_search_complete": complete, "elapsed_seconds": time.time() - started,
            "documented_values_loaded_after_all_candidates": True, "objective_pulses": 1, "diagnostic_pulses": 5,
            "actual_publication_configuration_identified": False, "global_argmax_kernel_proof": False,
            "new_full_Born_or_Gaussian_determinant_kernel_claim": False, "controller_advance": False,
            "retrospective": True, "event_files_read": 0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "independent-replay-r0006.json")
    args = parser.parse_args()
    source.require(not args.output.exists(), "first_independent_replay_receipt_already_exists")
    report = run()
    raw = (json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode()
    args.output.write_bytes(raw)
    print(json.dumps({"path": str(args.output), "sha256": hashlib.sha256(raw).hexdigest(),
                      "numerical_search_complete": report["numerical_search_complete"],
                      "verdicts": {key: value["verdict"] for key, value in report["cases"].items()}}), flush=True)
    return 0 if report["numerical_search_complete"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
