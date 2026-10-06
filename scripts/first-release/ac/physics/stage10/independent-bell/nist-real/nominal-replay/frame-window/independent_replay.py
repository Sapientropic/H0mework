#!/usr/bin/env python3
"""Independent gain-circle and four-receiver-angle Fock replay."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from functools import lru_cache
import itertools
import json
import math
from pathlib import Path
import sys

import independent as science

I = science.I
HERE = Path(__file__).resolve().parent


def atanh_interval(z):
    z = I.of(z)
    science.require(0 <= z.lo <= z.hi < 1, "illegal_raw_gain")
    out, term = I(0), z
    for k in range(1024):
        out += term / (2 * k + 1)
        remainder = z.hi ** (2 * k + 3) / ((2 * k + 3) * (1 - z.hi ** 2))
        if remainder <= F(1, 10 ** 38):
            return out + I(0, remainder)
        term = term * z.square()
    raise ValueError("GAIN_SERIES_UNRESOLVED")


def exp_interval(x):
    x = I.of(x)
    if x.hi <= 0:
        return 1 / exp_interval(-x)
    science.require(0 <= x.lo <= x.hi <= 1, "GAIN_EXP_SERIES_UNRESOLVED")
    out, term = I(1), I(1)
    for k in range(1, 64):
        term = term * x / k
        out += term
    remainder = 3 * x.hi ** 64 / math.factorial(64)
    return out + I(0, remainder)


def gain_norm(packet):
    h, v = [atanh_interval(I(F(x)).sqrt()) for x in packet["geometric_ratio"]]
    return (h.square() + v.square()).sqrt()


def actuator_ratios(gain, balance):
    s, c = science.trig(F(balance))
    h, v = gain * c, gain * s
    def ratio(g):
        exponential = exp_interval(2 * g)
        return ((exponential - 1) / (exponential + 1)).square()
    return ratio(h), ratio(v)


def normalize_angle(x):
    return (x + 90) % 180 - 90


def direction(packet):
    z, x = float(F(packet["rotation"]["Z"])), float(F(packet["rotation"]["X"]))
    return 0.0 if z == x == 0 else math.degrees(math.atan2(x, z)) / 2


def canonical(point, delta):
    angles = [normalize_angle(x) for x in point[1:]]
    relative = [normalize_angle(x - delta) for x in angles]
    reflect = relative[0] < 0 or (relative[0] == 0 and relative[1] < 0)
    if reflect:
        angles = [normalize_angle(2 * delta - x) for x in angles]
    return (point[0], *angles), reflect


class FockObjective:
    def __init__(self, packet, lam, config):
        loss = packet["loss"]
        ta, tb, _ = science.coupled_loss(loss["KA"], loss["KB"], loss["t_cal"])
        self.ta, self.tb = float(ta.interval().midpoint()), float(tb.interval().midpoint())
        self.lam = float(lam.midpoint())
        self.gain_interval = gain_norm(packet)
        self.gain = float(self.gain_interval.midpoint())
        self.delta = direction(packet)
        angle = math.radians(self.delta)
        self.c, self.s = math.cos(angle), math.sin(angle)
        self.config, self.evaluations = config, 0
        self.cache = {}

    @lru_cache(maxsize=1024)
    def pumps(self, balance):
        angle = math.radians(balance)
        th, tv = math.tanh(self.gain * math.cos(angle)) ** 2, math.tanh(self.gain * math.sin(angle)) ** 2
        norm = (1 - th) * (1 - tv)
        pure = science.complete_homogeneous(th + tv, th * tv, self.config["source_pair_cutoff"])
        matrices = []
        for phase in (1, -1):
            zh, zv = math.sqrt(th), phase * math.sqrt(tv)
            matrices.append((self.c * self.c * zh + self.s * self.s * zv,
                             self.c * self.s * (zv - zh),
                             self.s * self.s * zh + self.c * self.c * zv))
        return th, tv, norm, pure, matrices

    def rates(self, point):
        balance, a0, a1, b0, b1 = point
        if not 0 <= balance <= 45:
            return None
        th, tv, norm, pure, matrices = self.pumps(balance)
        va = [(math.sin(math.radians(x)), math.cos(math.radians(x))) for x in (a0, a1)]
        vb = [(math.sin(math.radians(x)), math.cos(math.radians(x))) for x in (b0, b1)]
        branch_rates = []
        for ghh, ghv, gvv in matrices:
            gva = [(ghh * s + ghv * c, ghv * s + gvv * c) for s, c in va]
            gvb = [(ghh * s + ghv * c, ghv * s + gvv * c) for s, c in vb]
            la = [self.ta * (x * x + y * y) for x, y in gva]
            lb = [self.tb * (x * x + y * y) for x, y in gvb]
            pa = [science.complete_homogeneous(th + tv - x, th * tv * (1 - self.ta),
                                              self.config["source_pair_cutoff"]) for x in la]
            pb = [science.complete_homogeneous(th + tv - x, th * tv * (1 - self.tb),
                                              self.config["source_pair_cutoff"]) for x in lb]
            sa = [norm * (la[i] + sum(pure[n] - pa[i][n] for n in range(2, len(pure)))) for i in range(2)]
            sb = [norm * (lb[j] + sum(pure[n] - pb[j][n] for n in range(2, len(pure)))) for j in range(2)]
            joint = []
            for i, j in ((0, 0), (0, 1), (1, 0), (1, 1)):
                coupling = gva[i][0] * vb[j][0] + gva[i][1] * vb[j][1]
                one = self.ta * self.tb * coupling * coupling
                pj = science.complete_homogeneous(th + tv - la[i] - lb[j] + one,
                           th * tv * (1 - self.ta) * (1 - self.tb), self.config["source_pair_cutoff"])
                joint.append(norm * (one + sum(pure[n] - pa[i][n] - pb[j][n] + pj[n]
                                               for n in range(2, len(pure)))))
            branch_rates.append((sa, sb, joint))
        sa = [(1 - self.lam) * branch_rates[0][0][i] + self.lam * branch_rates[1][0][i] for i in range(2)]
        sb = [(1 - self.lam) * branch_rates[0][1][i] + self.lam * branch_rates[1][1][i] for i in range(2)]
        joint = [(1 - self.lam) * branch_rates[0][2][i] + self.lam * branch_rates[1][2][i] for i in range(4)]
        ba, bb = map(lambda x: float(F(x)), self.config["background_per_pulse"])
        n = self.config["window_pulses"]
        oa, ob = [ba + (1 - ba) * x for x in sa], [bb + (1 - bb) * x for x in sb]
        wa = [sum((-1) ** (k + 1) * math.comb(n, k) * x ** k for k in range(1, n + 1)) for x in oa]
        wb = [sum((-1) ** (k + 1) * math.comb(n, k) * x ** k for k in range(1, n + 1)) for x in ob]
        result = []
        for cell, (i, j) in enumerate(((0, 0), (0, 1), (1, 0), (1, 1))):
            p = ((1 - ba) * (1 - bb) * joint[cell] + ba * (1 - bb) * sb[j] +
                 bb * (1 - ba) * sa[i] + ba * bb)
            union = oa[i] + ob[j] - p
            result.append(n * p + sum((-1) ** k * math.comb(n, k) *
                (union ** k - oa[i] ** k - ob[j] ** k) for k in range(2, n + 1)))
        return wa, wb, result

    def __call__(self, point):
        point = (point[0], *(normalize_angle(x) for x in point[1:]))
        if point in self.cache:
            return self.cache[point]
        rates = self.rates(point)
        self.evaluations += 1
        value = -math.inf if rates is None else sum(rates[2][:3]) - rates[2][3] - rates[0][0] - rates[1][0]
        self.cache[point] = value
        return value


def golden(function, left, right, config):
    ratio = (math.sqrt(5) - 1) / 2
    x, y = right - ratio * (right - left), left + ratio * (right - left)
    fx, fy = function(x), function(y)
    for k in range(config["golden_steps"]):
        if right - left <= float(F(config["golden_width_deg"])):
            break
        if fx < fy:
            left, x, fx = x, y, fy
            y = left + ratio * (right - left)
            fy = function(y)
        else:
            right, y, fy = y, x, fx
            x = right - ratio * (right - left)
            fx = function(x)
    return max(((fx, x), (fy, y), (function(left), left), (function(right), right)), key=lambda z: (z[0], -z[1]))[1], k + 1


def coordinate_search(start, objective, config):
    point = tuple(start)
    step = float(F(config["axis_grid_step_deg"]))
    records = []
    for cycle in range(config["cycles"]):
        before = point
        for axis in range(5):
            if axis == 0:
                grid = [i * step for i in range(int(45 // step) + 1)]
                if grid[-1] != 45:
                    grid.append(45.0)
            else:
                grid = [-90 + i * step for i in range(int(180 // step) + 1)]
            def at(value):
                candidate = list(point)
                candidate[axis] = value if axis == 0 else normalize_angle(value + objective.delta)
                return objective(tuple(candidate))
            best = max(range(len(grid)), key=lambda i: (at(grid[i]), -grid[i]))
            lo = max(0.0, grid[best] - step) if axis == 0 else grid[best] - step
            hi = min(45.0, grid[best] + step) if axis == 0 else grid[best] + step
            value, iterations = golden(at, lo, hi, config)
            candidate = list(point)
            candidate[axis] = value if axis == 0 else normalize_angle(value + objective.delta)
            candidate = tuple(candidate)
            if objective(candidate) > objective(point):
                point = candidate
            else:
                candidate = list(point)
                candidate[axis] = grid[best] if axis == 0 else normalize_angle(grid[best] + objective.delta)
                candidate = tuple(candidate)
                if objective(candidate) > objective(point):
                    point = candidate
            records.append({"cycle": cycle, "axis": axis, "golden_steps": iterations})
        displacement = max(abs(point[0] - before[0]), *(abs(normalize_angle(point[i] - before[i])) for i in range(1, 5)))
        if displacement <= float(F(config["update_stop_deg"])):
            return point, {"cycles": cycle + 1, "stop": "coordinate_update", "axis_steps": records}
    return point, {"cycles": config["cycles"], "stop": "cycle_cap", "axis_steps": records}


def optimized(packet, lam, config):
    objective = FockObjective(packet, lam, config)
    settings = config["independent_optimizer"]
    points = []
    for balance, a0, a1, b0, b1 in itertools.product(settings["pump_grid_deg"],
            settings["angle0_grid_deg"], settings["angle1_grid_deg"],
            settings["angle0_grid_deg"], settings["angle1_grid_deg"]):
        point = (float(balance), *(normalize_angle(float(x) + objective.delta) for x in (a0, a1, b0, b1)))
        points.append((objective(point), point))
    starts = sorted(points, key=lambda row: (-row[0], row[1]))[:settings["keep"]]
    completed = []
    for _, start in starts:
        candidate, log = coordinate_search(start, objective, settings)
        representative, reflected = canonical(candidate, objective.delta)
        completed.append((objective(representative), representative,
                          {"start": list(start), "candidate": list(candidate), "canonical_reflection": reflected, **log}))
    score, point, _ = sorted(completed, key=lambda row: (-row[0], row[1]))[0]
    return point, objective, {"coarse_count": len(points), "keep": settings["keep"],
        "completed": [row[2] for row in completed], "evaluations": objective.evaluations,
        "float_CH": score, "local_numeric_search": True, "global_optimum_kernel_proof": False}


def mathematical_point(packet, lam, point, gain, config):
    balance = F(str(point[0]))
    ratios = actuator_ratios(gain, balance)
    controls = [F(str(x)) for x in point[1:]]
    cells = []
    tails = []
    for a, b in ((controls[0], controls[2]), (controls[0], controls[3]),
                 (controls[1], controls[2]), (controls[1], controls[3])):
        no_click, tail = science.pulse(packet, lam, a, b, config["source_pair_cutoff"], ratios)
        cells.append(science.window(no_click, config))
        tails.append(tail.packet() if isinstance(tail, I) else I(tail).packet())
    ch = cells[0]["j"] + cells[1]["j"] + cells[2]["j"] - cells[3]["j"] - cells[0]["sA"] - cells[0]["sB"]
    ratio = (ratios[1] / ratios[0]).sqrt() if ratios[0].lo > 0 else I(0)
    return {"CH": ch, "r": ratio, "ratios": ratios,
            "cells": cells, "tails": tails, "angles": controls, "balance": balance}


def box_points(config):
    ca, cb = map(F, config["klyshko_target_center"])
    width = F(config["klyshko_probability_half_width"])
    dv = F(config["visibility_DA_center"])
    vlo, vhi = map(F, config["visibility_DA_interval"])
    return [("center", ca, cb, dv)] + [("corner_" + str(k), a, b, v)
        for k, (a, b, v) in enumerate(itertools.product((ca - width, ca + width),
                                                       (cb - width, cb + width), (vlo, vhi)))]


def replay():
    config, counts, _, freeze, bindings = science.configuration()
    executable = science.frozen(__file__)
    library = science.frozen(science.__file__)
    view = science.training_view(counts)
    results = []
    for name, ka, kb, target in box_points(config):
        packet, lam, construction, calibration = science.prepare(view, ka, kb, target, config)
        point, objective, log = optimized(packet, lam, config)
        exact = mathematical_point(packet, lam, point, objective.gain_interval, config)
        gh = math.atanh(math.sqrt(float(F(packet["geometric_ratio"][0]))))
        gv = math.atanh(math.sqrt(float(F(packet["geometric_ratio"][1]))))
        original_point = (math.degrees(math.atan2(gv, gh)), *map(lambda x: float(F(x)), config["angles_deg"]))
        original = mathematical_point(packet, lam, original_point, objective.gain_interval, config)
        gain = exact["CH"] - original["CH"]
        five = [exact["r"], *(I(F(str(x))) for x in point[1:])]
        results.append({"name": name, "K_targets": [str(ka), str(kb)], "DA_target": str(target),
            "source": packet, "single_construction": construction, "calibration": calibration,
            "gain_norm": objective.gain_interval.packet(), "control": list(point),
            "five_components": [x.packet() for x in five], "CH": exact["CH"].packet(),
            "original_control": list(original_point), "original_CH": original["CH"].packet(),
            "strict_gain": gain.packet(), "strict_improvement": gain.lo > 0,
            "cell_probabilities": [{k: v.packet() for k, v in row.items()} for row in exact["cells"]],
            "source_pair_tail": exact["tails"], "optimization": log})
    # Printed controls are consumed only after every source and optimization is generated.
    instrument = json.loads((HERE / config["documented_source"]).resolve().read_text())
    documented = [F(instrument["preparation"]["amplitudes"]["VV"]) / F(instrument["preparation"]["amplitudes"]["HH"]),
                  *map(F, instrument["controls"]["alice"]), *map(F, instrument["controls"]["bob"])]
    half = [F(config["five_component_rounding_half_width_r"])] + [F(config["five_component_rounding_half_width_angle_deg"])] * 4
    band = []
    for k in range(5):
        lo = min(F(point["five_components"][k]["exact_lower"]) for point in results) - half[k]
        hi = max(F(point["five_components"][k]["exact_upper"]) for point in results) + half[k]
        band.append(I(lo, hi))
    inclusion = [box.lo <= value <= box.hi for box, value in zip(band, documented)]
    return {"schema": "p23-frame-window-independent-replay/v1", "version": science.VERSION,
        "criterion_freeze": freeze, "executable_freeze": executable, "library_freeze": library,
        "bindings": bindings, "box_points": results, "box_point_count": len(results),
        "band_name": "fw_Klyshko_DA_nine_point_component_band", "band": [x.packet() for x in band],
        "documented": [str(x) for x in documented], "comparison": inclusion,
        "outcome": "NUMERICAL_BAND_CONTAINS_ALL_PRINTED_COMPONENTS" if all(inclusion) else "NUMERICAL_DEVIATION_EXCEEDS_DECLARED_BAND",
        "global_optimum_kernel_proof": False, "primary_code_or_results_read_before_first": False,
        "retrospective": True, "bell_event_files_read": 0, **{k: False for k in science.FLAGS}}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output")
    args = parser.parse_args()
    value = replay()
    text = science.json_dump(value)
    if args.output:
        path = Path(args.output)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
