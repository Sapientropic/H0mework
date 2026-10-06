#!/usr/bin/env python3
"""Frozen NIST source-code replay using commuting pair sectors and local number blocks.

The four-mode source is never postselected. Its HH/VV pair sectors are exponentiated
separately; the common (-i)^T phase cancels inside each number-preserving effect block.
This implementation uses no tensor eigensolver, external numerical library or event data.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import math
import re
import subprocess
import time
from decimal import Decimal
from functools import lru_cache
from pathlib import Path

HERE = Path(__file__).resolve().parent
CRITERION = HERE / "criterion.md"
VERSION = "nominal-source-code-r0005"
COMPONENTS = ("r_one_pair", "a0_deg", "a1_deg", "b0_deg", "b1_deg")
PASS = "REPLAY_CONSISTENT_WITH_PREDECLARED_BAND"
FAIL = "REPLAY_DEVIATION_EXCEEDS_PREDECLARED_BAND"


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load_frozen(path=None):
    text = Path(path or CRITERION).read_text()
    begin, end = "<!-- FROZEN-SOURCE-STUDY-BEGIN -->", "<!-- FROZEN-SOURCE-STUDY-END -->"
    if text.count(begin) != 1 or text.count(end) != 1:
        raise ValueError("nonunique_frozen_source_study")
    block = text.split(begin)[1].split(end)[0].strip()
    if not block.startswith("```json\n") or not block.endswith("```"):
        raise ValueError("invalid_frozen_source_study")
    study = json.loads(block[7:-3])
    efficiencies = re.findall(r"(\d+(?:\.\d+)?)\s*±\s*(\d+(?:\.\d+)?)\s*%", text)
    if len(efficiencies) != 2:
        raise ValueError("ambiguous_efficiency_text")
    for side, (center, half) in zip(("A", "B"), efficiencies):
        eta = study["published"]["eta_" + side]
        if (Decimal(center)/100 != Decimal(str(eta["center"]))
                or Decimal(half)/100 != Decimal(str(eta["half_width"]))):
            raise ValueError("efficiency_unit_mismatch_" + side)
    if (study["criterion_version"] != VERSION or study["source"] !=
            {"N": 4, "relative_phase_rad": 0.0, "detector_noise": "additive"}):
        raise ValueError("unsupported_frozen_source")
    return study


def criterion_freeze():
    root = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"],
                                       cwd=HERE, text=True).strip())
    relative = CRITERION.relative_to(root).as_posix()
    commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", relative],
                                     cwd=root, text=True).strip()
    if not commit:
        raise ValueError("criterion_not_committed")
    committed = subprocess.check_output(["git", "show", commit + ":" + relative], cwd=root)
    if committed != CRITERION.read_bytes():
        raise ValueError("criterion_has_uncommitted_changes")
    return {"commit": commit, "path": relative,
            "sha256": hashlib.sha256(committed).hexdigest()}


def input_points(study):
    historical, published = study["author_defaults"], study["published"]
    result = []
    for case in study["cases"]:
        if case == "author_defaults":
            result.append({"case": case, "point_id": case+":center",
                "eta_A": historical["eta_A"], "eta_B": historical["eta_B"],
                "background_A": historical["darks_A_per_second"] * historical["coincidence_window_seconds"],
                "background_B": historical["darks_B_per_second"] * historical["coincidence_window_seconds"],
                "epsilon_squared": historical["balanced_HH_coincidences_per_second"] /
                    (historical["eta_A"]*historical["eta_B"]*historical["rep_rate_per_second"]),
                "pair_scale": None})
            continue
        if case not in ("published_gain_half", "published_native_strength"):
            raise ValueError("unknown_input_case")
        a, b, q = published["eta_A"], published["eta_B"], published["pair_scale"]
        triples = [(case+":center", (a["center"], b["center"], q["center"]))]
        axes = ((a["center"]-a["half_width"], a["center"]+a["half_width"]),
                (b["center"]-b["half_width"], b["center"]+b["half_width"]),
                (q["box_low"], q["box_high"]))
        triples.extend((case+":corner_"+"".join(map(str, bits)), tuple(axis[bit] for axis, bit in zip(axes, bits)))
                       for bits in itertools.product((0, 1), repeat=3))
        for point_id, (eta_a, eta_b, pair) in triples:
            result.append({"case": case, "point_id": point_id,
                "eta_A": eta_a, "eta_B": eta_b,
                "background_A": published["background_A_per_trial"],
                "background_B": published["background_B_per_trial"],
                "epsilon_squared": pair / 2 if case == "published_gain_half" else pair,
                "pair_scale": pair})
    if len(result) != 19:
        raise ValueError("incomplete_frozen_input_points")
    return result


def detector(eta, background):
    if (not math.isfinite(eta) or not math.isfinite(background)
            or not 0 <= eta <= 1 or background < 0):
        raise ValueError("invalid_detector_input")
    values = tuple(1-(1-eta)**n+background for n in range(4))
    if any(not 0 <= value <= 1 for value in values):
        raise ValueError("detector_effect_outside_unit_interval")
    return values


def matrix_product(a, b):
    n = len(a)
    return tuple(tuple(math.fsum(a[i][k]*b[k][j] for k in range(n))
                       for j in range(n)) for i in range(n))


def matrix_exp_real(generator, angle):
    """Scaling-and-squaring Taylor evaluation of a real matrix of dimension at most four."""
    n = len(generator)
    norm = max(sum(abs(v) for v in row) for row in generator) * abs(angle)
    squarings = max(0, math.ceil(math.log2(norm/0.5))) if norm else 0
    scale = angle / (2**squarings)
    a = tuple(tuple(scale*v for v in row) for row in generator)
    term = tuple(tuple(float(i == j) for j in range(n)) for i in range(n))
    result = term
    for order in range(1, 81):
        product = matrix_product(a, term)
        term = tuple(tuple(v/order for v in row) for row in product)
        result = tuple(tuple(result[i][j]+term[i][j] for j in range(n)) for i in range(n))
        if max(abs(v) for row in term for v in row) < 2e-18:
            break
    else:
        raise ArithmeticError("matrix_exponential_failed_to_converge")
    for _ in range(squarings):
        result = matrix_product(result, result)
    return result


@lru_cache(maxsize=7)
def sector_basis(total):
    if not isinstance(total, int) or not 0 <= total <= 6:
        raise ValueError("invalid_total_photon_sector")
    return tuple(range(max(0, total-3), min(3, total)+1))


@lru_cache(maxsize=32768)
def sector_rotation(total, angle_deg):
    basis = sector_basis(total)
    n = len(basis)
    generator = [[0.0]*n for _ in range(n)]
    for column, k in enumerate(basis):
        if k-1 in basis:
            generator[column-1][column] = math.sqrt(k*(total-k+1))
        if k+1 in basis:
            generator[column+1][column] = -math.sqrt((k+1)*(total-k))
    return matrix_exp_real(generator, math.radians(angle_deg))


def pair_coefficients(gain):
    """Remove (-i)^n from exp(-i gain (a†b†+ab))|00> in its four-dimensional pair sector."""
    term, value = [1.0, 0.0, 0.0, 0.0], [1.0, 0.0, 0.0, 0.0]
    for order in range(1, 81):
        following = [gain * ((n*term[n-1] if n else 0.0) -
                              ((n+1)*term[n+1] if n < 3 else 0.0)) / order
                     for n in range(4)]
        term = following
        value = [a+b for a, b in zip(value, term)]
        if max(abs(t) for t in term) < 2e-18:
            break
    else:
        raise ArithmeticError("source_exponential_failed_to_converge")
    return tuple(value)


class Model:
    def __init__(self, point):
        self.point = dict(point)
        self.epsilon = math.sqrt(point["epsilon_squared"])
        if not math.isfinite(self.epsilon) or self.epsilon <= 0:
            raise ValueError("invalid_source_gain")
        self.detectors = (detector(point["eta_A"], point["background_A"]),
                          detector(point["eta_B"], point["background_B"]))
        self._source_cache = {}
        self._effect_cache = {}

    def source(self, gamma_deg):
        if gamma_deg not in self._source_cache:
            gamma = math.radians(gamma_deg)
            h = pair_coefficients(math.sqrt(2)*self.epsilon*math.sin(gamma))
            v = pair_coefficients(math.sqrt(2)*self.epsilon*math.cos(gamma))
            coefficients, outer = [], []
            for total in range(7):
                c = tuple(h[k]*v[total-k] for k in sector_basis(total))
                coefficients.append(c)
                outer.append(tuple((k, ell, c[k]*c[ell]*(1 if k == ell else 2))
                                   for k in range(len(c)) for ell in range(k, len(c))))
            self._source_cache[gamma_deg] = (h, v, tuple(coefficients), tuple(outer))
        return self._source_cache[gamma_deg]

    def effects(self, angle_deg, side):
        if side in ("A", "alice", "Alice"):
            side = 0
        elif side in ("B", "bob", "Bob"):
            side = 1
        if side not in (0, 1):
            raise ValueError("invalid_detector_side")
        key = (angle_deg, side)
        if key not in self._effect_cache:
            effects = []
            for total in range(7):
                basis, u = sector_basis(total), sector_rotation(total, angle_deg)
                values = self.detectors[side]
                effects.append(tuple(tuple(math.fsum(u[n][k]*values[photon]*u[n][ell]
                                         for n, photon in enumerate(basis))
                                     for ell in range(len(basis))) for k in range(len(basis))))
            self._effect_cache[key] = tuple(effects)
        return self._effect_cache[key]

    def source_norm(self, gamma_deg):
        _, _, coefficients, _ = self.source(gamma_deg)
        return math.fsum(c*c for sector in coefficients for c in sector)

    def r_one_pair(self, gamma_deg):
        h, v, _, _ = self.source(gamma_deg)
        return abs(h[1]*v[0] / (h[0]*v[1]))

    def single(self, gamma_deg, angle_deg, side):
        _, _, coefficients, _ = self.source(gamma_deg)
        effects = self.effects(angle_deg, side)
        return math.fsum(c*c*effect[k][k] for sector, effect in zip(coefficients, effects)
                         for k, c in enumerate(sector))

    def joint(self, gamma_deg, a_deg, b_deg):
        _, _, _, weights = self.source(gamma_deg)
        a, b = self.effects(a_deg, 0), self.effects(b_deg, 1)
        return math.fsum(weight*ea[k][ell]*eb[k][ell]
                         for sector, ea, eb in zip(weights, a, b) for k, ell, weight in sector)

    def score(self, value):
        gamma, a0, a1 = value
        _, _, coefficients, weights = self.source(gamma)
        ea0, ea1 = self.effects(a0, 0), self.effects(a1, 0)
        eb0, eb1 = self.effects(-a0, 1), self.effects(-a1, 1)
        joint_terms = (weight*(a[k][ell]*(b[k][ell]+bp[k][ell])+
                               ap[k][ell]*(b[k][ell]-bp[k][ell]))
                       for sector, a, ap, b, bp in zip(weights, ea0, ea1, eb0, eb1)
                       for k, ell, weight in sector)
        singles = math.fsum(c*c*(a[k][k]+b[k][k])
                           for sector, a, b in zip(coefficients, ea0, eb0)
                           for k, c in enumerate(sector))
        return math.fsum(joint_terms)-singles


def canonical(value):
    gamma, a0, a1 = value
    if a0 < 0 or (a0 == 0 and a1 < 0):
        a0, a1 = -a0, -a1
    return [gamma, a0, a1]


def pattern_search(model, start, study):
    cfg, domains = study["primary_optimizer"], study["domains"]
    bounds = [domains["gamma_deg"], domains["angle_deg"], domains["angle_deg"]]
    value = list(start)
    if any(not lo <= x <= hi for x, (lo, hi) in zip(value, bounds)):
        raise ValueError("optimizer_start_outside_frozen_domain")
    score, steps = model.score(value), [cfg["step_deg"]]*3
    offsets = [change for change in itertools.product((-1, 0, 1), repeat=3)
               if change != (0, 0, 0)]
    for _ in range(cfg["iterations"]):
        best, best_score = value, score
        for change in offsets:
            candidate = [x+s*d for x, s, d in zip(value, steps, change)]
            if any(not lo <= x <= hi for x, (lo, hi) in zip(candidate, bounds)):
                continue
            candidate_score = model.score(candidate)
            if candidate_score > best_score:
                best, best_score = candidate, candidate_score
        if best is value:
            steps = [step/2 for step in steps]
            if max(steps) < cfg["step_stop"]:
                break
        else:
            value, score = best, best_score
    return score, canonical(value)


def optimise(model, study, center=None):
    cfg = study["primary_optimizer"]
    if center is None:
        grid = itertools.product(cfg["grid_gamma_deg"], cfg["grid_angle0_deg"], cfg["grid_angle1_deg"])
        ranked = sorted(((model.score(value), list(value)) for value in grid), key=lambda row: -row[0])
        starts = [row[1] for row in ranked[:cfg["keep"]]] + [study["author_start_deg"]]
    else:
        starts = [center] + study["corner_starts_deg"]
    best = None
    for start in starts:
        result = pattern_search(model, start, study)
        if best is None or result[0] > best[0]:
            best = result
    score, (gamma, a0, a1) = best
    return {"gamma_deg": gamma, "r_one_pair": model.r_one_pair(gamma),
            "weak_r": math.tan(math.radians(gamma)), "a0_deg": a0, "a1_deg": a1,
            "b0_deg": -a0, "b1_deg": -a1, "CH": score}


def check_readouts(model, gamma, a, b):
    norm = model.source_norm(gamma)
    if abs(norm-1) > 3e-13:
        raise ArithmeticError("source_not_normalized")
    sa, sb, joint = model.single(gamma, a, 0), model.single(gamma, b, 1), model.joint(gamma, a, b)
    outcomes = (joint, sa-joint, sb-joint, 1-sa-sb+joint)
    if any(not math.isfinite(p) or p < -3e-13 or p > 1+3e-13 for p in outcomes):
        raise ArithmeticError("invalid_unconditioned_probability")
    return {"source_norm": norm, "single_A": sa, "single_B": sb, "joint": joint,
            "no_click_mass": outcomes[-1], "outcome_mass": math.fsum(outcomes)}


def cases_report(results, study):
    instrument = json.loads((HERE / "../../instrument.json").read_text())
    amplitudes = instrument["preparation"]["amplitudes"]
    documented = [float(amplitudes["VV"])/float(amplitudes["HH"])]
    documented.extend(map(float, instrument["controls"]["alice"]+instrument["controls"]["bob"]))
    cases = {}
    for case in study["cases"]:
        points = [row["optimum"] for row in results if row["case"] == case]
        expected = 1 if case == "author_defaults" else 9
        if len(points) != expected:
            raise ValueError("incomplete_case_results")
        band = {}
        for component in COMPONENTS:
            width = study["band"]["r_widen" if component == "r_one_pair" else "angle_widen_deg"]
            values = [point[component] for point in points]
            band[component] = [min(values)-width, max(values)+width]
        comparisons = [{"component": component, "documented_value": value,
                        "interval": band[component], "inside": band[component][0] <= value <= band[component][1]}
                       for component, value in zip(COMPONENTS, documented)]
        cases[case] = {"band": band, "comparisons": comparisons,
                       "verdict": PASS if all(row["inside"] for row in comparisons) else FAIL}
    return cases


def main():
    started = time.perf_counter()
    study, freeze = load_frozen(), criterion_freeze()
    centers, results = {}, []
    for point in input_points(study):
        model = Model(point)
        is_center = point["point_id"].endswith(":center")
        optimum = optimise(model, study, None if is_center else centers[point["case"]])
        if is_center:
            centers[point["case"]] = [optimum["gamma_deg"], optimum["a0_deg"], optimum["a1_deg"]]
        readouts = check_readouts(model, optimum["gamma_deg"], optimum["a0_deg"], optimum["b0_deg"])
        results.append({"case": point["case"], "point": point, "optimum": optimum,
                        "readouts": readouts})
        print("%s %s gamma=%.8f r=%.9f angles=(%.7f,%.7f) CH=%.12e" %
              (point["case"], point["point_id"], optimum["gamma_deg"], optimum["r_one_pair"],
               optimum["a0_deg"], optimum["a1_deg"], optimum["CH"]), flush=True)
    out = {"schema": "nist-source-code-replay/v1", "criterion_version": study["criterion_version"],
           "criterion_freeze": freeze, "model_source_identified": True,
           "publication_configuration_identified": False, "production_admitted": False,
           "implementation": "commuting finite pair sectors; local total-photon-number HWP/effect blocks",
           "bindings": {name: digest(HERE/name) for name in ["criterion.md", "replay.py"]+study["input_sources"]},
           "results": results, "cases": cases_report(results, study),
           "claim": "Frozen deterministic numerical search; no continuous global-optimum proof.",
           "elapsed_seconds": time.perf_counter()-started}
    (HERE/study["outputs"]["primary"]).write_text(json.dumps(out, indent=2)+"\n")
    for case, report in out["cases"].items():
        print(case, report["verdict"], "inside=%d/5" % sum(row["inside"] for row in report["comparisons"]), flush=True)
    print("elapsed_seconds=%.3f" % out["elapsed_seconds"], flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
