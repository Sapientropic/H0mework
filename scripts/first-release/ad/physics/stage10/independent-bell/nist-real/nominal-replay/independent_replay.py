#!/usr/bin/env python3
"""Genuinely independent re-computation of the nominal-apparatus replay.

Independence from replay.py:
  * probability code path -- 4x4 density matrix with explicit partial trace and Tr(rho J)
    tensor contraction, instead of the direct Born-rule amplitude of replay.py;
  * optimiser -- cycled golden-section coordinate ascent from a differently-offset coarse
    grid (replay.py uses a two-offset coarse grid plus an 18-neighbour pattern search);
  * the two modules share no code: everything below is written out again.

It independently parses criterion-r0003.md, generates its input box and recomputes every
optimum before reading replay-r0003.json for comparison. Background, band and tolerance
come from the criterion, never the primary output. Stdlib only, deterministic, offline.
"""

import json
import math
import os
import re
import subprocess
import time
from fractions import Fraction
from itertools import product

HERE = os.path.dirname(os.path.abspath(__file__))
REPLAY_PATH = os.path.join(HERE, "replay-r0003.json")
OUT_PATH = os.path.join(HERE, "independent_replay-r0003.json")
CRITERION_PATH = os.path.join(HERE, "criterion-r0003.md")
INSTRUMENT_PATH = os.path.join(HERE, "..", "instrument.json")

GOLDEN = 0.5 * (3.0 - math.sqrt(5.0))     # 0.381966...
INV_GOLDEN = 1.0 - GOLDEN


def sha256_file(path):
    import hashlib
    with open(path, "rb") as handle:
        return hashlib.sha256(handle.read()).hexdigest()


def parse_criterion(text):
    """Separate parser and percentage conversion; no imports from replay.py."""
    begin, end = "<!-- FROZEN-INSTRUMENT-BEGIN -->", "<!-- FROZEN-INSTRUMENT-END -->"
    if text.count(begin) != 1 or text.count(end) != 1:
        raise ValueError("REPLAY_MODEL_INADEQUATE_nonunique_frozen_instrument_block")
    body = text.split(begin)[1].split(end)[0].strip()
    if not body.startswith("```json\n") or not body.endswith("```"):
        raise ValueError("REPLAY_MODEL_INADEQUATE_invalid_frozen_instrument_block")
    frozen = json.loads(body[len("```json"): -3])
    for number, next_number in ((5, 6), (14, 15)):
        marker, following = "**F%d " % number, "**F%d " % next_number
        if text.count(marker) != 1 or text.count(following) != 1:
            raise ValueError("REPLAY_MODEL_INADEQUATE_missing_efficiency_text")
        section = text.split(marker)[1].split(following)[0]
        for side in ("A", "B"):
            values = re.findall(r"[εη]" + side + r"\s*[=∈]\s*([\d.]+)\s*%?\s*±\s*([\d.]+)\s*%",
                                section)
            if len(values) != 1:
                raise ValueError("REPLAY_MODEL_INADEQUATE_ambiguous_efficiency_text")
            center, half_width = [Fraction(v) / 100 for v in values[0]]
            channel = frozen["channel"]["eta_" + side]
            if (Fraction(str(channel["center"])) != center
                    or Fraction(str(channel["half_width"])) != half_width):
                raise ValueError("REPLAY_MODEL_INADEQUATE_efficiency_unit_mismatch_F%d_%s"
                                 % (number, side))
    return frozen


def load_frozen(criterion_path=CRITERION_PATH):
    with open(criterion_path, encoding="utf-8") as handle:
        return parse_criterion(handle.read())


def criterion_freeze():
    root = subprocess.check_output(["git", "rev-parse", "--show-toplevel"], cwd=HERE,
                                   text=True).strip()
    relative = os.path.relpath(CRITERION_PATH, root)
    commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", relative],
                                     cwd=root, text=True).strip()
    if not commit:
        raise ValueError("REPLAY_MODEL_INADEQUATE_uncommitted_criterion")
    committed = subprocess.check_output(["git", "show", commit + ":" + relative], cwd=root)
    with open(CRITERION_PATH, "rb") as handle:
        if handle.read() != committed:
            raise ValueError("REPLAY_MODEL_INADEQUATE_uncommitted_criterion_changes")
    return {"commit": commit, "path": relative, "sha256": sha256_file(CRITERION_PATH)}


def box_points(frozen):
    channel = frozen["channel"]
    a, b = channel["eta_A"], channel["eta_B"]
    q, v = channel["pair_probability"], channel["visibility"]
    points = [{"label": "center", "eta_a": a["center"], "eta_b": b["center"],
               "pair_probability": q["center"], "visibility": v["center"]}]
    axes = [(e["center"] - e["half_width"], e["center"] + e["half_width"]) for e in (a, b)]
    axes.extend([(q["box_low"], q["box_high"]), (v["box_low"], v["box_high"])])
    points.extend(dict(zip(("eta_a", "eta_b", "pair_probability", "visibility"), values),
                       label="corner") for values in product(*axes))
    return points


def context_for(frozen, point):
    channel = frozen["channel"]
    return {"eta_a": point["eta_a"], "eta_b": point["eta_b"],
            "b_a": channel["background_A_per_trial"], "b_b": channel["background_B_per_trial"],
            "n_pairs": point["pair_probability"], "delta_deg": frozen["model"]["delta_deg"],
            "werner": None}


def comparisons_match(stored, fresh, tolerance):
    if len(stored) != len(fresh) or len(fresh) != 5:
        return False
    for actual, expected in zip(stored, fresh):
        tol = tolerance["r" if expected["name"] == "r" else "angle_deg"]
        if (actual["name"] != expected["name"] or actual["documented"] != expected["documented"]
                or actual["inside"] is not expected["inside"] or len(actual["band"]) != 2
                or not all(math.isfinite(x) and abs(x - y) <= tol
                           for x, y in zip(actual["band"], expected["band"]))):
            return False
    return True


# --------------------------------------------------------------------- density-matrix model

def state_vector(r, delta_deg):
    """|psi_r> in the basis (V_A V_B, V_A H_B, H_A V_B, H_A H_B), thesis p.76."""
    d = math.radians(delta_deg)
    sn, cs = math.sin(d), math.cos(d)
    norm = math.sqrt(1.0 + r * r - 2.0 * r * sn * sn)
    return [(r - sn * sn) / norm, (sn * cs) / norm, (-sn * cs) / norm, (cs * cs) / norm]


def density_matrix(r, delta_deg):
    psi = state_vector(r, delta_deg)
    return [[psi[i] * psi[j] for j in range(4)] for i in range(4)]


def analyser_projector(theta_deg):
    """|theta><theta| in the (V, H) basis, |theta> = cos(theta)|V> + sin(theta)|H>."""
    c = math.cos(math.radians(theta_deg))
    s = math.sin(math.radians(theta_deg))
    return [[c * c, c * s], [c * s, s * s]]


def joint_operator(theta_a_deg, theta_b_deg):
    """J = |thetaA><thetaA| (x) |thetaB><thetaB| in the 4-dim tensor basis."""
    pa = analyser_projector(theta_a_deg)
    pb = analyser_projector(theta_b_deg)
    j = [[0.0] * 4 for _ in range(4)]
    for a1 in range(2):
        for b1 in range(2):
            for a2 in range(2):
                for b2 in range(2):
                    j[a1 * 2 + b1][a2 * 2 + b2] = pa[a1][a2] * pb[b1][b2]
    return j


def trace_product(rho, operator):
    """Re Tr(rho * operator) with explicit matrix multiplication (works for any square size)."""
    n = len(rho)
    total = 0.0
    for i in range(n):
        row = rho[i]
        for k in range(n):
            if row[k] == 0.0 or operator[k][i] == 0.0:
                continue
            total += row[k] * operator[k][i]
    return total


def partial_trace_b(rho):
    """rho_A[m][n] = sum_b rho[(m,b)][(n,b)]  (trace over Bob's index)."""
    red = [[0.0] * 2 for _ in range(2)]
    for m in range(2):
        for n in range(2):
            acc = 0.0
            for b in range(2):
                acc += rho[m * 2 + b][n * 2 + b]
            red[m][n] = acc
    return red


def pair_and_singles(r, delta_deg, theta_a_deg, theta_b_deg):
    """(p(1,1|thA,thB), p(1|thA), p(1|thB)) from rho by Tr(rho J) and Tr(rho_A S).

    The marginal is also cross-checked against the sum over Bob's complete basis, so the
    reduced-density-matrix route cannot silently disagree with the joint operator route.
    """
    rho = density_matrix(r, delta_deg)
    p11 = trace_product(rho, joint_operator(theta_a_deg, theta_b_deg))
    red = partial_trace_b(rho)
    pa = trace_product(red, analyser_projector(theta_a_deg))
    pb = trace_product(red, analyser_projector(theta_b_deg))
    return p11, pa, pb


# --------------------------------------------------------------------- model assembly

def measured(r_context, r, theta_a_deg, theta_b_deg):
    """Thesis p.77 in per-trial probabilities (criterion.md M3)."""
    p11, pa, pb = pair_and_singles(r, r_context["delta_deg"], theta_a_deg, theta_b_deg)
    vis = r_context["werner"]
    if vis is not None:
        p11 = vis * p11 + (1.0 - vis) * 0.25
        pa = vis * pa + (1.0 - vis) * 0.5
        pb = vis * pb + (1.0 - vis) * 0.5
    n = r_context["n_pairs"]
    single_a = n * r_context["eta_a"] * pa + r_context["b_a"]
    single_b = n * r_context["eta_b"] * pb + r_context["b_b"]
    joint = n * r_context["eta_a"] * r_context["eta_b"] * p11 + single_a * single_b
    return joint, single_a, single_b


def objective(context, r, theta_0_deg, theta_1_deg):
    j00, _, _ = measured(context, r, theta_0_deg, -theta_0_deg)
    j01, _, _ = measured(context, r, theta_0_deg, -theta_1_deg)
    j10, _, _ = measured(context, r, theta_1_deg, -theta_0_deg)
    j11, _, _ = measured(context, r, theta_1_deg, -theta_1_deg)
    _, sa0, _ = measured(context, r, theta_0_deg, 0.0)
    _, _, sb0 = measured(context, r, 0.0, -theta_0_deg)
    return j00 + j01 + j10 - j11 - sa0 - sb0


# --------------------------------------------------------------------- optimiser

def golden_max(f, lo, hi, rel_tol=1e-12, max_iter=200):
    """Golden-section maximisation of a unimodal 1-D function on [lo, hi]."""
    x1 = lo + GOLDEN * (hi - lo)
    x2 = lo + INV_GOLDEN * (hi - lo)
    f1, f2 = f(x1), f(x2)
    for _ in range(max_iter):
        if hi - lo <= rel_tol * (abs(lo) + abs(hi) + 1e-300):
            break
        if f1 > f2:
            hi, x2, f2 = x2, x1, f1
            x1 = lo + GOLDEN * (hi - lo)
            f1 = f(x1)
        else:
            lo, x1, f1 = x1, x2, f2
            x2 = lo + INV_GOLDEN * (hi - lo)
            f2 = f(x2)
    if f1 > f2:
        return x1, f1
    return x2, f2


def coordinate_ascent(context, start, r_span, angle_span, config):
    """Cycled golden-section coordinate ascent; deterministic."""
    r, t0, t1 = start
    value = objective(context, r, t0, t1)
    for _ in range(config["coordinate_cycles"]):
        moved = False
        for index, span in ((0, r_span), (1, angle_span), (2, angle_span)):
            if index == 0:
                lo, hi = max(1e-6, r - span), min(1.0, r + span)
                def line(x):
                    return objective(context, x, t0, t1)
            else:
                current = t0 if index == 1 else t1
                lo, hi = max(-90.0, current - span), min(90.0, current + span)
                if index == 1:
                    def line(x):
                        return objective(context, r, x, t1)
                else:
                    def line(x):
                        return objective(context, r, t0, x)
            if hi <= lo:
                continue
            best_x, best_v = golden_max(line, lo, hi, rel_tol=config["golden_rel_tol"],
                                       max_iter=config["golden_max_iter"])
            if best_v > value:
                value = best_v
                if index == 0:
                    r = best_x
                    moved = True
                elif index == 1:
                    t0 = best_x
                    moved = True
                else:
                    t1 = best_x
                    moved = True
        if not moved:
            r_span *= 0.5
            angle_span *= 0.5
            if max(r_span, angle_span) < config["span_stop"]:
                break
    return value, r, t0, t1


def coarse_starts(context, r_step=0.03, r_start=0.015, angle_step=3.0, keep=5):
    """Independent coarse grid (different offsets/steps from replay.py) -> best starts."""
    candidates = []
    n_ang = int(round(180.0 / angle_step)) + 1
    angles = [-90.0 + angle_step * k for k in range(n_ang)]
    n_r = int((1.0 - r_start) / r_step) + 1
    for k in range(n_r):
        r = r_start + r_step * k
        if r > 1.0:
            break
        for t0 in angles:
            for t1 in angles:
                candidates.append((objective(context, r, t0, t1), r, t0, t1))
    candidates.sort(key=lambda item: -item[0])
    return candidates[:keep]


def optimise(context, config):
    r_step, angle_step = config["grid_r_step"], config["grid_angle_step_deg"]
    best = None
    for _, r, t0, t1 in coarse_starts(context, r_step=r_step, angle_step=angle_step,
                                     r_start=config["grid_r_start"], keep=config["keep"]):
        value, rr, tt0, tt1 = coordinate_ascent(context, (r, t0, t1),
                                               r_span=r_step * config["span_factor"],
                                               angle_span=angle_step * config["span_factor"],
                                               config=config)
        if best is None or value > best[0]:
            best = (value, rr, tt0, tt1)
    value, r, t0, t1 = best
    raw = {"r": r, "theta0_deg": t0, "theta1_deg": t1}
    if t0 < 0.0 or (t0 == 0.0 and t1 < 0.0):
        r, t0, t1 = r, -t0, -t1
    return {"S": value, "r": r, "theta0_deg": t0, "theta1_deg": t1, "raw": raw}


# --------------------------------------------------------------------- main

def main():
    started = time.perf_counter()
    frozen = load_frozen()
    freeze = criterion_freeze()
    instrument = json.load(open(INSTRUMENT_PATH, encoding="utf-8"))
    tol = frozen["tolerance"]
    r_doc = (float(instrument["preparation"]["amplitudes"]["VV"])
             / float(instrument["preparation"]["amplitudes"]["HH"]))
    alice = [float(x) for x in instrument["controls"]["alice"]]
    bob = [float(x) for x in instrument["controls"]["bob"]]
    documented = frozen["documented_values"]
    if (abs(r_doc - documented["r"]) > 1e-12 or alice != documented["alice_angles_deg"]
            or bob != documented["bob_angles_deg"]):
        raise ValueError("REPLAY_MODEL_INADEQUATE_documented_values_mismatch")

    # Complete the independent computation before reading the reference output.
    recomputed_points = []
    for entry in box_points(frozen):
        ctx = context_for(frozen, entry)
        best = optimise(ctx, frozen["independent_optimizer"])
        recomputed_points.append({"label": entry["label"], "eta_a": entry["eta_a"],
                                  "eta_b": entry["eta_b"],
                                  "pair_probability": entry["pair_probability"],
                                  "visibility": entry["visibility"], "optimum": best})

    centre = recomputed_points[0]["optimum"]
    r_vals = [p["optimum"]["r"] for p in recomputed_points]
    t0_vals = [p["optimum"]["theta0_deg"] for p in recomputed_points]
    t1_vals = [p["optimum"]["theta1_deg"] for p in recomputed_points]
    band_cfg = frozen["band"]
    band = {
        "r": [min(r_vals) - band_cfg["r_widen"], max(r_vals) + band_cfg["r_widen"]],
        "theta0_deg": [min(t0_vals) - band_cfg["angle_widen_deg"],
                       max(t0_vals) + band_cfg["angle_widen_deg"]],
        "theta1_deg": [min(t1_vals) - band_cfg["angle_widen_deg"],
                       max(t1_vals) + band_cfg["angle_widen_deg"]],
    }
    comparisons = [{"name": "r", "documented": r_doc, "band": band["r"],
                    "inside": band["r"][0] <= r_doc <= band["r"][1]}]
    for name, value, lo, hi in (
            ("angle_theta0A_deg", alice[0], band["theta0_deg"][0], band["theta0_deg"][1]),
            ("angle_theta0B_deg", bob[0], -band["theta0_deg"][1], -band["theta0_deg"][0]),
            ("angle_theta1A_deg", alice[1], band["theta1_deg"][0], band["theta1_deg"][1]),
            ("angle_theta1B_deg", bob[1], -band["theta1_deg"][1], -band["theta1_deg"][0])):
        comparisons.append({"name": name, "documented": value, "band": [lo, hi],
                            "inside": lo <= value <= hi})
    verdict = (frozen["verdicts"]["pass"] if all(c["inside"] for c in comparisons)
               else frozen["verdicts"]["fail"])

    # ---- Only now consume the primary output, as a reference to be checked.
    replay = json.load(open(REPLAY_PATH, encoding="utf-8"))
    expected_sources = {name: sha256_file(os.path.join(HERE, name)) for name in
                        ("criterion-r0003.md", "../instrument.json", "christensen-appendix-a.txt",
                         "shalm2015-channel-inputs.txt", "replay.py")}
    sources_ok = (replay.get("schema") == "nominal-apparatus-replay/v1"
                  and replay.get("bindings") == expected_sources
                  and replay.get("criterion_version") == frozen["criterion_version"]
                  and replay.get("criterion_freeze") == freeze)
    point_keys = ("label", "eta_a", "eta_b", "pair_probability", "visibility")
    inputs_ok = (len(replay["box_points"]) == len(recomputed_points) == 17
                 and all(all(stored[k] == fresh[k] for k in point_keys)
                         for stored, fresh in zip(replay["box_points"], recomputed_points))
                 and replay["fixed_choices"]["F14_band"] == band_cfg
                 and replay["fixed_choices"]["F15_tolerance"] == tol)
    agreement = []
    ok = sources_ok and inputs_ok
    for stored, fresh in zip(replay["box_points"], recomputed_points):
        so, fo = stored["optimum"], fresh["optimum"]
        d_r = abs(so["r"] - fo["r"])
        d_t0 = abs(so["theta0_deg"] - fo["theta0_deg"])
        d_t1 = abs(so["theta1_deg"] - fo["theta1_deg"])
        d_s = abs(so["S"] - fo["S"])
        passed = (d_r <= tol["r"] and d_t0 <= tol["angle_deg"] and d_t1 <= tol["angle_deg"]
                  and d_s <= tol["S_abs"])
        ok = ok and passed
        agreement.append({"label": stored["label"], "eta_a": stored["eta_a"],
                          "eta_b": stored["eta_b"],
                          "pair_probability": stored["pair_probability"],
                          "visibility": stored["visibility"],
                          "delta_r": d_r, "delta_theta0_deg": d_t0,
                          "delta_theta1_deg": d_t1, "delta_S": d_s, "within_tolerance": passed})
    band_deltas = {
        "r": [abs(replay["band"]["widened"]["r"][0] - band["r"][0]),
              abs(replay["band"]["widened"]["r"][1] - band["r"][1])],
        "theta0_deg": [abs(replay["band"]["widened"]["theta0_deg"][0] - band["theta0_deg"][0]),
                       abs(replay["band"]["widened"]["theta0_deg"][1] - band["theta0_deg"][1])],
        "theta1_deg": [abs(replay["band"]["widened"]["theta1_deg"][0] - band["theta1_deg"][0]),
                       abs(replay["band"]["widened"]["theta1_deg"][1] - band["theta1_deg"][1])],
    }
    band_ok = all(max(v) <= tol["angle_deg"] for k, v in band_deltas.items() if k != "r")
    band_ok = band_ok and max(band_deltas["r"]) <= tol["r"]
    verdict_ok = (verdict == replay["verdict"])
    comparison_ok = comparisons_match(replay["comparison"], comparisons, tol)
    ok = ok and band_ok and verdict_ok and comparison_ok

    out = {
        "schema": "independent-nominal-apparatus-replay/v1",
        "criterion_version": frozen["criterion_version"],
        "criterion_freeze": freeze,
        "scope": "independent criterion-derived nominal-apparatus replay (NIST 2015)",
        "verdict": ("CERTIFIED_" if ok else "REFUTED_") + replay["verdict"],
        "independent_paths": {
            "probability": "4x4 density matrix, explicit partial trace, Tr(rho J)",
            "optimiser": "golden-section coordinate ascent from a 3.0 deg / 0.03 coarse grid",
            "shared_code_with_replay": "none",
        },
        "bindings": {"replay-r0003.json": sha256_file(REPLAY_PATH),
                     "criterion-r0003.md": sha256_file(CRITERION_PATH),
                     "../instrument.json": sha256_file(INSTRUMENT_PATH),
                     "christensen-appendix-a.txt": sha256_file(os.path.join(HERE, "christensen-appendix-a.txt")),
                     "shalm2015-channel-inputs.txt": sha256_file(os.path.join(HERE, "shalm2015-channel-inputs.txt")),
                     "independent_replay.py": sha256_file(os.path.abspath(__file__))},
        "tolerance": tol,
        "source_agreement": sources_ok,
        "input_agreement": inputs_ok,
        "comparison_agreement": comparison_ok,
        "box_points": recomputed_points,
        "agreement": agreement,
        "band_agreement": {"deltas": band_deltas, "within_tolerance": band_ok},
        "verdict_agreement": verdict_ok,
        "recomputed": {"centre_optimum": centre, "band_widened": band,
                       "comparison": comparisons, "verdict": verdict},
        "elapsed_seconds": time.perf_counter() - started,
    }
    with open(OUT_PATH, "w", encoding="utf-8") as handle:
        json.dump(out, handle, indent=2)
        handle.write("\n")

    worst = max(max(a["delta_r"], a["delta_theta0_deg"], a["delta_theta1_deg"], a["delta_S"])
                for a in agreement)
    print("verdict:", out["verdict"])
    print("recomputed centre: r*=%.6f theta0*=%.4f theta1*=%.4f S*=%.6e"
          % (centre["r"], centre["theta0_deg"], centre["theta1_deg"], centre["S"]))
    print("stored     centre: r*=%.6f theta0*=%.4f theta1*=%.4f S*=%.6e"
          % (replay["box_points"][0]["optimum"]["r"], replay["box_points"][0]["optimum"]["theta0_deg"],
             replay["box_points"][0]["optimum"]["theta1_deg"], replay["box_points"][0]["optimum"]["S"]))
    print("band agreement:", band_ok, "| verdict agreement:", verdict_ok,
          "| worst box-point delta: %.3e" % worst)
    print("elapsed_seconds: %.2f" % out["elapsed_seconds"])
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
