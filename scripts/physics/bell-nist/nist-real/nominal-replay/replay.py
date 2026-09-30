#!/usr/bin/env python3
"""Independent nominal-apparatus replay for the NIST 2015 loophole-free Bell test.

Model source : B. G. Christensen, PhD thesis (UIUC 2016), Appendix A (pages 76-78) and
               section 4.6.2 (pages 46-47); verbatim extract in christensen-appendix-a.txt.
Channel input: L. K. Shalm et al., arXiv:1511.03189v2 p.4 (global values); verbatim excerpt in
               shalm2015-channel-inputs.txt.
Freeze        : criterion.md, FROZEN-INSTRUMENT JSON block.  This file contains no tunable
                knob: every numeric choice is read from that block.  Stdlib only, offline,
                fully deterministic (no RNG anywhere).

Revision note: criterion.md r0002 changed only the normalisation mapping of the published
per-window background (per-trial, M3).  The superseded r0001 output is kept next to this
script as replay-r0001-superseded.json; criterion.md section 10 records the revision.

Verdict produced here is a candidate input for a later gate review -- not a gate pass.
"""

import hashlib
import json
import math
import os
import re
import time

HERE = os.path.dirname(os.path.abspath(__file__))
CRITERION_PATH = os.path.join(HERE, "criterion.md")
INSTRUMENT_PATH = os.path.join(HERE, "..", "instrument.json")
APPENDIX_PATH = os.path.join(HERE, "christensen-appendix-a.txt")
PAPER_PATH = os.path.join(HERE, "shalm2015-channel-inputs.txt")
REPLAY_PATH = os.path.join(HERE, "replay.json")


# --------------------------------------------------------------------------- bindings

def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


def sha256_file(path):
    with open(path, "rb") as handle:
        return sha256_bytes(handle.read())


def find_repo_root(start):
    cur = start
    while True:
        parent = os.path.dirname(cur)
        if parent == cur:
            return start
        if os.path.isdir(os.path.join(cur, ".git")) and os.path.isfile(
                os.path.join(cur, "AGENTS.md")):
            return cur
        cur = parent


def load_frozen(criterion_path=CRITERION_PATH):
    """Parse the FROZEN-INSTRUMENT JSON block out of criterion.md."""
    text = open(criterion_path, encoding="utf-8").read()
    m = re.search(r"<!--\s*FROZEN-INSTRUMENT-BEGIN\s*-->(.*?)<!--\s*FROZEN-INSTRUMENT-END\s*-->",
                  text, re.S)
    if not m:
        raise SystemExit("REPLAY_MODEL_INADEQUATE_missing_frozen_instrument_block")
    body = m.group(1)
    start = body.find("{")
    if start < 0:
        raise SystemExit("REPLAY_MODEL_INADEQUATE_empty_frozen_instrument_block")
    obj, _ = json.JSONDecoder().raw_decode(body[start:])
    return obj


def load_instrument(path=INSTRUMENT_PATH):
    return json.load(open(path, encoding="utf-8"))


# --------------------------------------------------------------------------- model (eq. refs -> criterion.md / thesis pages)

def state_amplitudes(r, delta_deg):
    """|psi_r> ∝ cos^2 d |HH> - sin d cos d |HV> + sin d cos d |VH> + (r - sin^2 d)|VV>.

    Thesis p.76: |psi_r> ∝ |H+d, H-d> + r|VV>.  Returns (amplitudes in the tensor basis
    (V,H)x(V,H) ordered (VV, VH, HV, HH) as used by the density-matrix path, norm).
    """
    d = math.radians(delta_deg)
    sn, cs = math.sin(d), math.cos(d)
    amps = (r - sn * sn, sn * cs, -sn * cs, cs * cs)   # VV, VH, HV, HH
    norm = math.sqrt(1.0 + r * r - 2.0 * r * sn * sn)
    return amps, norm


def p_joint(r, delta_deg, theta_a_deg, theta_b_deg):
    """p(1,1|thetaA,thetaB) = <thetaA|<thetaB|psi_r>^2   (thesis p.76)."""
    d = math.radians(delta_deg)
    sn, cs = math.sin(d), math.cos(d)
    ca = math.cos(math.radians(theta_a_deg))
    sa = math.sin(math.radians(theta_a_deg))
    cb = math.cos(math.radians(theta_b_deg))
    sb = math.sin(math.radians(theta_b_deg))
    amp = ((r - sn * sn) * ca * cb + cs * cs * sa * sb + sn * cs * (sb * ca - sa * cb))
    norm = math.sqrt(1.0 + r * r - 2.0 * r * sn * sn)
    amp /= norm
    return amp * amp


def p_single(r, delta_deg, theta_deg):
    """p(1|theta) = <theta|rho_A|theta>, rho_A = tr_B rho   (thesis p.76)."""
    d = math.radians(delta_deg)
    sn, cs = math.sin(d), math.cos(d)
    rho_vv = sn * sn * cs * cs + (r - sn * sn) ** 2
    rho_hh = cs ** 4 + sn * sn * cs * cs
    rho_hv = sn * cs * (1.0 - r)
    norm2 = 1.0 + r * r - 2.0 * r * sn * sn
    c = math.cos(math.radians(theta_deg))
    s = math.sin(math.radians(theta_deg))
    return (c * c * rho_vv + s * s * rho_hh + 2.0 * s * c * rho_hv) / norm2


# --------------------------------------------------------------------------- objective (thesis p.77-78)

def measured_probs(ctx, r, theta_a_deg, theta_b_deg):
    """Thesis p.77 noise assembly in per-trial probabilities (criterion.md M3, r0002).

    single_a = N*eta_a*p(1|thetaA) + b_a          (b_a = dcr_a + N*flr_a, per trial)
    single_b = N*eta_b*p(1|thetaB) + b_b
    joint    = N*eta_a*eta_b*p(1,1|thetaA,thetaB) + single_a*single_b
             = N*eta_a*eta_b*p(1,1|thetaA,thetaB) + N^2*pm_a*pm_b     (acc_u)
    """
    vis = ctx["werner"]
    pj = p_joint(r, ctx["delta_deg"], theta_a_deg, theta_b_deg)
    pa = p_single(r, ctx["delta_deg"], theta_a_deg)
    pb = p_single(r, ctx["delta_deg"], theta_b_deg)
    if vis is not None:
        pj = vis * pj + (1.0 - vis) * 0.25
        pa = vis * pa + (1.0 - vis) * 0.5
        pb = vis * pb + (1.0 - vis) * 0.5
    n = ctx["n_pairs"]
    single_a = n * ctx["eta_a"] * pa + ctx["b_a"]
    single_b = n * ctx["eta_b"] * pb + ctx["b_b"]
    joint = n * ctx["eta_a"] * ctx["eta_b"] * pj + single_a * single_b
    return joint, single_a, single_b


def s_ch(ctx, r, theta_0_deg, theta_1_deg):
    """S_CH in the symmetric reduction (thesis Eq. (A.1) with measured probabilities, p.78).

    theta0A = -theta0B = theta0, theta1A = -theta1B = theta1  (thesis p.76).
    """
    joint_00, _, _ = measured_probs(ctx, r, theta_0_deg, -theta_0_deg)
    joint_01, _, _ = measured_probs(ctx, r, theta_0_deg, -theta_1_deg)
    joint_10, _, _ = measured_probs(ctx, r, theta_1_deg, -theta_0_deg)
    joint_11, _, _ = measured_probs(ctx, r, theta_1_deg, -theta_1_deg)
    _, single_a0, _ = measured_probs(ctx, r, theta_0_deg, 0.0)
    _, _, single_b0 = measured_probs(ctx, r, 0.0, -theta_0_deg)
    return joint_00 + joint_01 + joint_10 - joint_11 - single_a0 - single_b0


# --------------------------------------------------------------------------- optimizer (criterion.md F13 / section 5)

def canonicalise(r, theta_0, theta_1):
    """criterion.md F13: representative with theta0 >= 0 (tie-break theta1 >= 0)."""
    if theta_0 < 0.0 or (theta_0 == 0.0 and theta_1 < 0.0):
        return r, -theta_0, -theta_1
    return r, theta_0, theta_1


def _grid_angles(step_deg, offset_frac):
    lo, hi = -90.0, 90.0
    first = lo + offset_frac * step_deg
    out = []
    k = 0
    while True:
        val = first + k * step_deg
        if val > hi + 1e-9:
            break
        out.append(round(val, 12))
        k += 1
    return out


def _grid_r_values(step, start, offset_frac):
    out = []
    k = 0
    while True:
        val = start + k * step + offset_frac * step
        if val > 1.0 + 1e-12:
            break
        if val > 0.0:
            out.append(round(val, 12))
        k += 1
    return out


def coarse_grid_best(ctx, opt):
    """Two complementary coarse grids (criterion.md section 5.1)."""
    step_ang = opt["grid_angle_step_deg"]
    step_r = opt["grid_r_step"]
    best = None
    for offset in [0.0] + list(opt["second_grid_offsets"]):
        angles = _grid_angles(step_ang, offset)
        r_values = _grid_r_values(step_r, opt["grid_r_start"], offset)
        n = len(angles)
        index_of = {}
        for i, a in enumerate(angles):
            index_of[round(a, 9)] = i
        # every offset grid stays symmetric about 0, so -theta is also on the grid
        neg = [index_of[round(-a, 9)] for a in angles]
        for r in r_values:
            p1 = [p_single(r, ctx["delta_deg"], a) for a in angles]
            vis = ctx["werner"]
            if vis is not None:
                p1 = [vis * v + (1.0 - vis) * 0.5 for v in p1]
            n_pairs = ctx["n_pairs"]
            single_a = [n_pairs * ctx["eta_a"] * v + ctx["b_a"] for v in p1]
            single_b = [n_pairs * ctx["eta_b"] * v + ctx["b_b"] for v in p1]
            pj = [[p_joint(r, ctx["delta_deg"], angles[i], angles[j]) for j in range(n)]
                  for i in range(n)]
            if vis is not None:
                pj = [[vis * v + (1.0 - vis) * 0.25 for v in row] for row in pj]
            sig = n_pairs * ctx["eta_a"] * ctx["eta_b"]
            for i in range(n):
                row_i = pj[i]
                sa_i = single_a[i]
                neg_i = neg[i]
                sb_negi = single_b[neg_i]
                acc_ii = sa_i * sb_negi
                for j in range(n):
                    neg_j = neg[j]
                    pos = (row_i[neg_i] + row_i[neg_j] + pj[j][neg_i] - pj[j][neg_j])
                    acc = (acc_ii + sa_i * single_b[neg_j]
                           + single_a[j] * sb_negi - single_a[j] * single_b[neg_j])
                    value = sig * pos + acc - sa_i - sb_negi
                    if best is None or value > best[0]:
                        best = (value, r, angles[i], angles[j])
    return best


def pattern_search(ctx, start, opt, steps=None):
    """Deterministic 26-neighbour pattern search (criterion.md section 5.2)."""
    shrink = opt["pattern_shrink"]
    stop = opt["pattern_stop"]
    if steps is None:
        steps = [opt["grid_r_step"], opt["grid_angle_step_deg"], opt["grid_angle_step_deg"]]
    steps = list(steps)
    current = list(start)
    current_value = s_ch(ctx, *current)
    offsets = []
    for dr in (-1, 1):
        for d0 in (-1, 0, 1):
            for d1 in (-1, 0, 1):
                if dr == 0 and d0 == 0 and d1 == 0:
                    continue
                offsets.append((dr, d0, d1))
    for _ in range(opt["pattern_max_iter"]):
        improved = False
        best_move = None
        best_value = current_value
        for (mr, m0, m1) in offsets:
            cand = [current[0] + mr * steps[0], current[1] + m0 * steps[1],
                    current[2] + m1 * steps[2]]
            if cand[0] <= 0.0 or cand[0] > 1.0:
                continue
            if abs(cand[1]) > 90.0 or abs(cand[2]) > 90.0:
                continue
            value = s_ch(ctx, *cand)
            if value > best_value:
                best_value = value
                best_move = cand
                improved = True
        if improved:
            current = best_move
            current_value = best_value
        else:
            steps = [s * shrink for s in steps]
            if max(steps) < stop:
                break
    return current_value, current[0], current[1], current[2]


def optimise(ctx, opt, coarse=True):
    if coarse:
        best = coarse_grid_best(ctx, opt)
        start = [best[1], best[2], best[3]]
    else:
        start = [0.3, 4.0, -26.0]
    value, r, t0, t1 = pattern_search(ctx, start, opt)
    raw = {"r": r, "theta0_deg": t0, "theta1_deg": t1}
    r, t0, t1 = canonicalise(r, t0, t1)
    return {"S": value, "r": r, "theta0_deg": t0, "theta1_deg": t1, "raw": raw}


# --------------------------------------------------------------------------- channel points

def make_context(frozen, eta_a, eta_b, n_pairs, delta_deg=None, werner=None,
                 background=None):
    """Context for one channel point.  Backgrounds are per-trial probabilities (M3)."""
    chan = frozen["channel"]
    ctx = {
        "eta_a": eta_a,
        "eta_b": eta_b,
        "b_a": chan["background_A_per_trial"] if background is None else background[0],
        "b_b": chan["background_B_per_trial"] if background is None else background[1],
        "n_pairs": n_pairs,
        "delta_deg": frozen["model"]["delta_deg"] if delta_deg is None else delta_deg,
        "werner": werner,
    }
    return ctx


def threshold_eta(frozen, opt, zero_background, diag_cfg):
    """D3b: symmetric-efficiency threshold where max S_CH = 0 (criterion.md section 5.5)."""
    thetas = []
    lo, hi = diag_cfg["eta_lo"], diag_cfg["eta_hi"]

    def max_s(eta):
        if zero_background:
            ctx = make_context(frozen, eta, eta,
                               diag_cfg["zero_background"]["N"], background=(0.0, 0.0))
        else:
            ctx = make_context(frozen, eta, eta, frozen["channel"]["pair_probability"]["center"])
        best = optimise(ctx, opt)
        thetas.append({"eta": eta, "S": best["S"], "r": best["r"],
                       "theta0_deg": best["theta0_deg"], "theta1_deg": best["theta1_deg"]})
        return best["S"]

    for _ in range(diag_cfg["iterations"]):
        mid = 0.5 * (lo + hi)
        if max_s(mid) > 0.0:
            hi = mid
        else:
            lo = mid
    return {"threshold": 0.5 * (lo + hi), "bracket": [lo, hi], "samples": thetas}


def box_points(frozen):
    chan = frozen["channel"]
    eta_a_lo = chan["eta_A"]["center"] - chan["eta_A"]["half_width"]
    eta_a_hi = chan["eta_A"]["center"] + chan["eta_A"]["half_width"]
    eta_b_lo = chan["eta_B"]["center"] - chan["eta_B"]["half_width"]
    eta_b_hi = chan["eta_B"]["center"] + chan["eta_B"]["half_width"]
    q_lo = chan["pair_probability"]["box_low"]
    q_hi = chan["pair_probability"]["box_high"]
    vis_lo = chan["visibility"]["box_low"]
    vis_hi = chan["visibility"]["box_high"]
    points = []
    points.append({"label": "center", "eta_a": chan["eta_A"]["center"],
                   "eta_b": chan["eta_B"]["center"], "pair_probability": chan["pair_probability"]["center"],
                   "visibility": chan["visibility"]["center"]})
    for eta_a in (eta_a_lo, eta_a_hi):
        for eta_b in (eta_b_lo, eta_b_hi):
            for q in (q_lo, q_hi):
                for vis in (vis_lo, vis_hi):
                    points.append({"label": "corner", "eta_a": eta_a, "eta_b": eta_b,
                                   "pair_probability": q, "visibility": vis})
    return points


# --------------------------------------------------------------------------- diagnostics

def doc_r(instrument):
    prep = instrument["preparation"]["amplitudes"]
    return float(prep["VV"]) / float(prep["HH"])


def visibility_defs(r, delta_deg):
    """Two textbook coherence definitions + the scanned-fringe contrast, at state parameter r."""
    amps, norm = state_amplitudes(r, delta_deg)
    rho = [[a * b / (norm * norm) for b in amps] for a in amps]
    p_hh, p_vv = rho[3][3], rho[0][0]
    v_coherence = 2.0 * abs(rho[3][0]) / (p_hh + p_vv)
    # parallel / crossed coincidence contrast in the H/V basis
    c_par = p_joint(r, delta_deg, 90.0, 90.0)
    c_cross = p_joint(r, delta_deg, 90.0, 0.0)
    v_contrast = (c_par - c_cross) / (c_par + c_cross)
    # scanned fringe contrast over thetaA = theta, thetaB = -theta
    vals = [p_joint(r, delta_deg, t, -t) for t in [x * 0.25 for x in range(-360, 361)]]
    lo, hi = min(vals), max(vals)
    v_fringe = (hi - lo) / (hi + lo)
    return {"coherence": v_coherence, "hv_contrast": v_contrast, "scanned_fringe": v_fringe}


def multi_pair_ratio(m, mean_pairs):
    return mean_pairs * (m + 1.0) / (2.0 * (m + mean_pairs))


# --------------------------------------------------------------------------- main

def main():
    started = time.perf_counter()
    frozen = load_frozen()
    instrument = load_instrument()
    opt = frozen["optimizer"]
    band_cfg = frozen["band"]
    chan_cfg = frozen["channel"]

    doc_amplitudes = instrument["preparation"]["amplitudes"]
    r_doc = doc_r(instrument)
    if abs(r_doc - frozen["documented_values"]["r"]) > 1e-12:
        raise SystemExit("REPLAY_MODEL_INADEQUATE_documented_r_mismatch")
    alice = [float(x) for x in instrument["controls"]["alice"]]
    bob = [float(x) for x in instrument["controls"]["bob"]]
    if (alice != frozen["documented_values"]["alice_angles_deg"]
            or bob != frozen["documented_values"]["bob_angles_deg"]):
        raise SystemExit("REPLAY_MODEL_INADEQUATE_documented_angles_mismatch")
    theta_0_doc, theta_1_doc = alice[0], alice[1]

    results = []
    for point in box_points(frozen):
        ctx = make_context(frozen, point["eta_a"], point["eta_b"], point["pair_probability"])
        best = optimise(ctx, opt, coarse=True)
        entry = dict(point)
        entry["optimum"] = best
        results.append(entry)

    centre = results[0]["optimum"]

    # ---- band (criterion.md F14)
    r_vals = [e["optimum"]["r"] for e in results]
    t0_vals = [e["optimum"]["theta0_deg"] for e in results]
    t1_vals = [e["optimum"]["theta1_deg"] for e in results]
    pre_band = {"r": [min(r_vals), max(r_vals)],
                "theta0_deg": [min(t0_vals), max(t0_vals)],
                "theta1_deg": [min(t1_vals), max(t1_vals)]}
    wid_r = band_cfg["r_widen"]
    wid_a = band_cfg["angle_widen_deg"]
    band = {"r": [pre_band["r"][0] - wid_r, pre_band["r"][1] + wid_r],
            "theta0_deg": [pre_band["theta0_deg"][0] - wid_a, pre_band["theta0_deg"][1] + wid_a],
            "theta1_deg": [pre_band["theta1_deg"][0] - wid_a, pre_band["theta1_deg"][1] + wid_a]}

    comparisons = []
    r_lo, r_hi = band["r"]
    comparisons.append({"name": "r", "documented": r_doc, "band": [r_lo, r_hi],
                        "inside": r_lo <= r_doc <= r_hi,
                        "margin": min(r_doc - r_lo, r_hi - r_doc)})
    signed = [("angle_theta0A_deg", theta_0_doc, band["theta0_deg"][0], band["theta0_deg"][1]),
              ("angle_theta0B_deg", bob[0], -band["theta0_deg"][1], -band["theta0_deg"][0]),
              ("angle_theta1A_deg", theta_1_doc, band["theta1_deg"][0], band["theta1_deg"][1]),
              ("angle_theta1B_deg", bob[1], -band["theta1_deg"][1], -band["theta1_deg"][0])]
    for name, value, lo, hi in signed:
        comparisons.append({"name": name, "documented": value, "band": [lo, hi],
                            "inside": lo <= value <= hi, "margin": min(value - lo, hi - value)})

    all_inside = all(c["inside"] for c in comparisons)
    if all_inside:
        verdict = frozen["verdicts"]["pass"]
    else:
        verdict = frozen["verdicts"]["fail"]

    # ---- diagnostics (never part of the verdict)
    ctx_centre = make_context(frozen, chan_cfg["eta_A"]["center"], chan_cfg["eta_B"]["center"],
                              chan_cfg["pair_probability"]["center"])
    s_opt = centre["S"]
    s_doc = s_ch(ctx_centre, r_doc, theta_0_doc, theta_1_doc)
    diagnostics = {
        "D1_objective_space": {"S_at_centre_optimum": s_opt, "S_at_documented_point": s_doc,
                               "distance": s_opt - s_doc},
        "D3_threshold_check": {},
        "D4_visibility_selfcheck": {
            "published_hv": 0.999, "published_da": 0.996,
            "at_replayed_centre_r": visibility_defs(centre["r"], ctx_centre["delta_deg"]),
            "at_documented_r": visibility_defs(r_doc, ctx_centre["delta_deg"])},
        "D5_coupling_check": {"eta_A_over_snspd": chan_cfg["eta_A"]["center"] / chan_cfg["snspd_efficiency"],
                              "eta_B_over_snspd": chan_cfg["eta_B"]["center"] / chan_cfg["snspd_efficiency"]},
        "D6_multi_pair_ratio": {"m": frozen["model"]["modes_m"],
                                "mean_pairs": chan_cfg["pair_probability"]["center"],
                                "p2_over_p1": multi_pair_ratio(frozen["model"]["modes_m"],
                                                               chan_cfg["pair_probability"]["center"])},
        "variants": {},
    }
    thr = chan_cfg["published_threshold"]["with_background"]
    ctx_thr = make_context(frozen, thr, thr, chan_cfg["pair_probability"]["center"])
    thr_best = optimise(ctx_thr, opt, coarse=True)
    diagnostics["D3_threshold_check"] = {
        "eta": thr, "max_S_CH": thr_best["S"], "optimum": thr_best,
        "note": "published statement: background raises the required efficiency from 2/3 to 72.5%"}

    diag_cfg = frozen["diagnostics"]["threshold_check"]
    zero_bg = threshold_eta(frozen, opt, True, diag_cfg)
    pub_bg = threshold_eta(frozen, opt, False, diag_cfg)
    diagnostics["D3b_threshold_validation"] = {
        "zero_background": {"model_threshold": zero_bg["threshold"],
                            "published": diag_cfg["zero_background"]["published"],
                            "bracket": zero_bg["bracket"]},
        "published_background": {"model_threshold": pub_bg["threshold"],
                                 "published": diag_cfg["published_background"]["published"],
                                 "bracket": pub_bg["bracket"]},
        "note": "model-adequacy check against the published 2/3 -> 72.5% statement (paper p.4); "
                "not a pass criterion",
    }

    var = diagnostics["variants"]
    for delta in frozen["variants"]["delta_deg"]:
        ctx = make_context(frozen, chan_cfg["eta_A"]["center"], chan_cfg["eta_B"]["center"],
                           chan_cfg["pair_probability"]["center"], delta_deg=delta)
        var["delta_%g_deg" % delta] = {"published_model_parameter": False, "optimum": optimise(ctx, opt)}
    for vis in frozen["variants"]["werner_visibility"]:
        ctx = make_context(frozen, chan_cfg["eta_A"]["center"], chan_cfg["eta_B"]["center"],
                           chan_cfg["pair_probability"]["center"], werner=vis)
        var["werner_%g" % vis] = {"published_model_parameter": False, "optimum": optimise(ctx, opt)}
    if frozen["variants"]["N_free"]:
        n_max = frozen["model"]["N_free_variant_max"]
        n_vals = [n_max * (k + 1) / 30.0 for k in range(30)]
        starts = [[centre["r"], centre["theta0_deg"], centre["theta1_deg"]],
                  [0.3, 4.0, -26.0], [0.5, 20.0, -45.0], [0.15, 2.0, -15.0]]
        best_n = None
        for n_val in n_vals:
            ctx = make_context(frozen, chan_cfg["eta_A"]["center"], chan_cfg["eta_B"]["center"], n_val)
            for start in starts:
                value, r, t0, t1 = pattern_search(ctx, start, opt)
                r, t0, t1 = canonicalise(r, t0, t1)
                if best_n is None or value > best_n["S_CH"]:
                    best_n = {"S_CH": value, "r": r, "theta0_deg": t0, "theta1_deg": t1,
                              "N": n_val}
        var["N_free"] = {"published_model_parameter": False, "grid": [n_vals[0], n_vals[-1],
                                                                      len(n_vals)],
                         "best": best_n}

    attr = frozen["diagnostics"]["attribution_kappa"]
    if attr.get("enabled"):
        diagnostics["D7_attribution"] = {
            "post_hoc_declared": attr["post_hoc_declared"], "note": attr["note"],
            "definition": "eta_A = kappa*74.7%, eta_B = kappa*75.6%, other inputs at centre",
            "points": []}
        for kappa in attr["values"]:
            ctx = make_context(frozen, kappa * chan_cfg["eta_A"]["center"],
                               kappa * chan_cfg["eta_B"]["center"],
                               chan_cfg["pair_probability"]["center"])
            best = optimise(ctx, opt)
            diagnostics["D7_attribution"]["points"].append(
                {"kappa": kappa, "optimum": best})

    bindings = {
        "criterion.md": sha256_file(CRITERION_PATH),
        "../instrument.json": sha256_file(INSTRUMENT_PATH),
        "christensen-appendix-a.txt": sha256_file(APPENDIX_PATH),
        "shalm2015-channel-inputs.txt": sha256_file(PAPER_PATH),
        "replay.py": sha256_file(os.path.abspath(__file__)),
    }
    out = {
        "root": find_repo_root(HERE),
        "scope": "stage10/independent-bell/nist-real/nominal-replay: documented real Born-conditional "
                 "nominal apparatus optimum replay (NIST 2015 CH inequality), candidate input for a "
                 "later gate review",
        "verdict": verdict,
        "criterion_version": frozen["criterion_version"],
        "bindings": bindings,
        "fixed_choices": {
            "F1_state_family": frozen["model"]["state_family"] + ", r in " + str(frozen["model"]["r_domain"]),
            "F2_delta_deg": frozen["model"]["delta_deg"],
            "F2_evidence": "thesis 4.6.2 pp.46-47: tilt requires non-collinear collection and a "
                           "non-periodically-poled crystal; the 2015 source is a PPKTP (paper p.3)",
            "F3_probability_path": "amplitude: p(1,1)=<thA|<thB|psi>^2, p(1|th)=<th|rho_A|th>",
            "F4_angle_convention": "|theta> = cos(theta)|V> + sin(theta)|H>, theta from vertical; "
                                   "theta0A=-theta0B=theta0, theta1A=-theta1B=theta1",
            "F5_efficiency_extension": frozen["model"]["joint_efficiency"]
                                       + " on the joint, per side on the singles (thesis writes eps^2)",
            "F6_background": {"b_A_per_trial": chan_cfg["background_A_per_trial"],
                              "b_B_per_trial": chan_cfg["background_B_per_trial"],
                              "normalisation": chan_cfg["background_normalisation"],
                              "split": frozen["model"]["background_representative"],
                              "note": "background enters only through dcr + N*flr, so the split is inert"},
            "F7_accidentals": frozen["model"]["accidentals"],
            "F8_modes_and_mean": {"m": frozen["model"]["modes_m"], "mean_pairs": "N = pair probability",
                                  "note": "acc = acc_u does not consume m"},
            "F9_N_rule": frozen["model"]["N_rule"],
            "F10_visibility": {"consumed": chan_cfg["visibility"]["consumed"],
                               "note": "thesis App. A has no visibility parameter; no published "
                                       "visibility -> state map exists, so the box dimension is inert "
                                       "and the sensitivity is reported as declared variants"},
            "F11_objective": frozen["model"]["objective"],
            "F12_domains": {"r": frozen["model"]["r_domain"],
                            "angles_deg": frozen["model"]["angle_domain_deg"]},
            "F13_canonicalisation": "theta0 >= 0 (tie-break theta1 >= 0)",
            "F14_band": band_cfg,
            "F15_tolerance": frozen["tolerance"],
            "F16_verdicts": frozen["verdicts"],
        },
        "documented": {"r": r_doc, "alice_angles_deg": alice, "bob_angles_deg": bob,
                       "amplitudes": doc_amplitudes,
                       "source": frozen["documented_source"]},
        "box_points": results,
        "band": {"pre_widening": pre_band, "widened": band},
        "comparison": comparisons,
        "diagnostics": diagnostics,
        "elapsed_seconds": time.perf_counter() - started,
    }
    with open(REPLAY_PATH, "w", encoding="utf-8") as handle:
        json.dump(out, handle, indent=2, sort_keys=False)
        handle.write("\n")

    print("verdict:", verdict)
    print("centre optimum: r*=%.6f  theta0*=%.4f deg  theta1*=%.4f deg  S_CH*=%.6e"
          % (centre["r"], centre["theta0_deg"], centre["theta1_deg"], centre["S"]))
    print("documented   : r =%.6f  theta0 =%.4f deg  theta1 =%.4f deg  S_CH =%.6e"
          % (r_doc, theta_0_doc, theta_1_doc, s_doc))
    print("band widened : r [%.6f, %.6f]  theta0 [%.4f, %.4f]  theta1 [%.4f, %.4f]"
          % (band["r"][0], band["r"][1], band["theta0_deg"][0], band["theta0_deg"][1],
             band["theta1_deg"][0], band["theta1_deg"][1]))
    for c in comparisons:
        print("  %-16s documented %12.6f  band [%9.5f, %9.5f]  inside=%s"
              % (c["name"], c["documented"], c["band"][0], c["band"][1], c["inside"]))
    d3b = diagnostics["D3b_threshold_validation"]
    print("D3b thresholds: no background %.5f (published %.5f) | published background %.5f "
          "(published %.5f)"
          % (d3b["zero_background"]["model_threshold"], d3b["zero_background"]["published"],
             d3b["published_background"]["model_threshold"],
             d3b["published_background"]["published"]))
    print("elapsed_seconds: %.2f" % out["elapsed_seconds"])


if __name__ == "__main__":
    main()
