#!/usr/bin/env python3
"""The calibrated Jones source -> fixed gain circle -> four receiver controls."""
from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
from fractions import Fraction as F
from functools import lru_cache
import heapq
import itertools
import json
import math
from pathlib import Path
import re
import subprocess

import forward as fw

HERE = Path(__file__).resolve().parent


def optimizer_spec(config):
    spec = config["primary_optimizer"]
    return {**config, "coarse_pump_balance_deg": spec["pump_grid_deg"],
            "coarse_unprimed_source_angles_deg": spec["angle0_grid_deg"],
            "coarse_primed_source_angles_deg": spec["angle1_grid_deg"],
            "coarse_point_count": len(spec["pump_grid_deg"])*len(spec["angle0_grid_deg"])**2*len(spec["angle1_grid_deg"])**2,
            "coarse_retained_seed_count": spec["keep"], "nelder_mead_simplex_step_deg": spec["simplex_step_deg"],
            "nelder_mead_alpha": spec["reflection"], "nelder_mead_gamma": spec["expansion"],
            "nelder_mead_rho": spec["contraction"], "nelder_mead_sigma": spec["shrink"],
            "nelder_mead_iteration_cap": spec["iterations"],
            "nelder_mead_diameter_tolerance_deg": spec["diameter_stop_deg"]}


def inputs():
    criterion = fw.committed(HERE/"criterion.md")
    fw.committed(HERE/"sources.json")
    executable = fw.committed(Path(__file__).resolve())
    source_program = fw.committed(HERE/"forward.py")
    source_result = fw.committed(HERE/"forward-source.json")
    compact_result = fw.committed(HERE/"forward.json")
    subprocess.run(["git", "merge-base", "--is-ancestor", criterion["commit"], executable["commit"]],
                   cwd=fw.ROOT, check=True)
    text = (HERE/"criterion.md").read_text()
    fw.require("FW-FROZEN-BEGIN" in text and "unfrozen_draft" not in text, "UNFROZEN_FRAME_CRITERION")
    blocks = re.findall(r"```json\s*(.*?)\s*```", text, re.S)
    fw.require(len(blocks) == 1, "NONUNIQUE_FRAME_CRITERION")
    config = json.loads(blocks[0])
    report = json.loads((HERE/"forward-source.json").read_text())
    compact = json.loads((HERE/"forward.json").read_text())
    fw.require(report["schema"] == "p23-frame-window-source-snapshot/v1" and
               compact["schema"] == "p23-frame-window-primary-intake/v1" and
               report["full_scientific_json_sha256"] == compact["derivative_intake"]["full_scientific_json_sha256"] and
               [r["source_parameters"] for r in report["points"] if "source_parameters" in r] ==
               [r["source_parameters"] for r in compact["points"] if "source_parameters" in r] and
               report["version"] == config["version"] == fw.VERSION and
               report["executable_freeze"]["sha256"] == source_program["sha256"] and
               report["criterion_freeze"]["sha256"] == criterion["sha256"] and
               type(report["point_count"]) is int and report["point_count"] == 9 and
               all(report[k] is False for k in fw.FLAGS), "UNBOUND_CALIBRATED_FRAME_SOURCE")
    gaussian = fw.module("_fw_replay_frozen_gaussian", HERE.parent/"gaussian-window/gaussian.py")
    gaussian.arithmetic.PRECISION = 10**config["primary_precision_digits"]
    gaussian.SCALE = gaussian.arithmetic.PRECISION
    config = optimizer_spec({**gaussian.specification(), **config})
    for row in report["points"]:
        if row["outcome"] == "FRAME_SOURCE_OR_CALIBRATION_NOT_REALIZED":
            continue
        point = {key: F(value) if key != "point_id" else value for key, value in row["point"].items()}
        view = [{key: F(value) for key, value in r.items()}
                for r in row["source_construction"]["training_marginals"]]
        rebuilt, _ = fw.source_from_singles(view, point, config, gaussian)
        expected = {key: row["source_parameters"][key] for key in ("geometric_ratio", "rotation", "loss_inverse")}
        fw.require(rebuilt == expected, "SOURCE_SINGLE_REPLAY_CHANGED")
    return config, report, gaussian, {"criterion": criterion, "executable": executable,
                                    "source_program": source_program, "source_result": source_result,
                                    "compact_scientific_intake": compact_result}


def interval(receipt, gaussian):
    return gaussian.I(F(receipt["exact_lower"]), F(receipt["exact_upper"]))


@lru_cache(maxsize=256)
def log_interval(x, gaussian):
    fw.require(x.lo > 0, "NONPOSITIVE_GAIN_LOG_ARGUMENT")
    with localcontext() as ctx:
        ctx.prec = 80
        lo = (Decimal(x.lo.numerator)/Decimal(x.lo.denominator)).next_minus()
        hi = (Decimal(x.hi.numerator)/Decimal(x.hi.denominator)).next_plus()
        return gaussian.I(F(lo.ln().next_minus()), F(hi.ln().next_plus()))


@lru_cache(maxsize=16384)
def exp_interval(x, gaussian):
    with localcontext() as ctx:
        ctx.prec = 80
        lo = (Decimal(x.lo.numerator)/Decimal(x.lo.denominator)).next_minus()
        hi = (Decimal(x.hi.numerator)/Decimal(x.hi.denominator)).next_plus()
        return gaussian.I(F(lo.exp().next_minus()), F(hi.exp().next_plus()))


@lru_cache(maxsize=256)
def atan_interval(x, gaussian):
    y = x/(1+gaussian.square_root(1+x.square()))
    fw.require(y.max_abs() <= F(1, 2), "GAIN_ANGLE_ATAN_REDUCTION_FAILED")
    polynomial = gaussian.I.point(0)
    for k in reversed(range(80)):
        polynomial = polynomial*y.square()+F((-1)**k, 2*k+1)
    remainder = y.max_abs()**161/161
    return 2*(polynomial*y+gaussian.I(-remainder, remainder))


@lru_cache(maxsize=16384)
def trig_cached(angle, terms, pi_lo, pi_hi, gaussian):
    argument = angle*gaussian.I(pi_lo, pi_hi)/180
    def trig(cosine):
        offset = 0 if cosine else 1
        coefficients = [F((-1)**k, math.factorial(2*k+offset)) for k in range(terms)]
        polynomial = gaussian.I.point(coefficients[-1])
        for c in reversed(coefficients[:-1]):
            polynomial = polynomial*argument.square()+c
        if not cosine:
            polynomial *= argument
        power = 2*terms+offset
        remainder = argument.max_abs()**power/math.factorial(power)
        result = polynomial+gaussian.I(-remainder, remainder)
        return gaussian.I(max(F(-1), result.lo), min(F(1), result.hi))
    return trig(False), trig(True)


def trig_interval(angle, config, gaussian):
    return trig_cached(angle, config["primary_terms"], *map(F, config["pi"]), gaussian)


def gains(packet, config, gaussian):
    th, tv = map(F, packet["geometric_ratio"])
    values = []
    for t in (th, tv):
        if t == 0:
            values.append(gaussian.I.point(0))
            continue
        root = gaussian.square_root(t)
        values.append(log_interval((1+root)/(1-root), gaussian)/2)
    G = gaussian.square_root(values[0].square()+values[1].square())
    if tv == 0:
        beta = gaussian.I.point(0)
    elif th == tv:
        beta = gaussian.I.point(45)
    else:
        beta = atan_interval(values[1]/values[0], gaussian)*180/gaussian.I(*map(F, config["pi"]))
    return G, beta, {"definition": "sqrt(atanh(sqrt(tH))^2+atanh(sqrt(tV))^2)",
                     "source_geometric_ratio": packet["geometric_ratio"], "initial_gains": values,
                     "gain_norm": G, "initial_pump_balance_deg": beta,
                     "physical_H_dominant": True, "author_gamma_relation": "beta=90deg-gamma"}


def pump_kernel(G, beta, config, gaussian):
    s, c = trig_interval(beta, config, gaussian)
    gH, gV = G*c, G*s
    means = []
    for gain in (gH, gV):
        sinh = (exp_interval(gain, gaussian)-exp_interval(-gain, gaussian))/2
        means.append(sinh.square())
    return [n/(1+n) for n in means], means


def rotate_vector(packet, angle, config, gaussian):
    s, c = trig_interval(angle, config, gaussian)
    row = packet["rotation"]
    cr, sr = rotation_cached(F(row["Z"]), F(row["X"]), F(row["C_squared"]), gaussian)
    return s*cr-c*sr, s*sr+c*cr


@lru_cache(maxsize=256)
def rotation_cached(z, x, rho, gaussian):
    return fw.rotation({"rotation": {"Z": str(z), "X": str(x), "C_squared": str(rho)}}, gaussian)


@lru_cache(maxsize=256)
def loss_enclosures(a, b, gaussian):
    return a.enclosure(gaussian), b.enclosure(gaussian)


def probability_range(value, gaussian):
    lo, hi = max(F(0), value.lo), min(F(1), value.hi)
    fw.require(lo <= hi, "PROBABILITY_ENCLOSURE_INCONSISTENT_WITH_EFFECT_LEGALITY")
    return gaussian.I(lo, hi)


def score_box(packet, lam, G, box, config, gaussian):
    _, means = pump_kernel(G, box[0], config, gaussian)
    nh, nv = means
    etaA, etaB = loss_enclosures(*fw.packet_losses(packet), gaussian)
    av = [rotate_vector(packet, angle, config, gaussian) for angle in box[1:3]]
    bv = [rotate_vector(packet, angle, config, gaussian) for angle in box[3:5]]
    am = [etaA*(nh*s.square()+nv*c.square()) for s, c in av]
    bm = [etaB*(nh*s.square()+nv*c.square()) for s, c in bv]
    ba, bb = map(F, config["background_per_pulse"])
    N = config["window_pulses"]
    singlesA = [probability_range(1-gaussian.power((1-ba)/(1+m), N), gaussian) for m in am]
    singlesB = [probability_range(1-gaussian.power((1-bb)/(1+m), N), gaussian) for m in bm]
    kh = gaussian.square_root(nh*(1+nh)*etaA*etaB)
    kv = gaussian.square_root(nv*(1+nv)*etaA*etaB)
    joints, loose = [], False
    for x, y in ((0, 0), (0, 1), (1, 0), (1, 1)):
        sa, ca = av[x]
        sb, cb = bv[y]
        plus, minus = kh*sa*sb+kv*ca*cb, kh*sa*sb-kv*ca*cb
        denplus, denminus = (1+am[x])*(1+bm[y])-plus.square(), (1+am[x])*(1+bm[y])-minus.square()
        if min(denplus.lo, denminus.lo) <= 0:
            joint = gaussian.I(0, min(singlesA[x].hi, singlesB[y].hi))
            loose = True
        else:
            q = (1-lam)/denplus+lam/denminus
            qa, qb = 1-singlesA[x], 1-singlesB[y]
            qab = gaussian.power((1-ba)*(1-bb)*q, N)
            raw = 1-qa-qb+qab
            joint = gaussian.I(max(F(0), raw.lo), min(raw.hi, singlesA[x].hi, singlesB[y].hi, F(1)))
            fw.require(joint.lo <= joint.hi, "JOINT_ENCLOSURE_INCONSISTENT_WITH_LOCAL_EFFECTS")
        joints.append(joint)
    CH = joints[0]+joints[1]+joints[2]-joints[3]-singlesA[0]-singlesB[0]
    return CH, {"joint": joints, "singles_A": singlesA, "singles_B": singlesB,
                 "means_HV": means, "used_valid_local_probability_upper_bound": loose}


def wrap_angle(a):
    return (a+90) % 180-90


def coordinates_box(beta0, offsets, gaussian):
    return [beta0+offsets[0]]+[gaussian.I.point(a) for a in offsets[1:]]


def local_candidate(packet, lam, G, beta0, config, gaussian, seed):
    current = (F(str(seed[0]))-beta0.midpoint(), *[F(str(a)) for a in seed[1:]])
    score, reads = score_box(packet, lam, G, coordinates_box(beta0, current, gaussian), config, gaussian)
    initial_score, initial_reads = score, reads
    moves, levels = [], []
    step = F(config["optimization_initial_step_deg"])
    for level in range(config["optimization_halving_levels"]):
        accepted, evaluated = 0, 0
        while accepted < config["optimization_accepted_moves_per_level"]:
            candidates = []
            for k in range(5):
                for sign in (-1, 1):
                    nxt = list(current)
                    nxt[k] += sign*step
                    if k:
                        nxt[k] = wrap_angle(nxt[k])
                    else:
                        balance = beta0+nxt[0]
                        if balance.lo < 0 or balance.hi > 45:
                            continue
                    nxt = tuple(nxt)
                    value, detail = score_box(packet, lam, G, coordinates_box(beta0, nxt, gaussian), config, gaussian)
                    evaluated += 1
                    if value.lo > score.hi:
                        candidates.append((value, nxt, detail))
            if not candidates:
                break
            candidates.sort(key=lambda item: (-item[0].lo, item[1]))
            value, nxt, detail = candidates[0]
            moves.append({"level": level, "step_deg": step, "before": current, "after": nxt,
                          "CH_before": score, "CH_after": value, "strict_gain_lower": value.lo-score.hi})
            current, score, reads = nxt, value, detail
            accepted += 1
        levels.append({"level": level, "step_deg": step, "accepted_moves": accepted,
                       "evaluated_neighbours": evaluated})
        step /= 2
    return {"status": "LOCAL_OPTIMIZATION_CANDIDATE", "source_balance_offset_and_angles_deg": current,
            "control_box": coordinates_box(beta0, current, gaussian), "CH": score, "reads": reads,
            "initial_CH": initial_score, "initial_reads": initial_reads, "moves": moves, "levels": levels,
            "joint_counts_used": False, "public_CI_used": False, "documented_state_ratio_used": False}


class FloatObjective:
    def __init__(self, packet, lam, G, config, gaussian):
        self.G = float(G.midpoint())
        self.delta = math.radians(float(source_delta(packet, config, gaussian).midpoint()))
        self.lam = float(lam.midpoint())
        self.eta = [float(v.enclosure(gaussian).midpoint()) for v in fw.packet_losses(packet)]
        self.background = list(map(float, map(F, config["background_per_pulse"])))
        self.N = config["window_pulses"]

    def __call__(self, controls):
        beta, a0, a1, b0, b1 = controls
        if not 0 <= beta <= 45:
            return -math.inf
        beta = math.radians(beta)
        nh, nv = math.sinh(self.G*math.cos(beta))**2, math.sinh(self.G*math.sin(beta))**2
        av = [(math.sin(math.radians(a)-self.delta), math.cos(math.radians(a)-self.delta)) for a in (a0, a1)]
        bv = [(math.sin(math.radians(b)-self.delta), math.cos(math.radians(b)-self.delta)) for b in (b0, b1)]
        muA = [self.eta[0]*(nh*s*s+nv*c*c) for s, c in av]
        muB = [self.eta[1]*(nh*s*s+nv*c*c) for s, c in bv]
        kh, kv = [math.sqrt(n*(1+n)*self.eta[0]*self.eta[1]) for n in (nh, nv)]
        sA = [-math.expm1(self.N*(math.log1p(-self.background[0])-math.log1p(m))) for m in muA]
        sB = [-math.expm1(self.N*(math.log1p(-self.background[1])-math.log1p(m))) for m in muB]
        joints = []
        for x, y in ((0, 0), (0, 1), (1, 0), (1, 1)):
            sa, ca = av[x]
            sb, cb = bv[y]
            base = muA[x]+muB[y]+muA[x]*muB[y]
            dp, dm = base-(kh*sa*sb+kv*ca*cb)**2, base-(kh*sa*sb-kv*ca*cb)**2
            minus_one = -(1-self.lam)*dp/(1+dp)-self.lam*dm/(1+dm)
            logq = self.N*(math.log1p(-self.background[0])+math.log1p(-self.background[1])+math.log1p(minus_one))
            joints.append(sA[x]+sB[y]+math.expm1(logq))
        return math.fsum((joints[0], joints[1], joints[2], -joints[3], -sA[0], -sB[0]))


def float_wrap(value):
    return (value+90.0) % 180.0-90.0


def normalize_controls(value):
    return (value[0], *(float_wrap(x) for x in value[1:]))


def lift_controls(value, anchor):
    return (value[0], *(anchor[i]+float_wrap(value[i]-anchor[i]) for i in range(1, 5)))


def nelder_mead(objective, seed, config):
    step = float(F(config["nelder_mead_simplex_step_deg"]))
    simplex = [normalize_controls(seed)]
    for axis in range(5):
        value = list(seed)
        value[axis] += step
        simplex.append(normalize_controls(value))
    scored = [(objective(v), v) for v in simplex]
    alpha, gamma, rho, sigma = [float(F(config[k])) for k in
                              ("nelder_mead_alpha", "nelder_mead_gamma", "nelder_mead_rho", "nelder_mead_sigma")]
    diameter = math.inf
    iterations = 0
    for iterations in range(config["nelder_mead_iteration_cap"]):
        scored.sort(key=lambda item: (-item[0], item[1]))
        best = scored[0][1]
        lifted = [lift_controls(v, best) for _, v in scored]
        diameter = max(abs(v[k]-best[k]) for v in lifted for k in range(5))
        if diameter <= float(F(config["nelder_mead_diameter_tolerance_deg"])):
            break
        centroid = tuple(math.fsum(v[k] for v in lifted[:-1])/5 for k in range(5))
        worst = lifted[-1]
        def evaluate(value):
            value = normalize_controls(value)
            return objective(value), value
        reflected = evaluate(tuple(centroid[k]+alpha*(centroid[k]-worst[k]) for k in range(5)))
        if reflected[0] > scored[0][0]:
            expanded = evaluate(tuple(centroid[k]+gamma*(lift_controls(reflected[1], best)[k]-centroid[k]) for k in range(5)))
            scored[-1] = expanded if expanded[0] > reflected[0] else reflected
        elif reflected[0] > scored[-2][0]:
            scored[-1] = reflected
        else:
            outside = reflected[0] > scored[-1][0]
            target = lift_controls(reflected[1], best) if outside else worst
            contracted = evaluate(tuple(centroid[k]+rho*(target[k]-centroid[k]) for k in range(5)))
            if contracted[0] > (reflected[0] if outside else scored[-1][0]):
                scored[-1] = contracted
            else:
                scored = [scored[0]]+[evaluate(tuple(best[k]+sigma*(v[k]-best[k]) for k in range(5)))
                                      for v in lifted[1:]]
    scored.sort(key=lambda item: (-item[0], item[1]))
    return {"controls_deg": scored[0][1], "float_CH": scored[0][0], "iterations": iterations+1,
            "simplex_diameter_deg": diameter,
            "converged": diameter <= float(F(config["nelder_mead_diameter_tolerance_deg"]))}


def multistart_candidate(packet, lam, G, config, gaussian):
    objective = FloatObjective(packet, lam, G, config, gaussian)
    delta = math.degrees(objective.delta)
    beta = list(map(float, map(F, config["coarse_pump_balance_deg"])))
    a0 = list(map(float, map(F, config["coarse_unprimed_source_angles_deg"])))
    a1 = list(map(float, map(F, config["coarse_primed_source_angles_deg"])))
    scored = []
    for b, uA, pA, uB, pB in itertools.product(beta, a0, a1, a0, a1):
        controls = normalize_controls((b, uA+delta, pA+delta, uB+delta, pB+delta))
        scored.append((objective(controls), controls))
    fw.require(len(scored) == config["coarse_point_count"], "INCOMPLETE_FIVE_VARIABLE_COARSE_DOMAIN")
    scored.sort(key=lambda item: (-item[0], item[1]))
    runs = [nelder_mead(objective, seed, config) for _, seed in scored[:config["coarse_retained_seed_count"]]]
    runs.sort(key=lambda row: (-row["float_CH"], row["controls_deg"]))
    best = runs[0]
    return best["controls_deg"], {"coarse_point_count": len(scored),
                                 "retained_seeds": [v for _, v in scored[:config["coarse_retained_seed_count"]]],
                                 "Nelder_Mead_runs": runs, "selected_converged": best["converged"],
                                 "lambda_midpoint_role": "float_candidate_only",
                                 "printed_r_used": False, "joint_counts_used": False, "public_CI_used": False}


def global_enclosure(packet, lam, G, candidate, config, gaussian):
    initial = [gaussian.I(0, 45)]+[gaussian.I(-90, 90) for _ in range(4)]
    heap, serial, pruned, splits = [], 0, [], []
    best = candidate["CH"].lo
    def add(box):
        nonlocal serial
        value, detail = score_box(packet, lam, G, box, config, gaussian)
        node = {"id": serial, "box": box, "CH_upper": value.hi,
                "used_valid_local_probability_upper_bound": detail["used_valid_local_probability_upper_bound"]}
        serial += 1
        if value.hi <= best:
            pruned.append(node)
        else:
            lex = tuple((x.lo, x.hi) for x in box)
            heapq.heappush(heap, (-value.hi, lex, node["id"], node))
        return node
    add(initial)
    for _ in range(config["global_optimum_split_cap"]):
        if not heap or -heap[0][0]-best <= F(config["global_optimum_gap_tolerance"]):
            break
        _, _, _, node = heapq.heappop(heap)
        box = node["box"]
        widths = [(x.hi-x.lo)/(45 if i == 0 else 180) for i, x in enumerate(box)]
        axis = min(i for i, v in enumerate(widths) if v == max(widths))
        mid = (box[axis].lo+box[axis].hi)/2
        left, right = list(box), list(box)
        left[axis], right[axis] = gaussian.I(box[axis].lo, mid), gaussian.I(mid, box[axis].hi)
        lnode, rnode = add(left), add(right)
        splits.append({"parent": node["id"], "axis": axis, "midpoint": mid,
                       "children": [lnode["id"], rnode["id"]]})
    upper = max(best, -heap[0][0] if heap else best)
    gap = upper-best
    return {"status": "GLOBAL_OPTIMUM_ENCLOSED" if gap <= F(config["global_optimum_gap_tolerance"])
            else "GLOBAL_OPTIMUM_UNRESOLVED", "candidate_lower": best, "global_upper": upper, "gap": gap,
            "root_box": initial, "partition_splits": splits, "pruned_boxes": pruned,
            "active_boxes": [item[3] for item in sorted(heap)], "split_count": len(splits)}


def source_delta(packet, config, gaussian):
    z, x = F(packet["rotation"]["Z"]), F(packet["rotation"]["X"])
    rho = F(packet["rotation"]["C_squared"])
    if rho == 0:
        return gaussian.I.point(0)
    if x == 0:
        return gaussian.I.point(90 if z < 0 else 0)
    C = gaussian.square_root(rho)
    pi = gaussian.I(*map(F, config["pi"]))
    if z >= 0:
        return atan_interval(x/(C+z), gaussian)*180/pi
    angle = 90-atan_interval((C+z)/abs(x), gaussian)*180/pi
    return angle if x > 0 else -angle


def candidate_components(packet, G, candidate, config, gaussian):
    t, _ = pump_kernel(G, candidate["control_box"][0], config, gaussian)
    ratio = gaussian.square_root(t[1]/t[0])
    delta = source_delta(packet, config, gaussian)
    original = candidate["control_box"][1:]
    reflected = []
    for a in original:
        raw = 2*delta-a
        shift = (raw.lo+90)//180
        lo, hi = raw.lo-180*shift, raw.hi-180*shift
        fw.require(-90 <= lo <= hi < 90, "REFLECTED_REPRESENTATIVE_UNRESOLVED")
        reflected.append(gaussian.I(lo, hi))
    sign = original[0]-delta
    if sign.lo >= 0:
        chosen = original
    elif sign.hi < 0:
        chosen = reflected
    else:
        fw.require(False, "SOURCE_SYMMETRY_REPRESENTATIVE_UNRESOLVED")
    return {"r_cond": ratio, "angles_deg": chosen, "original_angles_deg": original,
            "reflected_angles_deg": reflected, "source_delta_deg": delta,
            "representative_rule": "source reflection with a0-delta nonnegative"}


def documented_beta(target, G, config, gaussian):
    lo, hi = F(0), F(45)
    for _ in range(96):
        if hi-lo <= F(1, 2**60):
            return gaussian.I(lo, hi)
        mid = (lo+hi)/2
        t, _ = pump_kernel(G, gaussian.I.point(mid), config, gaussian)
        ratio = gaussian.square_root(t[1]/t[0])
        if ratio.lo > target:
            hi = mid
        elif ratio.hi < target:
            lo = mid
        else:
            fw.require(False, "DOCUMENTED_RATIO_GAIN_ROOT_UNRESOLVED")
    raise ValueError("DOCUMENTED_RATIO_GAIN_ROOT_UNRESOLVED")


def documented_readout(packet, lam, G, components, config, gaussian):
    instrument = json.loads((HERE/config["documented_source"]).resolve().read_text())
    amplitudes = instrument["preparation"]["amplitudes"]
    ratio = F(amplitudes["VV"])/F(amplitudes["HH"])
    angles = list(map(F, instrument["controls"]["alice"]+instrument["controls"]["bob"]))
    beta = documented_beta(ratio, G, config, gaussian)
    score, reads = score_box(packet, lam, G, [beta]+list(map(gaussian.I.point, angles)), config, gaussian)
    delta = components["source_delta_deg"]
    if (angles[0]-delta).hi < 0:
        canonical = [2*delta-a for a in angles]
    else:
        canonical = list(map(gaussian.I.point, angles))
    diffs = [components["r_cond"]-ratio]+[a-b for a, b in zip(components["angles_deg"], canonical)]
    widths = [F(config["five_component_rounding_half_width_r"])]+[F(config["five_component_rounding_half_width_angle_deg"])]*4
    return {"r_public": ratio, "raw_angles_deg": angles, "canonical_angles_deg": canonical,
            "fixed_gain_circle_balance_deg": beta, "CH": score, "reads": reads,
            "component_differences": diffs, "rounding_half_widths": widths,
            "candidate_rounding_checks": [v.lo >= -w and v.hi <= w for v, w in zip(diffs, widths)],
            "status": "CANDIDATE_COMPARISON_WITH_PRINTED_COMPONENTS"}


def generate(global_diagnostic=False):
    config, source, gaussian, bindings = inputs()
    records = []
    for row in source["points"]:
        if row["outcome"] == "FRAME_SOURCE_OR_CALIBRATION_NOT_REALIZED":
            records.append({"point": row["point"], "outcome": "NUMERICAL_BAND_UNRESOLVED",
                            "failure_reason": row["failure_reason"], "partial_point_discarded": False})
            continue
        packet = row["source_parameters"]
        lam = interval(row["phase_flip_probability_enclosure"], gaussian)
        G, beta0, gain_readout = gains(packet, config, gaussian)
        seed, multistart = multistart_candidate(packet, lam, G, config, gaussian)
        candidate = local_candidate(packet, lam, G, beta0, config, gaussian, seed)
        global_bound = global_enclosure(packet, lam, G, candidate, config, gaussian) if global_diagnostic else {
            "status": "OPTIONAL_GLOBAL_DIAGNOSTIC_NOT_EXECUTED", "required_for_numerical_band": False}
        components = candidate_components(packet, G, candidate, config, gaussian)
        documented = documented_readout(packet, lam, G, components, config, gaussian)
        records.append({"point": row["point"], "source_parameters": packet, "gain_readout": gain_readout,
                        "multistart_search": multistart, "candidate": candidate,
                        "global_optimum": global_bound, "five_components": components,
                        "documented_readout": documented,
                        "strict_improvement_over_documented_score_lower": candidate["CH"].lo-documented["CH"].hi,
                        "source_calibration_fields_reoptimized": False})
    complete = all("five_components" in r for r in records)
    bounds = [[r["five_components"]["r_cond"], *r["five_components"]["angles_deg"]] for r in records if "five_components" in r]
    component_band = [[min(v[i].lo for v in bounds), max(v[i].hi for v in bounds)] for i in range(5)] if complete else None
    rounding = [F(config["five_component_rounding_half_width_r"])]+[F(config["five_component_rounding_half_width_angle_deg"])]*4
    component_band = [[lo-w, hi+w] for (lo, hi), w in zip(component_band, rounding)] if complete else None
    all_converged = complete and all(r["multistart_search"]["selected_converged"] for r in records)
    return fw.serial({"schema": "p23-frame-window-replay/v1", "version": fw.VERSION, "bindings": bindings,
                       "points": records, "point_count": len(records), "five_component_candidate_band": component_band,
                       "band_status": "NUMERICAL_CANDIDATE_BAND" if all_converged else "NUMERICAL_BAND_UNRESOLVED",
                       "global_maximum_kernel_claimed": False,
                       "bell_event_files_read": 0, "retrospective": True,
                       "joint_counts_used_to_optimize": False, "public_CI_used_to_optimize": False,
                       **{k: False for k in fw.FLAGS}})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--global-diagnostic", action="store_true")
    args = parser.parse_args()
    result = generate(args.global_diagnostic)
    text = json.dumps(result, indent=2, allow_nan=False)+"\n"
    if not args.check_only:
        (HERE/"replay.json").write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
