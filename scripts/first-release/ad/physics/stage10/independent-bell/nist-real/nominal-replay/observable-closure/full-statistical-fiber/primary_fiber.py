#!/usr/bin/env python3
"""Complete public training fibre: observable chart and shared-phase outer cover."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import gzip
import hashlib
import heapq
import itertools
import json
import math
from pathlib import Path
import re
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import primary as parent

VERSION = "p23-full-statistical-fiber-ef0003"
NAMES = ("A0", "B0", "A1", "B1", "J0", "J1")
AXES = ("alpha0", "beta0", "alpha1", "beta1", "loss")
CTX = None


def require(value, reason):
    if not value:
        raise ValueError(reason)


def context():
    global CTX
    if CTX is not None:
        return CTX
    parent_config, _, gauss, utility, _, _ = parent.configuration()
    spec = json.loads(re.findall(r"\x60\x60\x60json\s*(.*?)\s*\x60\x60\x60",
                                (HERE / "criterion.md").read_text(), re.S)[0])
    require(spec["version"] == VERSION and spec["all_training_intervals_used"] is True,
            "incorrect_full_fiber_contract")
    manifest = json.loads((HERE / "sources.json").read_text())
    require(manifest["version"] == VERSION, "source_revision_mismatch")
    bindings = [parent.frozen(HERE / "criterion.md"), parent.frozen(HERE / "sources.json"),
                parent.frozen(__file__)]
    for row in manifest["inputs"]:
        path = parent.ROOT / row["path"]
        require(parent.digest(path) == row["sha256"], "full_fiber_source_binding_changed:" + row["path"])
    gauss.SCALE = gauss.arithmetic.PRECISION = 10 ** spec["precision_digits"]
    cfg = {**parent_config, **spec, "primary_terms": spec["primary_trig_terms"]}
    trig = lambda degrees: utility.trig_deg(F(degrees), cfg, gauss)
    sa, ca = zip(*(trig(2 * F(a)) for a in spec["angles_deg"][:2]))
    require(sa[0].lo > 0 and sa[1].hi < 0 and (ca[0] - ca[1]).lo > 0,
            "training_angle_signs_unresolved")
    cells = []
    angles = list(map(F, spec["angles_deg"]))
    for a, b in itertools.product(angles[:2], angles[2:]):
        ss, cc = trig(a + b)
        cells.append((trig(a - b)[1], cc, ss))
    CTX = {"spec": cfg, "manifest": manifest, "gauss": gauss, "utility": utility,
           "I": gauss.I, "s": sa, "c": ca, "cells": cells, "bindings": bindings}
    return CTX


def ci_view(report):
    q = report["common_mean_confidence"]
    fields = (q["sA_cell"][0], q["sB_cell"][0], q["sA_cell"][3], q["sB_cell"][3],
              q["j"][0], q["j"][3])
    I = context()["I"]
    return {name: I(F(row["exact_lower"]), F(row["exact_upper"])) for name, row in zip(NAMES, fields)}


def hull(values):
    I = context()["I"]
    return I(min(v.lo for v in values), max(v.hi for v in values))


def intersect(a, b):
    lo, hi = max(a.lo, b.lo), min(a.hi, b.hi)
    return None if lo > hi else context()["I"](lo, hi)


def positive_outer(value):
    return intersect(value, context()["I"](0, max(F(0), value.hi)))


def powi(value, n):
    return context()["gauss"].power(value, n)


def root1p_minus1(value):
    c = context()
    require(value.max_abs() <= F(c["spec"]["binomial_input_abs_max"]), "binomial_root_domain")
    I, coefficient = c["I"], F(1)
    polynomial, power = I.point(0), I.point(1)
    for k in range(1, c["spec"]["binomial_terms"] + 1):
        coefficient *= (F(1, 5) - (k - 1)) / k
        power *= value
        polynomial += coefficient * power
    next_coefficient = coefficient * (F(1, 5) - c["spec"]["binomial_terms"]) / (c["spec"]["binomial_terms"] + 1)
    remainder = abs(next_coefficient) * value.max_abs() ** (c["spec"]["binomial_terms"] + 1) / (1 - value.max_abs())
    return polynomial + I(-remainder, remainder)


def inverse_single(rate, background):
    c = context()
    lo = (1 - background) / c["utility"].nth_root(1 - rate.lo, 5, c["spec"]["precision_digits"], c["I"]) - 1
    hi = (1 - background) / c["utility"].nth_root(1 - rate.hi, 5, c["spec"]["precision_digits"], c["I"]) - 1
    return c["I"](lo.lo, hi.hi)


def training_domain(ci):
    c = context()
    ba, bb = map(F, c["spec"]["background_per_pulse"])
    means = [inverse_single(ci[name], bg) for name, bg in zip(NAMES[:4], (ba, bb, ba, bb))]
    require(all(v.lo > 0 for v in means), "single_not_above_background")
    require(ci["A1"].lo > ci["A0"].hi and ci["B1"].lo > ci["B0"].hi,
            "equal_mode_chart_requires_separate_coverage")
    return means + [c["I"](0, 1)]


def covariance(box):
    a0, b0, a1, b1, loss = box
    c = context()
    s0, s1 = c["s"]
    c0, c1 = c["c"]
    denominator = s1 * b0 - s0 * b1
    require(denominator.hi < 0, "ratio_denominator_not_strictly_negative")
    r = (s1 * a0 - s0 * a1) / denominator
    u0, u1 = (a0 + r * b0) / 2, (a1 + r * b1) / 2
    z = (u1 - u0) / (c0 - c1)
    m, x = u0 + z * c0, -(a0 - r * b0) / (2 * s0)
    require(r.lo > 0 and z.lo > 0, "source_chart_not_qualified")
    r2 = z.square() + x.square()
    psd = m.square() - r2
    if psd.hi < 0 or loss.lo > r.hi:
        return None
    psd = positive_outer(psd)
    t2 = psd * positive_outer((m + loss).square() - r2)
    t2 = positive_outer(t2)
    return {"m": m, "z": z, "x": x, "r": r, "e": loss, "R2": r2, "P": psd, "T2": t2,
            "means": ((a0, a1), (b0, b1))}


def single_window(mean, background):
    return 1 - powi((1 - background) / (1 + mean), 5)


def coefficients(source):
    c = context()
    m, z, x, r, e, r2 = (source[k] for k in ("m", "z", "x", "r", "e", "R2"))
    result = []
    for index, (d, co, si) in enumerate(c["cells"]):
        ax, by = divmod(index, 2)
        ma, mb = source["means"][0][ax], source["means"][1][by]
        y = z * co + x * si
        correlation = ((m.square() + r2 + e * m) * (d.square() + y.square() / r2) / 2
                       - (2 * m + e) * d * y) / r
        correlation = positive_outer(correlation)
        if correlation is None:
            return None
        g = (d.square() - y.square() / r2) / (2 * r)
        D = (1 + ma) * (1 + mb)
        L = D - correlation
        E = L.square() - g.square() * source["T2"]
        if E.lo <= 0:
            return None
        A = correlation * L + g.square() * source["T2"]
        result.append({"ma": ma, "mb": mb, "D": D, "L": L, "g": g, "E": E, "A": A})
    return result


def omega_bound(sa, sb, joint):
    return root1p_minus1((joint - sa * sb) / ((1 - sa) * (1 - sb)))


def affine_phase_clip(K, g, lower, upper):
    if g.lo == g.hi == 0:
        return None if lower.lo > 0 or upper.hi < 0 else K
    if g.contains(0):
        product = g * K
        return None if product.hi < lower.lo or product.lo > upper.hi else K
    lo, hi = lower / g, upper / g
    return intersect(K, context()["I"](lo.lo, hi.hi) if g.lo > 0
                     else context()["I"](hi.lo, lo.hi))


def phase_domain(source, cells, ci):
    c = context()
    T = c["gauss"].square_root(source["T2"])
    K = c["I"](-T.hi, T.hi)
    ba, bb = map(F, c["spec"]["background_per_pulse"])
    slabs = []
    for index, name in ((0, "J0"), (3, "J1")):
        cell = cells[index]
        sa, sb = single_window(cell["ma"], ba), single_window(cell["mb"], bb)
        low = omega_bound(sa, sb, c["I"].point(ci[name].lo))
        high = omega_bound(sa, sb, c["I"].point(ci[name].hi))
        lower, upper = (low * cell["E"] - cell["A"]) / cell["D"], (high * cell["E"] - cell["A"]) / cell["D"]
        K = affine_phase_clip(K, cell["g"], lower, upper)
        slabs.append({"cell": index, "lower": lower, "upper": upper, "g": cell["g"]})
        if K is None:
            return None, slabs
    return K, slabs


def window_readout(cell, K):
    c = context()
    ba, bb = map(F, c["spec"]["background_per_pulse"])
    pa, pb = (1 - ba) / (1 + cell["ma"]), (1 - bb) / (1 + cell["mb"])
    sa, sb = 1 - powi(pa, 5), 1 - powi(pb, 5)
    connected = positive_outer((cell["A"] + cell["D"] * cell["g"] * K) / cell["E"])
    require(connected is not None, "negative_connected_readout_outer")
    local = pa * pb
    excess = sum((math.comb(5, i) * powi(local, 5) * powi(connected, i)
                  for i in range(1, 6)), c["I"].point(0))
    joint = sa * sb + excess
    I = c["I"]
    joint = intersect(joint, I(0, min(sa.hi, sb.hi)))
    require(joint is not None, "empty_physical_joint_outer")
    outcomes = [joint, sa - joint, sb - joint, 1 - sa - sb + joint]
    return {"sA": sa, "sB": sb, "j": joint, "outcomes": [intersect(v, I(0, 1)) for v in outcomes]}


def evaluate(box, ci):
    source = covariance(box)
    if source is None:
        return {"status": "excluded", "reason": "whole_box_physical_violation"}
    cells = coefficients(source)
    if cells is None:
        return {"status": "unresolved", "reason": "source_denominator_outer_not_positive"}
    K, slabs = phase_domain(source, cells, ci)
    if K is None:
        return {"status": "excluded", "reason": "whole_box_shared_phase_intersection_empty", "slabs": slabs}
    try:
        windows = [window_readout(cell, K) for cell in cells]
    except ValueError:
        return {"status": "unresolved", "reason": "physical_readout_outer_requires_refinement"}
    for index, key in ((0, "J0"), (3, "J1")):
        if intersect(windows[index]["j"], ci[key]) is None:
            return {"status": "excluded", "reason": "whole_box_joint_training_disjoint"}
    return {"status": "retained", "phase": K, "slabs": slabs, "source": source,
            "cells": windows, "paired_joint_sum": windows[1]["j"] + windows[2]["j"],
            "paired_joint_difference": windows[1]["j"] - windows[2]["j"],
            "CH": windows[0]["j"] + windows[1]["j"] + windows[2]["j"] - windows[3]["j"]
                  - windows[0]["sA"] - windows[0]["sB"]}


def pack(value):
    c = context()
    if isinstance(value, c["I"]):
        return {"exact_lower": str(value.lo), "exact_upper": str(value.hi)}
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {k: pack(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [pack(v) for v in value]
    return value


def split_axis(unit):
    spec = context()["spec"]
    if unit[4][1] - unit[4][0] > F(spec["loss_first_normalized_width"]):
        return 4
    return min(range(5), key=lambda i: (-(unit[i][1] - unit[i][0]), i))


def source_box(unit, domain):
    I = context()["I"]
    return [I(d.lo + lo * (d.hi - d.lo), d.lo + hi * (d.hi - d.lo))
            for (lo, hi), d in zip(unit, domain)]


def cover(ci, domain, cap=None):
    spec = context()["spec"]
    cap = spec["primary_split_cap"] if cap is None else cap
    root = tuple((F(0), F(1)) for _ in range(5))
    queue, sequence = [(-5, 0, "", root, 0)], 0
    splits, nodes, leaves = [], [], []
    while queue:
        _, _, path, unit, depth = heapq.heappop(queue)
        box = source_box(unit, domain)
        value = evaluate(box, ci)
        nodes.append({"path": path, "status": value["status"], "reason": value.get("reason")})
        if value["status"] == "excluded":
            leaves.append({"path": path, "classification": "excluded", "proof": value})
            continue
        axis = split_axis(unit)
        width = unit[axis][1] - unit[axis][0]
        if width <= F(spec["normalized_width_stop"]) or depth >= spec["max_depth"] or len(splits) >= cap:
            leaves.append({"path": path, "classification": "retained_boundary",
                           "stop": "resource_cap" if len(splits) >= cap else "width_or_depth",
                           "unit_box": unit, "qualified_outer": value})
            continue
        lo, hi = unit[axis]
        mid = (lo + hi) / 2
        splits.append({"path": path, "axis": axis, "midpoint": mid})
        for label, ends in (("L", (lo, mid)), ("R", (mid, hi))):
            child = list(unit); child[axis] = ends; child = tuple(child)
            sequence += 1
            priority = -sum(b - a for a, b in child)
            heapq.heappush(queue, (priority, sequence, path + str(axis) + label, child, depth + 1))
        if len(splits) % 256 == 0:
            print(json.dumps({"primary_splits": len(splits), "pending": len(queue)}), flush=True)
    require(len(nodes) == 2 * len(splits) + 1 and len(leaves) == len(splits) + 1,
            "incomplete_cover_tree")
    return {"coordinate_space": "four_inverse_single_mean_intervals_and_loss", "axes": AXES,
            "initial_box": domain, "split_count": len(splits), "split_cap": cap,
            "all_leaves_preserved": True, "cap_reached": len(splits) >= cap,
            "splits": splits, "nodes": nodes, "leaves": leaves}


def point_member(box, ci):
    c = context()
    source, cells = covariance(box), None
    if source is None or box[4].lo <= 0 or box[4].hi > source["r"].lo or (source["m"].square() - source["R2"]).lo < 0:
        return []
    cells = coefficients(source)
    if cells is None:
        return []
    T = c["gauss"].square_root(source["T2"])
    lo, hi = -T.lo, T.lo
    ba, bb = map(F, c["spec"]["background_per_pulse"])
    for index, key in ((0, "J0"), (3, "J1")):
        cell = cells[index]
        if cell["g"].contains(0):
            continue
        sa, sb = single_window(cell["ma"], ba), single_window(cell["mb"], bb)
        lower = (omega_bound(sa, sb, c["I"].point(ci[key].lo)) * cell["E"] - cell["A"]) / (cell["D"] * cell["g"])
        upper = (omega_bound(sa, sb, c["I"].point(ci[key].hi)) * cell["E"] - cell["A"]) / (cell["D"] * cell["g"])
        a, b = (lower.hi, upper.lo) if cell["g"].lo > 0 else (upper.hi, lower.lo)
        lo, hi = max(lo, a), min(hi, b)
    if lo > hi:
        return []
    answer = []
    for k in ((lo + hi) / 2, lo, hi):
        K = c["I"].point(k)
        windows = [window_readout(cell, K) for cell in cells]
        checks = ((windows[0]["sA"], "A0"), (windows[0]["sB"], "B0"), (windows[3]["sA"], "A1"),
                  (windows[3]["sB"], "B1"), (windows[0]["j"], "J0"), (windows[3]["j"], "J1"))
        if not all(ci[name].lo <= value.lo <= value.hi <= ci[name].hi for value, name in checks):
            continue
        C = c["gauss"].square_root(source["R2"])
        e, r = box[4], source["r"]
        h, v = source["m"] + C, source["m"] - C
        coherence = K / T if T.lo > 0 else c["I"].point(0)
        if coherence.lo < -1 or coherence.hi > 1:
            continue
        answer.append({"recipe": {"inverse_single_means": box[:4], "loss": e, "phase_amplitude": K},
                       "source": {"nH": h / e, "nV": v / e, "etaA": e, "etaB": e / r,
                                  "cosR": c["gauss"].square_root((1 + source["z"] / C) / 2),
                                  "sinR": (source["x"] / C) /
                                          (2 * c["gauss"].square_root((1 + source["z"] / C) / 2)),
                                  "sin2R": source["x"] / C, "lambda": (1 - coherence) / 2,
                                  "pure_mode_phase_readout_equivalence": T.hi == 0},
                       "cells": windows, "all_six_training_enclosures_contained": True})
    return answer


def members(ci, domain):
    c = context()
    fractions = list(map(F, c["spec"]["witness_axis_fractions"]))
    result, evaluated = [], 0
    for weights in itertools.product(fractions, repeat=4):
        means = [c["I"].point(d.lo + w * (d.hi - d.lo)) for d, w in zip(domain[:4], weights)]
        for j in range(1, c["spec"]["witness_loss_denominator"] + 1):
            box = means + [c["I"].point(F(j, c["spec"]["witness_loss_denominator"]))]
            evaluated += 1
            for value in point_member(box, ci):
                value["recipe"]["ci_fractions"] = list(weights)
                result.append(value)
                if len(result) >= c["spec"]["member_limit"]:
                    return result, evaluated
    return result, evaluated


def logical_sha(value):
    raw = json.dumps(pack(value), sort_keys=True, separators=(",", ":"), allow_nan=False).encode()
    return hashlib.sha256(raw).hexdigest()


def comparisons(payload, report):
    I = context()["I"]
    q = report["common_mean_confidence"]
    target = {}
    for index in (1, 2):
        target[index] = {name: I(F(q[field][index]["exact_lower"]), F(q[field][index]["exact_upper"]))
                         for name, field in (("sA", "sA_cell"), ("sB", "sB_cell"), ("j", "j"))}
    retained = [r for r in payload["cover"]["leaves"] if r["classification"] != "excluded"]
    uniform, unresolved, envelopes = True, 0, {i: {} for i in (1, 2)}
    for leaf in retained:
        value = leaf["qualified_outer"]
        if value["status"] != "retained":
            unresolved += 1
            uniform = False
            continue
        for i in (1, 2):
            for name in ("sA", "sB", "j"):
                old = envelopes[i].get(name)
                v = value["cells"][i][name]
                envelopes[i][name] = v if old is None else hull((old, v))
                uniform &= target[i][name].lo <= v.lo <= v.hi <= target[i][name].hi
    violations = []
    for number, member in enumerate(payload["members"]):
        for i in (1, 2):
            for name in ("sA", "sB", "j"):
                value, bound = member["cells"][i][name], target[i][name]
                if value.hi < bound.lo or value.lo > bound.hi:
                    violations.append({"member": number, "cell": i, "feature": name, "prediction": value, "target": bound})
    verdict = ("UNIFORM_HELDOUT_CONTAINMENT" if uniform else "CERTIFIED_TRAINING_MEMBER_HELDOUT_DISAGREEMENT"
               if violations else "OUTER_NOT_CONTAINED_WITHOUT_MEMBER_COUNTEREXAMPLE")
    return {"verdict": verdict, "uniform_heldout_contained": uniform, "retained_unresolved_leaves": unresolved,
            "paired_prediction_display_hulls": envelopes, "member_violations": violations,
            "heldout_ci_used_only_after_source_stage_digest": True}


def run():
    start, c = time.monotonic(), context()
    report_path = HERE.parents[1] / "observable-prediction/public-comparison-po0003.json"
    report = json.loads(report_path.read_text())
    ci = ci_view(report)
    del report
    domain = training_domain(ci)
    candidates, evaluated = members(ci, domain)
    print(json.dumps({"primary_members": len(candidates), "training_candidates_evaluated": evaluated}), flush=True)
    payload = {"schema": "p23-full-statistical-fiber-primary/v1", "version": VERSION,
               "training_ci": ci, "cover": cover(ci, domain), "members": candidates,
               "candidate_count": evaluated, "all_six_training_intervals_used": True,
               "frozen_source_law": c["spec"]["conditional_source_law"],
               "scope": {"source_mapping_identified": False, "actual_epoch_identified": False,
                         "apparatus_optimum_verified": False, "controller_advance": False, "retrospective": True,
                         "new_full_Born_kernel_claim": False, "bell_event_files_read": 0}}
    stage_sha = logical_sha(payload)
    comparison = comparisons(payload, json.loads(report_path.read_text()))
    return {**pack(payload), "source_stage_sha256": stage_sha, "comparison": pack(comparison),
            "bindings": {"execution_sources": c["bindings"], "manifest": c["manifest"]},
            "nonempty_fiber_exhibited": bool(candidates), "runtime_seconds": time.monotonic() - start}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "primary-ef0003.json.gz")
    args = parser.parse_args()
    require(not args.output.exists(), "protected_existing_full_fiber_primary")
    value = run()
    raw = (json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False) + "\n").encode()
    compressed = gzip.compress(raw, compresslevel=9, mtime=0)
    args.output.write_bytes(compressed)
    metadata = {"schema": "p23-full-fiber-lossless-storage/v1", "version": VERSION,
                "logical_sha256": hashlib.sha256(raw).hexdigest(), "stored_sha256": hashlib.sha256(compressed).hexdigest(),
                "logical_bytes": len(raw), "stored_bytes": len(compressed), "source_stage_sha256": value["source_stage_sha256"],
                "scientific_content_changed": False}
    args.output.with_name(args.output.name.removesuffix(".json.gz") + "-storage.json").write_text(
        json.dumps(metadata, indent=2) + "\n")
    print(json.dumps({"output": str(args.output), **metadata,
                      "nonempty": value["nonempty_fiber_exhibited"], "verdict": value["comparison"]["verdict"]}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
