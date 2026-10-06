#!/usr/bin/env python3
"""Complete retrospective public-CI fibre under the frozen same-source law."""
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
import time

import primary_fiber as kernel
import independent_fiber as born_kernel

HERE = Path(__file__).resolve().parent
VERSION = "p23-all-data-statistical-fiber-ef0003.1"
CTX = None


def configuration():
    global CTX
    if CTX is not None:
        return CTX
    base = kernel.context()
    text = (HERE / "criterion-all-data.md").read_text()
    matches = re.findall(r"<!-- ALL-DATA-FIBER-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- ALL-DATA-FIBER-FROZEN-END -->", text, re.S)
    kernel.require(len(matches) == 1, "nonunique_all_data_contract")
    spec = json.loads(matches[0])
    manifest = json.loads((HERE / "sources-all-data.json").read_text())
    kernel.require(spec["version"] == manifest["version"] == VERSION and
                   spec["statistical_role"] == "retrospective_all_public_CI_intersection" and
                   spec["joint_rows"] == [0, 1, 2, 3] and spec["member_limit"] == 64 and
                   spec["all_twelve_original_CI_required"] is True and
                   spec["original_alpha_unchanged"] is True, "all_data_contract_changed")
    for row in manifest["inputs"]:
        path = kernel.parent.ROOT / row["path"]
        kernel.require(kernel.parent.digest(path) == row["sha256"], "all_data_source_binding_changed:" + row["path"])
    bindings = [kernel.parent.frozen(HERE / name) for name in
                ("criterion-all-data.md", "sources-all-data.json", "primary_all_data.py")]
    born_config, born_freeze, born_bindings = born_kernel.configuration()
    CTX = {**base, "all_spec": spec, "all_manifest": manifest, "all_bindings": bindings,
           "born_config": born_config, "born_const": born_kernel.constants(born_config),
           "born_bindings": born_bindings, "born_freeze": born_freeze}
    return CTX


def all_ci_view(report):
    c, result = configuration(), {}
    q = report["common_mean_confidence"]
    for name, rows in c["all_spec"]["single_row_intersections"].items():
        field = "sA_cell" if name.startswith("A") else "sB_cell"
        originals = [c["I"](F(q[field][i]["exact_lower"]), F(q[field][i]["exact_upper"])) for i in rows]
        value = kernel.intersect(*originals)
        kernel.require(value is not None, "incompatible_same_local_setting_CI:" + name)
        result[name] = value
    result["joint"] = [c["I"](F(row["exact_lower"]), F(row["exact_upper"])) for row in q["j"]]
    result["originals"] = {field: [c["I"](F(row["exact_lower"]), F(row["exact_upper"])) for row in q[field]]
                           for field in ("sA_cell", "sB_cell", "j")}
    result["J0"], result["J1"] = result["joint"][0], result["joint"][3]
    return result


def common_phase(source, cells, ci):
    c = configuration()
    T = c["gauss"].square_root(source["T2"])
    K, slabs = c["I"](-T.hi, T.hi), []
    ba, bb = map(F, c["spec"]["background_per_pulse"])
    for index, target in enumerate(ci["joint"]):
        cell = cells[index]
        sa, sb = kernel.single_window(cell["ma"], ba), kernel.single_window(cell["mb"], bb)
        low = kernel.omega_bound(sa, sb, c["I"].point(target.lo))
        high = kernel.omega_bound(sa, sb, c["I"].point(target.hi))
        lower = (low * cell["E"] - cell["A"]) / cell["D"]
        upper = (high * cell["E"] - cell["A"]) / cell["D"]
        K = kernel.affine_phase_clip(K, cell["g"], lower, upper)
        slabs.append({"cell": index, "lower": lower, "upper": upper, "g": cell["g"], "shared_k_after": K})
        if K is None:
            return None, slabs
    return K, slabs


def polynomial_bound(coefficients, domain):
    """Power-to-Bernstein bound keeps the common phase in each contrast."""
    c, degree = configuration(), len(coefficients) - 1
    low, width = c["I"].point(domain.lo), c["I"].point(domain.hi - domain.lo)
    translated = [sum((coefficients[j] * math.comb(j, k) * kernel.powi(low, j-k)
                       * kernel.powi(width, k) for j in range(k, degree+1)), c["I"].point(0))
                  for k in range(degree+1)]
    bernstein = [sum((translated[k] * F(math.comb(i, k), math.comb(degree, k))
                     for k in range(i+1)), c["I"].point(0)) for i in range(degree+1)]
    return kernel.hull(bernstein)


def joint_polynomial(cell):
    c = configuration()
    ba, bb = map(F, c["spec"]["background_per_pulse"])
    pa, pb = (1-ba)/(1+cell["ma"]), (1-bb)/(1+cell["mb"])
    sa, sb = 1-kernel.powi(pa, 5), 1-kernel.powi(pb, 5)
    u, v = cell["A"]/cell["E"], cell["D"]*cell["g"]/cell["E"]
    local5 = kernel.powi(pa*pb, 5)
    coefficients = [sa*sb] + [c["I"].point(0) for _ in range(5)]
    for j in range(1, 6):
        for k in range(j+1):
            coefficients[k] += local5*math.comb(5, j)*math.comb(j, k)*kernel.powi(u, j-k)*kernel.powi(v, k)
    return coefficients


def paired_contrasts(cells, windows, K):
    polys = [joint_polynomial(cell) for cell in cells]
    joint_sum = [a+b for a, b in zip(polys[1], polys[2])]
    joint_difference = [a-b for a, b in zip(polys[1], polys[2])]
    ch = [a+b+c-d for a, b, c, d in zip(*polys)]
    ch[0] -= windows[0]["sA"] + windows[0]["sB"]
    return {"joint_sum": polynomial_bound(joint_sum, K),
            "joint_difference": polynomial_bound(joint_difference, K),
            "CH_N5": polynomial_bound(ch, K),
            "same_k_polynomials": {"joint_sum": joint_sum, "joint_difference": joint_difference, "CH_N5": ch},
            "bound_method": "directed_degree5_Bernstein_on_the_same_k_interval"}


def evaluate(box, ci):
    source = kernel.covariance(box)
    if source is None:
        return {"status": "excluded", "reason": "whole_box_physical_violation"}
    cells = kernel.coefficients(source)
    if cells is None:
        return {"status": "unresolved", "reason": "source_denominator_outer_not_positive"}
    K, slabs = common_phase(source, cells, ci)
    if K is None:
        return {"status": "excluded", "reason": "whole_box_four_shared_phase_slabs_empty", "slabs": slabs}
    try:
        windows = [kernel.window_readout(cell, K) for cell in cells]
    except ValueError:
        return {"status": "unresolved", "reason": "physical_readout_outer_requires_refinement"}
    for index in range(4):
        for name, field in (("sA", "sA_cell"), ("sB", "sB_cell"), ("j", "j")):
            if kernel.intersect(windows[index][name], ci["originals"][field][index]) is None:
                return {"status": "excluded", "reason": "whole_box_original_CI_disjoint", "row": index, "field": field}
    return {"status": "retained", "phase": K, "slabs": slabs, "source": source,
            "cells": windows, "paired": paired_contrasts(cells, windows, K),
            "no_signaling_exact": True, "all_joint_slabs_share_one_k": True}


def cover(ci, domain, cap=None):
    c = configuration()
    cap = c["all_spec"]["primary_split_cap"] if cap is None else cap
    queue, sequence = [(-5, 0, "", tuple((F(0), F(1)) for _ in range(5)), 0)], 0
    splits, nodes, leaves = [], [], []
    while queue:
        _, _, path, unit, depth = heapq.heappop(queue)
        box = kernel.source_box(unit, domain)
        value = evaluate(box, ci)
        nodes.append({"path": path, "status": value["status"], "reason": value.get("reason")})
        if value["status"] == "excluded":
            leaves.append({"path": path, "classification": "excluded", "proof": value})
            continue
        axis = kernel.split_axis(unit)
        width = unit[axis][1]-unit[axis][0]
        if width <= F(c["spec"]["normalized_width_stop"]) or depth >= c["spec"]["max_depth"] or len(splits) >= cap:
            leaves.append({"path": path, "classification": "retained_boundary",
                           "stop": "resource_cap" if len(splits) >= cap else "width_or_depth",
                           "unit_box": unit, "qualified_outer": value})
            continue
        lo, hi = unit[axis]
        mid = (lo+hi)/2
        splits.append({"path": path, "axis": axis, "midpoint": mid})
        for label, ends in (("L", (lo, mid)), ("R", (mid, hi))):
            child = list(unit); child[axis] = ends; child = tuple(child)
            sequence += 1
            heapq.heappush(queue, (-sum(b-a for a, b in child), sequence, path+str(axis)+label, child, depth+1))
        if len(splits) % 256 == 0:
            print(json.dumps({"primary_all_data_splits": len(splits), "pending": len(queue)}), flush=True)
    kernel.require(len(nodes) == 2*len(splits)+1 and len(leaves) == len(splits)+1, "incomplete_all_data_cover")
    return {"coordinate_space": "four_all_CI_inverse_single_mean_intervals_and_loss", "axes": kernel.AXES,
            "initial_box": domain, "split_count": len(splits), "split_cap": cap,
            "all_leaves_preserved": True, "cap_reached": len(splits) >= cap,
            "splits": splits, "nodes": nodes, "leaves": leaves}


def actual_born(box, k, ci):
    c = configuration()
    ba, bb = map(F, c["spec"]["background_per_pulse"])
    raw = [1-((1-bg)/(1+mean.lo))**5 for mean, bg in zip(box[:4], (ba, bb, ba, bb))]
    shape, reconstruction = born_kernel.member_shape(raw, c["born_config"], c["born_const"])
    source = born_kernel.physical_source(shape+[born_kernel.I(box[4].lo)], born_kernel.I(k))
    result = born_kernel.fock_readout(source, c["born_const"], c["born_config"]["source_pair_cutoff"])
    for row in range(4):
        for name, field in (("sA", "sA_cell"), ("sB", "sB_cell"), ("j", "j")):
            target = ci["originals"][field][row]
            packet = {"exact_lower": str(target.lo), "exact_upper": str(target.hi)}
            kernel.require(result["cells"][row][name].within_exact(packet), "all_data_actual_Born_original_CI_not_contained")
    return {"recipe_conversion": {"inverse_single_means": box[:4], "exact_single_probability_coordinates": raw,
                                   "rational_loss": box[4].lo, "rational_common_k": k},
            "reconstruction": born_kernel.serial(reconstruction), "source": born_kernel.serial(source),
            "readout": born_kernel.serial(result), "all_twelve_original_CI_contained": True}


def point_members(box, ci):
    c = configuration()
    source = kernel.covariance(box)
    if source is None or box[4].lo <= 0 or box[4].hi > source["r"].lo or (source["m"].square()-source["R2"]).lo < 0:
        return []
    cells = kernel.coefficients(source)
    if cells is None:
        return []
    T = c["gauss"].square_root(source["T2"])
    lo, hi = -T.lo, T.lo
    ba, bb = map(F, c["spec"]["background_per_pulse"])
    for index, target in enumerate(ci["joint"]):
        cell = cells[index]
        if cell["g"].contains(0):
            continue
        sa, sb = kernel.single_window(cell["ma"], ba), kernel.single_window(cell["mb"], bb)
        lower = (kernel.omega_bound(sa, sb, c["I"].point(target.lo))*cell["E"]-cell["A"])/(cell["D"]*cell["g"])
        upper = (kernel.omega_bound(sa, sb, c["I"].point(target.hi))*cell["E"]-cell["A"])/(cell["D"]*cell["g"])
        a, b = (lower.hi, upper.lo) if cell["g"].lo > 0 else (upper.hi, lower.lo)
        lo, hi = max(lo, a), min(hi, b)
    if lo > hi:
        return []
    members = []
    for name, k in (("midpoint", (lo+hi)/2), ("lower", lo), ("upper", hi)):
        K = c["I"].point(k)
        windows = [kernel.window_readout(cell, K) for cell in cells]
        if not all(ci["originals"][field][row].lo <= windows[row][feature].lo <= windows[row][feature].hi <= ci["originals"][field][row].hi
                   for row in range(4) for feature, field in (("sA", "sA_cell"), ("sB", "sB_cell"), ("j", "j"))):
            continue
        C = c["gauss"].square_root(source["R2"])
        coherence = K/T if T.lo > 0 else c["I"].point(0)
        h, v = source["m"]+C, source["m"]-C
        if coherence.lo < -1 or coherence.hi > 1 or v.lo < 0:
            continue
        try:
            born = actual_born(box, k, ci)
        except (ValueError, ArithmeticError):
            continue
        for row in range(4):
            for field in ("sA", "sB", "j"):
                probability = born["readout"]["cells"][row][field]
                value = c["I"](F(probability["exact_lower"]), F(probability["exact_upper"]))
                kernel.require(kernel.intersect(windows[row][field], value) is not None, "all_data_Gaussian_positive_Born_disagree")
        cosR = c["gauss"].square_root((1+source["z"]/C)/2)
        members.append({"recipe": {"inverse_single_means": box[:4], "loss": box[4], "phase_amplitude": K, "phase_recipe": name},
                        "source": {"nH": h/box[4], "nV": v/box[4], "etaA": box[4], "etaB": box[4]/source["r"],
                                   "cosR": cosR, "sinR": (source["x"]/C)/(2*cosR), "lambda": (1-coherence)/2,
                                   "pure_mode_phase_readout_equivalence": T.hi == 0},
                        "cells": windows, "paired": paired_contrasts(cells, windows, K), "actual_positive_Fock": born,
                        "all_twelve_original_CI_contained": True, "retrospective_all_data_selection": True})
    return members


def members(ci, domain):
    c, result, evaluated = configuration(), [], 0
    for weights in itertools.product(map(F, c["spec"]["witness_axis_fractions"]), repeat=4):
        means = [c["I"].point(d.lo+w*(d.hi-d.lo)) for d, w in zip(domain[:4], weights)]
        for j in range(1, c["spec"]["witness_loss_denominator"]+1):
            box = means+[c["I"].point(F(j, c["spec"]["witness_loss_denominator"]))]
            evaluated += 1
            for value in point_members(box, ci):
                value["recipe"]["ci_fractions"] = list(weights)
                result.append(value)
                if len(result) >= c["all_spec"]["member_limit"]:
                    return result, evaluated
    return result, evaluated


def run():
    start, c = time.monotonic(), configuration()
    path = HERE.parents[1]/"observable-prediction/public-comparison-po0003.json"
    report = json.loads(path.read_text())
    ci = all_ci_view(report)
    domain = kernel.training_domain(ci)
    candidates, evaluated = members(ci, domain)
    print(json.dumps({"primary_all_data_members": len(candidates), "candidate_count": evaluated}), flush=True)
    tree = cover(ci, domain)
    retained = [leaf for leaf in tree["leaves"] if leaf["classification"] != "excluded"]
    qualified = [leaf["qualified_outer"] for leaf in retained if leaf["qualified_outer"]["status"] == "retained"]
    unresolved = len(retained)-len(qualified)
    ch = kernel.hull([value["paired"]["CH_N5"] for value in qualified]) if qualified else None
    payload = {"schema": "p23-all-data-statistical-fiber-primary/v1", "version": VERSION,
               "statistical_role": c["all_spec"]["statistical_role"], "all_ci": ci, "cover": tree,
               "members": candidates, "candidate_count": evaluated, "frozen_source_law": c["spec"]["conditional_source_law"],
               "scope": {key: c["all_spec"][key] for key in ("source_mapping_identified", "actual_epoch_identified",
                         "apparatus_optimum_verified", "controller_advance", "new_full_Born_kernel_claim", "bell_event_files_read")},
               "source_relations": {"same_k_all_four_cells": True, "no_signaling_exact": True,
                                    "same_source_original_twelve_CI": True},
               "whole_fibre_CH": {"qualified_outer_hull": ch, "unresolved_retained_leaves": unresolved,
                                  "strictly_positive_certified": bool(ch is not None and ch.lo > 0 and unresolved == 0)},
               "nonempty_fibre_exhibited": bool(candidates), "all_boundary_and_cap_leaves_preserved": True}
    return {**kernel.pack(payload), "source_stage_sha256": kernel.logical_sha(payload),
            "bindings": {"execution_sources": c["all_bindings"], "parent_execution_sources": c["bindings"],
                         "manifest": c["all_manifest"], "positive_Born_source_bindings": c["born_bindings"]},
            "runtime_seconds": time.monotonic()-start}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE/"primary-all-data-ef0003.1.json.gz")
    args = parser.parse_args()
    kernel.require(not args.output.exists(), "protected_existing_all_data_primary")
    value = run()
    raw = (json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)+"\n").encode()
    stored = gzip.compress(raw, compresslevel=9, mtime=0)
    args.output.write_bytes(stored)
    metadata = {"schema": "p23-all-data-fibre-first-storage/v1", "version": VERSION,
                "logical_sha256": hashlib.sha256(raw).hexdigest(), "stored_sha256": hashlib.sha256(stored).hexdigest(),
                "logical_bytes": len(raw), "stored_bytes": len(stored), "source_stage_sha256": value["source_stage_sha256"]}
    args.output.with_name(args.output.name.removesuffix(".json.gz")+"-storage.json").write_text(json.dumps(metadata, indent=2)+"\n")
    print(json.dumps({"output": str(args.output), **metadata, "nonempty": value["nonempty_fibre_exhibited"],
                      "whole_fibre_CH": value["whole_fibre_CH"]}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
