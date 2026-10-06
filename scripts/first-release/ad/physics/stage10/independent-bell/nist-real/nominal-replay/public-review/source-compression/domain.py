#!/usr/bin/env python3
"""Refine the certified XOR3 source cover using complete public exposures."""
from __future__ import annotations

import argparse
from collections import Counter, deque
from fractions import Fraction as F
import gzip
import hashlib
import itertools
import json
import lzma
import math
from pathlib import Path
import sys
import time

import compress as statistics

HERE, ROOT, MW = statistics.HERE, statistics.ROOT, statistics.MW
sys.path.insert(0, str(MW))
legacy = statistics.module("_sc_legacy_source", MW / "source_independent.py")
geometry, I, SCALE = legacy.geometry, legacy.I, legacy.geometry.SCALE
VERSION = statistics.VERSION
SCHEMA = "p23-source-compression-domain/v1"
FEATURES = ("both", "onlyA", "onlyB", "neither", "singleA", "singleB")
OLD_CERT_SHA = "3b410f8bb416ea513ec8244ce10ded1eaadefcb65e4273436b393c6d36ccde10"
OLD_INDEPENDENT_SHA = "8c414cad682c4cc20271e4a79ea63a84e4c02e0af53e072b70be6f24e06324a1"
OLD_PRIMARY_SHA = "a6e46e61bcababb4769aff21bbaf0675f1d1d2fb2e07930baeeaac7e7c1a0c90"
require = statistics.require


def load(path):
    raw = Path(path).read_bytes()
    if str(path).endswith(".xz"):
        raw = lzma.decompress(raw)
    elif str(path).endswith(".gz"):
        raw = gzip.decompress(raw)
    return json.loads(raw)


def value(packet):
    return I(F(packet["exact_lower"]), F(packet["exact_upper"]))


def exact_within(interval, packet):
    return interval.within_exact(packet)


def root_interval(q, n):
    """Enclose the exact rational n-th root on the native integer grid."""
    q = F(q)
    require(type(n) is int and n > 0 and 0 <= q <= 1, "invalid_single_root")
    target = q.numerator * SCALE ** n // q.denominator
    if not target:
        lower = 0
    elif n == 1:
        lower = target
    else:
        lower = 1 << ((target.bit_length() + n - 1) // n)
        while True:
            following = ((n - 1) * lower + target // lower ** (n - 1)) // n
            if following >= lower:
                break
            lower = following
        while lower ** n > target:
            lower -= 1
        while (lower + 1) ** n <= target:
            lower += 1
    upper = lower if F(lower, SCALE) ** n == q else lower + 1
    return I.raw(lower, upper)


def mean_from_single(packet, n, background, original):
    p = value(packet).intersect(I(0, 1))
    if p is None:
        return None, {"reason": "conditional_single_outside_probability_simplex"}
    lower_root = root_interval(F(SCALE - p.hi, SCALE), n)
    upper_root = root_interval(F(SCALE - p.lo, SCALE), n)
    # A q=0 outer boundary supplies no finite upper mean; it is never divided out.
    lo = ((1 - background) / upper_root - 1).lo if upper_root.lo > 0 else original.lo
    hi = ((1 - background) / lower_root - 1).hi if lower_root.lo > 0 else original.hi
    interval = original.intersect(I.raw(max(0, lo), max(0, hi))) if lo <= hi else None
    return interval, {"single_interval": p, "no_click_root_lower": lower_root,
                      "no_click_root_upper": upper_root, "finite_upper_boundary": lower_root.lo > 0,
                      "mean_after": interval}


def bernstein(coefficients, interval):
    """Directed coefficients after k=a+(b-a)t, followed by the Bernstein basis."""
    degree = len(coefficients) - 1
    a = I.raw(interval.lo, interval.lo)
    width = I.raw(interval.width, interval.width)
    shifted = [sum((coefficients[j] * math.comb(j, i) * a.power(j - i)
                    * width.power(i) for j in range(i, degree + 1)), I(0))
               for i in range(degree + 1)]
    result = [sum((shifted[j] * F(math.comb(i, j), math.comb(degree, j))
                   for j in range(i + 1)), I(0)) for i in range(degree + 1)]
    return I.raw(min(v.lo for v in result), max(v.hi for v in result)), result


def phase_parts(interval, count):
    require(type(count) is int and count > 0, "invalid_phase_partition")
    endpoints = [interval.lo + interval.width * i // count for i in range(count + 1)]
    return [I.raw(a, b) for a, b in zip(endpoints, endpoints[1:])]


def h_ranges(ch, losses, epsilon):
    l = ((1 - epsilon) / 2) ** 2
    cost = epsilon * (1 - epsilon)
    ranges = [l * ch - cost * loss for loss in losses]
    return I.raw(max(v.lo for v in ranges), max(v.hi for v in ranges)), ranges


def new_records(report):
    require(report["schema"] == "p23-source-compression-statistics/v1"
            and report["version"] == VERSION and len(report["records"]) == 24,
            "changed_statistics_schema")
    rows = [r for r in report["records"] if r["identity"]["workbook"] == "diag-xor3.xlsx"]
    rows.sort(key=lambda r: r["identity"]["pulse_count"])
    require([r["identity"]["pulse_count"] for r in rows] == [1, 3, 5, 7], "wrong_compression_run")
    for row in rows:
        require(sum(row["setting_trials"]) == row["total_trials"]
                and len(row["conditional"]) == 4, "conditional_exposure_identity_changed")
        for index, features in enumerate(row["conditional"]):
            require(tuple(f["feature"] for f in features) == FEATURES
                    and all(f["trials"] == row["setting_trials"][index] for f in features),
                    "conditional_feature_or_exposure_changed")
    return rows


def validate_statistics_cross(cross, primary_binding):
    require(cross["schema"] == "p23-source-compression-statistical-cross/v1"
            and cross["version"] == VERSION and cross["evidence_valid"] is True
            and all(cross[key] is True for key in ("all_23040_direction_bets_verified",
                "all_24_complete_records_verified", "all_24_support_cut_brackets_verified",
                "all_480_original_contrast_bets_verified", "all_576_conditional_intervals_verified",
                "all_72_original_CI_preserved", "joint_95_coverage_budget_paid"))
            and cross["original_CI_modified"] is False
            and cross["source_tree_or_Fock_producers_executed"] == 0,
            "statistics_cross_not_certified")
    matches = [b for b in cross["bindings"] if b["path"] == primary_binding["path"]]
    require(len(matches) == 1 and matches[0] == primary_binding, "statistics_first_not_cross_bound")


def configuration(cross_path):
    c = statistics.configuration()
    require(c["source_split_cap"] == 512 and c["phase_partition_count"] == 8
            and c["source_member_limit"] == 8 and c["source_member_loss_denominator"] == 128
            and c["source_pair_cutoff"] == 6
            and c["source_member_mean_fractions"] == ["1/2", "1/4", "3/4"]
            and c["source_member_phase_fractions"] == ["1/2", "1/4", "3/4"], "domain_contract_changed")
    cross_path = Path(cross_path).resolve()
    require(cross_path == (HERE / "statistics-cross-verification.json").resolve(), "foreign_statistics_cross")
    cross = load(cross_path)
    primary_path = HERE / "statistics-primary-first.json.xz"
    validate_statistics_cross(cross, statistics.frozen(primary_path))
    cert = load(MW / "source-cross-verification.json")
    require(statistics.sha(MW / "source-cross-verification.json") == OLD_CERT_SHA
            and cert["evidence_valid"] is True and cert["source_outer_cover_and_all_72_CI_certified"] is True
            and cert["all_32_positive_Born_members_regenerated"] is True
            and cert["trees"]["independent"]["retained_leaves"] == 11,
            "old_source_cover_not_certified")
    old_config, _ = legacy.configuration()
    paths = [HERE / "criterion.md", HERE / "sources.json", Path(__file__), HERE / "test_domain.py",
             HERE / "compress.py", primary_path, cross_path, MW / "source-cross-verification.json",
             MW / "source-independent.json.gz", MW / "source-primary-first.json.xz",
             MW / "source_independent.py", legacy.FIBER / "independent_fiber.py"]
    bindings = [statistics.frozen(p) for p in paths]
    return c, old_config, geometry.constants(old_config), new_records(load(primary_path)), bindings


def old_material():
    require(statistics.sha(MW / "source-independent.json.gz") == OLD_INDEPENDENT_SHA
            and statistics.sha(MW / "source-primary-first.json.xz") == OLD_PRIMARY_SHA,
            "changed_old_source_firsts")
    independent = load(MW / "source-independent.json.gz")
    roots = [{"old_node_id": r["node_id"], "source_box": [value(v) for v in r["source_box"]],
              "common_k": value(r["common_k"])} for r in independent["cover"]["paired_regions"]]
    require(len(roots) == 11, "wrong_old_retained_source_count")
    endpoints = independent["all_original_endpoint_CI"]
    for e in endpoints:
        e["CI"] = {field: [value(v) for v in e["original_CI"][field]] for field, _ in legacy.FIELDS}
    native = [value(v) for v in independent["four_native_pulse_mean_domain"]]
    initial = [value(v) for v in independent["cover"]["initial_source_box"]]
    members = [{"implementation": "independent", "old_member_id": m["id"], "recipe": m["recipe"],
                "source": m["source"], "windows": {str(e["N"]): e["cells"] for e in m["actual_positive_Born"]["endpoints"]},
                "native_Fock": m["actual_positive_Born"]["same_pulse_positive_Born"]}
               for m in independent["members"]]
    del independent
    primary = load(MW / "source-primary-first.json.xz")
    members += [{"implementation": "primary", "old_member_id": i, "recipe": m["recipe"],
                 "source": m["source"], "windows": m["native_windows"], "native_Fock": m["native_Fock"]}
                for i, m in enumerate(primary["members"])]
    require(len(members) == 32, "old_native_member_inventory_changed")
    return roots, endpoints, native, initial, members


def mean_constraints(native, records, const):
    current, witnesses = list(native), []
    for ai, feature, setting_rows, bg in ((0, 4, (0, 1), const["background"][0]),
                                         (1, 5, (0, 2), const["background"][1]),
                                         (2, 4, (2, 3), const["background"][0]),
                                         (3, 5, (1, 3), const["background"][1])):
        for record in records:
            for row in setting_rows:
                packet = record["conditional"][row][feature]["interval"]
                after, proof = mean_from_single(packet, record["identity"]["pulse_count"], bg, current[ai])
                witnesses.append({"mean_index": ai, "N": record["identity"]["pulse_count"],
                                  "row": row, "original_mean": current[ai], "proof": proof})
                if after is None:
                    return None, witnesses
                current[ai] = after
    return current, witnesses


def joined_endpoints(old, records):
    result = list(old)
    for record in records:
        raw = {field: [record["conditional"][row][feature]["interval"] for row in range(4)]
               for field, feature in (("sA_cell", 4), ("sB_cell", 5), ("j", 0))}
        result.append({"id": "conditional_N" + str(record["identity"]["pulse_count"]),
                       "N": record["identity"]["pulse_count"], "original_CI": raw,
                       "CI": {field: [value(p) for p in raw[field]] for field, _ in legacy.FIELDS}})
    return result


def source_polynomials(box, pop, const, means, records, epsilon):
    geos = [geometry.geometry(box, pop, const, row, means) for row in range(4)]
    ba, bb = const["background"]
    factor, result = (1 - ba) * (1 - bb), []
    pulses = []
    for g in geos:
        a, b = g["alpha"], g["beta"]
        base = a * b / g["D"] + (g["Ccorr"] * g["L"] + g["g"].square() * pop["T2"]) / (g["E"] * g["D"])
        pulses.append([factor * base + ba * (1 - bb) * b / (1 + b)
                       + bb * (1 - ba) * a / (1 + a) + ba * bb, factor * g["g"] / g["E"]])
    add, scale = geometry.padd, geometry.pscale
    for record in records:
        n, cells = record["identity"]["pulse_count"], []
        for g, pulse in zip(geos, pulses):
            a = geometry.clipped(legacy.window_single(g["pulse_A"], n), 0, SCALE)
            b = geometry.clipped(legacy.window_single(g["pulse_B"], n), 0, SCALE)
            j = legacy.window_joint_coefficients(g["pulse_A"], g["pulse_B"], pulse, n)
            cells.append([j, add([a], scale(j, -1)), add([b], scale(j, -1)),
                          add([1 - a - b], j), [a], [b]])
        losses = [cells[1][1], cells[2][2], cells[3][0]]
        ch = cells[0][0]
        for loss in losses:
            ch = add(ch, scale(loss, -1))
        l, cost = ((1 - epsilon) / 2) ** 2, epsilon * (1 - epsilon)
        hp = [add(scale(ch, l), scale(loss, -cost)) for loss in losses]
        result.append({"N": n, "cells": cells, "CH": ch, "H": hp,
                       "h_lower": F(record["contrast"]["h_bracket"]["lower"])})
    return result


def classify_phase(polynomials, phase, records, epsilon):
    upper_witnesses = []
    for polynomials_at_n, record in zip(polynomials, records):
        readings = []
        for row, features in enumerate(polynomials_at_n["cells"]):
            cell = []
            for feature, polynomial in enumerate(features):
                bound, coefficients = bernstein(polynomial, phase)
                legal = bound.intersect(I(0, 1))
                ci = value(record["conditional"][row][feature]["interval"])
                accepted = legal.intersect(ci) if legal is not None else None
                if accepted is None:
                    return {"status": "excluded", "reason": "strict_conditional_probability_violation",
                            "N": polynomials_at_n["N"], "row": row, "feature": FEATURES[feature],
                            "polynomial": polynomial, "bernstein_coefficients": coefficients,
                            "range": bound, "conditional_interval": ci}
                cell.append(accepted)
            readings.append(cell)
        losses = [readings[1][1], readings[2][2], readings[3][0]]
        ch = readings[0][0] - sum(losses, I(0))
        _, natural = h_ranges(ch, losses, epsilon)
        ranges, bernstein_coefficients = [], []
        for hp, constraint in zip(polynomials_at_n["H"], natural):
            bound, coefficients = bernstein(hp, phase)
            ranges.append(bound.intersect(constraint))
            bernstein_coefficients.append(coefficients)
        if any(v is None for v in ranges):
            return {"status": "excluded", "reason": "strict_source_h_identity_violation",
                    "N": polynomials_at_n["N"], "H_polynomials": polynomials_at_n["H"],
                    "H_bernstein_coefficients": bernstein_coefficients, "natural_H_ranges": natural}
        if all(F(v.hi, SCALE) <= polynomials_at_n["h_lower"] for v in ranges):
            return {"status": "excluded", "reason": "all_three_source_H_upper_at_or_below_lower",
                    "N": polynomials_at_n["N"], "H_polynomials": polynomials_at_n["H"],
                    "H_bernstein_coefficients": bernstein_coefficients, "H_ranges": ranges,
                    "natural_H_ranges": natural, "h_lower": polynomials_at_n["h_lower"]}
        upper_witnesses.append({"N": polynomials_at_n["N"], "H_ranges": ranges,
                                "h_lower": polynomials_at_n["h_lower"]})
    return {"status": "retained", "reason": "necessary_outer_region", "h_cuts": upper_witnesses}


def refine(roots, initial, native, const, endpoints, records, config, old_config):
    if native is None:
        return {"roots": list(range(len(roots))), "nodes": [dict(r, id=i, parent=None, root_index=i,
            depth=0, status="excluded", reason="complete_new_single_mean_intersection_empty") for i, r in enumerate(roots)],
            "leaves": [], "split_count": 0}
    means = {"alpha": [native[0], native[2]], "beta": [native[1], native[3]], "joint": []}
    constraints = geometry.linear_constraints(means, const)
    pending = deque((i, None, i, r["source_box"], r["common_k"], 0) for i, r in enumerate(roots))
    nodes, leaves, next_id, splits = [], [], len(roots), 0
    widths = [v.width or 1 for v in initial]
    while pending:
        index, parent, root_index, raw, inherited, depth = pending.popleft()
        box, contraction = geometry.linear_contract(raw, constraints)
        node = {"id": index, "parent": parent, "root_index": root_index, "depth": depth,
                "input_box": raw, "input_k": inherited, "contracted_box": box, "contraction": contraction}
        nodes.append(node)
        if box is None:
            node.update(status="excluded", reason="strict_new_single_or_loss_halfspace_violation"); continue
        pop = geometry.population(box)
        if pop is None:
            node.update(status="excluded", reason="strict_source_PSD_violation"); continue
        try:
            common, slabs, _ = legacy.common_phase(box, pop, const, means, endpoints, old_config)
            node["phase_slabs_sha256"] = geometry.sha(geometry.canonical(slabs))
            common = common.intersect(inherited) if common is not None else None
            if common is None:
                node.update(status="excluded", reason="strict_old_new_common_phase_empty", phase_slabs=slabs); continue
            polynomials = source_polynomials(box, pop, const, means, records, F(config["epsilon"]))
            partitions = [{"phase": part, **classify_phase(polynomials, part, records, F(config["epsilon"]))}
                          for part in phase_parts(common, config["phase_partition_count"])]
        except (ValueError, ArithmeticError) as error:
            # Denominator/pure-mode boundaries are covered, never called a failed source.
            common = inherited.intersect(I.raw(-pop["T2"].sqrt().hi, pop["T2"].sqrt().hi))
            partitions = [{"phase": inherited, "status": "retained", "reason": "boundary_arithmetic_unresolved",
                           "detail": str(error)}]
            common = inherited if common is None else common
        node.update(common_k=common, phase_partitions=partitions)
        retained = [p["phase"] for p in partitions if p["status"] == "retained"]
        if not retained:
            node.update(status="excluded", reason="complete_phase_partition_excluded"); continue
        hull = I.raw(min(p.lo for p in retained), max(p.hi for p in retained))
        node["surviving_k_hull"] = hull
        relative = [F(v.width, width) for v, width in zip(box, widths)]
        axis = max(range(5), key=lambda j: (relative[j], -j))
        midpoint = (box[axis].lo + box[axis].hi) // 2
        if (splits < config["source_split_cap"] and depth < old_config["max_depth"]
                and relative[axis] > F(old_config["normalized_width_stop"])
                and box[axis].lo < midpoint < box[axis].hi):
            children = [next_id, next_id + 1]; next_id += 2; splits += 1
            left, right = list(box), list(box)
            left[axis], right[axis] = I.raw(box[axis].lo, midpoint), I.raw(midpoint, box[axis].hi)
            node.update(status="split", split_axis=geometry.AXES[axis], split_at=F(midpoint, SCALE), children=children)
            pending.extend(((children[0], index, root_index, left, hull, depth + 1),
                            (children[1], index, root_index, right, hull, depth + 1)))
        else:
            node.update(status="retained", reason="cap_depth_width_or_boundary_preserved")
            leaves.append({"node_id": index, "root_index": root_index, "source_box": box,
                           "phase_components": retained, "necessary_outer_only": True})
        if len(nodes) % 64 == 0:
            print(json.dumps({"domain_nodes": len(nodes), "source_splits": splits, "pending": len(pending)}), flush=True)
    return {"roots": list(range(len(roots))), "nodes": nodes, "leaves": leaves,
            "linear_constraints": constraints, "split_count": splits}


def member_check(windows, old_endpoints, records, epsilon):
    old_checks = []
    for endpoint in old_endpoints:
        cells = windows[str(endpoint["N"])]
        for row in range(4):
            for field, name in legacy.FIELDS:
                old_checks.append(exact_within(value(cells[row][name]), endpoint["original_CI"][field][row]))
    require(len(old_checks) == 72 and all(old_checks), "reused_native_source_old_CI_identity_changed")
    checks, h_checks = [], []
    for record in records:
        n = record["identity"]["pulse_count"]
        cells = windows[str(n)]
        for row, cell in enumerate(cells):
            features = [value(v) for v in cell["outcomes"]] + [value(cell["sA"]), value(cell["sB"])]
            for feature, prediction in enumerate(features):
                packet = record["conditional"][row][feature]["interval"]
                checks.append({"N": n, "row": row, "feature": FEATURES[feature], "prediction": prediction,
                               "contained": exact_within(prediction, packet), "disjoint": prediction.disjoint_exact(packet)})
        losses = [value(cells[1]["outcomes"][1]), value(cells[2]["outcomes"][2]), value(cells[3]["j"])]
        ch = value(cells[0]["j"]) - sum(losses, I(0))
        h, branches = h_ranges(ch, losses, epsilon)
        lower = F(record["contrast"]["h_bracket"]["lower"])
        h_checks.append({"N": n, "H_ranges": branches, "h": h, "lower": lower,
                         "strictly_above_lower": F(h.lo, SCALE) > lower,
                         "wholly_rejected": F(h.hi, SCALE) <= lower})
    require(len(checks) == 96 and len(h_checks) == 4, "native_member_qualification_incomplete")
    return {"qualified": all(c["contained"] for c in checks) and all(c["strictly_above_lower"] for c in h_checks),
            "old_CI_containments": 72, "new_conditional_checks": checks, "new_h_checks": h_checks}


def members(old_members, native, const, old_endpoints, endpoints, records, config, old_config):
    accepted, reused = [], []
    for member in old_members:
        proof = member_check(member["windows"], old_endpoints, records, F(config["epsilon"]))
        record = {"implementation": member["implementation"], "old_member_id": member["old_member_id"],
                  "recipe_sha256": hashlib.sha256(json.dumps(member["recipe"], sort_keys=True).encode()).hexdigest(), **proof}
        reused.append(record)
        if proof["qualified"] and len(accepted) < config["source_member_limit"]:
            accepted.append({"id": len(accepted), "origin": "previously_certified_native_Gamma_Fock",
                             "source": member["source"], "recipe": member["recipe"],
                             "native_windows": member["windows"], "reuse_identity": record,
                             "native_Fock_recomputed": False})
    search = {"performed": False, "candidate_count": 0, "fresh_Fock_evaluations": 0, "selection_exhausted": False}
    if accepted or native is None:
        return accepted, reused, search
    search["performed"] = True
    means = {"alpha": [native[0], native[2]], "beta": [native[1], native[3]], "joint": []}
    failures = Counter()
    for fractions in itertools.product(map(F, config["source_member_mean_fractions"]), repeat=4):
        points = [F(v.lo, SCALE) + fraction * F(v.width, SCALE) for v, fraction in zip(native, fractions)]
        shape = legacy.shape_from_means(points, const)
        for loss_index in range(1, config["source_member_loss_denominator"] + 1):
            box = shape + [I(F(loss_index, config["source_member_loss_denominator"]))]
            try:
                geometry.require(box[3].lo >= box[4].hi, "grid_loss_above_ratio")
                pop = geometry.population(box)
                geometry.require(pop is not None, "grid_non_PSD")
                common, _, _ = legacy.common_phase(box, pop, const, means, endpoints, old_config)
                geometry.require(common is not None, "grid_no_shared_k")
                polynomials = source_polynomials(box, pop, const, means, records, F(config["epsilon"]))
            except (ValueError, ArithmeticError) as error:
                failures[str(error)] += 1; continue
            for fraction in map(F, config["source_member_phase_fractions"]):
                k = I(F(common.lo, SCALE) + fraction * F(common.width, SCALE))
                search["candidate_count"] += 1
                outer = classify_phase(polynomials, k, records, F(config["epsilon"]))
                if outer["status"] == "excluded":
                    failures[outer["reason"]] += 1; continue
                try:
                    source = geometry.physical_source(box, k)
                    actual = legacy.actual_windows(source, const, old_endpoints, old_config)
                    search["fresh_Fock_evaluations"] += 1
                    windows = {str(e["N"]): geometry.serial(e["cells"]) for e in actual["endpoints"]}
                    proof = member_check(windows, old_endpoints, records, F(config["epsilon"]))
                    if not proof["qualified"]:
                        failures["actual_native_source_new_constraints_not_contained"] += 1; continue
                    accepted.append({"id": len(accepted), "origin": "fixed_new_mean_phase_loss_grid",
                        "recipe": {"mean_fractions": fractions, "native_mean_points": points,
                                   "loss": F(loss_index, config["source_member_loss_denominator"]),
                                   "phase_fraction": fraction, "common_k": k.midpoint()},
                        "source": source, "native_windows": windows, "qualification": proof,
                        "native_Fock": actual["same_pulse_positive_Born"], "native_Fock_recomputed": True})
                except (ValueError, ArithmeticError) as error:
                    failures[str(error)] += 1
                if len(accepted) >= config["source_member_limit"]:
                    search["failures"] = dict(failures)
                    return accepted, reused, search
    search.update(selection_exhausted=True, failures=dict(failures))
    return accepted, reused, search


def generate(cross_path):
    start = time.monotonic()
    config, old_config, const, records, bindings = configuration(cross_path)
    roots, old_endpoints, old_native, initial, old_members = old_material()
    native, contractions = mean_constraints(old_native, records, const)
    endpoints = joined_endpoints(old_endpoints, records)
    accepted, reuse_checks, search = members(old_members, native, const, old_endpoints, endpoints, records, config, old_config)
    print(json.dumps({"qualified_native_members": len(accepted), "old_members_checked": len(reuse_checks),
                      "fresh_Fock_evaluations": search["fresh_Fock_evaluations"]}), flush=True)
    cover = refine(roots, initial, native, const, endpoints, records, config, old_config)
    counts = Counter(n["status"] for n in cover["nodes"])
    result = {"schema": SCHEMA, "version": VERSION, "bindings": bindings, "input_domains": roots,
        "old_native_mean_domain": old_native, "new_native_mean_domain": native, "mean_contractions": contractions,
        "records": [{"identity": r["identity"], "total_trials": r["total_trials"],
                     "setting_trials": r["setting_trials"], "h_lower": F(r["contrast"]["h_bracket"]["lower"])} for r in records],
        "cover": cover, "members": accepted, "reused_member_checks": reuse_checks, "member_search": search,
        "summary": {"old_retained_source_boxes": 11, "node_count": len(cover["nodes"]),
                    "new_split_count": cover["split_count"], "node_status_counts": dict(counts),
                    "retained_source_leaves": len(cover["leaves"]), "qualified_native_members": len(accepted)},
        "complete_source_outer_cover_generated": True, "empty_source_fibre_certified": not cover["leaves"],
        "nonempty_source_fibre_exhibited": bool(accepted), "all_72_old_CI_preserved": True,
        "all_96_conditional_constraints_consumed": True, "all_4_joint_source_h_cuts_consumed": True,
        "retained_leaves_are_members": False, "old_source_search_rerun": False,
        "posthoc_CH_positive_filter_used": False, "finite_prefix_renormalized": False,
        "source_stationarity_is_named_model_condition": True, "publication_configuration_identified": False,
        "actual_epoch_identified": False, "bell_event_files_read": 0, "controller_advance": False,
        "retrospective": True, "runtime_seconds": time.monotonic() - start}
    require(not result["empty_source_fibre_certified"] or not accepted, "outer_rejection_conflicts_with_native_member")
    return geometry.serial(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--statistics-cross", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    require(not args.output.exists(), "protected_existing_domain_first")
    result = generate(args.statistics_cross)
    logical = (json.dumps(result, sort_keys=True, separators=(",", ":"), allow_nan=False) + "\n").encode()
    args.output.write_bytes(lzma.compress(logical, preset=6))
    print(json.dumps({"output": str(args.output), "sha256": statistics.sha(args.output),
                      "logical_sha256": hashlib.sha256(logical).hexdigest(), **result["summary"],
                      "runtime_seconds": result["runtime_seconds"]}), flush=True)


if __name__ == "__main__":
    main()
