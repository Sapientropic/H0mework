#!/usr/bin/env python3
"""Independent source-polytope and actual Born witnesses for all XOR3 windows."""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
import gzip
import hashlib
import importlib.util
import itertools
import json
import math
from pathlib import Path
import re
import sys
import time

import independent as statistics

HERE = Path(__file__).resolve().parent
ROOT = statistics.ROOT
FIBER = HERE.parents[1] / "observable-closure/full-statistical-fiber"
loader = importlib.util.spec_from_file_location("mw_source_frozen_geometry", FIBER / "independent_fiber.py")
geometry = importlib.util.module_from_spec(loader)
sys.modules[loader.name] = geometry
loader.loader.exec_module(geometry)
I = geometry.I
VERSION = "p23-public-multi-window-source-mws0001"
SCHEMA = "p23-public-multi-window-source-independent/v1"
FREEZE = "14a03d224b"
STAT_FIRST_SHA = "ad30b467e881a1ae56f5ccea15144112d88e57b9cb054c2639fa476ad2c62538"
FIELDS = (("sA_cell", "sA"), ("sB_cell", "sB"), ("j", "j"))


def configuration():
    statistics.frozen(HERE / "criterion-source.md", FREEZE)
    statistics.frozen(HERE / "sources-source.json", FREEZE)
    matches = re.findall(r"<!-- MW-SOURCE-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- MW-SOURCE-FROZEN-END -->",
                         (HERE / "criterion-source.md").read_text(), re.S)
    geometry.require(len(matches) == 1, "nonunique_multi_window_source_contract")
    spec = json.loads(matches[0])
    geometry.require(spec["version"] == VERSION and spec["workbook"] == "diag-xor3.xlsx" and
        spec["pulse_counts"] == [1, 3, 5, 7, 9] and spec["all_CI_count"] == 72 and spec["independent_split_cap"] == 4096 and
        spec["member_limit"] == 16 and spec["member_per_sign_limit"] == 8 and spec["member_mean_fractions"] == ["1/2", "1/4", "3/4"] and
        spec["member_phase_fractions"] == ["1/2", "1/4", "3/4"] and spec["source_pair_cutoff"] == 6 and
        spec["alpha_unchanged"] is True and spec["calibration_sigma_inserted_as_CI"] is False, "multi_window_source_contract_changed")
    manifest = json.loads((HERE / "sources-source.json").read_text())
    for row in manifest["inputs"]:
        path = (ROOT / row["path"]).resolve()
        geometry.require(path.is_relative_to(ROOT) and statistics.sha(path.read_bytes()) == row["sha256"], "multi_window_source_binding_changed")
    kernel, _, kernel_bindings = geometry.configuration()
    bindings = {"source_contract": statistics.frozen(HERE / "criterion-source.md", FREEZE),
                "source_manifest": statistics.frozen(HERE / "sources-source.json", FREEZE),
                "program": statistics.frozen(__file__), "kernel_program": statistics.frozen(FIBER / "independent_fiber.py"),
                "independent_statistics_program": statistics.frozen(HERE / "independent.py"),
                "independent_statistics_first": statistics.frozen(HERE / "independent.json.gz"),
                "independent_statistics_storage": statistics.frozen(HERE / "independent-gzip-storage.json"),
                "kernel_inputs": kernel_bindings, "manifest": manifest}
    return {**kernel, **spec}, bindings


def packet_value(value):
    return I(value["exact_lower"], value["exact_upper"])


def all_CI(config):
    raw = gzip.decompress((HERE / "independent.json.gz").read_bytes())
    geometry.require(statistics.sha(raw) == STAT_FIRST_SHA, "changed_independent_statistical_first")
    report = json.loads(raw)
    run = next(row for row in report["runs"] if row["run"] == "xor3")
    endpoints = [{"id": "full_N" + str(g["pulse_count"]), "N": g["pulse_count"], "exposure": g["complete_trials"],
                  "original_CI": g["common_Born_CI"]} for g in run["groups"]]
    old_path = (HERE / config["old_cut_CI"]).resolve()
    old = json.loads(old_path.read_text())
    endpoints.append({"id": "old_stop_N5", "N": 5, "exposure": old["complete_trials"], "original_CI": old["common_mean_confidence"]})
    geometry.require(len(endpoints) == 6 and sum(4 * len(FIELDS) for _ in endpoints) == 72 and
                     run["complete_trials"] == 182137032 and old["complete_trials"] == 177358351,
                     "wrong_multi_window_or_old_stop_domain")
    for endpoint in endpoints:
        endpoint["CI"] = {field: [packet_value(p) for p in endpoint["original_CI"][field]] for field, _ in FIELDS}
    return endpoints


def root_delta(value, N, config):
    geometry.require(N in (1, 3, 5, 7, 9), "unsupported_window_power")
    if N == 1:
        return value
    radius = max(abs(value.lo), abs(value.hi))
    geometry.require(radius <= I(config["binomial_input_abs_max"]).hi, "window_root_outside_binomial_domain")
    coefficient, result = F(1), I(0)
    terms = config["binomial_terms"]
    for n in range(1, terms + 1):
        coefficient *= (F(1, N) - (n - 1)) / n
        result += coefficient * value.power(n)
    coefficient *= (F(1, N) - terms) / (terms + 1)
    rad = I.raw(radius, radius)
    remainder = abs(coefficient) * rad.power(terms + 1) / (1 - rad)
    return result + I.raw(-remainder.hi, remainder.hi)


def pulse_mean_domain(endpoints, config):
    stat_spec = {"background_per_pulse": config["background_per_pulse"]}
    windows = [{"pulse_count": e["N"], "sheet": e["id"], "common_Born_CI": {
        field: [statistics.I(p["exact_lower"], p["exact_upper"]) for p in e["original_CI"][field]] for field, _ in FIELDS}}
        for e in endpoints]
    necessary = statistics.necessary_intersection(windows, stat_spec, True)
    geometry.require(necessary["identical_fresh_pulse_necessary_relations_compatible"], "all_72_CI_common_pulse_necessary_intersection_empty")
    Q = necessary["common_bare_single_pulse_no_click"]
    native = []
    for name in ("QA0", "QB0", "QA1", "QB1"):
        interval = Q[name]
        geometry.require(0 < interval.lo <= interval.hi < 1, "pulse_single_mean_not_finite_positive")
        native.append(I(1 / interval.hi - 1, 1 / interval.lo - 1))
    means = {"alpha": [native[0], native[2]], "beta": [native[1], native[3]], "joint": []}
    return native, means, statistics.packet(necessary)


def window_single(probability, N):
    return sum(((-1) ** (n + 1) * math.comb(N, n) * probability.power(n) for n in range(1, N + 1)), I(0))


def window_joint_coefficients(pa, pb, pulse_joint, N):
    result = geometry.pscale(pulse_joint, N)
    base = geometry.padd([pa + pb], geometry.pscale(pulse_joint, -1))
    power = base
    for n in range(2, N + 1):
        power = geometry.pmul(power, base)
        term = geometry.padd(power, [-pa.power(n) - pb.power(n)])
        result = geometry.padd(result, geometry.pscale(term, (-1) ** n * math.comb(N, n)))
    return result


def common_phase(box, pop, const, means, endpoints, config):
    radius = pop["T2"].sqrt().hi
    common, slabs = I.raw(-radius, radius), []
    geos = [geometry.geometry(box, pop, const, row, means) for row in range(4)]
    for endpoint in endpoints:
        N = endpoint["N"]
        for row, geo in enumerate(geos):
            SA, SB = window_single(geo["pulse_A"], N), window_single(geo["pulse_B"], N)
            rho = (endpoint["CI"]["j"][row] - SA * SB) / ((1 - SA) * (1 - SB))
            omega = root_delta(rho, N, config)
            rhs = (omega * geo["E"] - geo["Ccorr"] * geo["L"] - geo["g"].square() * pop["T2"]) / geo["D"]
            if (geo["g"] * common).intersect(rhs) is None:
                return None, slabs + [{"endpoint": endpoint["id"], "row": row, "g": geo["g"], "rhs": rhs,
                                      "reason": "strict_common_phase_slab_violation"}], geos
            if not geo["g"].lo <= 0 <= geo["g"].hi:
                updated = common.intersect(rhs / geo["g"])
                if updated is None:
                    return None, slabs + [{"endpoint": endpoint["id"], "row": row, "g": geo["g"], "rhs": rhs,
                                          "reason": "empty_all_windows_common_k"}], geos
                common = updated
                mode = "nonzero_coupling_inverse"
            else:
                mode = "zero_or_crossing_g_preserved_without_division"
            slabs.append({"endpoint": endpoint["id"], "row": row, "g": geo["g"], "rhs": rhs,
                          "common_k_after": common, "mode": mode})
    return common, slabs, geos


def paired_readout(box, common, pop, const, means, endpoints):
    geos = [geometry.geometry(box, pop, const, row, means) for row in range(4)]
    ba, bb = const["background"]
    background_factor = (1 - ba) * (1 - bb)
    pulses = []
    for geo in geos:
        a, b = geo["alpha"], geo["beta"]
        base = a * b / geo["D"] + (geo["Ccorr"] * geo["L"] + geo["g"].square() * pop["T2"]) / (geo["E"] * geo["D"])
        pulses.append([background_factor * base + ba * (1 - bb) * b / (1 + b) + bb * (1 - ba) * a / (1 + a) + ba * bb,
                       background_factor * geo["g"] / geo["E"]])
    readings = []
    for endpoint in endpoints:
        N, cells = endpoint["N"], []
        for row, (geo, pulse) in enumerate(zip(geos, pulses)):
            SA = geometry.clipped(window_single(geo["pulse_A"], N), 0, geometry.SCALE)
            SB = geometry.clipped(window_single(geo["pulse_B"], N), 0, geometry.SCALE)
            poly = window_joint_coefficients(geo["pulse_A"], geo["pulse_B"], pulse, N)
            J = geometry.clipped(geometry.pvalue(poly, common), 0, min(SA.hi, SB.hi))
            values = {"sA": SA, "sB": SB, "j": J}
            for field, name in FIELDS:
                values[name] = values[name].intersect(endpoint["CI"][field][row])
                geometry.require(values[name] is not None, "strict_original_window_CI_violation")
            SA, SB, J = values["sA"], values["sB"], values["j"]
            cells.append({**values, "outcomes": [J, geometry.clipped(SA - J, 0, geometry.SCALE), geometry.clipped(SB - J, 0, geometry.SCALE),
                geometry.clipped(1 - SA - SB + J, 0, geometry.SCALE)], "joint_polynomial_in_common_k": poly})
        plus = geometry.padd(cells[1]["joint_polynomial_in_common_k"], cells[2]["joint_polynomial_in_common_k"])
        minus = geometry.padd(cells[1]["joint_polynomial_in_common_k"], geometry.pscale(cells[2]["joint_polynomial_in_common_k"], -1))
        ch = geometry.padd(geometry.padd(cells[0]["joint_polynomial_in_common_k"], plus), geometry.pscale(cells[3]["joint_polynomial_in_common_k"], -1))
        ch = geometry.padd(ch, [-cells[0]["sA"] - cells[0]["sB"]])
        natural_CH = cells[0]["j"] + cells[1]["j"] + cells[2]["j"] - cells[3]["j"] - cells[0]["sA"] - cells[0]["sB"]
        CH = geometry.pvalue(ch, common).intersect(natural_CH)
        geometry.require(CH is not None, "strict_paired_CH_original_CI_violation")
        readings.append({"endpoint": endpoint["id"], "N": N, "cells": cells,
                        "joint_sum": geometry.pvalue(plus, common), "joint_difference": geometry.pvalue(minus, common), "CH": CH})
    return {"endpoints": readings, "all_four_cells_and_six_endpoints_share_one_k": True,
            "no_signaling_exact_from_the_same_native_source": True, "CI_intersections_are_outer_only": True}


def unresolved_readout(endpoints, reason):
    return {"endpoints": [{"endpoint": e["id"], "N": e["N"], "cells": [{"sA": e["CI"]["sA_cell"][r],
        "sB": e["CI"]["sB_cell"][r], "j": e["CI"]["j"][r], "outcomes": [I(0, 1)] * 4} for r in range(4)],
        "CH": I(-2, 2), "joint_sum": I(0, 2), "joint_difference": I(-1, 1)} for e in endpoints],
        "unresolved_outer_reason": reason, "all_valid_boundary_sources_preserved": True}


def cover(initial, means, const, endpoints, config):
    constraints = geometry.linear_constraints(means, const)
    nodes, regions, pending, next_id, splits = [], [], [(0, None, initial, 0)], 1, 0
    initial_widths = [v.width for v in initial]
    while pending:
        index, parent, raw, depth = pending.pop()
        box, contraction = geometry.linear_contract(raw, constraints)
        node = {"id": index, "parent": parent, "depth": depth, "input_box": raw,
                "contracted_box": box, "contraction": contraction}
        nodes.append(node)
        if box is None:
            node.update(status="excluded", exclusion=contraction); continue
        pop = geometry.population(box)
        if pop is None:
            node.update(status="excluded", exclusion={"reason": "strict_PSD_population_violation"}); continue
        try:
            common, slabs, _ = common_phase(box, pop, const, means, endpoints, config)
            node["phase_slabs"] = slabs
            if common is None:
                node.update(status="excluded", exclusion={"reason": "strict_joint_or_shared_k_violation"}); continue
        except (ValueError, ArithmeticError) as error:
            radius = pop["T2"].sqrt().hi
            common = I.raw(-radius, radius)
            node["phase_unresolved"] = str(error)
        node["common_k"] = common
        normalized = [F(value.width, width) for value, width in zip(box, initial_widths)]
        axis = max(range(5), key=lambda j: (normalized[j], -j))
        if normalized[axis] > F(config["normalized_width_stop"]) and depth < config["max_depth"] and splits < config["independent_split_cap"]:
            midpoint = (box[axis].lo + box[axis].hi) // 2
            if box[axis].lo < midpoint < box[axis].hi:
                left, right = list(box), list(box)
                left[axis], right[axis] = I.raw(box[axis].lo, midpoint), I.raw(midpoint, box[axis].hi)
                children = [next_id, next_id + 1]; next_id += 2; splits += 1
                node.update(status="split", split_axis=geometry.AXES[axis], split_at=F(midpoint, geometry.SCALE), children=children)
                pending.append((children[1], index, right, depth + 1)); pending.append((children[0], index, left, depth + 1))
                if splits % 256 == 0:
                    print(json.dumps({"independent_source_splits": splits, "pending": len(pending)}), flush=True)
                continue
        node.update(status="retained_boundary", terminal_reason="resource_cap_or_depth_or_width_preserved",
                    maximum_normalized_width=normalized[axis])
        try:
            projection = paired_readout(box, common, pop, const, means, endpoints)
        except (ValueError, ArithmeticError) as error:
            projection = unresolved_readout(endpoints, str(error))
        regions.append({"node_id": index, "source_box": box, "common_k": common, "T2": pop["T2"], "projection": projection})
    nodes.sort(key=lambda node: node["id"])
    geometry.verify_tree(nodes, initial, regions)
    counts = Counter(node["status"] for node in nodes)
    return {"source_chart": "independent_m_z_x_r_e_polytope", "initial_source_box": initial,
        "linear_single_constraints": constraints, "cover_tree": nodes, "paired_regions": regions,
        "node_count": len(nodes), "split_count": splits, "excluded_count": counts["excluded"],
        "retained_count": counts["retained_boundary"], "all_cap_and_boundary_leaves_preserved": True,
        "complete_tree_verified": True, "all_original_72_CI_consumed": True}


def shape_from_means(points, const):
    a0, b0, a1, b1 = [I(point) for point in points]
    s0, c0 = const["singles"][0]; s1, c1 = const["singles"][1]
    r = ((-s1) * a0 + s0 * a1) / ((-s1) * b0 + s0 * b1)
    z = ((a1 - a0) + r * (b1 - b0)) / (2 * (c0 - c1))
    m = (a0 + r * b0) / 2 + z * c0
    x = -(a0 - r * b0) / (2 * s0)
    return [m, z, x, r]


def actual_windows(source, const, endpoints, config):
    born = geometry.fock_readout(source, const, config["source_pair_cutoff"])
    ba, bb = const["background"]
    readings = []
    for endpoint in endpoints:
        N, cells = endpoint["N"], []
        for row, pulse in enumerate(born["cells"]):
            physical = pulse["pulse_positive_Born"]
            pa, pb = ba + (1 - ba) * physical["A"], bb + (1 - bb) * physical["B"]
            joint = ((1 - ba) * (1 - bb) * physical["J"] + ba * (1 - bb) * physical["B"] + bb * (1 - ba) * physical["A"] + ba * bb)
            SA, SB = window_single(pa, N), window_single(pb, N)
            J = geometry.pvalue(window_joint_coefficients(pa, pb, [joint], N), I(0))
            cell = {"sA": SA, "sB": SB, "j": J, "outcomes": [J, SA - J, SB - J, 1 - SA - SB + J]}
            for field, name in FIELDS:
                geometry.require(cell[name].within_exact(endpoint["original_CI"][field][row]), "actual_Born_original_window_CI_not_contained")
            cells.append(cell)
        CH = cells[0]["j"] + cells[1]["j"] + cells[2]["j"] - cells[3]["j"] - cells[0]["sA"] - cells[0]["sB"]
        readings.append({"endpoint": endpoint["id"], "N": N, "cells": cells, "CH": CH})
    return {"same_pulse_positive_Born": born, "endpoints": readings, "all_72_original_CI_contained": True,
        "phase_mixture_before_each_window": True, "vacuum_clicked_Born_exactly_zero": True,
        "finite_prefix_renormalized": False, "tail_is_original_numberMass": True}


def generate_members(native, means, const, endpoints, config):
    members, signs, attempts, rejections = [], Counter(), 0, Counter()
    for fractions in itertools.product(map(F, config["member_mean_fractions"]), repeat=4):
        points = [F(value.lo, geometry.SCALE) + frac * F(value.width, geometry.SCALE) for frac, value in zip(fractions, native)]
        shape = shape_from_means(points, const)
        for j in range(1, config["member_loss_denominator"] + 1):
            e = F(j, config["member_loss_denominator"])
            box = shape + [I(e)]
            try:
                geometry.require(box[3].lo >= box[4].hi, "candidate_loss_above_ratio")
                pop = geometry.population(box)
                geometry.require(pop is not None, "candidate_non_PSD")
                common, _, _ = common_phase(box, pop, const, means, endpoints, config)
                geometry.require(common is not None, "candidate_no_common_phase")
            except (ValueError, ArithmeticError) as error:
                rejections[str(error)] += 1; continue
            for fraction in map(F, config["member_phase_fractions"]):
                k = F(common.lo, geometry.SCALE) + fraction * F(common.width, geometry.SCALE)
                attempts += 1
                try:
                    gaussian = paired_readout(box, I(k), pop, const, means, endpoints)
                    n5 = next(row for row in gaussian["endpoints"] if row["endpoint"] == "full_N5")
                    pre_sign = "positive" if n5["CH"].lo > 0 else "negative" if n5["CH"].hi < 0 else "unresolved"
                    if pre_sign == "unresolved" or signs[pre_sign] >= config["member_per_sign_limit"]:
                        continue
                    source = geometry.physical_source(box, I(k))
                    actual = actual_windows(source, const, endpoints, config)
                    actual_n5 = next(row for row in actual["endpoints"] if row["endpoint"] == "full_N5")
                    sign = "positive" if actual_n5["CH"].lo > 0 else "negative" if actual_n5["CH"].hi < 0 else "unresolved"
                    geometry.require(sign != "unresolved" and signs[sign] < config["member_per_sign_limit"], "actual_Born_sign_not_strict_or_quota_full")
                    for left, right in zip(gaussian["endpoints"], actual["endpoints"]):
                        for r in range(4):
                            for _, field in FIELDS:
                                geometry.require(left["cells"][r][field].intersect(right["cells"][r][field]) is not None,
                                                 "Gaussian_positive_Born_multiwindow_disjoint")
                    members.append({"id": len(members), "recipe": {"mean_fractions": fractions, "native_mean_points": points,
                        "loss": e, "common_k": k, "phase_fraction": fraction}, "source": source, "source_box": box,
                        "paired_Gaussian": gaussian, "actual_positive_Born": actual, "CH_N5_sign": sign,
                        "all_72_original_CI_contained": True, "old_source_or_member_used_as_generation_seed": False})
                    signs[sign] += 1
                except (ValueError, ArithmeticError) as error:
                    rejections[str(error)] += 1
                if len(members) >= config["member_limit"]:
                    return members, {"attempts": attempts, "sign_counts": signs, "rejection_counts": rejections, "selection_exhausted": False}
    return members, {"attempts": attempts, "sign_counts": signs, "rejection_counts": rejections, "selection_exhausted": True}


def science():
    start = time.monotonic()
    config, bindings = configuration()
    endpoints = all_CI(config)
    native, means, necessary = pulse_mean_domain(endpoints, config)
    const = geometry.constants(config)
    initial, evidence = geometry.initial_box(means, const)
    members, search = generate_members(native, means, const, endpoints, config)
    print(json.dumps({"independent_source_members": len(members), "sign_counts": search["sign_counts"]}), flush=True)
    tree = cover(initial, means, const, endpoints, config)
    value = geometry.serial({"schema": SCHEMA, "version": VERSION, "all_original_endpoint_CI": endpoints,
        "four_native_pulse_mean_domain": native, "shared_pulse_necessary": necessary,
        "initial_domain_evidence": evidence, "bindings": bindings, "members": members, "member_search": search,
        "cover": tree, "complete_source_outer_cover_generated": True, "all_72_original_CI_consumed": True,
        "nonempty_source_fibre_exhibited": bool(members), "empty_source_fibre_certified": not tree["paired_regions"],
        "primary_new_source_code_or_outputs_read_before_first": False,
        "foreign_source_fields_used_as_forward_inputs": False, "old_source_or_member_used_as_generation_seed": False,
        "publication_configuration_identified": False, "actual_epoch_identified": False,
        "calibration_sigma_inserted_as_CI": False, "nominal_optimum_contract_replaced": False,
        "new_full_Born_kernel_claim": False, "new_statistical_coverage_kernel_claim": False,
        "controller_advance": False, "bell_event_files_read": 0, "retrospective": True})
    value["source_stage_sha256"] = statistics.sha(json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False).encode())
    value["runtime_seconds"] = time.monotonic() - start
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    geometry.require(not args.output.exists(), "protected_existing_source_independent_first")
    value = science()
    logical = (json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False) + "\n").encode()
    stored = gzip.compress(logical, compresslevel=9, mtime=0)
    args.output.write_bytes(stored)
    metadata = {"schema": "p23-multi-window-source-independent-first-storage/v1", "version": VERSION,
        "logical_sha256": statistics.sha(logical), "logical_bytes": len(logical), "stored_sha256": statistics.sha(stored),
        "stored_bytes": len(stored), "source_stage_sha256": value["source_stage_sha256"], "program": statistics.frozen(__file__)}
    args.output.with_name(args.output.name.removesuffix(".json.gz") + "-storage.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(json.dumps(metadata, sort_keys=True), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
