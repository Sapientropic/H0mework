#!/usr/bin/env python3
"""Verify both sealed complete training-fibre trees and native positive-Born members."""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
import gc
import hashlib
import json
from pathlib import Path
import subprocess
import time

import independent_fiber as ind
import primary_fiber as primary
import receipt_codec_v2 as codec

HERE = Path(__file__).resolve().parent
ROOT = ind.ROOT
VERSION = "p23-full-statistical-fiber-cross-ef0003"
SCHEMA = "p23-full-statistical-fiber-cross-verification/v1"
SCIENCE_VERSION = ind.VERSION
DEFAULT_RECEIPT = HERE / "cross-verification.json"
FIRST_SHA = {
    "primary": "dbd033032c8f321be07379b75a6cc00ec8e4e46607069a87f17e9035a75502ac",
    "independent": "98c92df991a8a20b64c09a6c9340395f1a114bba8438193b72c3535cb6ea38f5",
}
PRIMARY_STAGE_KEYS = ("schema", "version", "training_ci", "cover", "members", "candidate_count",
                      "all_six_training_intervals_used", "frozen_source_law", "scope")
FALSE_SCOPE = ("source_mapping_identified", "actual_epoch_identified", "apparatus_optimum_verified",
               "controller_advance", "new_full_Born_kernel_claim", "new_statistical_coverage_kernel_claim")
POSITIVE_FIELDS = ("evidence_valid", "production_eligible", "readout_certified",
                   "full_training_fiber_outer_cover_verified", "nonempty_training_fiber_verified",
                   "certified_training_fiber_readout_disagreement", "uniform_heldout_containment_refuted",
                   "same_source_shared_phase_and_no_signaling_verified")


def require(value, reason):
    if not value:
        raise ValueError(reason)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def object_sha(value):
    digest = hashlib.sha256()
    encoder = json.JSONEncoder(sort_keys=True, separators=(",", ":"), allow_nan=False)
    for chunk in encoder.iterencode(value):
        digest.update(chunk.encode())
    return digest.hexdigest()


def read_json(path):
    return json.loads(Path(path).read_text())


def frozen(path, commit=None):
    path = Path(path).resolve()
    require(path.is_relative_to(ROOT), "foreign_scientific_source")
    rel = path.relative_to(ROOT).as_posix()
    if commit is None:
        commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", rel], cwd=ROOT, text=True).strip()
    require(commit, "uncommitted_verification_source:" + rel)
    blob = subprocess.check_output(["git", "show", commit + ":" + rel], cwd=ROOT)
    require(blob == path.read_bytes(), "unfrozen_verification_source:" + rel)
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=True)
    return {"path": rel, "commit": commit, "sha256": sha(blob)}


def check_bindings(rows):
    paths = set()
    for row in rows:
        rel = row["path"]
        require(rel not in paths, "duplicate_source_binding")
        paths.add(rel)
        path = (ROOT / rel).resolve()
        require(path.is_relative_to(ROOT) and path.is_file(), "missing_or_foreign_source_binding")
        require(sha(path.read_bytes()) == row["sha256"], "changed_source_binding:" + rel)
        if row.get("commit"):
            require(frozen(path, row["commit"])["sha256"] == row["sha256"], "changed_frozen_source")
    return True


def load_first(name):
    path = HERE / (name + "-ef0003.json.xz")
    sidecar = path.with_name(path.name + ".json")
    metadata = read_json(sidecar)
    original = read_json(HERE / (name + "-ef0003-storage.json"))
    expected = FIRST_SHA[name]
    require(metadata["logical_sha256"] == expected and metadata["original_JSON_bytes_preserved"] is True,
            "changed_first_scientific_bytes")
    require(metadata["stored_sha256"] == sha(path.read_bytes()) and metadata["stored_bytes"] == path.stat().st_size,
            "changed_first_storage")
    require(metadata["codec_sha256"] == sha((HERE / metadata["codec"]).read_bytes()), "changed_receipt_codec")
    if "base_codec_sha256" in metadata:
        require(metadata["base_codec_sha256"] == sha((HERE / "receipt_codec.py").read_bytes()), "changed_base_codec")
    original_sha = original.get("logical_sha256", original.get("logical_json_sha256"))
    require(original_sha == expected and original["logical_bytes"] == metadata["logical_bytes"], "wrong_original_first")
    raw = codec.decompress(path.read_bytes())
    require(len(raw) == metadata["logical_bytes"] and sha(raw) == expected, "first_receipt_roundtrip_changed")
    value = json.loads(raw)
    del raw
    require(value["version"] == SCIENCE_VERSION, "wrong_first_version")
    return value, {"path": path.relative_to(ROOT).as_posix(), "stored_sha256": metadata["stored_sha256"],
                   "logical_sha256": expected, "source_stage_sha256": value["source_stage_sha256"],
                   "storage_binding": frozen(path), "metadata_binding": frozen(sidecar)}


def bounds(packet):
    lo, hi = F(packet["exact_lower"]), F(packet["exact_upper"])
    require(lo <= hi, "reversed_exact_readout")
    return lo, hi


def exact(value):
    if isinstance(value, ind.I):
        return str(F(value.lo, ind.SCALE)), str(F(value.hi, ind.SCALE))
    if isinstance(value, primary.context()["I"]):
        return str(value.lo), str(value.hi)
    if isinstance(value, dict) and "exact_lower" in value and "exact_upper" in value:
        return tuple(map(str, bounds(value)))
    if isinstance(value, dict):
        return {k: exact(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [exact(v) for v in value]
    if isinstance(value, F):
        return str(value)
    return value


def same(left, right, reason):
    require(exact(left) == exact(right), reason)


def as_primary(packet):
    return primary.context()["I"](*bounds(packet))


def inside(value, packet):
    lo, hi = bounds(packet)
    a, b = bounds(value)
    return lo <= a <= b <= hi


def intersects(left, right):
    a, b = bounds(left)
    c, d = bounds(right)
    return max(a, c) <= min(b, d)


def monotone_inverse_cover(mean, probability, background):
    a, b = bounds(mean)
    lo, hi = bounds(probability)
    require(a > 0 and 1 - ((1 - background) / (1 + a)) ** 5 <= lo and
            1 - ((1 - background) / (1 + b)) ** 5 >= hi, "incomplete_inverse_single_interval")


def primary_structure(cover):
    nodes = {node["path"]: node for node in cover["nodes"]}
    splits = {row["path"]: row for row in cover["splits"]}
    leaves = {row["path"]: row for row in cover["leaves"]}
    require(len(nodes) == len(cover["nodes"]) and len(splits) == len(cover["splits"]) and
            len(leaves) == len(cover["leaves"]), "duplicate_primary_tree_entry")
    require(cover["all_leaves_preserved"] is True and cover["split_count"] == len(splits), "false_primary_complete_flag")
    require(set(splits).isdisjoint(leaves) and set(nodes) == set(splits) | set(leaves), "primary_missing_leaf")
    units, pending, volume = {}, [("", tuple((F(0), F(1)) for _ in range(5)))], F(0)
    while pending:
        path, unit = pending.pop()
        require(path not in units and path in nodes, "primary_missing_or_repeated_child")
        units[path] = unit
        if path in splits:
            row = splits[path]
            axis = row["axis"]
            require(type(axis) is int and 0 <= axis < 5, "invalid_primary_split_axis")
            lo, hi = unit[axis]
            mid = F(row["midpoint"])
            require(lo < mid < hi and mid == (lo + hi) / 2, "primary_split_gap_or_overlap")
            for label, ends in (("L", (lo, mid)), ("R", (mid, hi))):
                child = list(unit)
                child[axis] = ends
                pending.append((path + str(axis) + label, tuple(child)))
        else:
            leaf = leaves[path]
            require(leaf["classification"] in ("excluded", "retained_boundary"), "primary_false_inside_label")
            if leaf["classification"] != "excluded":
                same(leaf["unit_box"], unit, "changed_primary_terminal_box")
            product = F(1)
            for lo, hi in unit:
                product *= hi - lo
            volume += product
    require(set(units) == set(nodes) and volume == 1 and len(leaves) == len(splits) + 1 and
            len(nodes) == 2 * len(splits) + 1, "incomplete_primary_partition")
    return nodes, splits, leaves, units


def check_primary_tree(receipt, report):
    ci = primary.ci_view(report)
    domain = primary.training_domain(ci)
    same(receipt["training_ci"], ci, "primary_did_not_use_full_training_CI")
    cover = receipt["cover"]
    same(cover["initial_box"], domain, "changed_primary_initial_box")
    spec = primary.context()["spec"]
    require(cover["split_cap"] == spec["primary_split_cap"] and cover["axes"] == list(primary.AXES), "changed_primary_cover_contract")
    nodes, splits, leaves, units = primary_structure(cover)
    for name, d, background in zip(primary.NAMES[:4], domain[:4], map(F, spec["background_per_pulse"] * 2)):
        monotone_inverse_cover(primary.pack(d), primary.pack(ci[name]), background)
    replay = hashlib.sha256()
    excluded, retained, unresolved = 0, 0, 0
    for number, path in enumerate(nodes):
        unit = units[path]
        value = primary.evaluate(primary.source_box(unit, domain), ci)
        node = nodes[path]
        require(node["status"] == value["status"] and node["reason"] == value.get("reason"), "primary_node_replay_changed")
        if path in splits:
            require(value["status"] != "excluded" and splits[path]["axis"] == primary.split_axis(unit), "unlawful_primary_split")
        else:
            leaf = leaves[path]
            if leaf["classification"] == "excluded":
                require(value["status"] == "excluded", "unsupported_primary_exclusion")
                same(leaf["proof"], value, "changed_primary_exclusion_proof")
                excluded += 1
            else:
                require(value["status"] != "excluded", "primary_excluded_member_retained_as_inside")
                same(leaf["qualified_outer"], value, "changed_primary_paired_outer")
                axis = primary.split_axis(unit)
                stop = unit[axis][1] - unit[axis][0] <= F(spec["normalized_width_stop"]) or len(path) // 2 >= spec["max_depth"]
                require((leaf["stop"] == "resource_cap" and len(splits) == cover["split_cap"]) or
                        (leaf["stop"] == "width_or_depth" and stop), "unsupported_primary_terminal_stop")
                retained += 1
                unresolved += value["status"] != "retained"
        replay.update(object_sha({"path": path, "value": primary.pack(value)}).encode())
        if number % 4096 == 0:
            print(json.dumps({"primary_nodes_checked": number, "total": len(nodes)}), flush=True)
    require(cover["cap_reached"] is (len(splits) >= cover["split_cap"]), "incorrect_primary_cap_flag")
    return {"node_count": len(nodes), "split_count": len(splits), "terminal_count": len(leaves),
            "excluded_count": excluded, "retained_count": retained, "unresolved_outer_count": unresolved,
            "all_node_decisions_and_terminal_outers_recomputed": True, "closed_partition_volume": "1",
            "checked_node_digest": replay.hexdigest(), "cap_and_boundary_preserved": True}


def audited_contract(raw_box, constraints):
    """Reproduce each sound halfspace projection independently of the scientific contractor."""
    box, trace, sweeps = list(raw_box), [], 0
    for sweep in range(8):
        changed = False
        sweeps = sweep + 1
        for ri, row in enumerate(constraints):
            coefficients = row["coefficients"]
            total = ind.I(0)
            for coefficient, current in zip(coefficients, box):
                total += coefficient * current
            if ((row["lower"] is not None and total.hi < row["lower"]) or
                    (row["upper"] is not None and total.lo > row["upper"])):
                return None, {"reason": "strict_single_halfspace_violation", "constraint": row["name"],
                              "range": total, "sweeps": sweeps, "operations_sha256": ind.sha(ind.canonical(trace))}
            for axis in range(5):
                coefficient = coefficients[axis]
                if coefficient.lo <= 0 <= coefficient.hi:
                    continue
                rest = ind.I(0)
                for j in range(5):
                    if j != axis:
                        rest += coefficients[j] * box[j]
                before = box[axis]
                lower, upper = before.lo, before.hi
                if row["lower"] is not None:
                    bound = ind.I.raw(row["lower"] - rest.hi, row["lower"] - rest.hi) / coefficient
                    if coefficient.lo > 0:
                        lower = max(lower, bound.lo)
                    else:
                        upper = min(upper, bound.hi)
                if row["upper"] is not None:
                    bound = ind.I.raw(row["upper"] - rest.lo, row["upper"] - rest.lo) / coefficient
                    if coefficient.lo > 0:
                        upper = min(upper, bound.hi)
                    else:
                        lower = max(lower, bound.lo)
                if lower > upper:
                    return None, {"reason": "empty_single_halfspace_projection", "constraint": row["name"],
                                  "axis": ind.AXES[axis], "sweeps": sweeps, "operations_sha256": ind.sha(ind.canonical(trace))}
                if (lower, upper) != (before.lo, before.hi):
                    trace.append([ri, axis, before.lo, before.hi, lower, upper])
                    box[axis] = ind.I.raw(lower, upper)
                    changed = True
        e, r = box[4], box[3]
        lower, upper = max(0, e.lo), min(e.hi, ind.SCALE, r.hi)
        if lower > upper:
            return None, {"reason": "empty_physical_loss_projection", "sweeps": sweeps,
                          "operations_sha256": ind.sha(ind.canonical(trace))}
        if (lower, upper) != (e.lo, e.hi):
            trace.append(["physical_loss", 4, e.lo, e.hi, lower, upper])
            box[4] = ind.I.raw(lower, upper)
            changed = True
        if r.lo < box[4].lo:
            trace.append(["loss_ratio", 3, r.lo, r.hi, box[4].lo, r.hi])
            box[3] = ind.I.raw(box[4].lo, r.hi)
            changed = True
        if not changed:
            break
    return box, {"method": "directed_single_halfspace_and_physical_loss_projection", "sweeps": sweeps,
                 "update_count": len(trace), "operations_sha256": ind.sha(ind.canonical(trace))}


def independent_structure(stage):
    nodes, regions = stage["cover_tree"], stage["paired_regions"]
    converted = []
    for raw in nodes:
        node = dict(raw)
        for field in ("input_box", "contracted_box"):
            node[field] = None if raw[field] is None else list(map(ind.unpack, raw[field]))
        converted.append(node)
    root_box = list(map(ind.unpack, stage["initial_source_box"]))
    ind.verify_tree(converted, root_box, regions)
    return converted, {r["node_id"]: r for r in regions}


def check_independent_tree(receipt, report_text, config):
    stage = receipt["source_stage"]
    training = ind.parse_training(report_text)
    const = ind.constants(config)
    means = ind.training_means(training, config)
    initial, evidence = ind.initial_box(means, const)
    constraints = ind.linear_constraints(means, const)
    same(stage["training_view"], training, "independent_did_not_use_full_training_CI")
    same(stage["training_means"], means, "changed_independent_inverse_training_means")
    same(stage["initial_source_box"], initial, "changed_independent_initial_source_domain")
    same(stage["initial_box_evidence"], evidence, "changed_independent_initial_domain_proof")
    same(stage["linear_single_constraints"], constraints, "changed_independent_single_halfspaces")
    for field, background in (("alpha", const["background"][0]), ("beta", const["background"][1])):
        native = "sA_cell" if field == "alpha" else "sB_cell"
        for i, row in enumerate((0, 3)):
            monotone_inverse_cover(ind.serial(means[field][i]), training[native + "[" + str(row) + "]"], background)
    nodes, regions = independent_structure(stage)
    originals = {n["id"]: n for n in stage["cover_tree"]}
    replay, counts = hashlib.sha256(), Counter()
    for number, node in enumerate(nodes):
        original = originals[node["id"]]
        contracted, certificate = audited_contract(node["input_box"], constraints)
        same(node["contracted_box"], contracted, "unsound_independent_contraction")
        same(original["contraction"], certificate, "changed_independent_contraction_trace")
        status, exclusion = original["status"], None
        if contracted is None:
            exclusion = certificate
        else:
            pop = ind.population(contracted)
            if pop is None:
                exclusion = {"reason": "strict_PSD_population_violation"}
            else:
                try:
                    common, slabs = ind.phase_slabs(contracted, pop, const, means, config)
                    same(original.get("phase_slabs"), slabs, "changed_independent_phase_slab")
                    require("phase_unresolved" not in original, "false_independent_unresolved_flag")
                    if common is None:
                        exclusion = {"reason": "strict_training_joint_or_shared_phase_violation"}
                except (ValueError, ArithmeticError) as error:
                    # A comparison failure is evidence corruption, never a scientific unresolved branch.
                    if str(error).startswith(("changed_", "false_")):
                        raise
                    common = ind.I.raw(-pop["T2"].sqrt().hi, pop["T2"].sqrt().hi)
                    require(original.get("phase_unresolved") == str(error), "changed_independent_unresolved_branch")
                if exclusion is None:
                    same(original["common_k"], common, "changed_independent_common_phase")
                    relative = [F(value.width, base.width) for value, base in zip(contracted, initial)]
                    axis = max(range(5), key=lambda j: (relative[j], -j))
                    if status == "split":
                        require(original["split_axis"] == ind.AXES[axis] and
                                F(original["split_at"]) == F((contracted[axis].lo + contracted[axis].hi) // 2, ind.SCALE) and
                                relative[axis] > F(config["normalized_width_stop"]) and
                                original["depth"] < config["max_depth"], "changed_independent_split_rule")
                    if status == "retained_boundary":
                        region = regions[node["id"]]
                        same(region["source_box"], contracted, "changed_independent_region_source")
                        same(region["common_k"], common, "different_phase_in_paired_region")
                        same(region["T2"], pop["T2"], "changed_independent_region_physical_phase")
                        try:
                            projection = ind.paired_readout(contracted, common, pop, const, means)
                        except (ValueError, ArithmeticError) as error:
                            projection = {"cells": ind.unconstrained_cells(), "joint_sum": ind.I(0, 2),
                                          "joint_difference": ind.I(-1, 1), "CH_N5": ind.I(-2, 2),
                                          "unresolved": str(error), "shared_phase_parameter": "same_source_outer_preserved_without_projection"}
                        same(region["projection"], projection, "changed_independent_paired_projection")
                        require(region["reason"] == original["terminal_reason"], "changed_independent_stop_reason")
                        require(F(original["maximum_normalized_width"]) == relative[axis] and
                                ((original["terminal_reason"] == "normalized_width_reached" and
                                  relative[axis] <= F(config["normalized_width_stop"])) or
                                 (original["terminal_reason"] == "resource_split_cap_preserved" and
                                  stage["coverage"]["split_count"] == config["independent_split_cap"]) or
                                 (original["terminal_reason"] == "depth_cap_preserved" and
                                  original["depth"] >= config["max_depth"])), "unsupported_independent_cap_or_boundary")
        if status == "excluded":
            require(exclusion is not None, "unsupported_independent_exclusion")
            same(original["exclusion"], exclusion, "changed_independent_exclusion_proof")
        else:
            require(exclusion is None, "unsupported_independent_retained_branch")
        counts[status] += 1
        replay.update(object_sha({"id": node["id"], "contraction": ind.serial(certificate), "exclusion": ind.serial(exclusion)}).encode())
        if number % 4096 == 0:
            print(json.dumps({"independent_nodes_checked": number, "total": len(nodes)}), flush=True)
    coverage = stage["coverage"]
    require(coverage["node_count"] == len(nodes) and coverage["split_count"] == counts["split"] and
            coverage["terminal_leaf_count"] == counts["excluded"] + counts["retained_boundary"] and
            coverage["excluded_leaf_count"] == counts["excluded"] and coverage["retained_leaf_count"] == len(regions) and
            counts["split"] <= config["independent_split_cap"] and
            coverage["complete_tree_verified"] is True and coverage["all_boundary_and_cap_leaves_preserved"] is True,
            "incorrect_independent_coverage_summary")
    same(stage["projection_summary"], ind.projection_summary([
        {"projection": restore_ind(r["projection"])} for r in stage["paired_regions"]]), "changed_independent_projection_hull")
    return {"node_count": len(nodes), "split_count": counts["split"], "terminal_count": counts["excluded"] + counts["retained_boundary"],
            "excluded_count": counts["excluded"], "retained_count": counts["retained_boundary"],
            "all_contractor_shells_and_node_decisions_recomputed": True, "all_paired_regions_recomputed": True,
            "checked_node_digest": replay.hexdigest(), "cap_and_boundary_preserved": True}


def restore_ind(value):
    if isinstance(value, dict) and "exact_lower" in value and "exact_upper" in value:
        return ind.unpack(value)
    if isinstance(value, dict):
        return {k: restore_ind(v) for k, v in value.items()}
    if isinstance(value, list):
        return list(map(restore_ind, value))
    return value


def independent_shape_from_means(values, const):
    a0, b0, a1, b1 = values
    s0, c0 = const["singles"][0]
    s1, c1 = const["singles"][1]
    r = ((-s1) * a0 + s0 * a1) / ((-s1) * b0 + s0 * b1)
    z = ((a1 - a0) + r * (b1 - b0)) / (2 * (c0 - c1))
    m = (a0 + r * b0) / 2 + z * c0
    x = -(a0 - r * b0) / (2 * s0)
    return [m, z, x, r]


def cross_cells(left, right, tolerance):
    for row in range(4):
        for field in ("sA", "sB", "j"):
            a, b = left[row][field], right[row][field]
            require(intersects(a, b), "Gaussian_positive_Born_cross_disjoint")
            lo, hi = bounds(b)
            require(hi - lo <= tolerance, "positive_Born_tail_not_decisive")
        require(len(left[row]["outcomes"]) == len(right[row]["outcomes"]) == 4, "incomplete_four_outcomes")
        for a, b in zip(left[row]["outcomes"], right[row]["outcomes"]):
            require(intersects(a, b), "Gaussian_positive_Born_outcome_cross_disjoint")


def qualified_born(born, training):
    require(born["cutoff"] == 6 and born["vacuum_clicked_Born_exactly_zero"] is True and
            born["normalized_occupation_amplitudes"] is True and born["finite_prefix_renormalized"] is False and
            born["phase_mixture_before_window"] is True and born["tail_is_original_numberMass"] is True,
            "wrong_positive_Born_source_law")
    contained = True
    for field, row in ind.FIELDS:
        native = {"sA_cell": "sA", "sB_cell": "sB", "j": "j"}[field]
        contained &= inside(born["cells"][row][native], training[field + "[" + str(row) + "]"])
    return contained


def counterexamples(kind, member_id, born, report):
    out = []
    for row in (1, 2):
        for native, field in (("sA", "sA_cell"), ("sB", "sB_cell"), ("j", "j")):
            probability = born["cells"][row][native]
            target = report["common_mean_confidence"][field][row]
            if not intersects(probability, target):
                out.append({"implementation": kind, "member": member_id, "cell": row, "field": field,
                            "actual_positive_Born": probability,
                            "original_CI": {"exact_lower": target["exact_lower"], "exact_upper": target["exact_upper"]},
                            "all_six_training_CI_recomputed": True})
    return out


def check_members(receipt, kind, report, config):
    const = ind.constants(config)
    training = ind.parse_training(json.dumps(report))
    means = ind.training_means(training, config)
    ci = primary.ci_view(report)
    domain = primary.training_domain(ci)
    values = receipt["members"] if kind == "primary" else receipt["source_stage"]["members"]
    require(len(values) == config["member_limit"], "incomplete_native_member_set")
    checked, actual_training_qualified, witnesses, digest = 0, 0, [], hashlib.sha256()
    fractions = set(map(F, config["witness_axis_fractions"]))
    I = primary.context()["I"]
    for number, old in enumerate(values):
        recipe = old["recipe"]
        if kind == "primary":
            fs = list(map(F, recipe["ci_fractions"]))
            native = list(map(as_primary, recipe["inverse_single_means"]))
            require(len(native) == len(fs) == 4 and set(fs).issubset(fractions), "changed_primary_member_recipe")
            for v, weight, d in zip(native, fs, domain):
                same(v, I.point(d.lo + weight * (d.hi - d.lo)), "primary_member_not_native_CI_coordinate")
            loss, K = as_primary(recipe["loss"]), as_primary(recipe["phase_amplitude"])
            require(loss.lo == loss.hi and K.lo == K.hi and 0 < loss.lo <= 1 and
                    (loss.lo * config["witness_loss_denominator"]).denominator == 1, "illegal_primary_member_loss_or_phase")
            original_shape = primary.covariance(native + [loss])
            require(original_shape is not None, "primary_member_nonphysical")
            cell_geometry = primary.coefficients(original_shape)
            require(cell_geometry is not None, "primary_member_undefined_geometry")
            gaussian = [primary.window_readout(cell, K) for cell in cell_geometry]
            same(old["cells"], gaussian, "foreign_primary_readout_does_not_follow_recipe")
            ctx = primary.context()
            C, T = ctx["gauss"].square_root(original_shape["R2"]), ctx["gauss"].square_root(original_shape["T2"])
            coherence = K / T if T.lo > 0 else I.point(0)
            cosR = ctx["gauss"].square_root((1 + original_shape["z"] / C) / 2)
            same(old["source"], {"nH": (original_shape["m"] + C) / loss,
                 "nV": (original_shape["m"] - C) / loss, "etaA": loss, "etaB": loss / original_shape["r"],
                 "cosR": cosR, "sinR": (original_shape["x"] / C) / (2 * cosR),
                 "sin2R": original_shape["x"] / C, "lambda": (1 - coherence) / 2,
                 "pure_mode_phase_readout_equivalence": T.hi == 0}, "foreign_primary_source_does_not_follow_recipe")
            shape = independent_shape_from_means(list(map(ind.unpack, recipe["inverse_single_means"])), const)
            actual_source = ind.physical_source(shape + [ind.I(loss.lo)], ind.I(K.lo))
            born = ind.serial(ind.fock_readout(actual_source, const, 6))
            gaussian = primary.pack(gaussian)
        else:
            require(recipe["coordinate_space"] == "original_single_probability_CI" and
                    old["heldout_used_for_selection"] is False and old["id"] == number, "changed_independent_member_identity")
            fs = list(map(F, recipe["axis_fractions"]))
            raw_points = list(map(F, recipe["single_probability_coordinates"]))
            require(len(fs) == len(raw_points) == 4 and set(fs).issubset(fractions), "changed_independent_native_recipe")
            for point, weight, (field, row) in zip(raw_points, fs, ind.FIELDS[:4]):
                lo, hi = bounds(training[field + "[" + str(row) + "]"])
                require(point == lo + weight * (hi - lo), "independent_member_not_native_CI_coordinate")
            loss, k = F(recipe["loss"]), F(recipe["rational_common_k"])
            require(0 < loss <= 1 and (loss * config["witness_loss_denominator"]).denominator == 1, "illegal_independent_loss")
            shape, reconstruction = ind.member_shape(raw_points, config, const)
            value = ind.legal_member(training, means, raw_points, fs, shape, loss, recipe["phase_recipe"], k, const, config)
            value.update(id=number, single_reconstruction=reconstruction)
            same(old, value, "foreign_independent_member_does_not_follow_recipe")
            born = ind.serial(value["actual_positive_Fock_readout"])
            native = [primary.inverse_single(I.point(point), background)
                      for point, background in zip(raw_points, (const["background"] * 2))]
            psource = primary.covariance(native + [I.point(loss)])
            require(psource is not None, "cross_primary_nonphysical_member")
            cells = primary.coefficients(psource)
            require(cells is not None, "cross_primary_member_undefined_geometry")
            gaussian = primary.pack([primary.window_readout(cell, I.point(k)) for cell in cells])
        for field, row in ind.FIELDS:
            native_field = {"sA_cell": "sA", "sB_cell": "sB", "j": "j"}[field]
            require(inside(gaussian[row][native_field], training[field + "[" + str(row) + "]"]),
                    "not_training_qualified_Gaussian_member")
        actual_inside = qualified_born(born, training)
        require(kind != "independent" or actual_inside, "not_training_qualified_actual_Born")
        actual_training_qualified += actual_inside
        cross_cells(gaussian, born["cells"], F(config["comparison_tolerance"]))
        # Equal local settings consume the same native mean and common phase in all four cells.
        for first, second, field in ((0, 1, "sA"), (2, 3, "sA"), (0, 2, "sB"), (1, 3, "sB")):
            require(intersects(gaussian[first][field], gaussian[second][field]) and
                    intersects(born["cells"][first][field], born["cells"][second][field]), "source_no_signaling_cross_failed")
        if actual_inside:
            witnesses.extend(counterexamples(kind, number, born, report))
        digest.update(object_sha({"member": number, "recipe": recipe, "Born": born}).encode())
        checked += 1
        if checked % 64 == 0:
            print(json.dumps({kind + "_members_checked": checked}), flush=True)
    return {"members_checked": checked, "all_native_recipes_reconstructed": True,
            "all_actual_positive_Fock_readouts_recomputed": True, "all_six_Gaussian_training_CI_contained": True,
            "actual_Born_training_CI_contained_member_count": actual_training_qualified,
            "actual_Born_boundary_enclosure_member_count": checked - actual_training_qualified,
            "all_12_probabilities_and_16_outcomes_crossed": True, "shared_phase_no_signaling_crossed": True,
            "foreign_source_fields_used_as_forward_inputs": False, "checked_member_digest": digest.hexdigest()}, witnesses


def certificates():
    result = {}
    for name, schema in (("phase", "p23-phase-fiber-lean-certification/v1"), ("chart", "p23-training-chart-lean-certification/v1")):
        path = HERE / (name + "-certification.json")
        receipt = read_json(path)
        require(receipt["schema"] == schema and receipt["status"] == "certified" and
                set(receipt["authorized_axioms"]) == {"propext", "Classical.choice", "Quot.sound"}, "unqualified_Lean_certificate")
        rows = [{"path": p, **row} for p, row in receipt["bindings"].items() if p != "Lean/lakefile.toml"]
        check_bindings(rows)
        focused = receipt["focused_verification"]
        commands = focused.get("fresh_compilations", focused.get("fresh_cli", focused.get("commands", [])))
        if isinstance(commands, dict):
            commands = commands.get("commands", [])
        require(focused["fresh_source_compilation"] is True and focused["trust_level"] == 0 and
                focused["warning_as_error"] is True and len(commands) >= 6 and
                all(row["exit_code"] == 0 and "--trust=0" in row["command"] and
                    "-DwarningAsError=true" in row["command"] for row in commands), "invalid_Lean_compilation_receipt")
        # Receipt schema also binds the entire independently audited compilation and source inventory.
        require(receipt["actual_import_closure"]["unresolved"] == [] and
                receipt["kernel_claims"]["controller_advance"] is False, "changed_Lean_claim_scope")
        result[name] = {"binding": frozen(path), "status": receipt["status"], "kernel_claims": receipt["kernel_claims"],
                        "lsp_completed": focused["lsp"]["persistent_lsp_validation_completed"]}
    return result


def verify():
    start = time.monotonic()
    execution = [frozen(HERE / name) for name in ("criterion-cross.md", "sources-cross.json", "verify_fiber.py", "test_verify_fiber.py")]
    sources = read_json(HERE / "sources-cross.json")
    require(sources["version"] == VERSION, "wrong_cross_source_contract")
    check_bindings(sources["inputs"])
    config, _, _ = ind.configuration()
    lean = certificates()
    report_path = HERE.parent.parent / "observable-prediction/public-comparison-po0003.json"
    report_text = report_path.read_text()
    report = json.loads(report_text)
    firsts, audits, member_audits, witnesses = {}, {}, {}, []
    p, firsts["primary"] = load_first("primary")
    require(p["schema"] == "p23-full-statistical-fiber-primary/v1" and p["all_six_training_intervals_used"] is True,
            "wrong_primary_scientific_scope")
    require(object_sha({key: p[key] for key in PRIMARY_STAGE_KEYS}) == p["source_stage_sha256"], "primary_source_stage_digest_changed")
    check_bindings(p["bindings"]["execution_sources"])
    audits["primary"] = check_primary_tree(p, report)
    member_audits["primary"], outside = check_members(p, "primary", report, config)
    witnesses.extend(outside)
    require(p["comparison"]["uniform_heldout_contained"] is False and
            p["comparison"]["verdict"] == "CERTIFIED_TRAINING_MEMBER_HELDOUT_DISAGREEMENT" and outside,
            "unsupported_primary_uniform_verdict")
    del p
    gc.collect()
    other, firsts["independent"] = load_first("independent")
    require(other["schema"] == ind.SCHEMA and object_sha(other["source_stage"]) == other["source_stage_sha256"],
            "independent_source_stage_digest_changed")
    check_bindings([other["executable_freeze"]])
    require(all(other[key] is False for key in FALSE_SCOPE) and other["retrospective"] is True and
            other["foreign_source_fields_used_as_forward_inputs"] is False and
            other["primary_new_code_or_outputs_read_before_first"] is False, "changed_independent_scientific_scope")
    audits["independent"] = check_independent_tree(other, report_text, config)
    member_audits["independent"], outside = check_members(other, "independent", report, config)
    witnesses.extend(outside)
    require(other["comparison"]["uniform_heldout_contained"] is False and
            other["comparison"]["status"] == "TRAINING_LEGAL_MEMBER_OUTSIDE_HELDOUT_CI" and outside,
            "unsupported_independent_uniform_verdict")
    del other
    gc.collect()
    require(witnesses and any(w["implementation"] == "primary" for w in witnesses) and
            any(w["implementation"] == "independent" for w in witnesses), "missing_actual_Born_uniform_counterexample")
    return {"schema": SCHEMA, "version": VERSION, "status": "certified",
            **{key: True for key in POSITIVE_FIELDS}, "uniform_heldout_contained": False,
            "whole_source_family_rejected": False, **{key: False for key in FALSE_SCOPE},
            "publication_configuration_identified": False, "production_admitted": False,
            "retrospective": True, "bell_event_files_read": 0,
            "classification": "conditional public training-source-family outer cover and readout certificate",
            "production_eligible_role": "sealed mathematical evidence; no actual hardware admission",
            "source_law": config["conditional_source_law"], "training_fields": list(ind.FIELDS),
            "design_exposure": {"common_N": 177358351, "alpha": config["alpha"],
                                "features_in_global_union": 16, "fixed_bets": 40, "runs_covered": 6,
                                "pulse_subsets_covered": 32767, "settings_probability_bounds": config["settings_probability_bounds"]},
            "training_CI": ind.parse_training(report_text), "firsts": firsts,
            "tree_verification": audits, "member_verification": member_audits,
            "actual_Born_uniform_counterexamples": witnesses, "Lean_certificates": lean,
            "source_bindings": sources["inputs"], "execution_bindings": execution,
            "heldout_used_for_source_generation": False, "foreign_source_fields_used_as_forward_inputs": False,
            "all_cap_and_boundary_outers_retained": True,
            "scope_note": "All lawful members of the named conditional-stationary class are covered; outer boxes need not be wholly feasible. Concrete training-legal sources refute uniform heldout implication. Actual apparatus identity and the original nominal optimum gate retain their existing values.",
            "runtime_seconds": time.monotonic() - start}


def validate_result(receipt):
    require(receipt.get("schema") == SCHEMA and receipt.get("version") == VERSION and receipt.get("status") == "certified",
            "wrong_cross_certificate_kind")
    require(all(receipt.get(key) is True for key in POSITIVE_FIELDS) and receipt.get("uniform_heldout_contained") is False and
            receipt.get("whole_source_family_rejected") is False, "inconsistent_fiber_certificate_verdict")
    require(all(receipt.get(key) is False for key in FALSE_SCOPE) and receipt.get("retrospective") is True and
            type(receipt.get("bell_event_files_read")) is int and receipt.get("bell_event_files_read") == 0 and
            receipt.get("foreign_source_fields_used_as_forward_inputs") is False and receipt.get("production_admitted") is False,
            "inflated_fiber_certificate_scope")
    require(receipt.get("actual_Born_uniform_counterexamples"), "missing_uniform_counterexample")
    require("source_overrides" not in receipt and "force_pass" not in receipt, "scientific_source_override_forbidden")
    return True


def consume(certificate_path=None, disabled=False):
    """Lightweight production consumer; a path override may carry the same immutable certificate."""
    require(type(disabled) is bool, "disable_must_be_boolean")
    if disabled:
        return {"evidence_valid": False, "production_eligible": False, "readout_certified": False, "reason": "explicit_disable"}
    try:
        canonical = frozen(DEFAULT_RECEIPT)
        path = DEFAULT_RECEIPT if certificate_path is None else Path(certificate_path)
        require(sha(path.read_bytes()) == canonical["sha256"], "unfrozen_or_lookalike_cross_certificate")
        receipt = read_json(path)
        validate_result(receipt)
        check_bindings(receipt["source_bindings"] + receipt["execution_bindings"])
        for first in receipt["firsts"].values():
            check_bindings([first["storage_binding"], first["metadata_binding"]])
        return {"evidence_valid": True, "production_eligible": True, "readout_certified": True,
                "full_training_fiber_outer_cover_verified": True, "nonempty_training_fiber_verified": True,
                "uniform_heldout_contained": False, "certified_training_fiber_readout_disagreement": True,
                "same_source_shared_phase_and_no_signaling_verified": True,
                **{key: False for key in FALSE_SCOPE}, "production_admitted": False,
                "publication_configuration_identified": False,
                "production_eligible_role": "sealed mathematical evidence; no actual hardware admission",
                "retrospective": True, "certificate": canonical,
                "reason": "certified_conditional_training_fiber_and_uniform_counterexample"}
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        return {"evidence_valid": False, "production_eligible": False, "readout_certified": False, "reason": str(error)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--certificate", type=Path)
    parser.add_argument("--disabled", action="store_true")
    args = parser.parse_args()
    if args.check_only:
        require(args.output is None, "check_only_does_not_create_science")
        result = consume(args.certificate, args.disabled)
        print(json.dumps(result, sort_keys=True))
        return 0 if result["evidence_valid"] else 1
    require(args.output is not None and args.certificate is None and not args.disabled, "fresh_verification_requires_output")
    require(not args.output.exists(), "protected_existing_cross_verification")
    result = verify()
    validate_result(result)
    args.output.write_text(json.dumps(result, sort_keys=True, indent=2, allow_nan=False) + "\n")
    print(json.dumps({"output": str(args.output), "status": result["status"],
                      "full_training_fiber_outer_cover_verified": result["full_training_fiber_outer_cover_verified"],
                      "nonempty_training_fiber_verified": result["nonempty_training_fiber_verified"],
                      "uniform_heldout_contained": result["uniform_heldout_contained"],
                      "counterexamples": len(result["actual_Born_uniform_counterexamples"]),
                      "runtime_seconds": result["runtime_seconds"]}), flush=True)


if __name__ == "__main__":
    raise SystemExit(main())
