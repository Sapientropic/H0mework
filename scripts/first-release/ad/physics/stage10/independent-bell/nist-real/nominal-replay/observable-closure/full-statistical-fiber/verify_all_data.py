#!/usr/bin/env python3
"""Seal the complete retrospective all-CI fibre and actual positive-Born readout."""
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
import independent_all_data as independent
import primary_all_data as main_science
import receipt_codec_v2 as codec

HERE = Path(__file__).resolve().parent
ROOT = ind.ROOT
VERSION = "p23-all-data-statistical-fiber-cross-ef0003.1"
SCIENCE_VERSION = independent.VERSION
SCHEMA = "p23-all-data-statistical-fiber-cross-verification/v1"
ROLE = "retrospective_all_public_CI_intersection"
DEFAULT_RECEIPT = HERE / "all-data-verification.json"
FIRST_SHA = {
    "primary": "39c3e047fa3f3c7a7c0547642c1ff767038996a9fef023833c27a6cc3ba3a0d3",
    "independent": "29231bfbbc5a29015ea8030fb7f5910a81d6c7f9469edb337ffc9c49003b20fa",
}
PRIMARY_STAGE_KEYS = ("schema", "version", "statistical_role", "all_ci", "cover", "members", "candidate_count",
    "frozen_source_law", "scope", "source_relations", "whole_fibre_CH", "nonempty_fibre_exhibited",
    "all_boundary_and_cap_leaves_preserved")
FALSE_SCOPE = ("source_mapping_identified", "actual_epoch_identified", "apparatus_optimum_verified",
    "controller_advance", "new_full_Born_kernel_claim", "new_statistical_coverage_kernel_claim",
    "publication_configuration_identified", "production_admitted", "heldout_prediction_claimed")
POSITIVE_FIELDS = ("evidence_valid", "production_eligible", "readout_certified",
    "full_all_data_fiber_outer_cover_verified", "nonempty_all_data_fiber_verified",
    "same_source_shared_phase_and_no_signaling_verified")
ALL_FIELDS = tuple((field, row) for row in range(4) for field in ("sA_cell", "sB_cell", "j"))
LOCAL_PAIRS = ((0, 1, "sA"), (2, 3, "sA"), (0, 2, "sB"), (1, 3, "sB"))


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

def public_domain(report_text, config):
    report = json.loads(report_text)
    require(report["complete_trials"] == 177358351 and report["alpha"] == config["alpha"] and
            report["features_in_global_union"] == 16 and report["retrospective"] is True and
            report["bell_event_files_read"] == 0, "changed_original_statistical_exposure")
    original = independent.parse_all_CI(report_text)
    selected, provenance = independent.single_intersections(original)
    require(selected is not None and len(original) == 12, "empty_original_same_setting_intersection")
    require(config["fixed_bets"] == 40 and config["runs_covered"] == 6 and
            config["pulse_subsets_covered"] == 32767 and config["alpha"] == "1/20" and
            config["settings_probability_bounds"] == ["994009/4000000", "1006009/4000000"],
            "changed_global_confidence_budget")
    return report, original, selected, provenance


def load_first(kind):
    path = HERE / (kind + "-all-data-ef0003.1.json.xz")
    sidecar = path.with_name(path.name + ".json")
    original_path = HERE / (kind + "-all-data-ef0003.1-storage.json")
    metadata, original = read_json(sidecar), read_json(original_path)
    expected = FIRST_SHA[kind]
    require(metadata["logical_sha256"] == expected and metadata["original_JSON_bytes_preserved"] is True,
            "changed_all_data_first_scientific_bytes")
    require(metadata["stored_sha256"] == sha(path.read_bytes()) and metadata["stored_bytes"] == path.stat().st_size,
            "changed_all_data_first_storage")
    require(metadata["codec"] == "receipt_codec_v2.py" and metadata["codec_sha256"] == sha((HERE / metadata["codec"]).read_bytes()) and
            metadata["base_codec_sha256"] == sha((HERE / "receipt_codec.py").read_bytes()), "changed_all_data_receipt_codec")
    require(original.get("logical_sha256", original.get("logical_json_sha256")) == expected and
            original["logical_bytes"] == metadata["logical_bytes"] and
            original.get("stored_sha256", original.get("gzip_sha256")) == metadata["original_gzip_sha256"],
            "changed_all_data_original_metadata")
    bindings = [frozen(path), frozen(sidecar), frozen(original_path)]
    raw = codec.decompress(path.read_bytes())
    require(len(raw) == metadata["logical_bytes"] and sha(raw) == expected, "all_data_first_roundtrip_changed")
    value = json.loads(raw)
    del raw
    require(value["version"] == SCIENCE_VERSION and value["statistical_role"] == ROLE and
            value["source_stage_sha256"] == original["source_stage_sha256"], "wrong_all_data_first_role")
    return value, {"logical_sha256": expected, "source_stage_sha256": value["source_stage_sha256"],
                   "storage_bindings": bindings, "original_JSON_bytes_preserved": True}


def check_primary_tree(receipt, report):
    ci = main_science.all_ci_view(report)
    domain = primary.training_domain(ci)
    same(receipt["all_ci"], ci, "primary_changed_twelve_original_CI_or_single_intersections")
    cover = receipt["cover"]
    same(cover["initial_box"], domain, "primary_changed_all_data_initial_box")
    spec = main_science.configuration()["all_spec"]
    base_spec = primary.context()["spec"]
    require(cover["split_cap"] == spec["primary_split_cap"] == 16384 and cover["axes"] == list(primary.AXES),
            "changed_all_data_primary_cover_contract")
    nodes, splits, leaves, units = primary_structure(cover)
    for name, d, background in zip(primary.NAMES[:4], domain[:4], map(F, base_spec["background_per_pulse"] * 2)):
        monotone_inverse_cover(primary.pack(d), primary.pack(ci[name]), background)
    digest, counts, chs = hashlib.sha256(), Counter(), []
    for number, (path, node) in enumerate(nodes.items()):
        unit = units[path]
        value = main_science.evaluate(primary.source_box(unit, domain), ci)
        require(node["status"] == value["status"] and node["reason"] == value.get("reason"), "primary_all_data_node_replay_changed")
        if path in splits:
            require(value["status"] != "excluded" and splits[path]["axis"] == primary.split_axis(unit), "unlawful_all_data_primary_split")
        else:
            leaf = leaves[path]
            if leaf["classification"] == "excluded":
                require(value["status"] == "excluded", "unsupported_all_data_primary_exclusion")
                same(leaf["proof"], value, "changed_all_data_primary_exclusion_proof")
                counts["excluded"] += 1
            else:
                require(value["status"] != "excluded", "unlawful_all_data_primary_terminal")
                same(leaf["qualified_outer"], value, "changed_all_data_primary_paired_outer")
                axis = primary.split_axis(unit)
                stop = unit[axis][1] - unit[axis][0] <= F(base_spec["normalized_width_stop"]) or len(path) // 2 >= base_spec["max_depth"]
                require((leaf["stop"] == "resource_cap" and len(splits) == cover["split_cap"]) or
                        (leaf["stop"] == "width_or_depth" and stop), "unsupported_all_data_primary_stop")
                counts["retained"] += 1
                counts["unresolved"] += value["status"] != "retained"
                if value["status"] == "retained":
                    require(len(value["slabs"]) == 4 and value["all_joint_slabs_share_one_k"] is True and
                            value["no_signaling_exact"] is True and
                            value["paired"]["bound_method"] == "directed_degree5_Bernstein_on_the_same_k_interval",
                            "missing_all_data_shared_phase_or_Bernstein_contrast")
                    chs.append(value["paired"]["CH_N5"])
        digest.update(object_sha({"path": path, "value": primary.pack(value)}).encode())
        if number % 4096 == 0:
            print(json.dumps({"all_data_primary_nodes_checked": number, "total": len(nodes)}), flush=True)
    ch = primary.hull(chs) if chs else None
    strict = bool(ch is not None and ch.lo > 0 and counts["unresolved"] == 0)
    same(receipt["whole_fibre_CH"], {"qualified_outer_hull": ch, "unresolved_retained_leaves": counts["unresolved"],
          "strictly_positive_certified": strict}, "unsupported_primary_whole_fibre_CH_claim")
    require(cover["cap_reached"] is (len(splits) >= cover["split_cap"]), "false_all_data_primary_cap_flag")
    return {"node_count": len(nodes), "split_count": len(splits), "terminal_count": len(leaves), **dict(counts),
            "all_node_decisions_and_terminal_outers_recomputed": True, "closed_partition_volume": "1",
            "checked_node_digest": digest.hexdigest(), "all_cap_and_boundary_preserved": True,
            "whole_fibre_CH": primary.pack(ch), "uniform_CH_strictly_positive": strict}, ci, domain


def independent_partition(stage):
    originals = {n["id"]: n for n in stage["cover_tree"]}
    require(len(originals) == len(stage["cover_tree"]) and 0 in originals, "duplicate_or_missing_all_data_cover_node")
    nodes = {}
    for index, raw in originals.items():
        node = dict(raw)
        for field in ("input_box", "contracted_box"):
            node[field] = None if raw[field] is None else list(map(ind.unpack, raw[field]))
        nodes[index] = node
    root = list(map(ind.unpack, stage["initial_source_box"]))
    require(nodes[0]["parent"] is None and nodes[0]["depth"] == 0 and nodes[0]["input_box"] == root, "changed_all_data_cover_root")
    pending, seen, retained = [0], set(), set()
    while pending:
        index = pending.pop()
        require(index not in seen and index in nodes, "repeated_or_missing_all_data_child")
        seen.add(index)
        node = nodes[index]
        require(node["status"] in ("split", "excluded", "retained_boundary"), "unknown_all_data_cover_status")
        if node["contracted_box"] is not None:
            require(len(node["contracted_box"]) == 5 and all(new.contained(old) for new, old in
                    zip(node["contracted_box"], node["input_box"])), "all_data_contractor_enlargement")
        if node["status"] == "split":
            require(len(node["children"]) == 2 and len(set(node["children"])) == 2 and
                    all(child in nodes for child in node["children"]), "invalid_all_data_cover_children")
            left, right = [nodes[child] for child in node["children"]]
            axis = ind.AXES.index(node["split_axis"])
            before = node["contracted_box"]
            require(before is not None and left["parent"] == right["parent"] == index and
                    left["depth"] == right["depth"] == node["depth"] + 1, "incorrect_all_data_parent_or_depth")
            for j in range(5):
                if j == axis:
                    require(left["input_box"][j].lo == before[j].lo and right["input_box"][j].hi == before[j].hi and
                            left["input_box"][j].hi == right["input_box"][j].lo and
                            left["input_box"][j].width > 0 and right["input_box"][j].width > 0,
                            "all_data_cover_split_gap_or_overlap")
                else:
                    require(left["input_box"][j] == right["input_box"][j] == before[j], "changed_all_data_nonsplit_axis")
            pending.extend(node["children"])
        elif node["status"] == "retained_boundary":
            retained.add(index)
    require(seen == set(nodes), "unreachable_all_data_cover_node")
    regions = {r["node_id"]: r for r in stage["paired_regions"]}
    require(len(regions) == len(stage["paired_regions"]) and set(regions) == retained,
            "missing_or_duplicate_all_data_terminal_projection")
    return originals, nodes, regions


def check_independent_tree(receipt, original, selected, provenance, config):
    stage = receipt["source_stage"]
    const = ind.constants(config)
    means = independent.all_means(original, selected, config)
    initial, evidence = ind.initial_box(means, const)
    constraints = ind.linear_constraints(means, const)
    for key, value in (("original_twelve_CI", original), ("single_CI_intersections", provenance),
                       ("four_single_intersection_view", selected), ("training_means", means),
                       ("initial_source_box", initial), ("initial_box_evidence", evidence),
                       ("linear_single_constraints", constraints)):
        same(stage[key], value, "changed_all_data_independent_" + key)
    for field, background in (("alpha", const["background"][0]), ("beta", const["background"][1])):
        for i, axis in enumerate(("A0", "A1") if field == "alpha" else ("B0", "B1")):
            monotone_inverse_cover(ind.serial(means[field][i]), selected[axis], background)
    originals, nodes, regions = independent_partition(stage)
    digest, counts, chs = hashlib.sha256(), Counter(), []
    for number, (index, node) in enumerate(nodes.items()):
        old = originals[index]
        contracted, certificate = audited_contract(node["input_box"], constraints)
        same(node["contracted_box"], contracted, "unsound_all_data_independent_contraction")
        same(old["contraction"], certificate, "changed_all_data_independent_contraction_trace")
        status, exclusion = old["status"], None
        if contracted is None:
            exclusion = certificate
        else:
            pop = ind.population(contracted)
            if pop is None:
                exclusion = {"reason": "strict_PSD_population_violation"}
            else:
                try:
                    common, slabs = independent.phase_slabs_all(contracted, pop, const, means, config)
                except (ValueError, ArithmeticError) as error:
                    common = ind.I.raw(-pop["T2"].sqrt().hi, pop["T2"].sqrt().hi)
                    require(old.get("phase_unresolved") == str(error), "changed_all_data_independent_unresolved_branch")
                else:
                    same(old.get("phase_slabs"), slabs, "changed_all_data_independent_phase_slabs")
                    require("phase_unresolved" not in old, "false_all_data_unresolved_flag")
                    if common is None:
                        exclusion = {"reason": "strict_all_data_joint_or_shared_phase_violation"}
                if exclusion is None:
                    same(old["common_k"], common, "different_all_data_phase_in_node")
                    relative = [F(value.width, base.width) for value, base in zip(contracted, initial)]
                    axis = max(range(5), key=lambda j: (relative[j], -j))
                    if status == "split":
                        require(old["split_axis"] == ind.AXES[axis] and
                                F(old["split_at"]) == F((contracted[axis].lo + contracted[axis].hi) // 2, ind.SCALE) and
                                relative[axis] > F(config["normalized_width_stop"]) and old["depth"] < config["max_depth"],
                                "changed_all_data_independent_split_rule")
                    if status == "retained_boundary":
                        region = regions[index]
                        same(region["source_box"], contracted, "changed_all_data_paired_source")
                        same(region["common_k"], common, "changed_all_data_paired_common_phase")
                        same(region["T2"], pop["T2"], "changed_all_data_physical_phase")
                        try:
                            projection = independent.paired_readout_all(contracted, common, pop, const, means, original)
                        except (ValueError, ArithmeticError) as error:
                            projection = independent.unresolved_projection(original, str(error))
                        same(region["projection"], projection, "changed_all_data_independent_paired_projection")
                        require(region["reason"] == old["terminal_reason"] and
                                F(old["maximum_normalized_width"]) == relative[axis] and
                                ((old["terminal_reason"] == "normalized_width_reached" and relative[axis] <= F(config["normalized_width_stop"])) or
                                 (old["terminal_reason"] == "resource_split_cap_preserved" and stage["coverage"]["split_count"] == config["independent_split_cap"]) or
                                 (old["terminal_reason"] == "depth_cap_preserved" and old["depth"] >= config["max_depth"])),
                                "unsupported_all_data_terminal_stop")
                        chs.append(projection["CH_N5"])
        if status == "excluded":
            require(exclusion is not None, "unsupported_all_data_independent_exclusion")
            same(old["exclusion"], exclusion, "changed_all_data_independent_exclusion_proof")
        else:
            require(exclusion is None, "unsupported_all_data_independent_retained_branch")
        counts[status] += 1
        digest.update(object_sha({"id": index, "contraction": ind.serial(certificate), "exclusion": ind.serial(exclusion)}).encode())
        if number % 4096 == 0:
            print(json.dumps({"all_data_independent_nodes_checked": number, "total": len(nodes)}), flush=True)
    coverage = stage["coverage"]
    require(coverage["node_count"] == len(nodes) and coverage["split_count"] == counts["split"] and
            coverage["terminal_leaf_count"] == counts["excluded"] + counts["retained_boundary"] and
            coverage["excluded_leaf_count"] == counts["excluded"] and coverage["retained_leaf_count"] == len(regions) and
            counts["split"] <= config["independent_split_cap"] and coverage["base_dimensions"] == 5 and
            coverage["phase_dimensions_enumerated"] == 0 and coverage["complete_tree_verified"] is True and
            coverage["all_boundary_and_cap_leaves_preserved"] is True and coverage["all_four_joint_constraints_consumed"] is True,
            "incorrect_all_data_independent_coverage_summary")
    summary = ind.projection_summary([{ "projection": restore_ind(r["projection"])} for r in stage["paired_regions"]])
    same(stage["projection_summary"], summary, "changed_all_data_independent_projection_hull")
    positive, negative = bool(chs) and all(ch.lo > 0 for ch in chs), bool(chs) and all(ch.hi < 0 for ch in chs)
    require(stage["uniform_CH_N5_strictly_positive"] is positive and stage["uniform_CH_N5_strictly_negative"] is negative,
            "unsupported_all_data_independent_CH_sign")
    return {"node_count": len(nodes), "split_count": counts["split"], "terminal_count": counts["excluded"] + counts["retained_boundary"],
            "excluded_count": counts["excluded"], "retained_count": counts["retained_boundary"],
            "all_contractor_shells_and_node_decisions_recomputed": True, "all_paired_regions_recomputed": True,
            "checked_node_digest": digest.hexdigest(), "all_cap_and_boundary_preserved": True,
            "whole_fibre_CH": ind.serial(summary["CH_N5"]), "uniform_CH_strictly_positive": positive,
            "uniform_CH_strictly_negative": negative}, means
def qualified_born(born, original):
    require(born["cutoff"] == 6 and born["vacuum_clicked_Born_exactly_zero"] is True and
            born["normalized_occupation_amplitudes"] is True and born["finite_prefix_renormalized"] is False and
            born["phase_mixture_before_window"] is True and born["tail_is_original_numberMass"] is True,
            "wrong_all_data_positive_Born_source_law")
    require(len(born["cells"]) == 4, "missing_all_data_positive_Born_cell")
    for field, row in ALL_FIELDS:
        name = {"sA_cell": "sA", "sB_cell": "sB", "j": "j"}[field]
        require(inside(born["cells"][row][name], original[field + "[" + str(row) + "]"]),
                "actual_positive_Born_not_in_original_exact_CI")
    for cell in born["cells"]:
        require(len(cell["outcomes"]) == 4, "missing_all_data_outcome")
        total_lower = total_upper = F(0)
        for outcome in cell["outcomes"]:
            lo, hi = bounds(outcome)
            require(0 <= lo <= hi <= 1, "actual_positive_Born_outcome_not_probability")
            total_lower += lo
            total_upper += hi
        require(total_lower <= 1 <= total_upper, "actual_positive_Born_outcomes_not_normalized")
    return True


def source_summary(source):
    return ind.serial({"etaA": source["etaA"], "etaB": source["etaB"],
        "nH": source["h"] / source["e"], "nV": source["v"] / source["e"], "lambda": source["lambda"],
        "common_k": source["common_k"], "R": source["R"]})


def check_members(receipt, kind, original, selected, report, config):
    const = ind.constants(config)
    means = independent.all_means(original, selected, config)
    ci = main_science.all_ci_view(report)
    domain = primary.training_domain(ci)
    values = receipt["members"] if kind == "primary" else receipt["source_stage"]["members"]
    require(len(values) == config["member_limit"] == 64, "incomplete_all_data_native_member_set")
    fraction_set = set(map(F, config["witness_axis_fractions"]))
    I = primary.context()["I"]
    digest, witnesses, positive, negative = hashlib.sha256(), [], 0, 0
    for number, old in enumerate(values):
        recipe = old["recipe"]
        if kind == "primary":
            fs, native = list(map(F, recipe["ci_fractions"])), list(map(as_primary, recipe["inverse_single_means"]))
            require(len(fs) == len(native) == 4 and set(fs).issubset(fraction_set), "changed_all_data_primary_member_recipe")
            for point, weight, source_interval in zip(native, fs, domain):
                same(point, I.point(source_interval.lo + weight * (source_interval.hi - source_interval.lo)),
                     "primary_all_data_member_not_native_CI_coordinate")
            loss, K = as_primary(recipe["loss"]), as_primary(recipe["phase_amplitude"])
            require(loss.lo == loss.hi and K.lo == K.hi and 0 < loss.lo <= 1 and
                    (loss.lo * config["witness_loss_denominator"]).denominator == 1, "illegal_all_data_primary_loss_or_phase")
            shape = primary.covariance(native + [loss])
            require(shape is not None and (shape["m"].square() - shape["R2"]).lo >= 0 and loss.hi <= shape["r"].lo,
                    "all_data_primary_member_not_physical")
            geometry = primary.coefficients(shape)
            require(geometry is not None, "all_data_primary_member_geometry_undefined")
            gaussian = [primary.window_readout(cell, K) for cell in geometry]
            same(old["cells"], gaussian, "foreign_all_data_primary_readout_not_native")
            same(old["paired"], main_science.paired_contrasts(geometry, gaussian, K), "foreign_all_data_primary_paired_readout")
            ctx = primary.context()
            C, T = ctx["gauss"].square_root(shape["R2"]), ctx["gauss"].square_root(shape["T2"])
            coherence = K / T if T.lo > 0 else I.point(0)
            cr = ctx["gauss"].square_root((1 + shape["z"] / C) / 2)
            same(old["source"], {"nH": (shape["m"] + C) / loss, "nV": (shape["m"] - C) / loss,
                 "etaA": loss, "etaB": loss / shape["r"], "cosR": cr, "sinR": (shape["x"] / C) / (2 * cr),
                 "lambda": (1 - coherence) / 2, "pure_mode_phase_readout_equivalence": T.hi == 0},
                 "foreign_all_data_primary_source_not_native")
            raw = [1 - ((1 - bg) / (1 + point.lo)) ** 5 for point, bg in zip(native, const["background"] * 2)]
            native_shape, reconstruction = ind.member_shape(raw, config, const)
            actual_source = ind.physical_source(native_shape + [ind.I(loss.lo)], ind.I(K.lo))
            born = ind.serial(ind.fock_readout(actual_source, const, 6))
            stored_actual = old["actual_positive_Fock"]
            same(stored_actual["recipe_conversion"], {"inverse_single_means": native, "exact_single_probability_coordinates": raw,
                 "rational_loss": loss.lo, "rational_common_k": K.lo}, "foreign_primary_Born_recipe_conversion")
            same(stored_actual["reconstruction"], reconstruction, "foreign_primary_Born_reconstruction")
            same(stored_actual["source"], actual_source, "foreign_primary_actual_Born_source")
            same(stored_actual["readout"], born, "foreign_primary_actual_Born_readout")
            require(stored_actual["all_twelve_original_CI_contained"] is True and old["retrospective_all_data_selection"] is True,
                    "changed_all_data_primary_member_role")
            gaussian = primary.pack(gaussian)
        else:
            require(recipe["coordinate_space"] == "original_single_probability_CI_intersections" and
                    old["id"] == number and old["statistical_role"] == ROLE and
                    old["old_source_or_old_member_used_as_generation_seed"] is False, "changed_independent_all_data_member_role")
            fs = list(map(F, recipe["axis_fractions"]))
            raw = list(map(F, recipe["single_probability_coordinates"]))
            require(len(fs) == len(raw) == 4 and set(fs).issubset(fraction_set), "changed_independent_all_data_member_recipe")
            for point, weight, axis in zip(raw, fs, ("A0", "B0", "A1", "B1")):
                lo, hi = bounds(selected[axis])
                require(point == lo + weight * (hi - lo), "independent_all_data_member_not_native_CI_coordinate")
            loss, k = F(recipe["loss"]), F(recipe["rational_common_k"])
            require(0 < loss <= 1 and (loss * config["witness_loss_denominator"]).denominator == 1,
                    "illegal_independent_all_data_loss")
            shape, reconstruction = ind.member_shape(raw, config, const)
            rebuilt = independent.legal_member(original, means, raw, fs, shape, loss, recipe["phase_recipe"], k, const, config)
            rebuilt.update(id=number, single_reconstruction=reconstruction)
            same(old, rebuilt, "foreign_independent_all_data_member_not_native")
            actual_source = rebuilt["source"]
            born = ind.serial(rebuilt["actual_positive_Fock_readout"])
            native = [primary.inverse_single(I.point(point), bg) for point, bg in zip(raw, const["background"] * 2)]
            primary_shape = primary.covariance(native + [I.point(loss)])
            require(primary_shape is not None, "cross_primary_all_data_member_not_physical")
            geometry = primary.coefficients(primary_shape)
            require(geometry is not None, "cross_primary_all_data_member_geometry_undefined")
            gaussian = primary.pack([primary.window_readout(cell, I.point(k)) for cell in geometry])
        require(old["all_twelve_original_CI_contained"] is True, "changed_all_data_member_qualification")
        qualified_born(born, original)
        cross_cells(gaussian, born["cells"], F(config["comparison_tolerance"]))
        for first, second, field in LOCAL_PAIRS:
            require(intersects(gaussian[first][field], gaussian[second][field]) and
                    intersects(born["cells"][first][field], born["cells"][second][field]), "all_data_no_signaling_cross_failed")
        cells = [restore_ind(cell) for cell in born["cells"]]
        CH = cells[0]["j"] + cells[1]["j"] + cells[2]["j"] - cells[3]["j"] - cells[0]["sA"] - cells[0]["sB"]
        positive += CH.lo > 0
        negative += CH.hi < 0
        witnesses.append({"implementation": kind, "member": number, "recipe": recipe,
                          "source": source_summary(actual_source), "all_twelve_original_exact_CI_verified": True,
                          "actual_positive_Fock_CH_N5": ind.serial(CH)})
        digest.update(object_sha({"member": number, "recipe": recipe, "Born": born}).encode())
        if (number + 1) % 16 == 0:
            print(json.dumps({kind + "_all_data_members_checked": number + 1}), flush=True)
    return {"members_checked": len(values), "all_native_recipes_reconstructed": True,
            "all_actual_positive_Fock_readouts_recomputed": True, "all_twelve_original_exact_CI_verified": True,
            "all_12_probabilities_and_16_outcomes_crossed": True, "physical_source_bounds_verified": True,
            "shared_phase_no_signaling_crossed": True, "foreign_source_fields_used_as_forward_inputs": False,
            "positive_CH_member_count": positive, "negative_CH_member_count": negative,
            "checked_member_digest": digest.hexdigest()}, witnesses


def source_ambiguity(witnesses):
    for number, first in enumerate(witnesses):
        for second in witnesses[number + 1:]:
            if not intersects(first["source"]["etaA"], second["source"]["etaA"]):
                return {"certified": True, "separating_field": "etaA", "first": first, "second": second,
                        "same_twelve_original_CI_qualified": True, "actual_hardware_identity_assigned": False}
    return {"certified": False, "reason": "no_disjoint_source_coordinate_among_certified_members"}


def verify():
    start = time.monotonic()
    execution = [frozen(HERE / name) for name in
                 ("criterion-all-data-cross.md", "sources-all-data-cross.json", "verify_all_data.py", "test_verify_all_data.py")]
    sources = read_json(HERE / "sources-all-data-cross.json")
    require(sources["version"] == VERSION and sources["statistical_role"] == ROLE and
            sources["first_logical_sha256"] == FIRST_SHA, "wrong_all_data_cross_source_contract")
    check_bindings(sources["inputs"])
    config, _, _ = independent.configuration()
    lean = certificates()
    report_path = HERE.parent.parent / "observable-prediction/public-comparison-po0003.json"
    report, original, selected, provenance = public_domain(report_path.read_text(), config)
    firsts, trees, members, witnesses = {}, {}, {}, []
    value, firsts["primary"] = load_first("primary")
    require(value["schema"] == "p23-all-data-statistical-fiber-primary/v1" and
            object_sha({key: value[key] for key in PRIMARY_STAGE_KEYS}) == value["source_stage_sha256"],
            "changed_primary_all_data_source_stage")
    check_bindings(value["bindings"]["execution_sources"] + value["bindings"]["parent_execution_sources"])
    require(all(value["scope"][key] is False for key in ("source_mapping_identified", "actual_epoch_identified",
            "apparatus_optimum_verified", "controller_advance", "new_full_Born_kernel_claim")) and
            value["scope"]["bell_event_files_read"] == 0 and value["nonempty_fibre_exhibited"] is True and
            value["all_boundary_and_cap_leaves_preserved"] is True, "changed_primary_all_data_scope")
    same(value["source_relations"], {"same_k_all_four_cells": True, "no_signaling_exact": True,
         "same_source_original_twelve_CI": True}, "changed_primary_all_data_source_relations")
    trees["primary"], _, _ = check_primary_tree(value, report)
    members["primary"], native = check_members(value, "primary", original, selected, report, config)
    witnesses.extend(native)
    del value
    gc.collect()
    value, firsts["independent"] = load_first("independent")
    require(value["schema"] == independent.SCHEMA and object_sha(value["source_stage"]) == value["source_stage_sha256"],
            "changed_independent_all_data_source_stage")
    check_bindings([value["executable_freeze"]])
    require(all(value[key] is False for key in ("source_mapping_identified", "actual_epoch_identified",
            "apparatus_optimum_verified", "controller_advance", "new_full_Born_kernel_claim",
            "new_statistical_coverage_kernel_claim", "publication_configuration_identified", "heldout_prediction_claimed")) and
            value["bell_event_files_read"] == 0 and value["retrospective"] is True and
            value["foreign_source_fields_used_as_forward_inputs"] is False and
            value["primary_new_code_or_outputs_read_before_first"] is False and
            value["statistical_independence_claimed"] is False and value["old_uniform_prediction_counterexample_retracted"] is False,
            "changed_independent_all_data_scope")
    require(value["source_stage"]["nonempty_all_data_fiber_certified"] is True and
            value["source_stage"]["all_data_fiber_empty_certified"] is False and
            value["source_stage"]["shared_phase_all_four_rows_certified"] is True, "inconsistent_independent_all_data_fibre_result")
    trees["independent"], _ = check_independent_tree(value, original, selected, provenance, config)
    members["independent"], native = check_members(value, "independent", original, selected, report, config)
    witnesses.extend(native)
    del value
    gc.collect()
    ambiguity = source_ambiguity(witnesses)
    positive = all(tree["uniform_CH_strictly_positive"] for tree in trees.values())
    return {"schema": SCHEMA, "version": VERSION, "status": "certified", "statistical_role": ROLE,
            **{key: True for key in POSITIVE_FIELDS}, **{key: False for key in FALSE_SCOPE},
            "all_data_fibre_empty": False, "all_data_fibre_has_certified_source_ambiguity": ambiguity["certified"],
            "uniform_CH_N5_strictly_positive": positive,
            "uniform_CH_N5_sign": "positive" if positive else "unresolved",
            "crossing_zero_outer_proves_negative_source": False,
            "old_training_uniform_prediction_counterexample_retracted": False,
            "retrospective": True, "bell_event_files_read": 0, "foreign_source_fields_used_as_forward_inputs": False,
            "source_law": config["conditional_source_law"],
            "design_exposure": {"common_N": 177358351, "alpha": config["alpha"], "features_in_global_union": 16,
              "fixed_bets": 40, "runs_covered": 6, "pulse_subsets_covered": 32767,
              "settings_probability_bounds": config["settings_probability_bounds"]},
            "original_twelve_CI": original, "single_CI_intersections": provenance,
            "firsts": firsts, "tree_verification": trees, "member_verification": members,
            "source_ambiguity": ambiguity, "Lean_certificates": lean,
            "source_bindings": sources["inputs"], "execution_bindings": execution,
            "production_eligible_role": "sealed conditional public source-family mathematical evidence",
            "scope_note": "Complete outer coverage and actual all-CI legal sources are certified. Every cap and boundary is retained. Twelve public CIs are retrospective inputs; source/epoch identity and the original nominal optimum retain their prior values.",
            "science_first_access": {"both_scientific_firsts_formed_before_cross_result_access": True,
              "primary_program_frozen_before_execution": True,
              "independent_new_program_or_formula_or_result_used_in_primary_science": False,
              "primary_saw_independent_interface_names_and_storage_metadata_during_execution": True,
              "primary_execution_code_changed_after_interface_access": False,
              "blind_statistical_validation_claimed": False},
            "runtime_seconds": time.monotonic() - start}


def validate_result(receipt):
    require(receipt.get("schema") == SCHEMA and receipt.get("version") == VERSION and receipt.get("status") == "certified" and
            receipt.get("statistical_role") == ROLE, "wrong_all_data_certificate_kind")
    require(all(receipt.get(key) is True for key in POSITIVE_FIELDS) and receipt.get("all_data_fibre_empty") is False,
            "inconsistent_all_data_fibre_certificate_verdict")
    require(all(receipt.get(key) is False for key in FALSE_SCOPE) and receipt.get("retrospective") is True and
            type(receipt.get("bell_event_files_read")) is int and receipt["bell_event_files_read"] == 0 and
            receipt.get("foreign_source_fields_used_as_forward_inputs") is False and
            receipt.get("old_training_uniform_prediction_counterexample_retracted") is False and
            receipt.get("crossing_zero_outer_proves_negative_source") is False, "inflated_all_data_fibre_certificate_scope")
    require(type(receipt.get("uniform_CH_N5_strictly_positive")) is bool and
            receipt.get("uniform_CH_N5_sign") == ("positive" if receipt["uniform_CH_N5_strictly_positive"] else "unresolved"),
            "unsupported_all_data_uniform_CH_claim")
    require(set(receipt["firsts"]) == {"primary", "independent"} and all(
            receipt["firsts"][kind]["logical_sha256"] == FIRST_SHA[kind] for kind in FIRST_SHA), "wrong_all_data_first_identity")
    require("source_overrides" not in receipt and "force_pass" not in receipt, "scientific_all_data_source_override_forbidden")
    return True


def consume(certificate_path=None, disabled=False):
    """Only a byte-identical copy of the fixed frozen certificate may override its location."""
    require(type(disabled) is bool, "disable_must_be_boolean")
    if disabled:
        return {"evidence_valid": False, "production_eligible": False, "readout_certified": False, "reason": "explicit_disable"}
    try:
        canonical = frozen(DEFAULT_RECEIPT)
        path = DEFAULT_RECEIPT if certificate_path is None else Path(certificate_path)
        require(sha(path.read_bytes()) == canonical["sha256"], "unfrozen_or_lookalike_all_data_certificate")
        receipt = read_json(path)
        validate_result(receipt)
        check_bindings(receipt["source_bindings"] + receipt["execution_bindings"])
        for first in receipt["firsts"].values():
            check_bindings(first["storage_bindings"])
        for certificate in receipt["Lean_certificates"].values():
            check_bindings([certificate["binding"]])
        return {**{key: True for key in POSITIVE_FIELDS}, **{key: False for key in FALSE_SCOPE},
                "retrospective": True, "statistical_role": ROLE, "bell_event_files_read": 0,
                "all_data_fibre_has_certified_source_ambiguity": receipt["all_data_fibre_has_certified_source_ambiguity"],
                "uniform_CH_N5_strictly_positive": receipt["uniform_CH_N5_strictly_positive"],
                "uniform_CH_N5_sign": receipt["uniform_CH_N5_sign"],
                "old_training_uniform_prediction_counterexample_retracted": False,
                "production_eligible_role": receipt["production_eligible_role"], "certificate": canonical,
                "reason": "certified_complete_retrospective_public_CI_fibre_and_same_source_readouts"}
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
    require(args.output is not None and args.certificate is None and not args.disabled, "fresh_all_data_verification_requires_output")
    require(not args.output.exists(), "protected_existing_all_data_verification")
    result = verify()
    validate_result(result)
    args.output.write_text(json.dumps(result, sort_keys=True, indent=2, allow_nan=False) + "\n")
    print(json.dumps({"output": str(args.output), "status": result["status"],
         "full_all_data_fiber_outer_cover_verified": result["full_all_data_fiber_outer_cover_verified"],
         "nonempty_all_data_fiber_verified": result["nonempty_all_data_fiber_verified"],
         "source_ambiguity": result["source_ambiguity"]["certified"], "uniform_CH_N5_sign": result["uniform_CH_N5_sign"],
         "runtime_seconds": result["runtime_seconds"]}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
