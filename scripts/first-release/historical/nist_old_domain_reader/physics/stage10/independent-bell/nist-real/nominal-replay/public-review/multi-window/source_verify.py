#!/usr/bin/env python3
"""Check frozen full-source witnesses and trees without restarting their search."""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
import gzip
import hashlib
import heapq
import importlib.util
import json
import lzma
from pathlib import Path
import re
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[7]
VERSION = "p23-public-multi-window-source-cross-mwsc0001"
SOURCE_VERSION = "p23-public-multi-window-source-mws0001"
SCHEMA = "p23-public-multi-window-source-cross/v1"
EVIDENCE_SCHEMA = "p23-public-multi-window-source-evidence/v1"
FIELDS = (("sA_cell", "sA"), ("sB_cell", "sB"), ("j", "j"))
POSITIVE = ("source_outer_cover_and_all_72_CI_certified", "complete_original_domain_partition_certified",
            "all_32_positive_Born_members_regenerated", "source_family_has_positive_and_negative_CH_N5_members",
            "common_phase_before_window_certified")
NEGATIVE = ("actual_epoch_identified", "publication_configuration_identified", "nominal_optimum_verified",
            "local_Bell_null_rejected", "public_calibration_sigma_hard_bound", "new_full_Born_kernel_claim",
            "new_statistical_coverage_kernel_claim", "controller_advance", "source_search_rerun")


def require(value, reason):
    if not value:
        raise ValueError(reason)


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def frozen(path, commit=None):
    path = Path(path).resolve()
    require(path.is_relative_to(ROOT), "foreign_source_path")
    relative = path.relative_to(ROOT).as_posix()
    if commit is None:
        commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", relative], cwd=ROOT, text=True).strip()
    require(bool(commit), "uncommitted_source_cross:" + relative)
    blob = subprocess.check_output(["git", "show", commit + ":" + relative], cwd=ROOT)
    require(hashlib.sha256(blob).hexdigest() == digest(path), "unfrozen_source_cross:" + relative)
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=True)
    return {"path": relative, "commit": commit, "sha256": digest(path)}


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()


def equal(actual, expected, reason):
    require(canonical(actual) == canonical(expected), reason)


def bind_check(bindings):
    seen = set()
    for row in bindings:
        path = (ROOT / row["path"]).resolve()
        require(path.is_relative_to(ROOT) and row["path"] not in seen, "invalid_or_duplicate_source_binding")
        seen.add(row["path"])
        require(digest(path) == row["sha256"], "source_cross_bound_input_changed:" + row["path"])


def configuration():
    text = (HERE / "criterion-source-cross.md").read_text()
    blocks = re.findall(r"<!-- MW-SOURCE-CROSS-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- MW-SOURCE-CROSS-FROZEN-END -->", text, re.S)
    require(len(blocks) == 1, "nonunique_source_cross_contract")
    config = json.loads(blocks[0])
    manifest = json.loads((HERE / "sources-source-cross.json").read_text())
    require(config["version"] == manifest["version"] == VERSION and config["source_version"] == SOURCE_VERSION,
            "source_cross_contract_changed")
    require(config["primary_nodes"] == 4097 and config["primary_splits"] == 2048 and
            config["independent_nodes"] == 8193 and config["independent_splits"] == 4096 and
            config["all_CI_count"] == 72 and config["members_per_implementation"] == 16 and
            config["members_per_sign"] == 8 and config["source_pair_cutoff"] == 6 and
            config["pulse_counts"] == [1, 3, 5, 7, 9] and all(config[k] is False for k in NEGATIVE),
            "source_cross_exact_scope_changed")
    bind_check(manifest["inputs"])
    owned = [frozen(HERE / name) for name in ("criterion-source-cross.md", "sources-source-cross.json",
                                             "source_verify.py", "test_source_verify.py")]
    return config, manifest, owned


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def native_routes():
    # The statistics import name is resolved before the primary chart edits sys.path.
    load_module("independent", HERE / "independent.py")
    primary = load_module("mw_source_cross_primary", HERE / "source_primary.py")
    independent = load_module("mw_source_cross_independent", HERE / "source_independent.py")
    primary.configuration()
    independent.configuration()
    return primary, independent


def source_closure(manifest, owned):
    table = {row["path"]: row for row in owned}
    queue = list(manifest["inputs"])
    for module in list(sys.modules.values()):
        filename = getattr(module, "__file__", None)
        if filename:
            path = Path(filename).resolve()
            if path.is_relative_to(ROOT) and path.suffix == ".py":
                queue.append({"path": path.relative_to(ROOT).as_posix(), "sha256": digest(path)})
    while queue:
        row = queue.pop()
        path = (ROOT / row["path"]).resolve()
        require(path.is_relative_to(ROOT) and digest(path) == row["sha256"], "source_closure_binding_changed:" + row["path"])
        if row["path"] in table:
            require(table[row["path"]]["sha256"] == row["sha256"], "conflicting_source_closure_binding")
            continue
        table[row["path"]] = frozen(path)
        # Source manifests own transitive inputs; reports and compressed firsts do not.
        if path.name.startswith("sources") and path.suffix == ".json":
            value = json.loads(path.read_text())
            queue.extend(value.get("inputs", []))
    return [table[key] for key in sorted(table)]


def load_first(kind, override=None):
    names = {"primary": ("source-primary-first.json.xz", "source-primary-storage.json", lzma.decompress),
             "independent": ("source-independent.json.gz", "source-independent-storage.json", gzip.decompress)}
    name, metadata, decompress = names[kind]
    path = Path(override) if override is not None else HERE / name
    storage = json.loads((HERE / metadata).read_text())
    require(digest(path) == storage["stored_sha256"] and path.stat().st_size == storage["stored_bytes"],
            "unbound_or_lookalike_source_first:" + kind)
    raw = decompress(path.read_bytes())
    require(hashlib.sha256(raw).hexdigest() == storage["logical_sha256"] and len(raw) == storage["logical_bytes"],
            "source_first_lossless_identity_changed:" + kind)
    report = json.loads(raw)
    if kind == "independent":
        payload = {k: v for k, v in report.items() if k not in ("source_stage_sha256", "runtime_seconds")}
        require(hashlib.sha256(canonical(payload)).hexdigest() == storage["source_stage_sha256"] == report["source_stage_sha256"],
                "independent_source_stage_changed")
    return report, {"first": frozen(HERE / name), "storage": frozen(HERE / metadata),
                    "logical_sha256": storage["logical_sha256"], "logical_bytes": len(raw)}


def scope_check(primary, independent):
    require(primary["version"] == independent["version"] == SOURCE_VERSION and
            primary["schema"] == "p23-public-multi-window-source/v1" and
            independent["schema"] == "p23-public-multi-window-source-independent/v1", "wrong_source_first_version")
    require(primary["implementation"] == "primary" and primary["all_72_CI_consumed"] is True and
            primary["old_cut_and_full_run_not_independent"] is True and independent["all_72_original_CI_consumed"] is True,
            "source_input_role_changed")
    require(primary["bell_event_files_read"] == independent["bell_event_files_read"] == 0 and
            primary["publication_configuration_identified"] is independent["publication_configuration_identified"] is False,
            "source_publication_scope_changed")
    for field in ("actual_epoch_identified", "calibration_sigma_inserted_as_CI", "nominal_optimum_contract_replaced",
                  "new_full_Born_kernel_claim", "new_statistical_coverage_kernel_claim", "controller_advance",
                  "primary_new_source_code_or_outputs_read_before_first", "foreign_source_fields_used_as_forward_inputs",
                  "old_source_or_member_used_as_generation_seed"):
        require(independent[field] is False, "independent_source_role_changed:" + field)


def primary_shape(report, cfg):
    tree = report["cover"]
    nodes, splits, leaves = tree["nodes"], tree["splits"], tree["leaves"]
    require(len(nodes) == cfg["primary_nodes"] == 2 * len(splits) + 1 and
            len(splits) == cfg["primary_splits"] and len(leaves) == len(splits) + 1,
            "primary_source_wrong_node_split_or_leaf_count")
    for rows, label in ((nodes, "nodes"), (splits, "splits"), (leaves, "leaves")):
        require(len({row["path"] for row in rows}) == len(rows), "primary_duplicate_" + label)
    require(tree["all_leaves_preserved"] is True and len(report["members"]) == cfg["members_per_implementation"],
            "primary_boundary_or_member_count_changed")


def independent_shape(report, cfg):
    tree = report["cover"]
    nodes = tree["cover_tree"]
    counts = Counter(node["status"] for node in nodes)
    require(len(nodes) == tree["node_count"] == cfg["independent_nodes"] and
            counts["split"] == tree["split_count"] == cfg["independent_splits"] and
            len(nodes) == 2 * counts["split"] + 1 and counts["excluded"] + counts["retained_boundary"] == counts["split"] + 1,
            "independent_source_wrong_node_split_or_leaf_count")
    require(len({node["id"] for node in nodes}) == len(nodes) and
            tree["excluded_count"] == counts["excluded"] and tree["retained_count"] == counts["retained_boundary"] and
            len(tree["paired_regions"]) == counts["retained_boundary"] and
            len({row["node_id"] for row in tree["paired_regions"]}) == len(tree["paired_regions"]),
            "independent_source_missing_leaf_projection_or_wrong_count")
    require(tree["all_cap_and_boundary_leaves_preserved"] is tree["complete_tree_verified"] is tree["all_original_72_CI_consumed"] is True and
            len(report["members"]) == cfg["members_per_implementation"], "independent_source_boundary_or_member_count_changed")


def primary_tree(report, native, groups, domain, cfg):
    primary_shape(report, cfg)
    tree = report["cover"]
    equal(tree["initial_box"], native.kernel.pack(domain), "primary_initial_cover_domain_changed")
    splits = {row["path"]: row for row in tree["splits"]}
    leaves = {row["path"]: row for row in tree["leaves"]}
    queue = [(-5, 0, "", tuple((F(0), F(1)) for _ in range(5)), 0)]
    sequence, visited, split_count = 0, set(), 0
    reasons, classifications = Counter(), Counter()
    source_cfg = native.configuration()["config"]
    for saved in tree["nodes"]:
        require(bool(queue), "primary_tree_extra_node")
        _, _, path, unit, depth = heapq.heappop(queue)
        require(saved["path"] == path and path not in visited, "primary_tree_missing_unreachable_or_reordered_node")
        visited.add(path)
        value = native.evaluate(native.kernel.source_box(unit, domain), groups)
        equal(saved, {"path": path, "status": value["status"]}, "primary_node_native_classification_changed:" + path)
        classifications[value["status"]] += 1
        if value["status"] == "excluded":
            require(path not in splits and path in leaves, "primary_excluded_node_has_children_or_missing_leaf")
            expected = {"path": path, "classification": "excluded", "proof": value}
            reasons[value["reason"]] += 1
        else:
            axis = native.kernel.split_axis(unit)
            stopped = split_count >= source_cfg["primary_split_cap"] or depth >= source_cfg["max_depth"] or unit[axis][1] - unit[axis][0] <= F(source_cfg["normalized_width_stop"])
            if not stopped:
                require(path in splits and path not in leaves, "primary_nonterminal_missing_split")
                lo, hi = unit[axis]; mid = (lo + hi) / 2
                equal(splits[path], {"path": path, "axis": axis, "midpoint": str(mid)}, "primary_split_not_native_complete_partition")
                require(tree["splits"][split_count]["path"] == path, "primary_split_order_changed")
                split_count += 1
                for label, ends in (("L", (lo, mid)), ("R", (mid, hi))):
                    child = list(unit); child[axis] = ends; child = tuple(child); sequence += 1
                    heapq.heappush(queue, (-sum(b-a for a, b in child), sequence, path + str(axis) + label, child, depth+1))
                continue
            require(path not in splits and path in leaves, "primary_stopped_boundary_not_preserved")
            expected = {"path": path, "classification": "retained_boundary", "unit_box": unit, "qualified_outer": value,
                        "stop": "resource_cap" if split_count >= source_cfg["primary_split_cap"] else "width_or_depth"}
            reasons[expected["stop"]] += 1
        equal(leaves[path], native.kernel.pack(expected), "primary_leaf_full_native_proof_or_paired_outer_changed:" + path)
        if len(visited) % 512 == 0:
            print(json.dumps({"source_cross_primary_nodes_checked": len(visited)}), flush=True)
    require(not queue and visited == set(splits) | set(leaves) and split_count == cfg["primary_splits"], "primary_source_tree_incomplete")
    return {"nodes_recomputed": len(visited), "splits_verified": split_count, "leaves_verified": len(leaves),
            "excluded_leaves": sum(row["classification"] == "excluded" for row in leaves.values()),
            "retained_leaves": sum(row["classification"] == "retained_boundary" for row in leaves.values()),
            "native_node_classifications": dict(classifications), "leaf_reasons": dict(reasons),
            "all_native_exclusion_and_retained_payloads_equal": True, "full_root_partition_preserved": True}


def independent_tree(report, native, initial, means, const, endpoints, config, cfg):
    independent_shape(report, cfg)
    g = native.geometry; tree = report["cover"]
    equal(tree["initial_source_box"], g.serial(initial), "independent_initial_cover_domain_changed")
    constraints = g.linear_constraints(means, const)
    equal(tree["linear_single_constraints"], g.serial(constraints), "independent_single_constraints_changed")
    by_id = {row["id"]: row for row in tree["cover_tree"]}
    regions = {row["node_id"]: row for row in tree["paired_regions"]}
    stack = [(0, None, initial, 0)]; seen = set(); next_id, splits = 1, 0
    reasons, statuses = Counter(), Counter(); widths = [v.width for v in initial]
    while stack:
        index, parent, raw, depth = stack.pop()
        require(index in by_id and index not in seen, "independent_source_missing_or_repeated_node")
        seen.add(index)
        box, contraction = g.linear_contract(raw, constraints)
        expected = {"id": index, "parent": parent, "depth": depth, "input_box": raw,
                    "contracted_box": box, "contraction": contraction}
        pop = g.population(box) if box is not None else None
        if box is None:
            expected.update(status="excluded", exclusion=contraction)
        elif pop is None:
            expected.update(status="excluded", exclusion={"reason": "strict_PSD_population_violation"})
        else:
            try:
                common, slabs, _ = native.common_phase(box, pop, const, means, endpoints, config)
                expected["phase_slabs"] = slabs
                if common is None:
                    expected.update(status="excluded", exclusion={"reason": "strict_joint_or_shared_k_violation"})
            except (ValueError, ArithmeticError) as error:
                radius = pop["T2"].sqrt().hi; common = native.I.raw(-radius, radius)
                expected["phase_unresolved"] = str(error)
            if "status" not in expected:
                expected["common_k"] = common
                relative = [F(v.width, width) for v, width in zip(box, widths)]
                axis = max(range(5), key=lambda j: (relative[j], -j))
                mid = (box[axis].lo + box[axis].hi) // 2
                split = relative[axis] > F(config["normalized_width_stop"]) and depth < config["max_depth"] and splits < config["independent_split_cap"] and box[axis].lo < mid < box[axis].hi
                if split:
                    left, right = list(box), list(box)
                    left[axis], right[axis] = native.I.raw(box[axis].lo, mid), native.I.raw(mid, box[axis].hi)
                    children = [next_id, next_id+1]; next_id += 2; splits += 1
                    expected.update(status="split", split_axis=g.AXES[axis], split_at=F(mid, g.SCALE), children=children)
                    stack.extend(((children[1], index, right, depth+1), (children[0], index, left, depth+1)))
                else:
                    expected.update(status="retained_boundary", terminal_reason="resource_cap_or_depth_or_width_preserved", maximum_normalized_width=relative[axis])
                    try:
                        projection = native.paired_readout(box, common, pop, const, means, endpoints)
                    except (ValueError, ArithmeticError) as error:
                        projection = native.unresolved_readout(endpoints, str(error))
                    require(index in regions, "independent_boundary_lost_paired_outer")
                    equal(regions[index], g.serial({"node_id": index, "source_box": box, "common_k": common, "T2": pop["T2"], "projection": projection}),
                          "independent_retained_paired_native_outer_changed:" + str(index))
        status = expected["status"]; statuses[status] += 1
        require((index in regions) == (status == "retained_boundary"), "independent_projection_attached_to_wrong_node")
        if status == "excluded":
            reasons[expected["exclusion"]["reason"]] += 1
        equal(by_id[index], g.serial(expected), "independent_node_full_native_proof_changed:" + str(index))
        if len(seen) % 1024 == 0:
            print(json.dumps({"source_cross_independent_nodes_checked": len(seen)}), flush=True)
    require(seen == set(by_id) and splits == cfg["independent_splits"] and next_id == cfg["independent_nodes"], "independent_source_tree_incomplete")
    return {"nodes_recomputed": len(seen), "splits_verified": splits, "leaves_verified": statuses["excluded"] + statuses["retained_boundary"],
            "excluded_leaves": statuses["excluded"], "retained_leaves": statuses["retained_boundary"], "exclusion_reasons": dict(reasons),
            "all_native_exclusion_and_retained_payloads_equal": True, "full_root_partition_preserved": True}


def native_born_flags(packet):
    require(packet["cutoff"] == 6 and packet["phase_mixture_before_window"] is True and
            packet["finite_prefix_renormalized"] is False and packet["vacuum_clicked_Born_exactly_zero"] is True and
            packet["normalized_occupation_amplitudes"] is True and packet["tail_is_original_numberMass"] is True,
            "wrong_phase_order_normalization_vacuum_or_tail")


def strict_sign(value):
    require(value.lo > 0 or value.hi < 0, "member_CH_N5_not_strict")
    return "positive" if value.lo > 0 else "negative"


def source_legality(source, g):
    require(0 < source["etaA"].lo <= source["etaA"].hi <= g.SCALE and
            0 < source["etaB"].lo <= source["etaB"].hi <= g.SCALE and
            0 <= source["tH"].lo <= source["tH"].hi < g.SCALE and
            0 <= source["tV"].lo <= source["tV"].hi < g.SCALE and
            0 <= source["lambda"].lo <= source["lambda"].hi <= g.SCALE,
            "reconstructed_original_source_not_physical")


def primary_members(report, native, groups, domain, cfg):
    c = native.configuration(); g = native.born; I = c["I"]
    summaries, sources, signs = [], [], Counter()
    for index, member in enumerate(report["members"]):
        recipe = member["recipe"]; fs = list(map(F, recipe["mean_fractions"])); e = F(recipe["loss"])
        require(len(fs) == 4 and all(str(f) in c["config"]["member_mean_fractions"] for f in fs) and
                1 <= e * 64 <= 64 and (e * 64).denominator == 1, "primary_member_recipe_outside_frozen_domain")
        means = [I.point(d.lo + f*(d.hi-d.lo)) for d, f in zip(domain[:4], fs)]
        equal(recipe["means"], native.kernel.pack(means), "primary_member_mean_recipe_changed")
        value = native.evaluate(means + [I.point(e)], groups)
        require(value["status"] == "retained", "primary_member_recipe_has_no_common_phase")
        k = F(recipe["common_k"]); K = value["phase"]
        require(k in {K.lo + F(f)*(K.hi-K.lo) for f in c["config"]["member_phase_fractions"]}, "primary_member_phase_recipe_changed")
        points = [1-((1-bg)/(1+mean.lo))**5 for mean, bg in zip(means, c["background"]*2)]
        shape, reconstruction = g.member_shape(points, c["born_config"], c["born_const"])
        source = g.physical_source(shape + [g.I(e)], g.I(k)); source_legality(source, g)
        equal(member["source"], g.serial(source), "primary_member_source_not_recipe_generated")
        equal(member["reconstruction"], g.serial(reconstruction), "primary_member_reconstruction_changed")
        raw, windows = native.fock_windows(source); native_born_flags(raw)
        equal(member["native_Fock"], g.serial(raw), "primary_member_positive_Born_native_changed")
        equal(member["native_windows"], g.serial(windows), "primary_member_phase_before_window_readout_changed")
        cells = native.kernel.coefficients(value["source"])
        gaussian = {str(n): [native.window(cell, I.point(k), n) for cell in cells] for n in cfg["pulse_counts"]}
        equal(member["Gaussian_windows"], native.kernel.pack(gaussian), "primary_member_same_source_Gaussian_changed")
        checks = [windows[str(group["N"])][row][field].within_exact({"exact_lower": str(group["ci"][name][row].lo), "exact_upper": str(group["ci"][name][row].hi)})
                  for group in groups for row in range(4) for name, field in FIELDS]
        require(len(checks) == 72 and all(checks), "primary_actual_source_not_inside_original_72_CI")
        equal(member["checks"], checks, "primary_member_containment_flags_wrong")
        for group in groups:
            for row in range(4):
                for _, field in FIELDS:
                    a, b = gaussian[str(group["N"])][row][field], windows[str(group["N"])][row][field]
                    require(max(a.lo, F(b.lo, g.SCALE)) <= min(a.hi, F(b.hi, g.SCALE)), "primary_Gaussian_positive_Born_disjoint")
        rows = windows["5"]
        ch = rows[0]["j"] + rows[1]["j"] + rows[2]["j"] - rows[3]["j"] - rows[0]["sA"] - rows[0]["sB"]
        sign = strict_sign(ch); signs[sign] += 1
        equal(member["CH_N5"], g.serial(ch), "primary_member_CH_changed")
        require(member["strict_CH_N5_sign"] == sign and member["all_72_CI_contained"] is True, "primary_member_sign_or_containment_changed")
        summaries.append({"id": index, "sign": sign, "CH_N5": g.serial(ch), "recipe_sha256": hashlib.sha256(canonical(recipe)).hexdigest(), "original_CI_containments": 72})
        sources.append((source, rows, c["born_const"], g))
    require(signs == Counter(positive=cfg["members_per_sign"], negative=cfg["members_per_sign"]), "primary_not_eight_members_each_sign")
    return {"members_regenerated": len(summaries), "sign_counts": dict(signs), "original_CI_containments": 72*len(summaries), "members": summaries}, sources


def independent_members(report, native, native_means, means, const, endpoints, config, cfg):
    g = native.geometry; summaries, sources, signs = [], [], Counter()
    for index, member in enumerate(report["members"]):
        recipe = member["recipe"]; fs = list(map(F, recipe["mean_fractions"])); e = F(recipe["loss"])
        require(member["id"] == index and len(fs) == 4 and all(str(f) in config["member_mean_fractions"] for f in fs) and
                1 <= e*64 <= 64 and (e*64).denominator == 1 and recipe["phase_fraction"] in config["member_phase_fractions"],
                "independent_member_recipe_outside_frozen_domain")
        points = [F(value.lo, g.SCALE) + f*F(value.width, g.SCALE) for value, f in zip(native_means, fs)]
        equal(recipe["native_mean_points"], list(map(str, points)), "independent_member_mean_recipe_changed")
        box = native.shape_from_means(points, const) + [native.I(e)]
        equal(member["source_box"], g.serial(box), "independent_member_chart_not_recipe_generated")
        pop = g.population(box); require(pop is not None, "independent_member_non_PSD")
        common, _, _ = native.common_phase(box, pop, const, means, endpoints, config)
        require(common is not None, "independent_member_no_common_phase")
        k = F(common.lo, g.SCALE) + F(recipe["phase_fraction"])*F(common.width, g.SCALE)
        require(k == F(recipe["common_k"]), "independent_member_phase_recipe_changed")
        gaussian = native.paired_readout(box, native.I(k), pop, const, means, endpoints)
        source = g.physical_source(box, native.I(k)); source_legality(source, g)
        equal(member["source"], g.serial(source), "independent_member_source_not_recipe_generated")
        equal(member["paired_Gaussian"], g.serial(gaussian), "independent_member_same_source_Gaussian_changed")
        actual = native.actual_windows(source, const, endpoints, config)
        native_born_flags(actual["same_pulse_positive_Born"])
        equal(member["actual_positive_Born"], g.serial(actual), "independent_member_positive_Born_or_phase_window_changed")
        for left, right in zip(gaussian["endpoints"], actual["endpoints"]):
            for row in range(4):
                for _, field in FIELDS:
                    require(left["cells"][row][field].intersect(right["cells"][row][field]) is not None, "independent_Gaussian_positive_Born_disjoint")
        n5 = next(row for row in actual["endpoints"] if row["endpoint"] == "full_N5")
        sign = strict_sign(n5["CH"]); signs[sign] += 1
        require(member["CH_N5_sign"] == sign and member["all_72_original_CI_contained"] is True and
                member["old_source_or_member_used_as_generation_seed"] is False, "independent_member_source_role_or_sign_changed")
        summaries.append({"id": index, "sign": sign, "CH_N5": g.serial(n5["CH"]), "recipe_sha256": hashlib.sha256(canonical(recipe)).hexdigest(), "original_CI_containments": 72})
        sources.append((source, n5["cells"], const, g))
    require(signs == Counter(positive=cfg["members_per_sign"], negative=cfg["members_per_sign"]), "independent_not_eight_members_each_sign")
    return {"members_regenerated": len(summaries), "sign_counts": dict(signs), "original_CI_containments": 72*len(summaries), "members": summaries}, sources


def phase_order_control(source, lawful_rows, const, g):
    wrong = g.fock_readout(source, const, 6, phase_after_window=True)
    try:
        native_born_flags(wrong)
    except ValueError:
        pass
    else:
        raise ValueError("phase_after_window_negative_control_not_rejected")
    disjoint = []
    for index, (lawful, altered) in enumerate(zip(lawful_rows, wrong["cells"])):
        if lawful["j"].intersect(altered["j"]) is None:
            disjoint.append(index)
    require(bool(disjoint), "phase_after_window_negative_not_arithmetically_distinguished")
    return {"wrong_phase_flag_rejected": True, "native_N5_joint_disjoint_cells": disjoint,
            "CI_containment_alone_is_not_phase_order_evidence": True}


def input_cross(primary_groups, independent_endpoints, cfg):
    require([row["N"] for row in primary_groups] == [row["N"] for row in independent_endpoints] == [1, 3, 5, 7, 9, 5], "source_endpoint_identity_changed")
    max_difference = F(0)
    for left, right in zip(primary_groups, independent_endpoints):
        for name, _ in FIELDS:
            for row in range(4):
                a = left["ci"][name][row]; original = right["original_CI"][name][row]
                lo, hi = F(original["exact_lower"]), F(original["exact_upper"])
                require(max(a.lo, lo) <= min(a.hi, hi), "source_original_CI_implementations_disjoint")
                max_difference = max(max_difference, abs(a.lo-lo), abs(a.hi-hi))
    require(max_difference <= F(cfg["CI_endpoint_comparison_tolerance"]), "source_original_CI_endpoint_difference_exceeded")
    return {"features_compared": 72, "maximum_original_CI_endpoint_difference": str(max_difference),
            "each_native_witness_checked_against_its_own_unexpanded_exact_CI": True,
            "distinct_mean_domains_and_source_recipes_preserved": True}


def reused_certificates():
    stats = json.loads((HERE / "cross-verification.json").read_text())
    require(stats["schema"] == "p23-public-multi-window-cross/v1" and stats["evidence_valid"] is True and
            stats["CI_features"] == 360 and stats["count_bets"] == 14400 and stats["contrast_bets"] == 600 and
            stats["public_complete_counts_and_independent_CI_certified"] is stats["necessary_common_pulse_verdicts_agree"] is True and
            stats["optimum_verified"] is stats["actual_configuration_identified"] is stats["sigma_hard_bounds_used"] is False,
            "reused_statistical_certificate_exact_scope_changed")
    bind_check(stats["bindings"])
    cs_path = HERE.parents[1] / "observable-closure/full-statistical-fiber/covariance-source-certification.json"
    cs = json.loads(cs_path.read_text())
    require(cs["schema"] == "p23-covariance-source-lean-certification/v1" and cs["status"] == "certified" and
            cs["authorized_axioms"] == ["Classical.choice", "Quot.sound", "propext"] and
            cs["kernel_claims"]["all_legal_regular_z_positive_coordinate_tuples_generate_original_RawSource"] is True and
            cs["kernel_claims"]["every_lawful_signed_k_generates_phase_lambda_and_original_Snapshot"] is True and
            cs["kernel_claims"]["same_generated_source_all_original_pulse_cells_shared_phase_and_N5_OR_windows"] is True and
            cs["kernel_claims"]["numeric_tree_or_statistical_confidence_coverage_kernel"] is False and
            cs["kernel_claims"]["new_infinite_Born_or_detector_determinant_kernel"] is False,
            "reused_covariance_source_kernel_exact_scope_changed")
    reader = load_module("mw_source_cross_covariance_reader", cs_path.with_name("covariance_source_certify.py"))
    evidence = reader.consume()
    require(evidence["evidence_valid"] is True and evidence["source_realization_kernel_certified"] is True,
            "reused_covariance_source_kernel_live_binding_failed:" + str(evidence.get("reason", "")))
    return {"statistics": frozen(HERE / "cross-verification.json"), "statistics_counts": {key: stats[key] for key in ("CI_features", "count_bets", "contrast_bets")},
            "covariance_source_kernel": frozen(cs_path), "covariance_source_kernel_schema": cs["schema"],
            "covariance_source_immutable_kernel_and_semantic_import_bindings_valid": True,
            "neither_certificate_regenerated": True}


def verify_receipts(primary_path=None, independent_path=None):
    started = time.monotonic(); cfg, manifest, owned = configuration()
    primary, independent = native_routes()
    reused = reused_certificates(); bindings = source_closure(manifest, owned)
    a, a_identity = load_first("primary", primary_path)
    b, b_identity = load_first("independent", independent_path)
    scope_check(a, b); primary_shape(a, cfg); independent_shape(b, cfg)
    groups = primary.inputs(); domain = primary.initial_domain(groups)
    equal(a["input_groups"], primary.kernel.pack(groups), "primary_original_72_CI_changed")
    equal(a["domain"], primary.kernel.pack(domain), "primary_full_single_mean_domain_changed")
    config, native_bindings = independent.configuration()
    endpoints = independent.all_CI(config)
    native, means, necessary = independent.pulse_mean_domain(endpoints, config)
    const = independent.geometry.constants(config)
    initial, evidence = independent.geometry.initial_box(means, const)
    equal(b["all_original_endpoint_CI"], independent.geometry.serial(endpoints), "independent_original_72_CI_changed")
    equal(b["four_native_pulse_mean_domain"], independent.geometry.serial(native), "independent_full_single_mean_domain_changed")
    equal(b["shared_pulse_necessary"], necessary, "independent_full_shared_pulse_domain_changed")
    equal(b["initial_domain_evidence"], independent.geometry.serial(evidence), "independent_source_initial_domain_evidence_changed")
    equal(b["bindings"], native_bindings, "independent_frozen_native_binding_changed")
    equal(a["bindings"], primary.configuration()["bindings"], "primary_frozen_native_binding_changed")
    cross = input_cross(groups, endpoints, cfg)
    trees = {"primary": primary_tree(a, primary, groups, domain, cfg),
             "independent": independent_tree(b, independent, initial, means, const, endpoints, config, cfg)}
    am, a_sources = primary_members(a, primary, groups, domain, cfg)
    bm, b_sources = independent_members(b, independent, native, means, const, endpoints, config, cfg)
    controls = {"primary_phase_after_window": phase_order_control(*a_sources[0]),
                "independent_phase_after_window": phase_order_control(*b_sources[0])}
    bind_check(bindings)
    return {"schema": SCHEMA, "version": VERSION, "evidence_valid": True, "bindings": bindings,
            "first_identities": {"primary": a_identity, "independent": b_identity}, "reused_certificates": reused,
            "input_cross": cross, "trees": trees, "witnesses": {"primary": am, "independent": bm}, "native_controls": controls,
            **{key: True for key in POSITIVE}, **{key: False for key in NEGATIVE}, "bell_event_files_read": 0,
            "source_stationarity_is_named_model_condition": True, "retrospective": True,
            "retained_leaves_are_necessary_outer_regions_not_members": True,
            "native_Gamma_Fock_kernel_shared_by_both_routes": True,
            "kernel_inputs_not_optimizer_or_tree_search_reexecuted": True,
            "runtime_seconds": time.monotonic() - started}


def summary_check(report):
    require(report["schema"] == SCHEMA and report["version"] == VERSION and report["evidence_valid"] is True and
            all(report[key] is True for key in POSITIVE) and all(report[key] is False for key in NEGATIVE) and
            report["bell_event_files_read"] == 0 and report["retrospective"] is True and
            report["retained_leaves_are_necessary_outer_regions_not_members"] is True and
            report["native_Gamma_Fock_kernel_shared_by_both_routes"] is True, "source_certificate_exact_scope_changed")
    for kind, nodes, splits in (("primary", 4097, 2048), ("independent", 8193, 4096)):
        tree = report["trees"][kind]; witness = report["witnesses"][kind]
        require(tree["nodes_recomputed"] == nodes and tree["splits_verified"] == splits and
                tree["leaves_verified"] == splits+1 and tree["excluded_leaves"] + tree["retained_leaves"] == splits+1 and
                tree["all_native_exclusion_and_retained_payloads_equal"] is tree["full_root_partition_preserved"] is True and
                witness["members_regenerated"] == 16 and witness["sign_counts"] == {"positive": 8, "negative": 8} and
                witness["original_CI_containments"] == 1152 and len(witness["members"]) == 16,
                "source_certificate_incomplete_tree_or_witness_summary")


def consume(certificate_path=None, disabled=False):
    result = {"schema": EVIDENCE_SCHEMA, "evidence_valid": False, "disabled": disabled,
              **{key: False for key in POSITIVE + NEGATIVE}, "bell_event_files_read": 0}
    if disabled:
        result["reason"] = "explicitly_disabled"; return result
    try:
        canonical_path = HERE / "source-cross-verification.json"
        identity = frozen(canonical_path)
        path = Path(certificate_path) if certificate_path is not None else canonical_path
        require(digest(path) == identity["sha256"], "unbound_or_lookalike_source_cross_certificate")
        report = json.loads(path.read_text()); summary_check(report); bind_check(report["bindings"])
        reused_certificates()
        result.update(evidence_valid=True, reason="certified_full_72CI_shared_source_outer_cover_and_both_CH_signs",
                      certificate=identity, trees=report["trees"], input_cross=report["input_cross"],
                      witnesses={kind: {key: report["witnesses"][kind][key] for key in ("members_regenerated", "sign_counts", "original_CI_containments")} for kind in ("primary", "independent")},
                      **{key: True for key in POSITIVE}, retrospective=True, native_Gamma_Fock_kernel_shared_by_both_routes=True,
                      retained_leaves_are_necessary_outer_regions_not_members=True, no_tree_Fock_statistics_or_search_rerun=True)
    except (ValueError, OSError, KeyError, TypeError, json.JSONDecodeError, subprocess.CalledProcessError) as error:
        result.update(reason=str(error), exception_kind=type(error).__name__)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--certificate", type=Path)
    parser.add_argument("--disabled", action="store_true")
    args = parser.parse_args()
    if args.check_only:
        result = consume(args.certificate, args.disabled); print(json.dumps(result, sort_keys=True))
        return 0 if result["evidence_valid"] or args.disabled else 1
    require(args.output is not None and not args.output.exists(), "new_source_cross_certificate_path_required")
    result = verify_receipts(); summary_check(result)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True, allow_nan=False) + "\n")
    print(json.dumps({"output": str(args.output), "sha256": digest(args.output), "nodes_checked": 12290,
                      "native_members_regenerated": 32, "original_CI_containments": 2304, "runtime_seconds": result["runtime_seconds"]}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
