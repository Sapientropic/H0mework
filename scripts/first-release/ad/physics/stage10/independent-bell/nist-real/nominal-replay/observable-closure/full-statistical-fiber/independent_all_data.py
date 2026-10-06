#!/usr/bin/env python3
"""Retrospective all-CI source polytope and common four-joint phase fiber."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import gzip
import hashlib
import itertools
import json
from pathlib import Path
import re

import independent_fiber as base

HERE = Path(__file__).resolve().parent
FREEZE = "b55cb2459d"
VERSION = "p23-all-data-statistical-fiber-ef0003.1"
SCHEMA = "p23-all-data-statistical-fiber-independent/v1"
ROLE = "retrospective_all_public_CI_intersection"
I = base.I
SCALE = base.SCALE
AXES = base.AXES
INTERSECTIONS = {"A0":[0, 1], "A1":[2, 3], "B0":[0, 2], "B1":[1, 3]}
ALL_FIELDS = tuple((field, row) for row in range(4) for field in ("sA_cell", "sB_cell", "j"))
SCOPE = {**base.SCOPE, "heldout_prediction_claimed":False,
         "old_uniform_prediction_counterexample_retracted":False}


def configuration():
    parent, parent_freeze, parent_bindings = base.configuration()
    freeze = base.frozen(HERE/"criterion-all-data.md", FREEZE)
    base.frozen(HERE/"sources-all-data.json", FREEZE)
    matches = re.findall(r"<!-- ALL-DATA-FIBER-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- ALL-DATA-FIBER-FROZEN-END -->",
                         (HERE/"criterion-all-data.md").read_text(), re.S)
    base.require(len(matches) == 1, "nonunique_all_data_contract")
    revision = json.loads(matches[0])
    manifest = json.loads((HERE/"sources-all-data.json").read_text())
    base.require(revision["version"] == manifest["version"] == VERSION and
                 revision["status"] == manifest["status"] == "frozen_before_execution" and
                 revision["parent_version"] == base.VERSION and revision["statistical_role"] == ROLE and
                 revision["single_row_intersections"] == INTERSECTIONS and revision["joint_rows"] == [0, 1, 2, 3] and
                 revision["member_limit"] == 64 and revision["independent_split_cap"] == 24576 and
                 revision["all_twelve_original_CI_required"] is True and revision["shared_phase_required"] is True and
                 revision["original_alpha_unchanged"] is True and revision["original_training_firsts_unchanged"] is True and
                 revision["independent_member_coordinates"] == "four_original_single_probability_CI" and
                 all(revision[key] == SCOPE[key] for key in ("source_mapping_identified", "actual_epoch_identified",
                     "apparatus_optimum_verified", "controller_advance", "new_full_Born_kernel_claim", "bell_event_files_read")),
                 "all_data_fiber_contract_changed")
    bindings = dict(parent_bindings)
    for row in manifest["inputs"]:
        path = (base.ROOT/row["path"]).resolve()
        base.require(path.is_relative_to(base.ROOT) and base.sha(path.read_bytes()) == row["sha256"],
                     "all_data_fiber_source_changed")
        bindings[row["path"]] = row["sha256"]
    freeze["sources_sha256"] = base.sha((HERE/"sources-all-data.json").read_bytes())
    freeze["parent_criterion_freeze"] = parent_freeze
    return {**parent, **revision}, freeze, bindings


def parse_all_CI(text):
    common = base.field_container(text, "common_mean_confidence", "{")
    result = {}
    for field in ("sA_cell", "sB_cell", "j"):
        packets = base.selected_objects(base.field_container(common, field, "["), (0, 1, 2, 3))
        for row, packet in packets.items():
            lower, upper = F(packet["exact_lower"]), F(packet["exact_upper"])
            base.require(0 <= lower <= upper < 1, "invalid_all_data_original_CI")
            result[field+"["+str(row)+"]"] = {"exact_lower":str(lower), "exact_upper":str(upper)}
    base.require(len(result) == 12, "missing_original_CI")
    return result


def single_intersections(original):
    selected, provenance = {}, {}
    for axis, rows in INTERSECTIONS.items():
        field = "sA_cell" if axis[0] == "A" else "sB_cell"
        packets = [original[field+"["+str(row)+"]"] for row in rows]
        lo = max(F(packet["exact_lower"]) for packet in packets)
        hi = min(F(packet["exact_upper"]) for packet in packets)
        provenance[axis] = {"source_rows":rows, "source_CI":packets,
                            "exact_lower":str(lo), "exact_upper":str(hi), "nonempty":lo <= hi}
        if lo > hi:
            return None, provenance
        selected[axis] = {"exact_lower":str(lo), "exact_upper":str(hi)}
    return selected, provenance


def source_input_view(original, selected):
    return {"sA_cell[0]":selected["A0"], "sB_cell[0]":selected["B0"],
            "sA_cell[3]":selected["A1"], "sB_cell[3]":selected["B1"],
            "j[0]":original["j[0]"], "j[3]":original["j[3]"]}


def all_means(original, selected, config):
    means = base.training_means(source_input_view(original, selected), config)
    means["joint"] = [base.unpack(original["j["+str(row)+"]"]) for row in range(4)]
    return means


def phase_slabs_all(box, pop, const, means, config):
    radius = pop["T2"].sqrt().hi
    common, slabs = I.raw(-radius, radius), []
    for index in range(4):
        geo = base.geometry(box, pop, const, index, means)
        denominator = (1-geo["SA"])*(1-geo["SB"])
        rho = (means["joint"][index]-geo["SA"]*geo["SB"])/denominator
        omega = base.fifth_root_delta(rho, config)
        rhs = (omega*geo["E"]-geo["Ccorr"]*geo["L"]-geo["g"].square()*pop["T2"])/geo["D"]
        if (geo["g"]*common).intersect(rhs) is None:
            return None, slabs+[{"cell":index, "g":geo["g"], "rhs":rhs,
                                 "reason":"strict_all_data_common_phase_slab_violation"}]
        if not geo["g"].lo <= 0 <= geo["g"].hi:
            inverse = rhs/geo["g"]
            updated = common.intersect(inverse)
            if updated is None:
                return None, slabs+[{"cell":index, "g":geo["g"], "rhs":rhs, "inverse":inverse,
                                     "reason":"empty_all_four_shared_phase_intersection"}]
            common = updated
            mode = "directed_nonzero_coupling_inverse"
        else:
            mode = "zero_or_crossing_coupling_preserved_without_division"
        slabs.append({"cell":index, "g":geo["g"], "rhs":rhs, "common_k_after_slab":common, "mode":mode})
    return common, slabs


def intersect_cell_constraints(cells, original):
    result = []
    for row, old in enumerate(cells):
        cell = dict(old)
        for field, name in (("sA_cell", "sA"), ("sB_cell", "sB"), ("j", "j")):
            target = base.unpack(original[field+"["+str(row)+"]"])
            value = cell[name].intersect(target)
            base.require(value is not None, "strict_original_CI_readout_violation:"+field+"["+str(row)+"]")
            cell[name] = value
        SA, SB, J = cell["sA"], cell["sB"], cell["j"]
        cell["outcomes"] = [J, base.clipped(SA-J, 0, SCALE), base.clipped(SB-J, 0, SCALE),
                            base.clipped(1-SA-SB+J, 0, SCALE)]
        result.append(cell)
    return result


def paired_readout_all(box, common, pop, const, means, original):
    projection = base.paired_readout(box, common, pop, const, means)
    projection["cells"] = intersect_cell_constraints(projection["cells"], original)
    cells = projection["cells"]
    natural = {"joint_sum":cells[1]["j"]+cells[2]["j"],
               "joint_difference":cells[1]["j"]-cells[2]["j"],
               "CH_N5":cells[0]["j"]+cells[1]["j"]+cells[2]["j"]-cells[3]["j"]-cells[0]["sA"]-cells[0]["sB"]}
    for name, value in natural.items():
        common_bound = projection[name].intersect(value)
        base.require(common_bound is not None, "empty_correlated_and_component_outer:"+name)
        projection[name] = common_bound
    projection["original_CI_intersections_are_outer_constraints_only"] = True
    projection["all_four_joints_use_the_same_k"] = True
    return projection


def unresolved_projection(original, reason):
    cells = intersect_cell_constraints(base.unconstrained_cells(), original)
    return {"cells":cells, "joint_sum":cells[1]["j"]+cells[2]["j"],
            "joint_difference":cells[1]["j"]-cells[2]["j"],
            "CH_N5":cells[0]["j"]+cells[1]["j"]+cells[2]["j"]-cells[3]["j"]-cells[0]["sA"]-cells[0]["sB"],
            "unresolved":reason, "shared_phase_parameter":"same_source_outer_preserved_without_projection",
            "original_CI_intersections_are_outer_constraints_only":True}


def cover(source_box, means, const, original, config):
    constraints = base.linear_constraints(means, const)
    widths = [value.width for value in source_box]
    base.require(all(width > 0 for width in widths), "zero_width_initial_all_data_source_box")
    stop, cap = F(config["normalized_width_stop"]), config["independent_split_cap"]
    nodes, regions, pending, splits, next_id = [], [], [(0, None, source_box, 0)], 0, 1
    while pending:
        node_id, parent, raw_box, depth = pending.pop()
        contracted, certificate = base.linear_contract(raw_box, constraints)
        node = {"id":node_id, "parent":parent, "depth":depth, "input_box":raw_box,
                "contracted_box":contracted, "contraction":certificate}
        nodes.append(node)
        if contracted is None:
            node.update(status="excluded", exclusion=certificate)
            continue
        pop = base.population(contracted)
        if pop is None:
            node.update(status="excluded", exclusion={"reason":"strict_PSD_population_violation"})
            continue
        try:
            common, slabs = phase_slabs_all(contracted, pop, const, means, config)
            node["phase_slabs"] = slabs
            if common is None:
                node.update(status="excluded", exclusion={"reason":"strict_all_data_joint_or_shared_phase_violation"})
                continue
            node["common_k"] = common
            phase_unresolved = None
        except (ValueError, ArithmeticError) as error:
            radius = pop["T2"].sqrt().hi
            common = I.raw(-radius, radius)
            phase_unresolved = str(error)
            node.update(common_k=common, phase_unresolved=phase_unresolved)
        relative = [F(value.width, width) for value, width in zip(contracted, widths)]
        axis = max(range(5), key=lambda index:(relative[index], -index))
        if relative[axis] > stop and depth < config["max_depth"] and splits < cap:
            midpoint = (contracted[axis].lo+contracted[axis].hi)//2
            if contracted[axis].lo < midpoint < contracted[axis].hi:
                left, right = list(contracted), list(contracted)
                left[axis], right[axis] = I.raw(contracted[axis].lo, midpoint), I.raw(midpoint, contracted[axis].hi)
                children = [next_id, next_id+1]
                next_id += 2
                splits += 1
                node.update(status="split", split_axis=AXES[axis], split_at=F(midpoint, SCALE), children=children)
                pending.append((children[1], node_id, right, depth+1))
                pending.append((children[0], node_id, left, depth+1))
                continue
        reason = ("normalized_width_reached" if relative[axis] <= stop else
                  "resource_split_cap_preserved" if splits >= cap else "depth_cap_preserved")
        node.update(status="retained_boundary", terminal_reason=reason, maximum_normalized_width=relative[axis])
        try:
            projection = paired_readout_all(contracted, common, pop, const, means, original)
        except (ValueError, ArithmeticError) as error:
            projection = unresolved_projection(original, str(error))
        regions.append({"node_id":node_id, "source_box":contracted, "common_k":common, "T2":pop["T2"],
                        "reason":reason, "projection":projection})
    nodes.sort(key=lambda item:item["id"])
    base.verify_tree(nodes, source_box, regions)
    terminal = [node for node in nodes if node["status"] != "split"]
    cap_leaves = sum(node.get("terminal_reason") != "normalized_width_reached" for node in terminal if node["status"] != "excluded")
    summary = {"split_count":splits, "node_count":len(nodes), "terminal_leaf_count":len(terminal),
               "excluded_leaf_count":sum(node["status"] == "excluded" for node in terminal),
               "retained_leaf_count":len(regions), "cap_leaf_count":cap_leaves,
               "resource_cap_triggered":cap_leaves > 0, "base_dimensions":5, "phase_dimensions_enumerated":0,
               "all_boundary_and_cap_leaves_preserved":True, "complete_tree_verified":True,
               "all_four_joint_constraints_consumed":True}
    return nodes, regions, summary


def legal_member(original, means, raw_points, fractions, shape, loss, phase_recipe, k, const, config):
    box = shape+[I(loss)]
    source = base.physical_source(box, I(k))
    pop = base.population(box)
    base.require(pop is not None, "all_data_member_PSD_not_legal")
    gaussian = paired_readout_all(box, I(k), pop, const, means, original)
    born = base.fock_readout(source, const, config["source_pair_cutoff"])
    checks, cross = [], []
    for field, row in ALL_FIELDS:
        name = {"sA_cell":"sA", "sB_cell":"sB", "j":"j"}[field]
        target = original[field+"["+str(row)+"]"]
        actual = born["cells"][row][name]
        base.require(actual.within_exact(target), "member_actual_Born_all_twelve_CI_not_contained")
        checks.append({"field":field+"["+str(row)+"]", "probability":actual, "original_CI":target, "contained":True})
        left = gaussian["cells"][row][name]
        base.require(left.intersect(actual) is not None and actual.width <= F(config["comparison_tolerance"])*SCALE,
                     "all_data_member_Gaussian_positive_Born_cross_unresolved")
        cross.append({"row":row, "field":field, "Gaussian":left, "positive_Born":actual, "intersects":True})
    cells = born["cells"]
    CH = cells[0]["j"]+cells[1]["j"]+cells[2]["j"]-cells[3]["j"]-cells[0]["sA"]-cells[0]["sB"]
    return {"recipe":{"coordinate_space":"original_single_probability_CI_intersections", "axis_fractions":fractions,
                      "single_probability_coordinates":raw_points, "loss":loss, "phase_recipe":phase_recipe,
                      "rational_common_k":k}, "source":source, "source_box":box,
            "physical_legal":True, "all_twelve_original_CI_contained":True, "all_twelve_checks":checks,
            "all_four_joints_share_one_k":True, "paired_Gaussian_readout":gaussian,
            "actual_positive_Fock_readout":born, "Gaussian_positive_Fock_cross":cross,
            "actual_positive_Fock_CH_N5":CH, "CH_N5_strictly_positive":CH.lo > 0,
            "CH_N5_strictly_negative":CH.hi < 0, "statistical_role":ROLE,
            "old_source_or_old_member_used_as_generation_seed":False}


def generate_members(original, selected, means, const, config):
    fractions = tuple(map(F, config["witness_axis_fractions"]))
    axes = ("A0", "B0", "A1", "B1")
    boxes = [(F(selected[axis]["exact_lower"]), F(selected[axis]["exact_upper"])) for axis in axes]
    members, rejections, digest = [], {}, hashlib.sha256()
    attempted, limit = 0, False
    for fs in itertools.product(fractions, repeat=4):
        points = [lo+fraction*(hi-lo) for (lo, hi), fraction in zip(boxes, fs)]
        try:
            shape, reconstruction = base.member_shape(points, config, const)
        except (ValueError, ArithmeticError) as error:
            rejections[str(error)] = rejections.get(str(error), 0)+1
            digest.update(base.canonical({"fractions":fs, "reason":str(error)}))
            continue
        for j in range(1, config["witness_loss_denominator"]+1):
            loss = F(j, config["witness_loss_denominator"])
            box = shape+[I(loss)]
            try:
                base.require(box[3].lo >= box[4].hi, "all_data_candidate_loss_above_ratio")
                pop = base.population(box)
                base.require(pop is not None, "all_data_candidate_non_PSD_source")
                common, _ = phase_slabs_all(box, pop, const, means, config)
                base.require(common is not None, "all_data_candidate_empty_shared_phase_intersection")
            except (ValueError, ArithmeticError) as error:
                rejections[str(error)] = rejections.get(str(error), 0)+1
                digest.update(base.canonical({"fractions":fs, "loss":loss, "reason":str(error)}))
                continue
            phase_values = (("midpoint", common.midpoint()), ("lower", F(common.lo, SCALE)), ("upper", F(common.hi, SCALE)))
            for phase_recipe, k in phase_values:
                attempted += 1
                try:
                    member = legal_member(original, means, points, fs, shape, loss, phase_recipe, k, const, config)
                    member["id"] = len(members)
                    member["single_reconstruction"] = reconstruction
                    members.append(member)
                    digest.update(base.canonical({"recipe":member["recipe"], "qualified":True}))
                except (ValueError, ArithmeticError) as error:
                    rejections[str(error)] = rejections.get(str(error), 0)+1
                    digest.update(base.canonical({"fractions":fs, "loss":loss, "phase":phase_recipe, "k":k, "reason":str(error)}))
                if len(members) >= config["member_limit"]:
                    limit = True
                    break
            if limit:
                break
        if limit:
            break
    return members, {"coordinate_space":"original_single_probability_CI_intersections", "axis_order":axes,
                     "axis_fractions":fractions, "loss_denominator":config["witness_loss_denominator"],
                     "phase_order":["midpoint", "lower", "upper"], "member_count":len(members),
                     "member_limit_reached":limit, "phase_candidates_attempted":attempted,
                     "rejection_counts":rejections, "selection_trace_sha256":digest.hexdigest(),
                     "statistical_role":ROLE, "old_source_or_old_member_used_as_generation_seed":False}


def source_stage(original, config):
    selected, provenance = single_intersections(original)
    identity = {"statistical_role":ROLE, "original_twelve_CI":original,
                "single_CI_intersections":provenance, "original_alpha":config["alpha"],
                "design_exposure":{"common_N":177358351, "features_in_global_union":config["features_in_global_union"],
                    "fixed_bets":config["fixed_bets"], "runs_covered":config["runs_covered"],
                    "pulse_subsets_covered":config["pulse_subsets_covered"]},
                "old_uniform_prediction_counterexample_retracted":False,
                "old_source_or_old_member_used_as_generation_seed":False}
    if selected is None:
        return {**identity, "status":"ORIGINAL_SINGLE_CI_INTERSECTION_EMPTY", "members":[], "paired_regions":[],
                "nonempty_all_data_fiber_certified":False, "all_data_fiber_empty_certified":True,
                "empty_fiber_certificate":provenance, "full_all_data_fiber_outer_coverage_certified":True,
                "uniform_CH_N5_strictly_positive":False, "uniform_CH_N5_strictly_negative":False}
    const = base.constants(config)
    means = all_means(original, selected, config)
    initial, initial_evidence = base.initial_box(means, const)
    tree, regions, coverage = cover(initial, means, const, original, config)
    members, search = generate_members(original, selected, means, const, config)
    summary = base.projection_summary(regions)
    positive = bool(regions) and all(region["projection"]["CH_N5"].lo > 0 for region in regions)
    negative = bool(regions) and all(region["projection"]["CH_N5"].hi < 0 for region in regions)
    status = ("EXHIBITED_ALL_DATA_COMPATIBLE_SOURCE_MEMBERS" if members else
              "ALL_DATA_FIBER_EMPTY_CERTIFIED_BY_COMPLETE_EXCLUSION" if not regions else
              "ALL_DATA_FIBER_OUTER_UNRESOLVED_WITHOUT_QUALIFIED_MEMBER")
    return {**identity, "status":status, "source_chart":"m_z_x_r_e_with_all_four_shared_k_slabs", "axes":AXES,
            "four_single_intersection_view":selected, "training_means":means,
            "initial_source_box":initial, "initial_box_evidence":initial_evidence,
            "linear_single_constraints":base.linear_constraints(means, const),
            "cover_tree":tree, "coverage":coverage, "paired_regions":regions, "projection_summary":summary,
            "members":members, "member_search":search, "nonempty_all_data_fiber_certified":bool(members),
            "all_data_fiber_empty_certified":not regions, "full_all_data_fiber_outer_coverage_certified":True,
            "shared_phase_all_four_rows_certified":True,
            "uniform_CH_N5_strictly_positive":positive, "uniform_CH_N5_strictly_negative":negative,
            "uniform_CH_N5_sign":"positive" if positive else "negative" if negative else "unresolved",
            "member_positive_CH_count":sum(member["CH_N5_strictly_positive"] for member in members),
            "member_negative_CH_count":sum(member["CH_N5_strictly_negative"] for member in members),
            "no_signaling_exact":{"A01_equals_A00":True, "A10_equals_A11":True,
                                    "B10_equals_B00":True, "B01_equals_B11":True}}


def science():
    executable = base.frozen(__file__)
    config, freeze, bindings = configuration()
    report_path = HERE.parent.parent/"observable-prediction/public-comparison-po0003.json"
    original = parse_all_CI(report_path.read_text())
    stage = source_stage(original, config)
    return base.serial({"schema":SCHEMA, "version":VERSION, "statistical_role":ROLE,
                        "criterion_freeze":freeze, "executable_freeze":executable, "bindings":bindings,
                        "source_stage_sha256":base.sha(base.canonical(stage)), "source_stage":stage,
                        "primary_new_code_or_outputs_read_before_first":False,
                        "foreign_source_fields_used_as_forward_inputs":False,
                        "statistical_independence_claimed":False, **SCOPE})


def save_first(result, output):
    base.require(not output.exists(), "refusing_to_overwrite_all_data_first")
    logical = (json.dumps(result, sort_keys=True, separators=(",", ":"), allow_nan=False)+"\n").encode()
    compressed = gzip.compress(logical, compresslevel=9, mtime=0)
    storage = output.with_name(output.name[:-8]+"-storage.json")
    base.require(not storage.exists(), "refusing_to_overwrite_all_data_storage_receipt")
    output.write_bytes(compressed)
    metadata = {"schema":"p23-lossless-first-storage/v1", "version":VERSION, "statistical_role":ROLE,
                "path":output.name, "logical_bytes":len(logical), "logical_json_sha256":base.sha(logical),
                "gzip_bytes":len(compressed), "gzip_sha256":base.sha(compressed), "source_stage_sha256":result["source_stage_sha256"],
                "gzip_mtime":0, "lossless_json_bytes":True, "first_science_outcome":result["source_stage"]["status"]}
    storage.write_text(json.dumps(metadata, sort_keys=True, indent=2)+"\n")
    return metadata


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(save_first(science(), args.output), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
