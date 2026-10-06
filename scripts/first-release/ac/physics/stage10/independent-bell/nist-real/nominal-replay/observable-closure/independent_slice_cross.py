#!/usr/bin/env python3
"""Post-first independent coherent readback of the primary ef0002 witness."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

import independent_slice as independent

HERE = Path(__file__).resolve().parent


def interval(packet, I):
    independent.require(isinstance(packet, dict) and set(("exact_lower", "exact_upper")) <= set(packet),
                        "missing_cross_readback_interval")
    return I(F(packet["exact_lower"]), F(packet["exact_upper"]))


def checked_overlap(actual, reported, tolerance, I, name):
    report = interval(reported, I)
    delta = actual-report
    independent.require(delta.lo <= 0 <= delta.hi and delta.width <= tolerance,
                        "independent_cross_readback_mismatch:"+name)
    return {"independent": actual, "reported": report, "residual": delta,
            "mathematical_enclosures_overlap": True, "residual_width_within_frozen_tolerance": True}


def verify_primary(receipt, view, shape, polys, config, fw, old, confidence):
    independent.require(receipt["schema"] == "p23-observable-scalar-slice-primary/v1" and
                        receipt["version"] == independent.VERSION and
                        receipt["retrospective"] is True and type(receipt["bell_event_files_read"]) is int and
                        receipt["bell_event_files_read"] == 0 and all(receipt[k] is False for k in
                        ("apparatus_optimum_verified", "source_mapping_identified", "production_admitted",
                         "controller_advance", "full_statistical_fiber_certified")), "primary_cross_scope_changed")
    member = receipt["result"]["canonical_member"]
    independent.require(isinstance(member, dict), "primary_canonical_slice_member_missing")
    e = F(member["e"])
    # Only the foreign rational slice coordinate enters the independent forward call.
    source = independent.canonical_source(shape, polys, e, fw)
    a0, a1, b0, b1 = map(F, config["angles_deg"])
    cells, tails = [], []
    for a, b in ((a0, b0), (a0, b1), (a1, b0), (a1, b1)):
        cell, tail = old.coherent_window(source, a, b, config, fw)
        cells.append(cell)
        tails.append(tail)
    tolerance = F(config["implementation_tolerance"])
    pair = (("sA0", 0, "sA"), ("sB0", 0, "sB"), ("j00", 0, "j"), ("sA1", 3, "sA"), ("sB1", 3, "sB"))
    residuals = {name: cells[row][field]-view["centers"][name] for name, row, field in pair}
    independent.require(all(v.lo <= 0 <= v.hi and v.width <= tolerance for v in residuals.values()),
                        "independent_cross_five_training_readback_failed")
    joint11_ok = cells[3]["j"].contained(*view["joint11_CI"])
    independent.require(joint11_ok, "independent_cross_joint11_CI_readback_failed")
    source_checks = {}
    primary_shape = receipt["result"]["source"]
    for name in ("r", "m", "z", "x", "h", "v"):
        source_checks[name] = checked_overlap(shape[name], primary_shape[name], tolerance, fw.I, name)
    for name in ("etaA", "etaB", "lambda", "tH", "tV"):
        source_checks[name] = checked_overlap(source[name], member[name], tolerance, fw.I, name)
    for name, actual in (("rotation_cos", source["R"][0][0]), ("rotation_sin", source["R"][0][1]),
                         ("phase_coherence", source["phase_coordinate"])):
        source_checks[name] = checked_overlap(actual, member[name], tolerance, fw.I, name)
    independent.require(len(member["cells"]) == 4, "primary_cross_four_cells_missing")
    probability_checks, outcome_checks = [], []
    for index, (actual, reported) in enumerate(zip(cells, member["cells"])):
        independent.require(reported["setting"] == [index//2, index%2] and len(reported["outcomes"]) == 4,
                            "primary_cross_cell_order_or_outcomes_changed")
        probability_checks.append({field: checked_overlap(actual[field], reported[field], tolerance, fw.I,
                                                           str(index)+":"+field) for field in ("j", "sA", "sB")})
        outcome_checks.append([checked_overlap(actual["outcomes"][k], reported["outcomes"][k], tolerance, fw.I,
                                               str(index)+":outcome:"+str(k)) for k in range(4)])
    inclusion = {key: [cells[index][field].contained(ci["exact_lower"], ci["exact_upper"])
                      for index, ci in enumerate(confidence[key])]
                 for key, field in (("j", "j"), ("sA_cell", "sA"), ("sB_cell", "sB"))}
    independent.require(all(all(values) for values in inclusion.values()), "independent_cross_original_twelve_CI_failed")
    return {"status": "INDEPENDENT_FOCK_READBACK_OF_PRIMARY_CANONICAL_SLICE_MEMBER",
            "selected_primary_rational_e": e, "independent_source": source, "independent_cells": cells,
            "independent_source_tails": tails, "source_field_comparisons": source_checks,
            "twelve_probability_comparisons": probability_checks, "sixteen_outcome_comparisons": outcome_checks,
            "five_training_center_residuals": residuals, "five_training_centers_verified": True,
            "joint11_original_training_CI_verified": joint11_ok, "all_six_training_constraints_verified": True,
            "original_CI_inclusion": inclusion, "all_twelve_original_CI_verified": True,
            "all_fourteen_source_fields_verified": len(source_checks) == 14,
            "all_sixteen_complete_outcomes_verified": True, "finite_prefix_renormalized": False,
            "same_source_used_for_both_heldout_cells": True,
            "foreign_source_fields_or_probabilities_used_as_forward_inputs": False,
            "source_or_cover_parameters_reselected_using_comparison": False,
            "mathematical_overlap_is_comparison_not_prediction_input": True}


def run():
    program = independent.frozen(__file__)
    independent_program = independent.frozen(HERE/"independent_slice.py")
    config, freeze, bindings, fw, old = independent.configuration()
    own_first = independent.frozen(HERE/"independent-slice.json")
    primary_first = independent.frozen(HERE/"slice-primary.json")
    primary_program = independent.frozen(HERE/"slice.py")
    confidence_path = (HERE/config["public_confidence_report"]).resolve()
    training_confidence = independent.training_intervals(confidence_path)
    view = independent.source_view((HERE/config["public_counts"]).resolve(), training_confidence, old)
    shape = independent.single_shape(view, config, fw)
    polys = independent.polynomials(shape, fw)
    # The two immutable first receipts predate this consumer. No candidate output is overwritten.
    target = json.loads((HERE/"slice-primary.json").read_text())
    independent.require(target["program_freeze"]["sha256"] == primary_program["sha256"] and
                        target["manifest_sha256"] == independent.digest(HERE/"sources-ef0002.json"),
                        "primary_cross_program_or_manifest_changed")
    confidence = json.loads(confidence_path.read_text())["common_mean_confidence"]
    result = verify_primary(target, view, shape, polys, config, fw, old, confidence)
    return old.serial({"schema": "p23-observable-closure-independent-slice-cross/v1",
                       "version": independent.VERSION, "criterion_freeze": freeze, "program_freeze": program,
                       "independent_science_program_freeze": independent_program, "bindings": bindings,
                       "primary_first_freeze": primary_first, "independent_first_freeze": own_first,
                       "primary_science_program_freeze": primary_program, "cross_result": result,
                       "science_first_isolation": "mutually_blind_until_both_first_receipts_completed",
                       "both_science_first_receipts_preceded_cross_consumer": True,
                       "retrospective": True, "statistical_independence_claimed": False,
                       "bell_event_files_read": 0, **{k: False for k in independent.FLAGS}})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE/"cross-receipt.json")
    args = parser.parse_args()
    independent.require(not args.output.exists(), "cross_receipt_exists_use_new_path")
    result = run()
    text = json.dumps(result, indent=2, allow_nan=False)+"\n"
    args.output.write_text(text)
    print(json.dumps({"output": str(args.output), "status": result["cross_result"]["status"],
                      "sha256": hashlib.sha256(text.encode()).hexdigest()}))


if __name__ == "__main__":
    main()
