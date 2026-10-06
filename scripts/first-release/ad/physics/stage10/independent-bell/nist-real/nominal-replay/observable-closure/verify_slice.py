"""Consume frozen source certificates, both scalar partitions and independent Fock readback."""
from fractions import Fraction as F
import argparse
import json
from pathlib import Path
import subprocess

import primary
import slice as scalar

HERE = Path(__file__).resolve().parent


def bindings_current(bindings):
    rows = bindings.items() if isinstance(bindings, dict) else ((x["path"], x["sha256"]) for x in bindings)
    for name, expected in rows:
        if isinstance(expected, dict):
            expected = expected["sha256"]
        path = (primary.ROOT/name).resolve()
        primary.require(path.is_relative_to(primary.ROOT) and primary.digest(path) == expected,
                        "STALE_VERIFICATION_BINDING:"+name)


def strict_scope(receipt):
    for name in ("source_mapping_identified", "production_admitted", "controller_advance",
                 "full_statistical_fiber_certified"):
        primary.require(receipt[name] is False, "UNPAID_SCOPE:"+name)
    primary.require(receipt["retrospective"] is True and type(receipt["bell_event_files_read"]) is int and
                    receipt["bell_event_files_read"] == 0, "WRONG_ACCESS_SCOPE")


def interval(value, I):
    return I(F(value["exact_lower"]), F(value["exact_upper"]))


def check_primary_partition(receipt, source, config, I):
    partition = receipt["result"]["partition"]
    rows = partition["segments"]
    upper = min(F(1), source["r"].hi)
    primary.require(rows and F(rows[0]["lower"]) == 0 and F(rows[-1]["upper"]) == upper,
                    "PRIMARY_COVER_ENDPOINT_CHANGED")
    primary.require(all(F(x["lower"]) < F(x["upper"]) for x in rows) and
                    all(F(a["upper"]) == F(b["lower"]) for a, b in zip(rows, rows[1:])),
                    "PRIMARY_COVER_GAP_OR_OVERLAP")
    active = 0
    for row in rows:
        lo, hi = F(row["lower"]), F(row["upper"])
        bounds = {name: scalar.bernstein_range(p, lo, hi, I) for name, p in source["polynomials"].items()}
        for name, value in bounds.items():
            primary.require(interval(row["bounds"][name], I) == value, "PRIMARY_BOUND_SNAPSHOT_CHANGED")
        status = row["classification"]
        if status == "inside":
            primary.require(lo > 0 and hi <= min(F(1), source["r"].lo) and bounds["phase"].hi <= 0 and
                            bounds["low"].lo >= 0 and bounds["high"].lo >= 0 and bounds["denominator"].lo > 0,
                            "PRIMARY_INSIDE_NOT_CERTIFIED")
        elif status == "excluded":
            primary.require(bounds["phase"].lo > 0 or bounds["low"].hi < 0 or bounds["high"].hi < 0 or
                            lo > source["r"].hi or bounds["denominator"].hi <= 0, "PRIMARY_EXCLUSION_NOT_CERTIFIED")
        else:
            primary.require(status == "boundary" and (hi-lo <= F(config["scalar_cover_width"]) or
                            partition["cap_reached"] is True), "PRIMARY_BOUNDARY_DROPPED_OR_PREMATURE")
        active += status != "excluded"
    paired = receipt["result"]["paired_predictions"]
    primary.require(len(paired) == active, "PRIMARY_ACTIVE_SEGMENT_MISSING")
    expected = [x for x in rows if x["classification"] != "excluded"]
    primary.require(all(p["loss_interval"] == [x["lower"], x["upper"]] for p, x in zip(paired, expected)),
                    "PRIMARY_PAIRED_LOSS_IDENTITY_CHANGED")
    return {"segments": len(rows), "active_segments": active, "all_bounds_recomputed": True,
            "complete_partition": True, "boundary_preserved": True}


def check_independent_partition(receipt, shape, polys, config, fw):
    rows = receipt["cover"]
    boxes = [interval(x["e"], fw.I) for x in rows]
    primary.require(boxes and boxes[0].lo == 0 and boxes[-1].hi == min(F(1), shape["r"].hi) and
                    all(x.lo < x.hi for x in boxes) and all(a.hi == b.lo for a, b in zip(boxes, boxes[1:])),
                    "INDEPENDENT_COVER_GAP_OR_OVERLAP")
    independent = primary.module("_ef_verify_independent", HERE/"independent_slice.py")
    active = []
    for index, (row, box) in enumerate(zip(rows, boxes)):
        bounds = {k: independent.polynomial_range(polys[k], box, fw.I)
                  for k in ("Pphase", "Plow", "Phigh", "Q1")}
        primary.require(all(interval(row["classification_evidence"][k], fw.I) == v for k, v in bounds.items()),
                        "INDEPENDENT_BOUND_SNAPSHOT_CHANGED")
        if row["status"] == "inside":
            primary.require(box.lo > 0 and box.hi <= min(F(1), shape["r"].lo) and bounds["Pphase"].hi <= 0 and
                            bounds["Plow"].lo >= 0 and bounds["Phigh"].lo >= 0 and bounds["Q1"].lo > 0,
                            "INDEPENDENT_INSIDE_NOT_CERTIFIED")
        elif row["status"] == "outside":
            primary.require(bounds["Pphase"].lo > 0 or bounds["Plow"].hi < 0 or bounds["Phigh"].hi < 0 or
                            bounds["Q1"].hi <= 0 or box.lo > min(F(1), shape["r"].hi),
                            "INDEPENDENT_EXCLUSION_NOT_CERTIFIED")
        else:
            primary.require(row["status"] == "boundary" and (box.width <= F(config["scalar_cover_width"]) or
                            receipt["coverage"]["resource_cap_triggered"] is True), "INDEPENDENT_BOUNDARY_INVALID")
        if row["status"] != "outside":
            active.append(index)
    primary.require([x["cover_index"] for x in receipt["paired_regions"]] == active and
                    all(x["same_e_for_both_cells"] is True for x in receipt["paired_regions"]),
                    "INDEPENDENT_PAIRED_LOSS_IDENTITY_CHANGED")
    return {"segments": len(rows), "active_segments": len(active), "all_bounds_recomputed": True,
            "complete_partition": True, "boundary_preserved": True}


def run():
    executable = primary.frozen(__file__)
    config, manifest, g, fw, _, _ = scalar.load()
    files = ["slice-primary.json", "independent-slice.json", "cross-receipt.json",
             "certification.json", "scalar-certification.json"]
    receipts = {name: json.loads((HERE/name).read_text()) for name in files}
    freezes = {name: primary.frozen(HERE/name) for name in files}
    p, ind, cross = (receipts[name] for name in files[:3])
    for x in (p, ind, cross):
        strict_scope(x)
        bindings_current(x.get("inputs", x.get("bindings")))
    for name in files[3:]:
        cert = receipts[name]
        bindings_current(cert["bindings"])
        primary.require(cert["authorized_axioms"] == ["propext", "Classical.choice", "Quot.sound"], "UNEXPECTED_AXIOMS")
        primary.require(all(cert["kernel_claims"][key] is True for key in
                        (["actual_source_generates_H_equals_coherence_gT", "generated_polynomial_degree_at_most_two"]
                         if name == "certification.json" else
                         ["pointwise_legal_scalar_domain_generates_physical_Snapshot", "generated_actual_named_pulse_seed_readback"])),
                        "SOURCE_KERNEL_CONSUMER_MISSING")
    counts = json.loads((HERE/config["public_counts"]).read_text())["counts"]
    ci = json.loads((HERE/config["public_confidence_report"]).read_text())["common_mean_confidence"]
    training = scalar.training_view(counts)
    source = scalar.shape(training, scalar.interval_from_receipt(ci["j"][3], g.I), config, g, fw)
    primary_cover = check_primary_partition(p, source, config, g.I)
    independent = primary.module("_ef_verify_independent_source", HERE/"independent_slice.py")
    icfg, _, _, ifw, old = independent.configuration()
    view = independent.source_view(HERE/icfg["public_counts"], independent.training_intervals(HERE/icfg["public_confidence_report"]), old)
    ishape = independent.single_shape(view, icfg, ifw)
    polys = independent.polynomials(ishape, ifw)
    independent_cover = check_independent_partition(ind, ishape, polys, icfg, ifw)
    p_member = p["result"]["canonical_member"]
    primary.require(p_member and ind["canonical_member"] and p_member["outcome"] ==
                    ind["canonical_member"]["member_outcome"] == "EXHIBITED_CALIBRATION_FREE_SLICE_MEMBER",
                    "NO_TWO_CERTIFIED_MEMBERS")
    primary.require(p["result"]["held_out_envelope_outcome"] == ind["projection_summary"]["outcome"] ==
                    "SLICE_PREDICTION_ENVELOPE_CONTAINED", "HELDOUT_ENVELOPE_NOT_CONTAINED")
    c = cross["cross_result"]
    primary.require(c["status"] == "INDEPENDENT_FOCK_READBACK_OF_PRIMARY_CANONICAL_SLICE_MEMBER" and
                    F(c["selected_primary_rational_e"]) == F(p_member["e"]) and
                    all(c[key] is True for key in ("all_fourteen_source_fields_verified", "all_sixteen_complete_outcomes_verified",
                        "all_twelve_original_CI_verified", "all_six_training_constraints_verified")) and
                    c["foreign_source_fields_or_probabilities_used_as_forward_inputs"] is False and
                    c["finite_prefix_renormalized"] is False, "INDEPENDENT_FOCK_CROSS_NOT_PAID")
    tests = []
    for filename in ("tests.py", "slice_tests.py"):
        primary.frozen(HERE/filename)
        result = subprocess.run(["python3", str(HERE/filename)], capture_output=True, text=True)
        primary.require(result.returncode == 0, "FOCUSED_CONTROLS_FAILED:"+filename+result.stderr[-2000:])
        tests.append({"file": filename, "sha256": primary.digest(HERE/filename), "returncode": result.returncode,
                      "output": result.stdout+result.stderr})
    return {"schema": "p23-observable-closure-verification/v1", "version": config["version"],
            "status": "CERTIFIED_CALIBRATION_FREE_SLICE_AND_PAIRED_PUBLIC_OBSERVABLES",
            "program_freeze": executable, "receipt_freezes": freezes, "inputs": manifest["inputs"],
            "primary_cover": primary_cover, "independent_cover": independent_cover,
            "independent_Fock_cross": {"source_fields": 14, "probabilities": 12, "complete_outcomes": 16,
                                       "source_and_probability_inputs_from_foreign_receipt": False},
            "focused_tests": tests, "full_statistical_fiber_certified": False, "source_mapping_identified": False,
            "apparatus_optimum_verified": False, "controller_advance": False, "production_admitted": False,
            "retrospective": True, "bell_event_files_read": 0}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=HERE/"verification.json")
    args = parser.parse_args()
    primary.require(not args.output.exists(), "OUTPUT_EXISTS_USE_NEW_PATH")
    result = run()
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True, allow_nan=False)+"\n")
    print(json.dumps({"status": result["status"], "output": str(args.output)}))
