"""Recompute the selected uniform angular certificate and independent Fock endpoints."""
from fractions import Fraction as F
import argparse
import json
import gzip
from pathlib import Path
import subprocess

import primary
import receiver
import slice as scalar

HERE = Path(__file__).resolve().parent


def run(independent_report):
    executable = primary.frozen(__file__)
    config, manifest, g, fw, criterion, _ = receiver.load()
    ppath = HERE/"receiver-primary-contracted.json"
    primary.frozen(ppath)
    primary.frozen(independent_report)
    independent_text = (gzip.decompress(independent_report.read_bytes()).decode()
                        if independent_report.suffix == ".gz" else independent_report.read_text())
    p, q = json.loads(ppath.read_text()), json.loads(independent_text)
    for record in (p, q):
        primary.require(record["source_mapping_identified"] is False and record["apparatus_optimum_verified"] is False and
                        record["controller_advance"] is False and record["actual_hardware_drive_identified"] is False,
                        "UNPAID_RECEIVER_SCOPE")
    selected = p["result"]["selected_update"]
    primary.require(selected is not None and q["canonical_update"] is not None, "TWO_RECEIVER_CERTIFICATES_REQUIRED")
    chosen = selected["update"]
    name, sign, step = selected["name"], chosen["sign"], F(chosen["step_degree"])
    primary.require(selected["direction"] == config["directions"][name], "RECEIVER_DIRECTION_CHANGED")
    counts = json.loads((HERE/config["public_counts"]).read_text())["counts"]
    ci = json.loads((HERE/config["public_confidence_report"]).read_text())["common_mean_confidence"]
    source = scalar.shape(scalar.training_view(counts), scalar.interval_from_receipt(ci["j"][3], g.I), config, g, fw)
    segments = [x for x in json.loads((HERE/"slice-primary.json").read_text())["result"]["partition"]["segments"]
                if x["classification"] != "excluded"]
    half = F(config["receiver_rounding_half_width_degree"])
    original = list(map(F, config["angles_deg"]))
    vector = [sign*x for x in config["directions"][name]]
    tube = [g.I(a-half+min(F(0), d*step), a+half+max(F(0), d*step)) for a, d in zip(original, vector)]
    _, rows = receiver.aggregate_gradients(source, segments, tube, config, g)
    lower = min(sum((d*grad for d, grad in zip(vector, row["gradients"])), g.I.point(0)).lo for row in rows)
    gain = step*lower
    primary.require(gain == F(chosen["gain_lower_bound"]) and gain > F(config["strict_improvement_lower_bound"]),
                    "UNIFORM_RECEIVER_GAIN_NOT_RECOMPUTED")
    independent = primary.module("_rx_verifier_independent", HERE/"independent_receiver.py")
    icfg, _, _, ifw, old = independent.load()
    _, _, _, _, _, _, _, canonical = independent.source_domain(icfg, ifw, old)
    # Receiver coordinates come from the checked update; every source field is independently regenerated.
    updated = [a+d*step for a, d in zip(original, vector)]
    before = independent.fock_score(canonical, original, icfg, ifw, old)
    after = independent.fock_score(canonical, updated, icfg, ifw, old)
    difference = after["raw_CH"]-before["raw_CH"]
    primary.require(difference.lo > F(config["strict_improvement_lower_bound"]), "INDEPENDENT_FOCK_GAIN_NOT_CERTIFIED")
    primary.frozen(HERE/"receiver_tests.py")
    tests = subprocess.run(["python3", str(HERE/"receiver_tests.py")], capture_output=True, text=True)
    primary.require(tests.returncode == 0, "ANGULAR_JET_CONTROLS_FAILED")
    return primary.serial({"schema": "p23-receiver-update-verification/v1", "version": config["version"],
                           "status": "CERTIFIED_FIXED_SOURCE_RECEIVER_UPDATE_WITH_INDEPENDENT_FOCK_ENDPOINTS",
                           "criterion_freeze": criterion, "program_freeze": executable,
                           "primary_receipt": primary.frozen(ppath), "independent_receipt": primary.frozen(independent_report),
                           "independent_program": primary.frozen(HERE/"independent_receiver.py"),
                           "angular_jet": primary.frozen(HERE/"angular_jet.py"), "inputs": manifest["inputs"],
                           "selected_direction": name, "sign": sign, "step_degree": step, "updated_angles_deg": updated,
                           "uniform_gain_lower_bound": gain, "scalar_segments_recomputed": len(rows),
                           "all_boundaries_preserved": True, "receiver_rounding_half_width_degree": half,
                           "independent_Fock_gain": difference.packet(), "independent_source_reselected_to_match_update": False,
                           "foreign_source_fields_or_gain_as_forward_inputs": False,
                           "focused_tests": {"returncode": tests.returncode, "output": tests.stdout+tests.stderr},
                           "source_mapping_identified": False, "actual_hardware_drive_identified": False,
                           "apparatus_optimum_verified": False, "controller_advance": False,
                           "retrospective": True, "bell_event_files_read": 0,
                           "new_Born_or_derivative_kernel_claim": False}, g.I)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--independent-report", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=HERE/"receiver-verification.json")
    args = parser.parse_args()
    primary.require(not args.output.exists(), "OUTPUT_EXISTS_USE_NEW_PATH")
    result = run(args.independent_report.resolve())
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True, allow_nan=False)+"\n")
    print(json.dumps({"status": result["status"], "output": str(args.output)}))
