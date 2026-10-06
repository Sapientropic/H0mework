"""Post-calculation receipt comparison; scientific receipts remain byte-identical."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
OUTPUT = HERE/"independent-comparison.json"
FIRST = {"independent_count.json": "0858761ce5840aa1ed1a7dc09f37604a7a1ed08b2a97aad4d5bb3a35dac2bf54",
         "calibration.json": "547ebf134776b1c6707e79929579dcb58047f70fa10d44fb047cd568639408a3"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def program_freeze():
    path = Path(__file__).resolve()
    relative = str(path.relative_to(ROOT))
    commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", relative], cwd=ROOT, text=True).strip()
    if not commit or subprocess.check_output(["git", "show", commit+":"+relative], cwd=ROOT) != path.read_bytes():
        raise ValueError("commit the posthoc comparator before executing it")
    subprocess.check_call(["git", "merge-base", "--is-ancestor", "c3032d45bf", commit], cwd=ROOT)
    return {"commit": commit, "program_sha256": digest(path)}


def exact(value):
    return F(value["exact"])


def packet_key(packet):
    return tuple(tuple(exact(x) if isinstance(x, dict) else F(x) for x in packet[key])
                 for key in ("geometric_ratio", "transmission_A", "transmission_B"))


def endpoints(interval):
    return F(interval["exact_lower"]), F(interval["exact_upper"])


def contains(interval, value):
    lo, hi = endpoints(interval)
    return lo <= value <= hi


def delta(interval, value):
    lo, hi = endpoints(interval)
    return abs((lo+hi)/2-value)


def compare():
    freeze = program_freeze()
    bound = {}
    reports = {}
    for name, first_sha in FIRST.items():
        path = HERE/name
        if digest(path) != first_sha:
            raise ValueError("first scientific receipt changed: "+name)
        reports[name] = json.loads(path.read_text())
        bound[str(path.relative_to(ROOT))] = first_sha
    own, primary = reports["independent_count.json"], reports["calibration.json"]
    for filename, receipt, field in (("independent_count.py", own, "program_sha256"), ("calibration.py", primary, "sha256")):
        path = HERE/filename
        commit = receipt["executable_freeze"]["commit"]
        relative = str(path.relative_to(ROOT))
        if digest(path) != receipt["executable_freeze"][field] or subprocess.check_output(["git", "show", commit+":"+relative], cwd=ROOT) != path.read_bytes():
            raise ValueError("scientific program/source occurrence changed: "+filename)
        bound[relative] = digest(path)
    own_sources = {row["preparation"]: row for row in own["preparations"]}
    primary_rows = {}
    for row in primary["branches"]:
        key = (packet_key(row["source_parameters"]), row["window_pulses"], row["background_model"])
        if key in primary_rows:
            raise ValueError("duplicate primary calibration branch")
        primary_rows[key] = row
    eta = {}
    criterion = HERE/"criterion.md"
    for side in ("A", "B"):
        match = re.search(r"η"+side+r"∈\[([0-9.]+),([0-9.]+)\]", criterion.read_text())
        if match is None:
            raise ValueError("missing frozen probability-unit efficiency interval")
        eta[side] = tuple(map(F, match.groups()))
    errors, rows = [], []
    quantities = {"pair_at_least_one": "at_least_one", "exactly_one": "exactly_one", "mean_pair": "mean_pair"}
    source_equal = pair_equal = ratio_status_equal = matched_exact_equal = True
    rate_count = ratio_count = matched_count = 0
    worst_rate = worst_ratio = F(0)
    used = set()
    for row in own["branches"]:
        source = own_sources[row["preparation"]]
        key = (packet_key(source["source_parameters"]), row["window_pulses"], row["background_model"])
        if key not in primary_rows:
            errors.append("missing actual-parameter branch: "+row["case_id"])
            continue
        used.add(key)
        primary_row = primary_rows[key]
        record = {"case_id": row["case_id"], "primary_preparation_name": primary_row["preparation"],
                  "exact_primary_rates_inside_independent": {}, "exact_primary_ratios_inside_independent": {},
                  "conditional_efficiency_interval_relations": {}}
        same_source = packet_key(source["source_parameters"]) == packet_key(primary_row["source_parameters"])
        source_equal &= same_source
        for name, primary_name in quantities.items():
            same = exact(source["source_pair_readouts"][name]) == exact(primary_row["pair_quantities_per_pulse"][primary_name])
            pair_equal &= same
            if not same:
                errors.append("source pair readout changed: "+row["case_id"]+"/"+name)
        for name in ("sA", "sB", "j"):
            value = exact(primary_row["probabilities"][name])
            enclosed = contains(row["rates"][name], value)
            record["exact_primary_rates_inside_independent"][name] = enclosed
            rate_count += 1
            worst_rate = max(worst_rate, delta(row["rates"][name], value))
            if not enclosed:
                errors.append("primary probability outside number enclosure: "+row["case_id"]+"/"+name)
        for side, primary_side, eta_side in (("alice", "Alice", "A"), ("bob", "Bob", "B")):
            ratio = row["Klyshko"][side]
            primary_ratio = primary_row["Klyshko"][primary_side]
            if primary_ratio["status"] != "defined":
                same_status = ratio["status"] == "UNDEFINED_ZERO_HERALD"
                ratio_status_equal &= same_status
                record["exact_primary_ratios_inside_independent"][side] = same_status
                if not same_status:
                    errors.append("zero-herald ratio status mismatch: "+row["case_id"]+"/"+side)
                continue
            if ratio["status"] != "DEFINED":
                ratio_status_equal = False
                errors.append("positive herald ratio status mismatch: "+row["case_id"]+"/"+side)
                continue
            value = exact(primary_ratio["value"])
            enclosed = contains(ratio["interval"], value)
            record["exact_primary_ratios_inside_independent"][side] = enclosed
            ratio_count += 1
            worst_ratio = max(worst_ratio, delta(ratio["interval"], value))
            if not enclosed:
                errors.append("primary Klyshko point outside number enclosure: "+row["case_id"]+"/"+side)
            lo, hi = endpoints(ratio["interval"])
            bounds = eta[eta_side]
            intersects = max(lo, bounds[0]) <= min(hi, bounds[1])
            record["conditional_efficiency_interval_relations"][side] = {
                "primary_exact_point_inside_public_eta": bounds[0] <= value <= bounds[1],
                "independent_enclosure_intersects_public_eta": intersects,
                "independent_recorded_verdict_consistent": row["conditional_public_eta"][side]["status"] == ("INTERSECTS" if intersects else "DISJOINT"),
                "calibration_identity_identified": False}
            if "matched_single_polarization" in row:
                matched = row["matched_single_polarization"][side]
                same = matched["status"] == "DEFINED" and exact(matched["K"]) == value
                matched_exact_equal &= same and matched["bound_passed"] and matched["number_enclosed"]
                matched_count += 1
                if not same:
                    errors.append("matched-polarization exact formula mismatch: "+row["case_id"]+"/"+side)
        rows.append(record)
    criterion_relative = str(criterion.relative_to(ROOT))
    sources_relative = str((HERE/"sources.json").relative_to(ROOT))
    flags = ("calibration_preparation_identified", "calibration_ports_identified", "calibration_pump_identified",
             "background_subtraction_identified", "source_mapping_identified", "publication_configuration_identified", "production_admitted")
    shared = {"version": own["version"] == primary["version"],
              "criterion_sha256": own["criterion_freeze"]["criterion_sha256"] == primary["bindings"][criterion_relative] == digest(criterion),
              "sources_sha256": own["criterion_freeze"]["sources_sha256"] == primary["bindings"][sources_relative] == digest(HERE/"sources.json"),
              "source_parameters": source_equal, "source_pair_quantities": pair_equal,
              "ratio_definedness": ratio_status_equal, "matched_exact_values_and_bounds": matched_exact_equal,
              "seven_unbound_calibration_roles_false": all(own[name] is False and primary[name] is False for name in flags)}
    checks = {"twelve_branches_bijective": len(used) == len(rows) == len(primary_rows) == len(own["branches"]) == 12,
              "probabilities_and_ratios_inside_number_enclosures": not errors and rate_count == 36 and ratio_count == 24,
              "four_matched_exact_conditional_efficiencies": matched_count == 4 and matched_exact_equal,
              "independent_control_aggregate": own["controls"]["passed"],
              "primary_control_aggregate": all(primary["controls"]["checks"].values()),
              "zero_herald_not_zero_efficiency": own["controls"]["checks"]["zero_herald_explicitly_undefined"]
                  and own["controls"]["checks"]["zero_source_not_fake_transmission_efficiency"]
                  and primary["controls"]["checks"]["vacuum_herald_is_undefined"]}
    bound[criterion_relative] = digest(criterion)
    bound[sources_relative] = digest(HERE/"sources.json")
    bound[str(Path(__file__).resolve().relative_to(ROOT))] = digest(Path(__file__))
    return {"schema": "p23-calibration-readout-independent-comparison/v1", "version": own["version"],
            "status": "PASS" if not errors and all(shared.values()) and all(checks.values()) else "FAIL",
            "executable_freeze": freeze, "bindings": bound, "shared_input_identity": shared,
            "checks": checks, "errors": errors, "branches": rows,
            "control_counts": {"primary": primary["controls"]["case_count"], "independent": own["controls"]["case_count"]},
            "worst_midpoint_deltas": {"rates": {"exact": str(worst_rate), "value": float(worst_rate)},
                                      "Klyshko": {"exact": str(worst_ratio), "value": float(worst_ratio)}},
            "scientific_receipts_preserved_byte_identical": True,
            "post_calculation_primary_access": True, "actual_calibration_failure_claimed": False,
            "no_calibration_branch_selected": True, **{name: False for name in flags}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    result = compare()
    if not args.check_only:
        OUTPUT.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"status": result["status"], "branches": len(result["branches"]), "checks": result["checks"],
                      "worst_midpoint_deltas": {key: value["value"] for key, value in result["worst_midpoint_deltas"].items()}}))
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
