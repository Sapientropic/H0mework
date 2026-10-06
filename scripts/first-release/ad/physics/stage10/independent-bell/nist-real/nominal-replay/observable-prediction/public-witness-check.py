"""Independent full-mode forward validation of public source representatives."""
from __future__ import annotations

import argparse
import cmath
import hashlib
import importlib.util
import json
import math
import re
import subprocess
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
CS = HERE.parent / "investigation" / "collected-source"
CRITERION = HERE / "criterion.md"
SOURCE_SHA = "1a243a2bc00de0120f2296b7149cfbd9dfecd1b9584c9924c57591f78cc8c716"
ORDER = ((0, 0), (0, 1), (1, 0), (1, 1))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def executable_freeze():
    path = str(Path(__file__).relative_to(ROOT))
    commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", path], cwd=ROOT, text=True).strip()
    if not commit:
        raise ValueError("commit this checker before first execution")
    saved = subprocess.check_output(["git", "show", commit+":"+path], cwd=ROOT)
    if saved != Path(__file__).read_bytes():
        raise ValueError("checker differs from its executable freeze")
    return {"commit": commit, "sha256": digest(Path(__file__))}


def specification():
    path = str(CRITERION.relative_to(ROOT))
    saved = subprocess.check_output(["git", "show", "be90dbed91:"+path], cwd=ROOT)
    if saved != CRITERION.read_bytes():
        raise ValueError("observable-prediction criterion differs from its freeze")
    blocks = re.findall(r"```json\s*(.*?)\s*```", CRITERION.read_text(), re.S)
    if len(blocks) != 1:
        raise ValueError("one observable-prediction specification required")
    return json.loads(blocks[0])


def native_source():
    path = CS/"independent.py"
    if digest(path) != SOURCE_SHA:
        raise ValueError("frozen native amplitude producer changed")
    spec = importlib.util.spec_from_file_location("public_native_full_amplitudes", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def numeric_recipe(recipe):
    result = dict(recipe)
    for field in ("power_H", "power_V", "source_mode_phase_H", "source_mode_phase_V",
                  "beta_A", "beta_B", "phase_A", "phase_B"):
        if field in result:
            result[field] = [[float(F(value)) for value in row] for row in result[field]]
    for field in ("power_H", "power_V"):
        total = sum((F(value) for row in recipe[field] for value in row), F(0))
        if total != 1:
            raise ValueError("public source profile is not exactly normalized: "+field)
    return result


def source_statistics(state, Q, uA, uB):
    collected = ({}, {})
    powers = {"AH": 0., "AV": 0., "BH": 0., "BV": 0.}
    for (ap, pa, ai, bp, pb, bi), z in state.items():
        power = abs(z)**2
        if ap == 0:
            powers["AH" if pa == 0 else "AV"] += Q*uA*power
        if bp == 0:
            powers["BH" if pb == 0 else "BV"] += Q*uB*power
        if ap == bp == 0:
            if pa != pb:
                raise ValueError("source representative is outside HH/VV support")
            collected[pa][(ai, bi)] = z
    scale = Q*uA*uB
    H = scale*math.fsum(abs(z)**2 for z in collected[0].values())
    V = scale*math.fsum(abs(z)**2 for z in collected[1].values())
    X = scale*sum(z*collected[1].get(label, 0j).conjugate() for label, z in collected[0].items()).real
    return {"H": H, "V": V, "X": X, **powers}


def named_rates(signal, model, background):
    bA, bB = background
    result = {"j": [], "sA_cell": [], "sB_cell": []}
    for pA, pB, pJ in zip(signal["sA_cell"], signal["sB_cell"], signal["j"]):
        if model == "S1_signal":
            sA, sB, j = pA+bA, pB+bB, pJ
        elif model == "independent_OR":
            fA, fB = 1-bA, 1-bB
            sA, sB = bA+fA*pA, bB+fB*pB
            j = fA*fB*pJ+bA*fB*pB+bB*fA*pA+bA*bB
        elif model == "named_M3":
            sA, sB = pA+bA, pB+bB
            j = pJ+sA*sB
        else:
            raise ValueError("unrecognized public rate model")
        result["j"].append(j)
        result["sA_cell"].append(sA)
        result["sB_cell"].append(sB)
    return result


def forward_member(member, model, background, angles, source):
    power_H, power_V = F(member["preparation_power_H"]), F(member["preparation_power_V"])
    if min(power_H, power_V) < 0 or power_H+power_V != 1:
        raise ValueError("normalized preparation powers required")
    Q, uA, uB = (float(F(member[name])) for name in ("Q", "uA", "uB"))
    if any(not 0 <= value <= 1 for value in (Q, uA, uB)):
        raise ValueError("invalid Bernoulli source or postcollection efficiency")
    # Relative signs/phases belong to the recipe; preparation powers are positive.
    state = source.state_from_preparation(numeric_recipe(member["recipe"]),
                                          (math.sqrt(float(power_H)), math.sqrt(float(power_V))))
    a0, a1, b0, b1 = angles
    signal = {"j": [], "sA_cell": [], "sB_cell": []}
    for a, b in ORDER:
        setting_a = (0.5-(a0, a1)[a]/180, 0.)
        setting_b = (0.5-(b0, b1)[b]/180, 0.)
        values = source.amplitude_read(state, setting_a, setting_b, Q, uA, uB)
        signal["j"].append(values["j"])
        signal["sA_cell"].append(values["sA"])
        signal["sB_cell"].append(values["sB"])
    statistics = source_statistics(state, Q, uA, uB)
    norm = math.fsum(abs(value)**2 for value in state.values())
    return signal, named_rates(signal, model, background), statistics, norm


def bounds(interval):
    lower, upper = F(interval["exact_lower"]), F(interval["exact_upper"])
    if lower > upper:
        raise ValueError("reversed public interval")
    return lower, upper


def point_inside(interval, value):
    lower, upper = bounds(interval)
    return lower <= F(value) <= upper


def envelope_subset(inner, outer):
    lower, upper = bounds(inner)
    outer_lower, outer_upper = bounds(outer)
    return outer_lower <= lower and upper <= outer_upper


def check_report(report_path):
    code_freeze = executable_freeze()
    spec = specification()
    source = native_source()
    report_bytes = report_path.read_bytes()
    report = json.loads(report_bytes)
    if not report["schema"].startswith("p23-public-observable-comparison/"):
        raise ValueError("public comparison schema required")
    if sorted(branch["model"] for branch in report["branches"]) != sorted(spec["models"]):
        raise ValueError("all three named rate models are required exactly once")
    confidence = report["common_mean_confidence"]
    for field in ("j", "sA_cell", "sB_cell"):
        if len(confidence[field]) != 4:
            raise ValueError("four confidence cells are required: "+field)
    angles = [float(F(value)) for value in spec["angles_deg"][0]]
    tolerance = float(F(spec["probability_tolerance"]))
    branches = []
    for branch in report["branches"]:
        model = branch["model"]
        member = branch["source_member"]
        background = [float(F(value)) for value in branch["background"]]
        signal, actual, statistics, norm = forward_member(member, model, background, angles, source)
        theory = branch["forward_probability_enclosures"]
        for field in ("j", "sA_cell", "sB_cell"):
            if len(theory[field]) != 4:
                raise ValueError("four theoretical cells are required: "+field)
        # These three relations are distinct; a wide enclosure does not locate
        # a true point outside the confidence region.
        actual_in_confidence = {name: [point_inside(interval, value) for interval, value in zip(confidence[name], actual[name])]
                                for name in ("j", "sA_cell", "sB_cell")}
        theory_in_confidence = {name: [envelope_subset(interval, outer) for interval, outer in zip(theory[name], confidence[name])]
                                for name in ("j", "sA_cell", "sB_cell")}
        actual_in_theory = {name: [point_inside(interval, value) for interval, value in zip(theory[name], actual[name])]
                            for name in ("j", "sA_cell", "sB_cell")}
        expected = member["statistics"]
        statistic_errors = {name: abs(value-float(F(expected[name]))) for name, value in statistics.items()}
        H, V, X, AH, AV, BH, BV = (statistics[name] for name in ("H", "V", "X", "AH", "AV", "BH", "BV"))
        loss = [AH, AV, BH, BV, AH-H, BH-H, AV-V, BV-V, 1-(AH+BH-H+AV+BV-V)]
        source_checks = {"norm": abs(norm-1) <= tolerance, "source_statistics": max(statistic_errors.values()) <= tolerance,
                         "PSD": min(H, V, H*V-X*X) >= -tolerance, "loss": min(loss) >= -tolerance}
        flatten = lambda values: all(value for row in values.values() for value in row)
        branches.append({"model": model, "signal_rates": signal, "actual_float_rates": actual,
                         "source_gram": {name: statistics[name] for name in ("H", "V", "X")},
                         "complete_source_statistics": statistics, "source_statistic_errors": statistic_errors,
                         "source_norm": norm, "loss_slacks": loss, "source_checks": source_checks,
                         "actual_float_in_confidence": actual_in_confidence,
                         "theory_envelope_subset_confidence": theory_in_confidence,
                         "actual_float_in_theory_envelope": actual_in_theory,
                         "independent_forward_validation_passed": all(source_checks.values()) and flatten(actual_in_theory),
                         "exact_interval_membership_certified": flatten(theory_in_confidence),
                         "floating_point_membership_check": flatten(actual_in_confidence)})
    if hashlib.sha256(report_path.read_bytes()).hexdigest() != hashlib.sha256(report_bytes).hexdigest():
        raise ValueError("public source report changed during validation")
    return {"schema": "p23-public-witness-independent/v1", "input_version": report["version"],
            "executable_freeze": code_freeze,
            "report_sha256": hashlib.sha256(report_bytes).hexdigest(),
            "bindings": {"member_report": hashlib.sha256(report_bytes).hexdigest(),
                         str(CRITERION.relative_to(ROOT)): digest(CRITERION),
                         str((CS/"independent.py").relative_to(ROOT)): SOURCE_SHA,
                         str(Path(__file__).relative_to(ROOT)): digest(Path(__file__))},
            "branches": branches, "source_mapping_identified": False,
            "publication_configuration_identified": False, "production_admitted": False,
            "statistical_verdict_enabled": False, "bell_event_files_read": 0,
            "primitive": "original CS state_from_preparation and full-modal amplitude_read; supplied member recipe only",
            "interval_check_scope": "exact containment of supplied theoretical rational enclosures; floating replication is an independent implementation check",
            "passed_scope": "independent full-modal forward replication and containment in supplied theory enclosures",
            "passed": all(row["independent_forward_validation_passed"] for row in branches)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report_path", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = check_report(args.report_path)
    if args.output is not None:
        args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False)+"\n")
    print(json.dumps({"independent_forward_passed": result["passed"], "branches": [
        {"model": row["model"], "float_in_confidence": row["floating_point_membership_check"],
         "envelope_subset_confidence": row["exact_interval_membership_certified"],
         "float_in_theory": row["independent_forward_validation_passed"]} for row in result["branches"]]}))
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
