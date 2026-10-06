#!/usr/bin/env python3
"""Public exposure intervals and full-trial source-normalized confidence inversion."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from functools import lru_cache
import hashlib
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
MW = HERE.parent / "multi-window"
VERSION = "p23-public-source-compression-sc0001"


def require(value, reason):
    if not value:
        raise ValueError(reason)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    sys.modules[name] = result
    spec.loader.exec_module(result)
    return result


public = module("_sc_public_arithmetic", MW / "primary.py")
I = public.I


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def frozen(path):
    path = Path(path).resolve()
    require(path.is_relative_to(ROOT), "foreign_source")
    relative = path.relative_to(ROOT).as_posix()
    commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", relative], cwd=ROOT, text=True).strip()
    require(commit and subprocess.check_output(["git", "show", commit + ":" + relative], cwd=ROOT) == path.read_bytes(),
            "unfrozen_source:" + relative)
    return {"path": relative, "commit": commit, "sha256": sha(path)}


@lru_cache(maxsize=1)
def configuration():
    text = (HERE / "criterion.md").read_text()
    blocks = re.findall(r"<!-- SOURCE-COMPRESSION-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- SOURCE-COMPRESSION-FROZEN-END -->", text, re.S)
    require(len(blocks) == 1, "nonunique_contract")
    c = json.loads(blocks[0])
    require(c["version"] == VERSION and c["alpha_total"] == "1/20" and c["old_CI_count"] == 72
            and c["old_inverse_delta"] == 2516505600 and c["old_bets_per_CI"] == 40
            and c["new_budget_split"] == "1/2" and c["epsilon"] == "3/1000"
            and c["public_family_size"] == 24 and c["spacelike_pulse_counts"] == [1, 3, 5, 7]
            and c["setting_count"] == 4 and c["bet_powers"] == [1, 20]
            and c["conditional_features"] == ["both", "onlyA", "onlyB", "neither", "singleA", "singleB"],
            "statistical_contract_changed")
    manifest = json.loads((HERE / "sources.json").read_text())
    require(manifest["version"] == VERSION, "source_version_changed")
    for item in manifest["inputs"]:
        require(sha(ROOT / item["path"]) == item["sha256"], "input_binding_changed:" + item["path"])
    public.stats.arithmetic.PRECISION = 10 ** c["decimal_precision"]
    return c


def budget():
    c = configuration()
    alpha = F(c["alpha_total"])
    old = F(c["old_CI_count"] * c["old_bets_per_CI"], c["old_inverse_delta"])
    new = (alpha - old) * F(c["new_budget_split"])
    require(new > 0 and old + 2 * new == alpha, "invalid_joint_coverage_allocation")
    return {"alpha_total": alpha, "old_CI_failure_upper": old, "alpha_contrast": new,
            "alpha_conditional": new, "contrast_threshold": F(c["public_family_size"]) / new,
            "conditional_inverse_delta": F(c["public_family_size"] * 4 * 6 * 40) / new}


@lru_cache(maxsize=200)
def elementary(value, operation):
    return public.decimal_bound(F(value), operation, configuration()["decimal_precision"])


def log_interval(value):
    require(value.lo > 0, "log_interval_not_positive")
    return I(elementary(value.lo, "ln").lo, elementary(value.hi, "ln").hi)


def shifted_exp(value):
    if value.hi < -256:
        return I(0, F(1, 10 ** 80))
    return I(elementary(value.lo, "exp").lo, elementary(value.hi, "exp").hi)


def envelope(count, trials, inverse_delta):
    require(type(count) is int and type(trials) is int and 0 <= count <= trials and trials > 0,
            "invalid_conditional_count")
    logarithm = elementary(inverse_delta, "ln")
    lo, hi, grid = F(0), F(trials), []
    for power in range(1, 21):
        for sign in (1, -1):
            lam = F(sign, 2 ** power)
            bound = (lam * count - logarithm) / (elementary(lam, "exp") - 1)
            if sign > 0:
                lo = max(lo, bound.lo)
            else:
                hi = min(hi, bound.hi)
            grid.append({"lambda": lam, "bound_expected_count": bound})
    require(lo <= hi, "conditional_confidence_empty")
    return I(lo, hi) / trials, grid


def fixed_bets(win, loss):
    eps = F(configuration()["epsilon"])
    lower, upper = ((1 - eps) / 2) ** 2, ((1 + eps) / 2) ** 2
    rho, q0 = lower / upper, upper / (lower + upper)
    result = []
    for power in range(1, 21):
        t = F(1, 2 ** power)
        a, b = 1 + rho * t, 1 - t
        result.append({"power": power, "a": a, "b": b,
                       "base_log_e": win * elementary(a, "ln") + loss * elementary(b, "ln")})
    return q0, result


def normalized_log_e(h, trials, bets):
    h = F(h)
    require(-1 <= h <= 1 and type(trials) is int and trials > 0, "source_h_domain")
    values = [row["base_log_e"] - trials * elementary(1 + h / 2 ** row["power"], "ln") for row in bets]
    # Only nonpositive shifted exponentials are evaluated, including at physical boundaries.
    shift = max(value.hi for value in values)
    total = sum((shifted_exp(value - shift) for value in values), I.point(0)) / len(values)
    return shift + log_interval(total)


def invert(trials, bets, threshold):
    log_threshold = elementary(threshold, "ln")
    lo, hi = F(-1), F(1)
    lower = normalized_log_e(lo, trials, bets)
    upper = normalized_log_e(hi, trials, bets)
    require(lower.lo > log_threshold.hi and upper.hi <= log_threshold.lo, "inversion_bracket_not_certified")
    steps = 0
    for _ in range(configuration()["bisection_steps"]):
        mid = (lo + hi) / 2
        value = normalized_log_e(mid, trials, bets)
        if value.lo > log_threshold.hi:
            lo, lower = mid, value
        elif value.hi <= log_threshold.lo:
            hi, upper = mid, value
        else:
            break
        steps += 1
    return {"lower": lo, "upper": hi, "log_e_at_lower": lower, "log_e_at_upper": upper,
            "log_threshold": log_threshold, "lower_rejected": True, "upper_not_rejected": True,
            "steps": steps}


def input_records():
    c = configuration()
    old = json.loads((MW / "primary-first.json").read_text())
    result = []
    for run in old["runs"]:
        for group in run["groups"]:
            n = group["pulse_count"]
            if n not in c["spacelike_pulse_counts"]:
                continue
            counts = group["counts"]
            total = public.validate_counts(counts)
            settings = [sum(row) for row in counts]
            require(total == group["complete_trials"] == run["complete_trials"]
                    and settings == group["setting_trial_totals"]
                    and group["paper_pulse_numbers"] == [int(v) + 1 for v in group["sheet"]], "public_count_identity_changed")
            result.append({"identity": {"workbook": run["workbook"], "pulse_count": n,
                                        "pulse_indices": group["paper_pulse_numbers"]},
                           "total_trials": total, "setting_trials": settings, "counts": counts})
    require(len(result) == 24, "public_family_incomplete")
    return result


def conditional_events(row):
    require(len(row) == 4 and all(type(n) is int and n >= 0 for n in row), "outcome_table_invalid")
    return row + [row[0] + row[1], row[0] + row[2]]


def generate():
    c, allocation = configuration(), budget()
    bindings = [frozen(HERE / name) for name in ("criterion.md", "sources.json", "compress.py")]
    result = []
    for record in input_records():
        tables = []
        for row, trials in zip(record["counts"], record["setting_trials"]):
            features = []
            for name, count in zip(c["conditional_features"], conditional_events(row)):
                interval, grid = envelope(count, trials, allocation["conditional_inverse_delta"])
                features.append({"feature": name, "count": count, "trials": trials,
                                 "interval": interval, "grid": grid})
            tables.append(features)
        counts = record["counts"]
        win, loss = counts[0][0], counts[1][1] + counts[2][2] + counts[3][0]
        q0, bets = fixed_bets(win, loss)
        result.append({**record, "conditional": tables,
                       "contrast": {"win_count": win, "loss_count": loss, "old_q0": q0,
                                    "fixed_bets": bets, "h_bracket": invert(record["total_trials"], bets, allocation["contrast_threshold"])}})
        print(json.dumps({"statistics_record": len(result), **record["identity"]}), flush=True)
    return {"schema": "p23-source-compression-statistics/v1", "version": VERSION,
            "implementation": "primary", "bindings": bindings, "budget": allocation, "records": result,
            "conditional_source_law_required": True, "setting_can_depend_on_past": True,
            "joint_95_coverage_budget_paid": True, "original_CI_modified": False,
            "actual_hardware_identity_claimed": False, "bell_event_files_read": 0}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    require(not args.output.exists(), "first_receipt_already_exists")
    started = time.monotonic()
    result = generate()
    raw = json.dumps(public.pack(result), indent=2, sort_keys=True, allow_nan=False).encode() + b"\n"
    args.output.write_bytes(lzma.compress(raw, preset=6))
    print(json.dumps({"output": str(args.output), "sha256": sha(args.output),
                      "logical_sha256": hashlib.sha256(raw).hexdigest(), "records": len(result["records"]),
                      "conditional_intervals": 576, "runtime_seconds": time.monotonic() - started}))


if __name__ == "__main__":
    main()
