#!/usr/bin/env python3
"""Posterior comparison of the two frozen complete-trial contrast receipts."""

from __future__ import annotations

import argparse
import ast
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
VERSION = "p23-structured-contrast-sc0001.1"
CONTRACT_FREEZE = "b4114c8e818d788bfb3df8b804b086b651b259fd"
PRIMARY_INITIAL_FREEZE = "1a09029d51541f8e6259fb930c3aec4f1fb6e3dd"
PRIMARY_SUCCESSFUL_FREEZE = "337c370db781f34149d781b4650993cd95c931eb"
INDEPENDENT_FREEZE = "193c84708192631d0a76e5ca29aded290cf2e6a5"
FIRST_RECEIPT_HASHES = {
    "contrast.json": "030e1d5eb0d255099c30c57e6549b58c33872548cc0beace2ed330e78d2295ba",
    "independent.json": "8d4ea59ddcca4e3f402f4d2b626947c7d3654923d4a6d3c6d4d731efd24f36b2",
}
FLAGS = (
    "source_mapping_identified", "publication_configuration_identified", "production_admitted",
    "calibration_protocol_identified", "actual_source_failure_claimed", "kernel_closed_form_Born_identity",
)


def require(condition: bool, reason: str) -> None:
    if not condition:
        raise ValueError(reason)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical(value: object) -> str:
    return json.dumps(value, sort_keys=True, ensure_ascii=False, allow_nan=False, separators=(",", ":"))


def git_blob(path: Path, commit: str) -> bytes:
    relative = path.relative_to(ROOT).as_posix()
    return subprocess.check_output(["git", "show", f"{commit}:{relative}"], cwd=ROOT)


def frozen_source(path: Path, commit: str) -> None:
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=True)
    require(git_blob(path, commit) == path.read_bytes(), "frozen source differs: " + path.name)


def load_owned_module(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    require(spec is not None and spec.loader is not None, "owned implementation cannot be loaded")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def repair_scope_check() -> bool:
    path = HERE / "contrast.py"
    initial = ast.parse(git_blob(path, PRIMARY_INITIAL_FREEZE))
    successful = ast.parse(git_blob(path, PRIMARY_SUCCESSFUL_FREEZE))
    left = {node.name: node for node in initial.body if isinstance(node, ast.FunctionDef)}
    right = {node.name: node for node in successful.body if isinstance(node, ast.FunctionDef)}
    require(set(left) == set(right), "primary repair changed the function inventory")
    added = ast.parse("if value == 1:\n    return F(0), F(0)\n").body[0]
    require(ast.dump(right["logarithm"].body[2]) == ast.dump(added), "primary repair lacks the exact log-one branch")
    del right["logarithm"].body[2]
    successful.body = [node for node in successful.body if not isinstance(node, ast.FunctionDef) or node.name != "controls"]
    initial.body = [node for node in initial.body if not isinstance(node, ast.FunctionDef) or node.name != "controls"]
    require(ast.dump(initial) == ast.dump(successful), "primary scientific AST changed outside exact zero and positive controls")
    return True


def primary_interval(packet: dict) -> tuple[Fraction, Fraction]:
    require(isinstance(packet, dict), "primary log enclosure is not an object")
    lo, hi = Fraction(packet["exact_lower"]), Fraction(packet["exact_upper"])
    require(lo <= hi, "primary rational log enclosure is reversed")
    return lo, hi


def independent_interval(packet: dict) -> tuple[Fraction, Fraction]:
    require(isinstance(packet, dict), "independent log enclosure is not an object")
    lo, hi = Fraction(packet["lo"]), Fraction(packet["hi"])
    require(lo <= hi, "independent outward log enclosure is reversed")
    return lo, hi


def overlap(left: tuple[Fraction, Fraction], right: tuple[Fraction, Fraction]) -> bool:
    return max(left[0], right[0]) <= min(left[1], right[1])


def row_key(row: dict, model_field: str) -> tuple[str, int, int]:
    require(isinstance(row, dict) and isinstance(row.get(model_field), str), "contrast row model is missing")
    require(type(row.get("cell")) is int and type(row.get("lambda_exponent")) is int, "contrast grid coordinates need integer identity")
    return row[model_field], row["cell"], row["lambda_exponent"]


def row_map(rows: list, model_field: str) -> dict:
    require(isinstance(rows, list), "contrast grid is not a list")
    indexed = {}
    for row in rows:
        key = row_key(row, model_field)
        require(key not in indexed, "duplicate contrast grid row")
        indexed[key] = row
    return indexed


def compare(directory: Path | None = None) -> dict:
    directory = HERE if directory is None else Path(directory).resolve()
    frozen_source(HERE / "criterion-sc0001.1.md", CONTRACT_FREEZE)
    frozen_source(HERE / "sources-sc0001.1.json", CONTRACT_FREEZE)
    frozen_source(HERE / "contrast.py", PRIMARY_SUCCESSFUL_FREEZE)
    frozen_source(HERE / "independent.py", INDEPENDENT_FREEZE)
    source_path = Path(__file__).resolve()
    source_commit = subprocess.check_output(
        ["git", "log", "-1", "--format=%H", "--", source_path.relative_to(ROOT).as_posix()],
        cwd=ROOT, text=True,
    ).strip()
    frozen_source(source_path, source_commit)
    receipts = {}
    for name, expected in FIRST_RECEIPT_HASHES.items():
        path = directory / name
        require(digest(path) == expected, "frozen first science receipt differs: " + name)
        receipts[name] = json.loads(path.read_text(encoding="utf-8"))
    primary, independent = receipts["contrast.json"], receipts["independent.json"]
    require(primary.get("schema") == "p23-structured-contrast-primary/v1", "primary receipt schema differs")
    require(independent.get("schema") == "p23-structured-contrast-independent/v1", "independent receipt schema differs")
    for report in (primary, independent):
        require(report.get("version") == VERSION, "receipt contract version differs")
        require(all(report.get(flag) is False for flag in FLAGS), "receipt asserts an unbound actual apparatus identity")
        require(report.get("retrospective") is True, "receipt loses retrospective identity")
        require(type(report.get("bell_event_files_read")) is int and report["bell_event_files_read"] == 0, "receipt accesses trial archives")
    require(primary.get("other_implementation_output_used_as_input") is False, "primary receipt used the other output as numerical input")
    require(primary.get("nominal_optimum_verdict_changed") is False, "contrast cannot change the nominal-optimum verdict")
    for flag in ("primary_implementation_imported", "primary_science_read_before_first_run", "comparison_to_primary_performed"):
        require(independent.get("method", {}).get(flag) is False, "independent first receipt changes its access identity")
    require(independent.get("combined_with_po0003_alpha") is False, "separate alpha allocations were combined")

    primary_module = load_owned_module("p23_structured_primary_posterior", "contrast.py")
    independent_module = load_owned_module("p23_structured_independent_posterior", "independent.py")
    fresh_primary = primary_module.generate()
    fresh_independent = independent_module.compute()
    require(canonical(primary) == canonical(fresh_primary), "primary first receipt differs from fresh owned science computation")
    require(canonical(independent) == canonical(fresh_independent), "independent first receipt differs from fresh owned science computation")
    spec, manifest = independent_module.specification()
    expected_bindings = {binding["path"]: binding["sha256"] for binding in manifest["inputs"]}
    for path in (HERE / "criterion-sc0001.1.md", HERE / "sources-sc0001.1.json"):
        expected_bindings[path.relative_to(ROOT).as_posix()] = digest(path)
    require(primary["bindings"] == expected_bindings, "primary manifest bindings are incomplete")
    require(primary["criterion_freeze"]["criterion_sha256"] == independent["source_bindings"]["criterion_sha256"], "criterion identities differ")
    require(primary["criterion_freeze"]["sources_sha256"] == independent["source_bindings"]["sources_sha256"], "source manifest identities differ")
    require(primary["executable_freeze"]["commit"] == PRIMARY_SUCCESSFUL_FREEZE, "primary successful executable freeze differs")
    require(primary["executable_freeze"]["sha256"] == digest(HERE / "contrast.py"), "primary executable binding differs")
    require(independent["source_bindings"]["program_sha256"] == digest(HERE / "independent.py"), "independent executable binding differs")
    require(independent["source_bindings"]["all_manifest_bindings_verified"] is True, "independent source binding verification is missing")
    require(type(independent["source_bindings"]["manifest_input_count"]) is int and independent["source_bindings"]["manifest_input_count"] == len(manifest["inputs"]), "independent input binding count differs")

    allocated = independent_module.budget(spec)
    require(type(primary["family_size"]) is int and primary["family_size"] == allocated["family"], "full family budgets differ")
    require(Fraction(primary["alpha"]) == Fraction(allocated["alpha"]), "alpha differs")
    require(Fraction(primary["per_process_delta"]) == Fraction(allocated["alpha"]) / allocated["family"], "per-process allocation differs")
    require(canonical(independent["budget"]) == canonical({**allocated, "threshold_log": independent["budget"]["threshold_log"]}), "independent full family metadata differs")
    primary_threshold = primary_interval(primary["log_threshold"])
    independent_threshold = independent_interval(independent["budget"]["threshold_log"])
    exact_threshold = independent_module.log_enclosure(Fraction(allocated["threshold"]))
    require(overlap(primary_threshold, independent_threshold), "displayed threshold log intervals do not overlap")
    require(overlap(primary_threshold, (exact_threshold.lo, exact_threshold.hi)), "exact threshold log intervals do not overlap")
    require(independent_threshold[0] <= primary_threshold[0] <= primary_threshold[1] <= independent_threshold[1], "primary threshold escapes independent outward display")

    indexed_primary = row_map(primary["rows"], "efficiency_model")
    indexed_independent = row_map(independent["results"], "model")
    expected_keys = {
        (name, cell, exponent)
        for name in spec["efficiency_ratios"]
        for cell in spec["mirror_cells"]
        for exponent in spec["lambda_exponents"]
    }
    require(set(indexed_primary) == set(indexed_independent) == expected_keys and len(expected_keys) == 120, "complete 120-row scientific grid differs")
    comparisons = []
    maximum_midpoint_gap = Fraction(0)
    for key in sorted(expected_keys):
        name, cell, exponent = key
        left, right = indexed_primary[key], indexed_independent[key]
        c, lam = Fraction(spec["efficiency_ratios"][name]), Fraction(1, 2**exponent)
        require(Fraction(left["c"]) == Fraction(right["c"]) == c and Fraction(left["lambda"]) == Fraction(right["lambda"]) == lam, "row uses a different frozen ratio or bet")
        require(left["counts"] == right["counts"] == independent["counts"][cell], "row uses different published complete outcomes")
        require(right["trial_factors"] == [str(factor) for factor in independent_module.outcome_factors(c, lam)], "independent row does not use shared ++ factor")
        require(right["decision_uses_exact_rational_bounds"] is True, "independent decision uses display rounding")
        primary_log = primary_interval(left["log_M"])
        displayed_independent_log = independent_interval(right["log_e_value"])
        exact_independent_log = independent_module.log_product(right["counts"], c, lam)
        exact_pair = (exact_independent_log.lo, exact_independent_log.hi)
        require(overlap(primary_log, exact_pair), "exact rational log intervals disagree at " + str(key))
        require(overlap(primary_log, displayed_independent_log), "displayed rational log intervals disagree at " + str(key))
        require(displayed_independent_log[0] <= primary_log[0] <= primary_log[1] <= displayed_independent_log[1], "primary interval escapes independent outward display at " + str(key))
        require(right["threshold_log"] == independent["budget"]["threshold_log"], "row threshold changes after model selection")
        primary_reject = primary_log[0] > primary_threshold[1]
        independent_reject = exact_independent_log.lo > exact_threshold.hi
        require(left["rejected"] is primary_reject and right["rejects_named_conditional_null"] is independent_reject, "stored row decision differs from its exact bound")
        require(primary_reject is independent_reject, "row rejection decisions disagree")
        expected_decision = "REJECT_NAMED_CONDITIONAL_NULL" if independent_reject else "NOT_REJECTED_AT_ALLOCATED_LEVEL"
        require(right["decision"] == expected_decision, "row conditional-null conclusion mouth differs")
        midpoint_gap = abs((primary_log[0] + primary_log[1] - exact_pair[0] - exact_pair[1]) / 2)
        maximum_midpoint_gap = max(maximum_midpoint_gap, midpoint_gap)
        comparisons.append({
            "efficiency_model": name, "cell": cell, "lambda_exponent": exponent,
            "exact_arithmetic_intervals_overlap": True,
            "primary_interval_contained_in_independent_outward_display": True,
            "frozen_ratios_counts_and_trial_factors_agree": True,
            "threshold_rejection_decisions_agree": True,
            "rejects_named_conditional_null": independent_reject,
        })

    summaries = {}
    for name, ratio in spec["efficiency_ratios"].items():
        selected = [row for row in comparisons if row["efficiency_model"] == name]
        rejected = any(row["rejects_named_conditional_null"] for row in selected)
        require(primary["summary"][name]["rejected"] is rejected and independent["by_model"][name]["rejects_named_conditional_null"] is rejected, "named-domain summary rejection differs")
        require(Fraction(primary["summary"][name]["worst_case_null_ratio"]) == Fraction(independent["by_model"][name]["c"]) == Fraction(ratio), "named-domain summary ratio differs")
        cells = []
        for cell in spec["mirror_cells"]:
            cell_rejected = any(row["rejects_named_conditional_null"] for row in selected if row["cell"] == cell)
            independent_cell = next(item for item in independent["by_model"][name]["cells"] if item["cell"] == cell)
            require(independent_cell["any_grid_rejects"] is cell_rejected and independent_cell["grid_size"] == 20 and independent_cell["summary_selection_is_paid_by_family_budget"] is True, "cell summary loses grid or budget identity")
            cells.append({"cell": cell, "rejects_named_conditional_null": cell_rejected, "lambda_grid_size": 20})
        best = max(
            (indexed_primary[key] for key in expected_keys if key[0] == name),
            key=lambda row: Fraction(row["log_M"]["exact_lower"]),
        )
        require(primary["summary"][name]["max_cell"] == best["cell"] and primary["summary"][name]["max_lambda_exponent"] == best["lambda_exponent"], "primary maximum summary differs from the paid full grid")
        require(primary["summary"][name]["max_log_M"] == best["log_M"], "primary maximum interval was altered")
        summaries[name] = {"c": ratio, "rejects_named_conditional_null": rejected, "cells": cells, "summary_selection_paid_by_full_budget": True}
    all_rejected = all(summary["rejects_named_conditional_null"] for summary in summaries.values())
    require(primary["all_named_mappings_rejected"] is all_rejected and independent["all_three_named_models_rejected"] is all_rejected, "whole-family summary differs")
    require(all(value is True for value in primary["controls"].values()), "primary mathematical control failed")
    require(all(value is True for value in independent["mathematical_controls"].values()), "independent mathematical control failed")
    repair_checked = repair_scope_check()
    return {
        "schema": "p23-structured-contrast-independent-comparison/v1",
        "version": VERSION,
        "status": "verified",
        "evidence_valid": True,
        "first_receipt_hashes": FIRST_RECEIPT_HASHES,
        "comparison_source": {"commit": source_commit, "sha256": digest(source_path)},
        "criterion_freeze": CONTRACT_FREEZE,
        "primary_initial_freeze": PRIMARY_INITIAL_FREEZE,
        "primary_successful_freeze": PRIMARY_SUCCESSFUL_FREEZE,
        "independent_freeze": INDEPENDENT_FREEZE,
        "source_bindings_verified": True,
        "fresh_owned_science_receipts_match": True,
        "full_grid_size": len(comparisons),
        "all_120_exact_log_intervals_compatible": True,
        "all_120_threshold_decisions_agree": True,
        "full_family_size": allocated["family"],
        "alpha": allocated["alpha"],
        "log_threshold": independent["budget"]["threshold_log"],
        "maximum_exact_midpoint_gap_outward_decimal_90": independent_module.outward_decimal(maximum_midpoint_gap, True, digits=90),
        "comparisons": comparisons,
        "by_model": summaries,
        "all_named_mappings_rejected": all_rejected,
        "primary_controls_count": len(primary["controls"]),
        "independent_controls_count": len(independent["mathematical_controls"]),
        "information_access": {
            "independent_first_read_primary_code_or_result": False,
            "primary_initial_execution_produced_complete_receipt": False,
            "primary_initial_execution_failure": "exact log(1) neighboring Decimal exponents could not be serialized as Fraction",
            "primary_repair_before_successful_run_seen_independent_statistical_summary": True,
            "primary_repair_scope": ["exact log(1)=0", "positive source-null controls"],
            "primary_scientific_AST_unchanged_outside_exact_zero_and_controls": repair_checked,
            "scientific_contract_data_family_or_bet_grid_changed_after_summary": False,
            "two_successful_first_receipts_mutually_blind": False,
            "other_output_used_as_numerical_input": False,
            "comparison_is_after_both_successful_first_receipts": True,
        },
        "conditional_null": independent["conditional_null"],
        "conclusion_scope": "named aligned scalar-efficiency and mirror local-count-law bridge",
        "retrospective": True,
        "bell_event_files_read": 0,
        "nominal_optimum_verdict_changed": False,
        "combined_with_po0003_alpha": False,
        **{flag: False for flag in FLAGS},
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path)
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    report = compare(args.directory)
    rendered = json.dumps(report, indent=2, ensure_ascii=False, allow_nan=False) + "\n"
    if args.check_only:
        print(rendered, end="")
    else:
        (HERE / "independent-comparison.json").write_text(rendered, encoding="utf-8")
        print(json.dumps({"status": report["status"], "full_grid_size": report["full_grid_size"]}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
