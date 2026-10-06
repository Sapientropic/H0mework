"""Consume frozen shared-response profiles and source-coupled error bounds."""
import argparse
from pathlib import Path
import subprocess

import response_projection_verify as previous
import shared_response_independent as independent
import shared_response_run as science
import verify as parent
from run import exclusive_json


BASE, ROOT = parent.BASE, parent.ROOT
SCHEMA = "stage10-munich-shared-response-evidence/v1"
FIRSTS = ("shared-response-first.json", "shared-response-independent-first.json")


def validate(primary, checked, counts, biases, legacy):
    parent.require(primary.get("schema") == "stage10-munich-shared-response-primary/v1" and
                   checked.get("schema") == "stage10-munich-shared-response-independent/v1" and
                   primary.get("version") == checked.get("version") == science.VERSION and
                   checked.get("evidence_valid") is True, "shared_response_receipt_identity")
    parent.require(primary.get("status") == "generated_shared_response_parent_confidence_bounds", "shared_response_primary_failed")
    for report in (primary, checked):
        parent.require(report.get("shared_response_profile_certified") is True and
                       report.get("whole_empirical_confidence_set_bounds") is True and
                       report.get("parent_confidence_budget") == "1/20" and
                       report.get("profile_threshold_bracket_precision") == "1/68719476736" and
                       report.get("full_component_threshold") == "80", "shared_response_contract_changed")
        for name in ("new_confidence_budget_spent", "fixed_law_point_used_as_confidence_bound",
                     "hardware_parameter_uniqueness_certified", "actual_gain_extremum_sharpness_claimed",
                     "source_theorem_changed", "optimizer_executed", "new_statistical_fit_executed"):
            parent.require(report.get(name) is False, "shared_response_scope_promoted")
        parent.require(type(report.get("trial_event_files_read")) is int and report["trial_event_files_read"] == 0,
                       "shared_response_event_access")
    rebuilt = independent.verify_report(primary, counts, biases, legacy)
    for name in ("runs", "shared_response_envelopes_checked", "shared_response_endpoints_checked",
                 "context_likelihood_checks", "strictly_improved_gain_count"):
        parent.require(checked[name] == rebuilt[name], "shared_response_independent_result_changed")
    parent.require(rebuilt["shared_response_envelopes_checked"] == 8 and rebuilt["shared_response_endpoints_checked"] == 16 and
                   rebuilt["context_likelihood_checks"] == 64 and
                   rebuilt["old_cp0001_envelopes_preserved_or_tightened"] is True, "shared_response_coverage_incomplete")
    return rebuilt


def generate():
    science.source_review()
    admitted = previous.consume()
    primary, checked = (parent.strict_json(parent.frozen(BASE / name)) for name in FIRSTS)
    commit = primary["freeze_commit"]
    bindings = science.frozen_bindings(commit)
    for report, attempt_name in ((primary, "shared-response-attempt.json"), (checked, "shared-response-independent-attempt.json")):
        raw = parent.frozen(BASE / attempt_name)
        attempt = parent.strict_json(raw)
        parent.require(report["attempt_sha256"] == parent.sha256(raw) and
                       report["source_bindings"] == attempt["source_bindings"] == bindings and
                       report["freeze_commit"] == attempt["freeze_commit"] == commit and
                       report["execution_head"] == attempt["execution_head"], "shared_response_attempt_identity_changed")
        ancestor = subprocess.run(["git", "merge-base", "--is-ancestor", commit, report["execution_head"]],
                                  cwd=ROOT, capture_output=True)
        parent.require(ancestor.returncode == 0, "shared_response_not_frozen_before_execution")
        parent.require(report["source_kernel_sha256"] == parent.sha256(parent.frozen(BASE / "response-bounds-certification-first.json")) and
                       report["previous_response_certificate_sha256"] == parent.sha256(parent.frozen(BASE / "response-projection-verification.json")),
                       "shared_response_paid_source_changed")
    parent.require(checked["primary_receipt_sha256"] == parent.sha256(parent.frozen(BASE / FIRSTS[0])), "shared_response_primary_identity_changed")
    counts = parent.strict_json(parent.frozen(BASE / "primary-first-c0002.json"))
    biases = parent.strict_json(parent.frozen(BASE / "identification-first.json"))
    legacy = parent.strict_json(parent.frozen(BASE / "response-projection-first.json"))
    rebuilt = validate(primary, checked, counts, biases, legacy)
    return {**rebuilt, "schema": SCHEMA, "criterion_version": science.VERSION, "evidence_valid": True,
            "status": "certified_shared_response_parent_confidence_bounds",
            "shared_response_profile_certified": True, "parent_confidence_hardware_envelopes_certified": True,
            "parent_joint_adjudication_preserved": admitted["parent_joint_adjudication_preserved"],
            "whole_empirical_confidence_set_bounds": True, "parent_confidence_budget": "1/20",
            "new_confidence_budget_spent": False, "hardware_parameter_uniqueness_certified": False,
            "fixed_law_point_used_as_confidence_bound": False, "actual_gain_extremum_sharpness_claimed": False,
            "controller_advance": False, "trial_event_files_read_at_intake": 0, "new_science_executed_at_intake": 0,
            "source_bindings": [parent.binding(BASE / name) for name in
                                ("criterion-cp0002.md", "shared_response_verify.py", "shared-response-audit.json", *FIRSTS)]}


def consume(certificate=None):
    result = generate()
    path = BASE / "shared-response-verification.json" if certificate is None else Path(certificate)
    parent.require(parent.canonical(result) == parent.canonical(parent.strict_json(path.read_bytes())), "shared_response_certificate_changed")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--certificate", type=Path)
    args = parser.parse_args()
    try:
        result = consume(args.certificate) if args.check_only else generate()
        if not args.check_only:
            parent.require(args.certificate is None, "shared_response_override_is_consume_only")
            exclusive_json(BASE / "shared-response-verification.json", result)
        print(parent.canonical(result))
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(parent.canonical({"schema": SCHEMA, "evidence_valid": False, "reason": str(error)}))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
