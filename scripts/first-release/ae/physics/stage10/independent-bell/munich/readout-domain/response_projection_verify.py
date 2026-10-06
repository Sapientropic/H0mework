"""Consume whole-parent-CS response envelopes without generating new endpoints."""
import argparse
from pathlib import Path
import subprocess

import identify_verify as identification
import response_projection_independent as independent
import response_projection_run as science
import verify as parent
from run import exclusive_json


BASE, ROOT = parent.BASE, parent.ROOT
SCHEMA = "stage10-munich-readout-response-projection-evidence/v1"
FIRSTS = ("response-projection-first.json", "response-projection-independent-first.json")


def validate(primary, checked, counts, biases):
    parent.require(primary.get("schema") == "stage10-munich-readout-response-projection-primary/v1" and
                   checked.get("schema") == "stage10-munich-readout-response-projection-independent/v1", "response_projection_schema")
    parent.require(primary.get("version") == checked.get("version") == science.VERSION and
                   checked.get("evidence_valid") is True, "response_projection_not_certified")
    parent.require(primary.get("status") == "generated_parent_confidence_response_envelopes", "response_projection_primary_failed")
    for report in (primary, checked):
        parent.require(report.get("whole_empirical_confidence_set_bounds") is True and
                       report.get("simultaneous_necessary_outer_projections") is True and
                       report.get("parent_confidence_budget") == "1/20" and
                       report.get("full_component_threshold") == "80", "response_projection_contract_changed")
        parent.require(report.get("new_confidence_budget_spent") is False and
                       report.get("fixed_law_point_used_as_confidence_bound") is False and
                       report.get("hardware_parameter_uniqueness_certified") is False,
                       "response_projection_scope_promoted")
        parent.require(type(report.get("trial_event_files_read")) is int and report["trial_event_files_read"] == 0,
                       "response_projection_event_access")
    parent.require(primary.get("optimizer_executed") is False and primary.get("new_statistical_fit_executed") is False and
                   checked.get("source_optimizer_executed") is False, "response_projection_repeated_science")
    rebuilt = independent.verify_report(primary, counts, biases)
    for key in ("runs", "correlation_envelopes_checked", "response_envelopes_checked"):
        parent.require(checked[key] == rebuilt[key], "response_projection_independent_result_changed")
    parent.require(rebuilt["correlation_envelopes_checked"] == 16 and rebuilt["response_envelopes_checked"] == 8,
                   "response_projection_incomplete")
    return rebuilt


def generate():
    import response_bounds_certify
    kernel = response_bounds_certify.consume()
    admitted = identification.consume()
    primary, checked = (parent.strict_json(parent.frozen(BASE / name)) for name in FIRSTS)
    for report, attempt_name in ((primary, "response-projection-attempt.json"),
                                 (checked, "response-projection-independent-attempt.json")):
        raw = parent.frozen(BASE / attempt_name)
        attempt = parent.strict_json(raw)
        parent.require(report["attempt_sha256"] == parent.sha256(raw) and
                       report["source_bindings"] == attempt["source_bindings"], "response_projection_attempt_changed")
        provenance = report if attempt_name == "response-projection-attempt.json" else report["provenance"]
        attempt_provenance = attempt if attempt_name == "response-projection-attempt.json" else attempt["provenance"]
        commit, head = provenance["freeze_commit"], provenance["execution_head"]
        parent.require(commit == attempt_provenance["freeze_commit"] and head == attempt_provenance["execution_head"],
                       "response_projection_attempt_provenance")
        ancestor = subprocess.run(["git", "merge-base", "--is-ancestor", commit, head], cwd=ROOT, capture_output=True)
        parent.require(ancestor.returncode == 0 and report["source_bindings"] == science.frozen_bindings(commit),
                       "response_projection_freeze_or_source_changed")
    parent.require(primary["kernel_sha256"] == parent.sha256(parent.frozen(BASE / "response-bounds-certification-first.json")) and
                   primary["parent_identification_sha256"] == parent.sha256(parent.frozen(BASE / "identification-verification.json")) and
                   checked["parent_counts_sha256"] == parent.sha256(parent.frozen(BASE / "primary-first-c0002.json")) and
                   checked["parent_biases_sha256"] == parent.sha256(parent.frozen(BASE / "identification-first.json")),
                   "response_projection_source_identity_changed")
    parent.require(primary["freeze_commit"] == checked["provenance"]["freeze_commit"] and
                   checked["primary_receipt_sha256"] == parent.sha256(parent.frozen(BASE / FIRSTS[0])),
                   "response_projection_primary_identity_changed")
    counts = parent.strict_json(parent.frozen(BASE / "primary-first-c0002.json"))
    biases = parent.strict_json(parent.frozen(BASE / "identification-first.json"))
    rebuilt = validate(primary, checked, counts, biases)
    return {**rebuilt, "schema": SCHEMA, "criterion_version": science.VERSION, "evidence_valid": True,
            "status": "certified_parent_confidence_hardware_envelopes",
            "parent_confidence_hardware_envelopes_certified": True,
            "simultaneous_necessary_outer_projections": True, "whole_empirical_confidence_set_bounds": True,
            "parent_joint_adjudication_preserved": admitted["parent_joint_adjudication_preserved"],
            "hardware_parameter_uniqueness_certified": False, "fixed_law_point_used_as_confidence_bound": False,
            "parent_confidence_budget": "1/20", "new_confidence_budget_spent": False,
            "controller_advance": False, "trial_event_files_read_at_intake": 0, "new_science_executed_at_intake": 0,
            "explicit_declarations": len(kernel["explicit_declarations"]),
            "source_bindings": [parent.binding(BASE / name) for name in
                                ("criterion-cp0001.md", "response_projection_verify.py", "response-bounds-certification-first.json", *FIRSTS)]}


def consume(certificate=None):
    result = generate()
    path = BASE / "response-projection-verification.json" if certificate is None else Path(certificate)
    parent.require(parent.canonical(result) == parent.canonical(parent.strict_json(path.read_bytes())), "response_projection_certificate_changed")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--certificate", type=Path)
    args = parser.parse_args()
    try:
        result = consume(args.certificate) if args.check_only else generate()
        if not args.check_only:
            parent.require(args.certificate is None, "response_projection_override_is_consume_only")
            exclusive_json(BASE / "response-projection-verification.json", result)
        print(parent.canonical(result))
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(parent.canonical({"schema": SCHEMA, "evidence_valid": False, "reason": str(error)}))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
