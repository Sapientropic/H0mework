"""Consume source-coupled joint gain caps and the complete identity fibre."""
import argparse
from pathlib import Path
import subprocess

import joint_response_independent as independent
import joint_response_run as science
import shared_response_verify as previous
import verify as parent
from run import exclusive_json


BASE, ROOT = parent.BASE, parent.ROOT
SCHEMA = "stage10-munich-joint-response-evidence/v1"
FIRSTS = ("joint-response-first.json", "joint-response-independent-first.json")
NEGATIVE = ("new_confidence_budget_spent", "fixed_law_point_used_as_confidence_bound",
            "hardware_parameter_uniqueness_certified", "actual_ideal_label_identity_selected",
            "actual_gain_extremum_sharpness_claimed", "profile_pass_used_as_full_source_membership",
            "source_theorem_changed", "optimizer_executed", "new_statistical_fit_executed")


def validate(primary, checked, counts, biases, shared, primitive):
    parent.require(primary.get("schema") == "stage10-munich-joint-response-primary/v1" and
                   checked.get("schema") == "stage10-munich-joint-response-independent/v1" and
                   primary.get("version") == checked.get("version") == science.VERSION and
                   checked.get("evidence_valid") is True, "joint_response_receipt_identity")
    parent.require(primary.get("status") == "generated_joint_response_parent_confidence_qualification", "joint_response_primary_failed")
    for report in (primary, checked):
        parent.require(report.get("joint_response_profile_certified") is True and
                       report.get("whole_empirical_confidence_set_bounds") is True and
                       report.get("parent_confidence_budget") == "1/20" and
                       report.get("profile_threshold_bracket_precision") == "1/68719476736" and
                       report.get("full_component_threshold") == "80", "joint_response_contract_changed")
        parent.require(all(report.get(name) is False for name in NEGATIVE), "joint_response_scope_promoted")
        parent.require(type(report.get("trial_event_files_read")) is int and report["trial_event_files_read"] == 0,
                       "joint_response_event_access")
    rebuilt = independent.verify_report(primary, counts, biases, shared, primitive)
    names = ("runs", "profile_brackets_checked", "endpoints_checked", "context_likelihood_checks",
             "controls_checked", "control_context_likelihood_checks", "individual_projection_lookalikes_excluded",
             "lawful_witness_controls_not_excluded")
    parent.require(all(checked[name] == rebuilt[name] for name in names), "joint_response_independent_result_changed")
    parent.require(rebuilt["profile_brackets_checked"] == 6 and rebuilt["endpoints_checked"] == 12 and
                   rebuilt["context_likelihood_checks"] == 96 and rebuilt["controls_checked"] == 4 and
                   rebuilt["control_context_likelihood_checks"] == 32 and
                   rebuilt["lawful_witness_controls_not_excluded"] == 2, "joint_response_coverage_incomplete")
    return rebuilt


def generate():
    science.source_review()
    # cp0002 consumes cp0001, which consumes the complete identification certificate.
    admitted = previous.consume()
    parent.require(admitted["parent_joint_adjudication_preserved"] is True, "joint_response_original_joint_lost")
    identity = parent.strict_json(parent.frozen(BASE / "identification-verification.json"))
    identity_fields = ("maximal_observable_quotient_certified", "registered_regular_law_fibers_complete",
                       "continuous_equivalent_hardware_certified", "isotropic_nonuniqueness_preserves_axes")
    parent.require(identity["evidence_valid"] is True and all(identity.get(name) is True for name in identity_fields) and
                   identity["hardware_parameter_uniqueness_certified"] is False and
                   identity["actual_hardware_identity_claimed"] is False, "joint_response_identity_fibre_changed")
    primary, checked = (parent.strict_json(parent.frozen(BASE / name)) for name in FIRSTS)
    commit = primary["freeze_commit"]
    bindings = science.frozen_bindings(commit)
    for report, attempt_name in ((primary, "joint-response-attempt.json"), (checked, "joint-response-independent-attempt.json")):
        raw = parent.frozen(BASE / attempt_name)
        attempt = parent.strict_json(raw)
        parent.require(report["attempt_sha256"] == parent.sha256(raw) and
                       report["source_bindings"] == attempt["source_bindings"] == bindings and
                       report["freeze_commit"] == attempt["freeze_commit"] == commit and
                       report["execution_head"] == attempt["execution_head"], "joint_response_attempt_identity_changed")
        ancestor = subprocess.run(["git", "merge-base", "--is-ancestor", commit, report["execution_head"]],
                                  cwd=ROOT, capture_output=True)
        parent.require(ancestor.returncode == 0, "joint_response_not_frozen_before_execution")
        parent.require(report["source_kernel_sha256"] == parent.sha256(parent.frozen(BASE / "response-bounds-certification-first.json")) and
                       report["previous_shared_certificate_sha256"] == parent.sha256(parent.frozen(BASE / "shared-response-verification.json")),
                       "joint_response_paid_source_changed")
    parent.require(checked["primary_receipt_sha256"] == parent.sha256(parent.frozen(BASE / FIRSTS[0])), "joint_response_primary_identity_changed")
    counts, biases, shared, primitive = (parent.strict_json(parent.frozen(BASE / name)) for name in
                                        ("primary-first-c0002.json", "identification-first.json",
                                         "shared-response-first.json", "primitive-witness-c0002.json"))
    rebuilt = validate(primary, checked, counts, biases, shared, primitive)
    return {**rebuilt, "schema": SCHEMA, "criterion_version": science.VERSION, "evidence_valid": True,
            "status": "certified_joint_response_qualification_and_identity_fibre",
            "joint_response_profile_certified": True, "joint_hardware_necessary_qualification_certified": True,
            "parent_joint_adjudication_preserved": True, "old_cp0002_envelopes_preserved": True,
            **{name: identity[name] for name in identity_fields},
            "identity_resolution": "complete_observable_quotient_and_registered_regular_equivalence_fibres",
            "whole_empirical_confidence_set_bounds": True, "parent_confidence_budget": "1/20",
            "full_component_threshold": "80", **{name: False for name in NEGATIVE},
            "controller_advance": False, "trial_event_files_read_at_intake": 0, "new_science_executed_at_intake": 0,
            "source_bindings": [parent.binding(BASE / name) for name in
                                ("criterion-cp0003.md", "joint_response_verify.py", "joint-response-audit.json",
                                 "identification-verification.json", "shared-response-verification.json", *FIRSTS)]}


def consume(certificate=None):
    result = generate()
    path = BASE / "joint-response-verification.json" if certificate is None else Path(certificate)
    parent.require(parent.canonical(result) == parent.canonical(parent.strict_json(path.read_bytes())), "joint_response_certificate_changed")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--certificate", type=Path)
    args = parser.parse_args()
    try:
        result = consume(args.certificate) if args.check_only else generate()
        if not args.check_only:
            parent.require(args.certificate is None, "joint_response_override_is_consume_only")
            exclusive_json(BASE / "joint-response-verification.json", result)
        print(parent.canonical(result))
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print(parent.canonical({"schema": SCHEMA, "evidence_valid": False, "reason": str(error)}))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
