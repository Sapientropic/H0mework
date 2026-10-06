"""Consume complete continuous-fiber hardware-range certificates without optimization."""
import argparse
from pathlib import Path
import subprocess

import fiber_independent as independent
import fiber_run as science
import identify_verify as identification
import verify as parent
from run import exclusive_json


BASE, ROOT = parent.BASE, parent.ROOT
SCHEMA = "stage10-munich-readout-fiber-evidence/v1"
FIRSTS = ("fiber-first.json", "fiber-independent-first.json")


def validate(primary, checked, witness, counts):
    parent.require(primary.get("schema") == "stage10-munich-readout-fiber-primary/v1" and
                   checked.get("schema") == "stage10-munich-readout-fiber-independent/v1", "fiber_schema")
    parent.require(primary.get("version") == checked.get("version") == science.VERSION and
                   checked.get("evidence_valid") is True, "fiber_not_certified")
    parent.require(primary.get("status") == "certified_complete_fiber_hardware_ranges", "fiber_primary_failed")
    for report in (primary, checked):
        parent.require(report.get("uniform_fiber_coverage") is True and
                       report.get("gain_squared_optimality_gap") == "1/100000000", "fiber_coverage_changed")
        parent.require(report.get("whole_empirical_confidence_set_bounds") is False and
                       report.get("actual_hardware_uniquely_identified") is False and
                       report.get("new_confidence_budget_spent") is False, "fiber_scope_promoted")
        parent.require(type(report.get("trial_event_files_read")) is int and report["trial_event_files_read"] == 0,
                       "fiber_event_access")
    parent.require(primary.get("new_statistical_fit_executed") is False and
                   checked.get("source_optimizer_executed") is False, "fiber_repeated_science")
    rebuilt = independent.verify_report(primary, witness)
    for field in ("endpoints_checked", "hardware_ranges_checked", "runs"):
        parent.require(checked[field] == rebuilt[field], "fiber_independent_result_changed")
    parent.require(tuple(row["run"] for row in counts["runs"]) == parent.RUNS, "fiber_parent_family_changed")
    for p, c in zip(primary["runs"], counts["runs"]):
        parent.require(p["parent_prefixes_inherited"] == c["trials"] and
                       p["parent_factor_sequence_sha256"] == c["prefix_check"]["factor_sequence_sha256"],
                       "fiber_parent_prefix_identity_changed")
    return rebuilt


def generate():
    import fiber_certify
    kernel = fiber_certify.consume()
    admitted = identification.consume()
    p, i = (parent.strict_json(parent.frozen(BASE / name)) for name in FIRSTS)
    for report, attempt_name in ((p, "fiber-attempt.json"), (i, "fiber-independent-attempt.json")):
        raw = parent.frozen(BASE / attempt_name)
        attempt = parent.strict_json(raw)
        parent.require(report["attempt_sha256"] == parent.sha256(raw), "fiber_attempt_changed")
        parent.require(report["source_bindings"] == attempt["source_bindings"], "fiber_binding_changed")
        provenance = report
        commit, head = provenance["freeze_commit"], provenance["execution_head"]
        parent.require(commit == attempt["freeze_commit"] and head == attempt["execution_head"], "fiber_attempt_provenance_changed")
        ancestry = subprocess.run(["git", "merge-base", "--is-ancestor", commit, head], cwd=ROOT, capture_output=True)
        parent.require(ancestry.returncode == 0, "fiber_not_frozen_before_execution")
        parent.require(report["source_bindings"] == science.frozen_bindings(commit), "fiber_scientific_bindings_incomplete")
        parent.require(report["kernel_sha256"] == parent.sha256(parent.frozen(BASE / "fiber-certification-first.json")) and
                       report["parent_identification_sha256"] == parent.sha256(parent.frozen(BASE / "identification-verification.json")),
                       "fiber_source_identity_changed")
    parent.require(p["freeze_commit"] == i["freeze_commit"], "fiber_different_freezes")
    parent.require(i["primary_receipt_sha256"] == parent.sha256(parent.frozen(BASE / FIRSTS[0])), "fiber_primary_identity_changed")
    witness = parent.strict_json(parent.frozen(BASE / "primitive-witness-c0002.json"))
    counts = parent.strict_json(parent.frozen(BASE / "primary-first-c0002.json"))
    rebuilt = validate(p, i, witness, counts)
    return {**rebuilt, "schema": SCHEMA, "criterion_version": science.VERSION, "evidence_valid": True,
            "status": "certified_complete_fixed_law_hardware_ranges",
            "complete_fixed_law_hardware_ranges_certified": True,
            "uniform_continuous_fiber_bounds_certified": True, "near_attainable_extrema_certified": True,
            "parent_joint_adjudication_preserved": admitted["parent_joint_adjudication_preserved"],
            "hardware_parameter_uniqueness_certified": False, "whole_empirical_confidence_set_bounds": False,
            "gain_squared_optimality_gap": "1/100000000", "new_confidence_budget_spent": False,
            "controller_advance": False, "trial_event_files_read_at_intake": 0, "new_science_executed_at_intake": 0,
            "source_bindings": [parent.binding(BASE / name) for name in
                                ("criterion-fb0001.md", "fiber_verify.py", "fiber-certification-first.json", *FIRSTS)],
            "explicit_declarations": len(kernel["explicit_declarations"])}


def consume(certificate=None):
    result = generate()
    path = BASE / "fiber-verification.json" if certificate is None else Path(certificate)
    parent.require(parent.canonical(result) == parent.canonical(parent.strict_json(path.read_bytes())), "fiber_certificate_changed")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--certificate", type=Path)
    args = parser.parse_args()
    try:
        result = consume(args.certificate) if args.check_only else generate()
        if not args.check_only:
            parent.require(args.certificate is None, "fiber_override_is_consume_only")
            exclusive_json(BASE / "fiber-verification.json", result)
        print(parent.canonical(result))
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(parent.canonical({"schema": SCHEMA, "evidence_valid": False, "reason": str(error)}))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
