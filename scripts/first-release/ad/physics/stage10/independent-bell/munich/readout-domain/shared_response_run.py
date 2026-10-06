"""Generate frozen shared-response bounds of the original full confidence set."""
import argparse
import subprocess

import response_projection_verify as previous
import shared_response as producer
import verify as parent
from run import exclusive_json


BASE, ROOT = parent.BASE, parent.ROOT
VERSION = "stage10-munich-readout-cp0002"
FILES = ("criterion-cp0002.md", "shared_response.py", "test_shared_response.py", "shared_response_run.py",
         "shared_response_independent.py", "test_shared_response_independent.py",
         "shared-response-audit.md", "shared-response-audit.json")
INPUTS = ("primary-first-c0002.json", "identification-first.json", "response-projection-first.json",
          "response-projection-verification.json", "response-bounds-certification-first.json",
          "response_projection.py", "response_projection_independent.py", "likelihood.py")
MODULE = ROOT / "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/ReadoutResponseBounds.lean"


def source_review():
    audit = parent.strict_json(parent.frozen(BASE / "shared-response-audit.json"))
    parent.require(audit.get("schema") == "stage10-munich-readout-shared-response-audit/v1" and
                   audit.get("version") == VERSION and audit.get("evidence_valid") is True and
                   audit.get("status") == "accepted_shared_response_source_and_statistical_logic" and
                   audit.get("substantive_defects") == [], "shared_response_source_review_rejected")
    parent.require(audit["confidence_contract"]["parent_confidence_budget"] == "1/20" and
                   audit["confidence_contract"]["new_confidence_budget_spent"] is False,
                   "shared_response_confidence_contract_changed")
    for entry in audit["source_bindings"]:
        parent.require(parent.sha256(parent.frozen(ROOT / entry["path"])) == entry["sha256"], "shared_response_audit_source_changed")
    return audit


def frozen_bindings(commit):
    entries = []
    for path in [*(BASE / name for name in (*FILES, *INPUTS)), MODULE]:
        raw = parent.frozen(path, commit)
        parent.require(raw == parent.frozen(path), "shared_response_science_changed")
        entries.append({"path": str(path.relative_to(ROOT)), "sha256": parent.sha256(raw)})
    return entries


def generate(commit):
    bindings = frozen_bindings(commit)
    source_review()
    admitted = previous.consume()
    parent.require(admitted["evidence_valid"] is True, "original_confidence_response_not_certified")
    counts = parent.strict_json(parent.frozen(BASE / "primary-first-c0002.json"))
    biases = parent.strict_json(parent.frozen(BASE / "identification-first.json"))
    legacy = parent.strict_json(parent.frozen(BASE / "response-projection-first.json"))
    parent.require(tuple(row["run"] for row in counts["runs"]) == tuple(row["run"] for row in biases["runs"]) ==
                   tuple(row["run"] for row in legacy["runs"]) == parent.RUNS, "shared_response_parent_family_changed")
    results = []
    for counted, biased, old in zip(counts["runs"], biases["runs"], legacy["runs"]):
        full = producer.FullProfile(counted["four_outcomes"])
        bounds = []
        for (side, setting), old_entry in zip(producer.ROLES, old["response_envelopes"]):
            parent.require((old_entry["side"], old_entry["setting"]) == (side, setting), "legacy_response_role_changed")
            bounds.append(producer.SharedProfile(full, biased["bias_envelopes"], side, setting).bounds(old_entry["canonical_gain"][0]))
        results.append({"run": counted["run"], "shared_response_envelopes": bounds,
                        "parent_trials": counted["trials"],
                        "parent_factor_sequence_sha256": counted["prefix_check"]["factor_sequence_sha256"]})
    return {"schema": "stage10-munich-shared-response-primary/v1", "version": VERSION,
            "status": "generated_shared_response_parent_confidence_bounds", "source_bindings": bindings,
            "source_kernel_sha256": parent.sha256(parent.frozen(BASE / "response-bounds-certification-first.json")),
            "previous_response_certificate_sha256": parent.sha256(parent.frozen(BASE / "response-projection-verification.json")),
            "profile_threshold_bracket_precision": str(producer.BRACKET),
            "shared_response_profile_certified": True, "whole_empirical_confidence_set_bounds": True,
            "parent_confidence_budget": "1/20", "new_confidence_budget_spent": False,
            "fixed_law_point_used_as_confidence_bound": False, "hardware_parameter_uniqueness_certified": False,
            "actual_gain_extremum_sharpness_claimed": False, "source_theorem_changed": False,
            "trial_event_files_read": 0, "optimizer_executed": False, "new_statistical_fit_executed": False,
            "full_component_threshold": "80", "strictly_improved_gain_count": sum(
                row["strictly_improved_gain_lower"] for run in results for row in run["shared_response_envelopes"]), "runs": results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--freeze-commit", required=True)
    args = parser.parse_args()
    attempt, first = BASE / "shared-response-attempt.json", BASE / "shared-response-first.json"
    try:
        parent.require(not attempt.exists() and not first.exists(), "shared_response_first_already_reserved")
        def git(*arguments):
            result = subprocess.run(["git", *arguments], cwd=ROOT, text=True, capture_output=True)
            parent.require(result.returncode == 0, "shared_response_freeze_not_ancestor")
            return result.stdout.strip()
        commit = git("rev-parse", "--verify", args.freeze_commit + "^{commit}")
        head = git("rev-parse", "--verify", "HEAD^{commit}")
        git("merge-base", "--is-ancestor", commit, head)
        bindings = frozen_bindings(commit)
        exclusive_json(attempt, {"version": VERSION, "freeze_commit": commit, "execution_head": head,
                                 "source_bindings": bindings, "event_files_read_at_reservation": 0})
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(parent.canonical({"status": "not_started", "reason": str(error)}))
        return 2
    try:
        report = generate(commit)
    except Exception as error:
        report = {"schema": "stage10-munich-shared-response-primary/v1", "version": VERSION,
                  "status": "execution_failed", "reason": str(error), "error_type": type(error).__name__}
    report.update(attempt_sha256=parent.sha256(attempt.read_bytes()), freeze_commit=commit, execution_head=head)
    exclusive_json(first, report)
    print(parent.canonical({"status": report["status"], "strictly_improved_gain_count": report.get("strictly_improved_gain_count")}))
    return 1 if report["status"] == "execution_failed" else 0


if __name__ == "__main__":
    raise SystemExit(main())
