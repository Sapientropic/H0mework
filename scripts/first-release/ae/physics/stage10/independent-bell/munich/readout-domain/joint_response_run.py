"""Generate predeclared joint gain-cap qualifications of the original confidence set."""
import argparse
import subprocess

import joint_response as producer
import shared_response_verify as previous
import verify as parent
from run import exclusive_json


BASE, ROOT = parent.BASE, parent.ROOT
VERSION = "stage10-munich-readout-cp0003"
FILES = ("criterion-cp0003.md", "joint_response.py", "test_joint_response.py", "joint_response_run.py",
         "joint_response_independent.py", "test_joint_response_independent.py",
         "joint-response-audit.md", "joint-response-audit.json")
INPUTS = ("primary-first-c0002.json", "identification-first.json", "primitive-witness-c0002.json",
          "shared-response-first.json", "shared-response-verification.json", "response-bounds-certification-first.json",
          "response_projection.py", "response_projection_independent.py", "shared_response.py", "likelihood.py")
MODULE = ROOT / "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/ReadoutResponseBounds.lean"


def source_review():
    audit = parent.strict_json(parent.frozen(BASE / "joint-response-audit.json"))
    parent.require(audit.get("schema") == "stage10-munich-readout-joint-response-audit/v1" and
                   audit.get("version") == VERSION and audit.get("evidence_valid") is True and
                   audit.get("status") == "accepted_joint_response_source_and_statistical_logic" and
                   audit.get("substantive_defects") == [], "joint_response_source_review_rejected")
    parent.require(audit["confidence_contract"]["parent_confidence_budget"] == "1/20" and
                   audit["confidence_contract"]["new_confidence_budget_spent"] is False,
                   "joint_response_confidence_contract_changed")
    for entry in audit["source_bindings"]:
        parent.require(parent.sha256(parent.frozen(ROOT / entry["path"])) == entry["sha256"], "joint_response_audit_source_changed")
    return audit


def frozen_bindings(commit):
    result = []
    for path in [*(BASE / name for name in (*FILES, *INPUTS)), MODULE]:
        raw = parent.frozen(path, commit)
        parent.require(raw == parent.frozen(path), "joint_response_science_changed")
        result.append({"path": str(path.relative_to(ROOT)), "sha256": parent.sha256(raw)})
    return result


def generate(commit):
    bindings = frozen_bindings(commit)
    source_review()
    admitted = previous.consume()
    parent.require(admitted["evidence_valid"] is True and admitted["parent_joint_adjudication_preserved"] is True,
                   "original_joint_response_not_certified")
    counts, biases, shared, primitive = (parent.strict_json(parent.frozen(BASE / name)) for name in
                                        ("primary-first-c0002.json", "identification-first.json",
                                         "shared-response-first.json", "primitive-witness-c0002.json"))
    for receipt in (counts, biases, shared, primitive):
        parent.require(tuple(row["run"] for row in receipt["runs"]) == parent.RUNS, "joint_response_parent_family_changed")
    results = []
    for counted, biased, old, witness in zip(counts["runs"], biases["runs"], shared["runs"], primitive["runs"]):
        for precision in (80, 160, 320):
            try:
                profile = producer.JointProfile(producer.FullProfile(counted["four_outcomes"], precision), biased["bias_envelopes"])
                rays = [profile.bounds(ray) for ray in producer.RAYS]
                controls = [profile.control("original_lawful_witness", producer.witness_caps(witness["primitive"])),
                            profile.control("individual_projection_lookalike", producer.individual_box_caps(old["shared_response_envelopes"]))]
                parent.require(controls[0]["status"] == "necessary_profile_not_excluded", "lawful_witness_profile_conflict")
                break
            except ValueError:
                if precision == 320:
                    raise
        results.append({"run": counted["run"], "joint_response_rays": rays, "controls": controls,
                        "parent_trials": counted["trials"], "primary_precision_digits": precision,
                        "parent_factor_sequence_sha256": counted["prefix_check"]["factor_sequence_sha256"]})
    return {"schema": "stage10-munich-joint-response-primary/v1", "version": VERSION,
            "status": "generated_joint_response_parent_confidence_qualification", "source_bindings": bindings,
            "source_kernel_sha256": parent.sha256(parent.frozen(BASE / "response-bounds-certification-first.json")),
            "previous_shared_certificate_sha256": parent.sha256(parent.frozen(BASE / "shared-response-verification.json")),
            "profile_threshold_bracket_precision": str(producer.BRACKET),
            "joint_response_profile_certified": True, "whole_empirical_confidence_set_bounds": True,
            "parent_confidence_budget": "1/20", "full_component_threshold": "80",
            "new_confidence_budget_spent": False, "fixed_law_point_used_as_confidence_bound": False,
            "hardware_parameter_uniqueness_certified": False, "actual_ideal_label_identity_selected": False,
            "actual_gain_extremum_sharpness_claimed": False, "profile_pass_used_as_full_source_membership": False,
            "source_theorem_changed": False, "trial_event_files_read": 0, "optimizer_executed": False,
            "new_statistical_fit_executed": False, "runs": results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--freeze-commit", required=True)
    args = parser.parse_args()
    attempt, first = BASE / "joint-response-attempt.json", BASE / "joint-response-first.json"
    try:
        parent.require(not attempt.exists() and not first.exists(), "joint_response_first_already_reserved")
        def git(*arguments):
            result = subprocess.run(["git", *arguments], cwd=ROOT, text=True, capture_output=True)
            parent.require(result.returncode == 0, "joint_response_freeze_not_ancestor")
            return result.stdout.strip()
        commit = git("rev-parse", "--verify", args.freeze_commit + "^{commit}")
        head = git("rev-parse", "--verify", "HEAD^{commit}")
        git("merge-base", "--is-ancestor", commit, head)
        exclusive_json(attempt, {"version": VERSION, "freeze_commit": commit, "execution_head": head,
                                 "source_bindings": frozen_bindings(commit), "event_files_read_at_reservation": 0})
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(parent.canonical({"status": "not_started", "reason": str(error)}))
        return 2
    try:
        report = generate(commit)
    except Exception as error:
        report = {"schema": "stage10-munich-joint-response-primary/v1", "version": VERSION,
                  "status": "execution_failed", "reason": str(error), "error_type": type(error).__name__}
    report.update(attempt_sha256=parent.sha256(attempt.read_bytes()), freeze_commit=commit, execution_head=head)
    exclusive_json(first, report)
    print(parent.canonical({"status": report["status"], "runs_certified": len(report.get("runs", []))}))
    return 1 if report["status"] == "execution_failed" else 0


if __name__ == "__main__":
    raise SystemExit(main())
