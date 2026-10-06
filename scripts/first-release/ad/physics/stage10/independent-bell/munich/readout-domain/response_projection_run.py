"""Generate correlation and response envelopes from the frozen original sufficient counts."""
import argparse
import subprocess

import identify_verify as identification
import response_projection as producer
import verify as parent
from run import exclusive_json


BASE, ROOT = parent.BASE, parent.ROOT
VERSION = "stage10-munich-readout-cp0001"
FILES = ("criterion-cp0001.md", "response_projection.py", "test_response_projection.py", "response_projection_run.py",
         "response_projection_independent.py", "test_response_projection_independent.py",
         "ResponseBoundsCertification.lean", "response_bounds_certify.py", "test_response_bounds_certify.py",
         "response-bounds-certification-first.json")
INPUTS = ("verification.json", "primary-first-c0002.json", "identification-first.json",
          "identification-verification.json", "identification-certification-first.json", "likelihood.py")
MODULE = ROOT / "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/ReadoutResponseBounds.lean"


def frozen_bindings(commit):
    result = []
    for path in [*(BASE / name for name in (*FILES, *INPUTS)), MODULE]:
        raw = parent.frozen(path, commit)
        parent.require(raw == parent.frozen(path), "response_projection_not_at_execution_HEAD")
        result.append({"path": str(path.relative_to(ROOT)), "sha256": parent.sha256(raw)})
    return result


def generate(commit):
    import response_bounds_certify
    bindings = frozen_bindings(commit)
    parent.require(response_bounds_certify.consume()["evidence_valid"] is True, "source_response_not_certified")
    parent.require(identification.consume()["evidence_valid"] is True, "parent_confidence_bias_not_certified")
    counts = parent.strict_json(parent.frozen(BASE / "primary-first-c0002.json"))
    biases = parent.strict_json(parent.frozen(BASE / "identification-first.json"))
    parent.require(tuple(row["run"] for row in counts["runs"]) == tuple(row["run"] for row in biases["runs"]) == parent.RUNS,
                   "response_projection_source_family_changed")
    runs = []
    for counted, biased in zip(counts["runs"], biases["runs"]):
        profile = producer.FullProfile(counted["four_outcomes"])
        correlations = [profile.correlation(context).bounds() for context in producer.CONTEXTS]
        responses = producer.response_envelopes(correlations, biased["bias_envelopes"])
        runs.append({"run": counted["run"], "correlation_envelopes": correlations,
                     "response_envelopes": responses, "bias_envelopes": biased["bias_envelopes"],
                     "parent_trials": counted["trials"],
                     "parent_factor_sequence_sha256": counted["prefix_check"]["factor_sequence_sha256"]})
    return {"schema": "stage10-munich-readout-response-projection-primary/v1", "version": VERSION,
            "status": "generated_parent_confidence_response_envelopes", "source_bindings": bindings,
            "kernel_sha256": parent.sha256(parent.frozen(BASE / "response-bounds-certification-first.json")),
            "parent_identification_sha256": parent.sha256(parent.frozen(BASE / "identification-verification.json")),
            "whole_empirical_confidence_set_bounds": True, "simultaneous_necessary_outer_projections": True,
            "parent_confidence_budget": "1/20", "new_confidence_budget_spent": False,
            "fixed_law_point_used_as_confidence_bound": False, "hardware_parameter_uniqueness_certified": False,
            "trial_event_files_read": 0, "optimizer_executed": False, "new_statistical_fit_executed": False,
            "full_component_threshold": "80", "runs": runs}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--freeze-commit", required=True)
    args = parser.parse_args()
    attempt, first = BASE / "response-projection-attempt.json", BASE / "response-projection-first.json"
    try:
        parent.require(not attempt.exists() and not first.exists(), "response_projection_first_already_reserved")
        def git(*arguments):
            result = subprocess.run(["git", *arguments], cwd=ROOT, text=True, capture_output=True)
            parent.require(result.returncode == 0, "response_projection_freeze_not_ancestor")
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
        report = {"schema": "stage10-munich-readout-response-projection-primary/v1", "version": VERSION,
                  "status": "execution_failed", "reason": str(error), "error_type": type(error).__name__}
    report.update(attempt_sha256=parent.sha256(attempt.read_bytes()), freeze_commit=commit, execution_head=head)
    exclusive_json(first, report)
    print(parent.canonical({"status": report["status"]}))
    return 1 if report["status"] == "execution_failed" else 0


if __name__ == "__main__":
    raise SystemExit(main())
