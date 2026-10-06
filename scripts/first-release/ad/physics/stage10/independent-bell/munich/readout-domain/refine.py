"""Frozen analytic candidate refinement of the unchanged rd0001 confidence domain."""
from datetime import datetime, timezone
import argparse
from pathlib import Path
import sys

import run as baseline
import candidate


BASE, ROOT = baseline.BASE, baseline.ROOT
VERSION, RUNS = baseline.VERSION, baseline.RUNS
REVISION = "c0002"
BASE_FREEZE = "4a6960e9bb"
FILES = ("criterion-c0002.md", "candidate.py", "test_candidate.py", "refine.py", "test_refine.py", "refine_independent.py")


def snapshot(commit):
    paid = baseline.committed_snapshot(BASE_FREEZE)
    freeze = baseline.git("rev-parse", "--verify", commit + "^{commit}").decode().strip()
    head = paid["execution_head"]
    baseline.git("merge-base", "--is-ancestor", freeze, head)
    paths = [BASE / name for name in FILES]
    baseline.require(baseline.git("status", "--porcelain", "--", *[str(p.relative_to(ROOT)) for p in paths]) == b"",
                     "dirty_candidate_revision")
    bindings = list(paid["program_bindings"])
    for path in paths:
        item = baseline.frozen_binding(path)
        baseline.frozen_bytes(path, freeze)
        bindings.append(item)
    return {"freeze_commit": freeze, "execution_head": head, "program_bindings": bindings,
            "candidate_revision": REVISION, "base_scientific_freeze": BASE_FREEZE}


def certify_run(admitted, summary):
    counts = baseline.TerminalCounts(tuple(tuple(row["counts"]) for row in summary["four_outcomes"]))
    candidates = candidate.search_terminal(counts, baseline.search_starts(), max_iterations=baseline.MAX_ITERATIONS)
    checks, accepted = [], None
    for proposed in candidates:
        checked = baseline.check_candidate(admitted, proposed["primitive"])
        checked.update({k: v for k, v in proposed.items() if k != "primitive"})
        checks.append(checked)
        if checked["prefix_check"]["status"] == "all_prefix_witness_verified":
            accepted = checked
            break
    result = {"run": admitted.run, **summary, "candidate_revision": REVISION,
              "status": "all_prefix_witness_verified" if accepted else "unresolved",
              "all_prefixes_below_threshold_certified": accepted is not None,
              "all_pair_records_scored": accepted is not None,
              "primitive": accepted["primitive"] if accepted else None,
              "source_probabilities": accepted["source_probabilities"] if accepted else None,
              "prefix_check": accepted["prefix_check"] if accepted else None,
              "precision_attempts": accepted["precision_attempts"] if accepted else [],
              "candidate_checks": checks,
              "searchcount": {"declared_starts": 35, "finite_candidates": len(candidates), "checked_candidates": len(checks)},
              "search_results": [{k: v for k, v in proposed.items() if k != "primitive"} for proposed in candidates],
              "local_audit": admitted.audit, "token_dictionaries": admitted.token_dictionaries,
              "threshold": "40", "per_run_alpha": "1/40", "global_domain_rejection_claimed": False}
    if accepted:
        baseline.require(accepted["prefix_check"]["counts"] == summary["four_outcomes"] and
                         accepted["prefix_check"]["pooled_counts"] == summary["pooled_counts"] and
                         accepted["prefix_check"]["trial_bit_sequence_sha256"] == summary["trial_bit_sequence_sha256"],
                         "accepted_prefix_accounting_changed")
    return result


def execute(archive_dir, commit, output_dir=BASE):
    attempt_path = output_dir / "primary-attempt-c0002.json"
    first_path = output_dir / "primary-first-c0002.json"
    witness_path = output_dir / "primitive-witness-c0002.json"
    baseline.require(not any(p.exists() for p in (attempt_path, first_path, witness_path)), "candidate_first_already_reserved")
    state = snapshot(commit)
    inputs = baseline.load_frozen_inputs(state)
    environment = baseline.solver_environment()
    declaration = {**candidate.SEARCH_DECLARATION, "candidate_revision": REVISION,
                   "precision_escalation": list(baseline.PRECISIONS)}
    baseline.exclusive_json(attempt_path, {"schema": "stage10-munich-readout-primary-attempt/v1", "version": VERSION,
                             **state, "started_utc": datetime.now(timezone.utc).isoformat(),
                             "solver_environment": environment, "search_declaration": declaration,
                             "event_records_decoded_at_reservation": 0})
    access, results = {}, []
    try:
        parser = inputs["parser"]
        for spec in parser.ARCHIVES:
            admitted = parser.admit_archive(archive_dir, spec, access)
            summary = baseline.summarize(admitted)
            cross = baseline.legacy_cross(admitted, summary, inputs["legacy_firsts"])
            result = certify_run(admitted, summary)
            result["legacy_cross"] = cross
            results.append(result)
        baseline.require(snapshot(commit)["program_bindings"] == state["program_bindings"], "science_changed_during_refinement")
        qualified = all(r["all_prefixes_below_threshold_certified"] is True for r in results) and len(results) == 2
        witness_sha = None
        if qualified:
            baseline.exclusive_json(witness_path, {"schema": baseline.WITNESS_SCHEMA, "version": VERSION,
                           "runs": [{"run": r["run"], "primitive": r["primitive"]} for r in results]})
            witness_sha = baseline.digest(witness_path.read_bytes())
        report = {"schema": baseline.SCHEMA, "version": VERSION, **state,
                  "status": "certified_source_point" if qualified else "unresolved",
                  "source_point_certified": qualified, "scientific_adjudication_completed": qualified,
                  "scientific_verdict": "complete_joint_confidence_domain_nonempty" if qualified else "unresolved",
                  "global_domain_rejection_claimed": False, "runs": results, "witness_sha256": witness_sha,
                  "familywise_alpha": "1/20", "solver_environment": environment, "search_declaration": declaration}
    except Exception as error:
        report = {"schema": baseline.SCHEMA, "version": VERSION, **state, "status": "execution_failed",
                  "source_point_certified": False, "global_domain_rejection_claimed": False,
                  "reason": str(error), "error_type": type(error).__name__, "runs": results, "witness_sha256": None}
    report.update({"attempt_sha256": baseline.digest(attempt_path.read_bytes()),
                   "source_bindings": inputs["bindings"], "legacy_first_bindings": inputs["legacy_first_bindings"],
                   "archive_bindings": inputs["bindings"]["parent"]["archive_bindings"],
                   "record_access": baseline.record_access(access)})
    baseline.exclusive_json(first_path, report)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive-dir", type=Path, required=True)
    parser.add_argument("--freeze-commit", required=True)
    args = parser.parse_args()
    try:
        report = execute(args.archive_dir, args.freeze_commit)
        print(baseline.canonical({k: report[k] for k in ("status", "source_point_certified", "candidate_revision")}))
        return 0 if report["source_point_certified"] else 1
    except (ValueError, OSError, KeyError, TypeError) as error:
        print(baseline.canonical({"status": "not_started", "source_point_certified": False, "reason": str(error)}))
        return 2


if __name__ == "__main__":
    sys.exit(main())
