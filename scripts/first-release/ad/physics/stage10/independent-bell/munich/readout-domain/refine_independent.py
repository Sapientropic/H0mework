"""Independent replay of c0002 primitives under the unchanged rd0001 statistic."""
import argparse
from pathlib import Path
import sys

import independent as checker


BASE, ROOT, PARENT = checker.BASE, checker.ROOT, checker.PARENT
NEW_FILES = ("criterion-c0002.md", "refine_independent.py")


def execute(archive_dir, witness, commit, output_dir=BASE):
    attempt, first = output_dir / "independent-attempt-c0002.json", output_dir / "independent-first-c0002.json"
    checker.require(not attempt.exists() and not first.exists(), "independent_candidate_first_already_reserved")
    provenance = checker.execution_provenance(commit)
    bindings = checker.freeze_bindings(provenance["freeze_commit"])
    bindings += [{"path": str((BASE / name).relative_to(ROOT)),
                  "sha256": checker.digest(checker.frozen_bytes(BASE / name, provenance["freeze_commit"]))}
                 for name in NEW_FILES]
    raw = witness.read_bytes()
    points = checker.load_witness(raw)
    legacy_raw = [checker.frozen_bytes(PARENT / name) for name in checker.OLD_FIRSTS]
    legacy_bindings = [{"path": str((PARENT / name).relative_to(ROOT)), "sha256": checker.digest(raw)}
                       for name, raw in zip(checker.OLD_FIRSTS, legacy_raw)]
    checker.exclusive_json(attempt, {"schema": "stage10-munich-readout-independent-attempt/v1",
                              "version": checker.VERSION, **provenance, "candidate_revision": "c0002",
                              "program_bindings": bindings, "witness_sha256": checker.digest(raw),
                              "event_records_decoded_at_reservation": 0})
    results, archives = [], []
    try:
        parser = checker.fixed_module(checker.PARSER_PATH, checker.PARSER_SHA, "_c0002_independent_old_parser")
        legacy = [checker.strict_json(old) for old in legacy_raw]
        for spec in parser.ARCHIVE_IDENTITIES:
            data = (archive_dir / spec["name"]).read_bytes()
            admitted = parser.archive_run(data, spec)
            cross = checker.legacy_cross(admitted, legacy)
            result = checker.certify_run(admitted, points[spec["run"]])
            result["legacy_cross"] = cross
            results.append(result)
            archives.append({"run": spec["run"], "bytes": len(data), "sha256": checker.digest(data)})
        qualified = len(results) == 2 and all(r["all_prefixes_below_threshold_certified"] is True for r in results)
        report = {"schema": checker.SCHEMA, "version": checker.VERSION, **provenance,
                  "candidate_revision": "c0002", "status": "certified_source_point" if qualified else "point_not_certified",
                  "source_point_certified": qualified, "familywise_alpha": "1/20", "runs": results,
                  "archive_bindings": archives,
                  "scope": {"independent_8D_Born_contraction": True, "all_original_prefixes_checked": True,
                            "primary_numeric_receipt_read": False, "optimizer_run": False,
                            "global_domain_rejection_claimed": False, "finite_grid_is_continuous_cover": False,
                            "actual_hardware_identity_claimed": False, "controller_advance": False,
                            "conditional_selected_fixed_run_source_contract_required": True}}
    except Exception as error:
        report = {"schema": checker.SCHEMA, "version": checker.VERSION, **provenance,
                  "candidate_revision": "c0002", "status": "execution_failed", "source_point_certified": False,
                  "global_domain_rejection_claimed": False, "reason": str(error), "error_type": type(error).__name__, "runs": results}
    report.update({"program_bindings": bindings, "witness_sha256": checker.digest(raw),
                   "attempt_sha256": checker.digest(attempt.read_bytes()), "legacy_first_bindings": legacy_bindings})
    checker.exclusive_json(first, report)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive-dir", type=Path, required=True)
    parser.add_argument("--witness", type=Path, required=True)
    parser.add_argument("--freeze-commit", required=True)
    args = parser.parse_args()
    try:
        report = execute(args.archive_dir, args.witness, args.freeze_commit)
        print(checker.canonical({k: report[k] for k in ("status", "source_point_certified", "candidate_revision")}))
        return 0 if report["source_point_certified"] else 1
    except (ValueError, OSError, KeyError, TypeError) as error:
        print(checker.canonical({"status": "not_started", "source_point_certified": False, "reason": str(error)}))
        return 2


if __name__ == "__main__":
    sys.exit(main())
