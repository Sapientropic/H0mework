"""Produce frozen, near-sharp hardware ranges over each complete generated-law fiber."""
import argparse
import itertools
import subprocess
import sys

import fiber_bounds as producer
import identify_verify as identification
import verify as parent
from run import exclusive_json


BASE, ROOT = parent.BASE, parent.ROOT
VERSION = "stage10-munich-readout-fb0001"
FILES = ("criterion-fb0001.md", "fiber_bounds.py", "test_fiber_bounds.py", "fiber_run.py",
         "fiber_independent.py", "test_fiber_independent.py", "FiberBoundsCertification.lean",
         "fiber_certify.py", "test_fiber_certify.py", "fiber-certification-first.json")
INPUTS = ("primitive-witness-c0002.json", "verification.json", "primary-first-c0002.json",
          "identification-verification.json", "identification-certification-first.json")
MODULE = ROOT / "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/ReadoutFiberBounds.lean"


def frozen_bindings(commit):
    bindings = []
    for path in [*(BASE / name for name in (*FILES, *INPUTS)), MODULE]:
        raw = parent.frozen(path, commit)
        parent.require(raw == parent.frozen(path), "fiber_science_not_at_execution_HEAD")
        bindings.append({"path": str(path.relative_to(ROOT)), "sha256": parent.sha256(raw)})
    return bindings


def generate(commit):
    import numpy
    import scipy
    import fiber_certify
    parent.require(scipy.__version__ == "1.13.1" and numpy.__version__ == "2.2.6" and
                   sys.version_info[:3] == (3, 12, 13), "frozen_fiber_proposal_runtime_changed")
    bindings = frozen_bindings(commit)
    parent.require(fiber_certify.consume()["evidence_valid"] is True, "fiber_dual_kernel_not_certified")
    admitted = identification.consume()
    parent.require(admitted["evidence_valid"] is True, "original_regular_fiber_not_certified")
    witness = parent.strict_json(parent.frozen(BASE / "primitive-witness-c0002.json"))
    counts = parent.strict_json(parent.frozen(BASE / "primary-first-c0002.json"))
    runs = []
    for saved, counted in zip(witness["runs"], counts["runs"]):
        ranges = []
        for side, setting in itertools.product(("alice", "bob"), (0, 1)):
            lo = producer.propose(saved["primitive"], side, setting, "minimum")
            hi = producer.propose(saved["primitive"], side, setting, "maximum")
            ranges.append({"side": side, "setting": setting, "minimum": lo, "maximum": hi,
                           "ranges": producer.channel_ranges(saved["primitive"], side, setting, lo["checked"], hi["checked"])})
        runs.append({"run": saved["run"], "primitive": saved["primitive"], "hardware_ranges": ranges,
                     "parent_prefixes_inherited": counted["trials"],
                     "parent_factor_sequence_sha256": counted["prefix_check"]["factor_sequence_sha256"]})
    return {"schema": "stage10-munich-readout-fiber-primary/v1", "version": VERSION,
            "status": "certified_complete_fiber_hardware_ranges", "source_bindings": bindings,
            "parent_identification_sha256": parent.sha256(parent.frozen(BASE / "identification-verification.json")),
            "kernel_sha256": parent.sha256(parent.frozen(BASE / "fiber-certification-first.json")),
            "scope": "complete_regular_fiber_of_each_frozen_generated_joint_law",
            "gain_squared_optimality_gap": str(producer.GAP), "uniform_fiber_coverage": True,
            "finite_grid_used_as_coverage": False, "new_confidence_budget_spent": False,
            "whole_empirical_confidence_set_bounds": False, "actual_hardware_uniquely_identified": False,
            "trial_event_files_read": 0, "new_statistical_fit_executed": False,
            "geometric_optimizer_executed": True,
            "runtime": {"python": "3.12.13", "numpy": numpy.__version__, "scipy": scipy.__version__}, "runs": runs}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--freeze-commit", required=True)
    args = parser.parse_args()
    attempt, first = BASE / "fiber-attempt.json", BASE / "fiber-first.json"
    try:
        parent.require(not attempt.exists() and not first.exists(), "fiber_first_already_reserved")
        def git(*arguments):
            result = subprocess.run(["git", *arguments], cwd=ROOT, text=True, capture_output=True)
            parent.require(result.returncode == 0, "fiber_freeze_not_execution_ancestor")
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
        report = {"schema": "stage10-munich-readout-fiber-primary/v1", "version": VERSION,
                  "status": "execution_failed", "reason": str(error), "error_type": type(error).__name__}
    report.update({"attempt_sha256": parent.sha256(attempt.read_bytes()), "freeze_commit": commit, "execution_head": head})
    exclusive_json(first, report)
    print(parent.canonical({"status": report["status"]}))
    return 1 if report["status"] == "execution_failed" else 0


if __name__ == "__main__":
    raise SystemExit(main())
