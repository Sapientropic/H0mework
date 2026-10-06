"""Run the frozen parameter-identification readout without event access or fitting."""
from pathlib import Path
from fractions import Fraction
import argparse
import itertools
import subprocess

import identification as producer
import verify as parent
from model import decode, encode, source_joint
from run import exclusive_json


BASE, ROOT = parent.BASE, parent.ROOT
VERSION = "stage10-munich-readout-id0001"
FILES = ("criterion-id0001.md", "identification.py", "test_identification.py", "identify.py",
         "identification_independent.py", "test_identification_independent.py",
         "IdentificationCertification.lean", "identification_certify.py",
         "test_identification_certify.py", "identification-certification-first.json")
INPUTS = ("primitive-witness-c0002.json", "primary-first-c0002.json", "independent-first-c0002.json",
          "verification.json", "criterion.md")


def frozen_bindings(commit):
    entries = []
    for name in (*FILES, *INPUTS):
        path = BASE / name
        raw = parent.frozen(path, commit)
        parent.require(raw == parent.frozen(path), "identification_input_not_at_HEAD")
        entries.append({"path": str(path.relative_to(ROOT)), "sha256": parent.sha256(raw)})
    return entries


def generate(commit):
    bindings = frozen_bindings(commit)
    import identification_certify
    identification_kernel = identification_certify.consume()
    parent.require(identification_kernel["evidence_valid"] is True, "identification_kernel_not_certified")
    # The fixed parent certificate already pays both event parsers and complete prefixes.
    admitted = parent.consume()
    witness = parent.strict_json(parent.frozen(BASE / "primitive-witness-c0002.json"))
    counts = parent.strict_json(parent.frozen(BASE / "primary-first-c0002.json"))
    results = []
    for saved, counted in zip(witness["runs"], counts["runs"]):
        point = decode(saved["primitive"])
        table = {key: source_joint(point, *key) for key in itertools.product((0, 1), repeat=5)}
        observed = producer.recover_quotient(table)
        parent.require(observed == producer.quotient(point), "source_quotient_recovery_failed")
        alternatives = []
        for kind, s, t in (("isotropic", Fraction(21, 20), Fraction(21, 20)),
                           ("anisotropic", Fraction(21, 20), Fraction(19, 20))):
            alternative = producer.scale(point, s, t)
            parent.require(producer.recover_scales(point, alternative) == (s, t), "complete_regular_fiber_failed")
            parent.require(all(source_joint(alternative, *key) == q for key, q in table.items()), "gauge_changed_source_law")
            gains = [{"side": side, "setting": setting, "original_gain_squared": str(e.u ** 2 + e.z ** 2),
                      "alternative_gain_squared": str(new.u ** 2 + new.z ** 2)}
                     for side in ("alice", "bob")
                     for setting, (e, new) in enumerate(zip(getattr(point, side), getattr(alternative, side)))]
            parent.require(any(row["original_gain_squared"] != row["alternative_gain_squared"] for row in gains),
                           "hardware_gain_did_not_change")
            alternatives.append({"kind": kind, "s": str(s), "t": str(t), "primitive": encode(alternative),
                                 "gain_changes": gains, "all_generated_probabilities_unchanged": True,
                                 "all_original_prefixes_inherited": counted["trials"]})
        own = producer.own_counts(counted["four_outcomes"])
        envelopes = [{"side": side, **producer.Profile(own[side], setting).bounds()}
                     for side in ("alice", "bob") for setting in (0, 1)]
        results.append({"run": saved["run"], "primitive": saved["primitive"], "observable_quotient": observed,
                        "regular_fiber": producer.fixed_law_fiber(point), "continuous_legal_rectangle": producer.positive_rectangle(point),
                        "equivalent_hardware": alternatives, "bias_envelopes": envelopes,
                        "own_setting_counts": own, "parent_factor_sequence_sha256": counted["prefix_check"]["factor_sequence_sha256"]})
    return {"schema": "stage10-munich-readout-identification-primary/v1", "version": VERSION,
            "status": "generated_parameter_fibers_and_parent_confidence_projections", "source_bindings": bindings,
            "parent_certificate_sha256": parent.sha256(parent.frozen(BASE / "verification.json")),
            "parent_confidence_budget": "1/20", "new_confidence_budget_spent": False,
            "trial_event_files_read": 0, "optimizer_run": False, "actual_hardware_uniquely_identified": False,
            "isotropic_nonuniqueness_preserves_axes": True, "runs": results,
            "identification_kernel_sha256": parent.sha256(parent.frozen(BASE / "identification-certification-first.json")),
            "parent_adjudication_preserved": admitted["full_joint_source_model_certified"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--freeze-commit", required=True)
    args = parser.parse_args()
    attempt, first = BASE / "identification-attempt.json", BASE / "identification-first.json"
    try:
        parent.require(not attempt.exists() and not first.exists(), "identification_first_already_reserved")
        def git(*arguments):
            result = subprocess.run(["git", *arguments], cwd=ROOT, text=True, capture_output=True, check=False)
            parent.require(result.returncode == 0, "identification_freeze_not_execution_ancestor")
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
        report = {"schema": "stage10-munich-readout-identification-primary/v1", "version": VERSION,
                  "status": "execution_failed", "reason": str(error), "error_type": type(error).__name__}
    report.update({"attempt_sha256": parent.sha256(attempt.read_bytes()), "freeze_commit": commit, "execution_head": head})
    exclusive_json(first, report)
    print(parent.canonical({"status": report["status"]}))
    return 0 if report["status"] != "execution_failed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
