"""Once-only exact Munich balanced-complement adjudication of both fixed archives."""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import subprocess
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

from schema import ARCHIVES, README_SHA256, RUNS, AdmissionError, admit_archive, require, validate_bindings


BASE = Path(__file__).resolve().parent
THRESHOLD = Fraction(40)
PROTOCOL = {
    "version": "stage10-munich-mu0001.1", "source": "positiveSmoothUnifiedSource",
    "root_visit": 10, "current_tick": 16, "next_tick": 17, "controller_advance": False,
    "runs": list(RUNS), "null": "conditional_balanced_complement_all_unit_XZ_axes_both_heralds",
    "encoding": "per_run_per_role_ascii_byte_sorted_at_most_two_raw_tokens",
    "finite_global_label_maps": 32, "selection": "all_official_pairs_strict_original_local_row_join",
    "per_lab_global_row_offsets": [0, 1], "pair_window_ms": 100,
    "valid_pair_flag": "per_lab_constant_raw_token_including_empty",
    "lab2_record_tail": "six_semantic_fields_optional_seventh_empty",
    "predictor": "context_herald_settingA_settingB_parity_Jeffreys_past_only",
    "per_run_alpha": "1/40", "familywise_alpha": "1/20", "per_run_threshold": "40",
    "e_process": "equal_mixture_joint_Alice_marginal_Bob_marginal",
    "component_weights": ["1/3", "1/3", "1/3"],
    "anytime": True, "exact_prefix_arithmetic": "fractions.Fraction",
    "score_all_records_after_crossing": True, "empirical_fit_parameters": 0,
    "actual_angles_required": False, "physical_label_dictionary_required": False,
    "hardware_identity_validated": False, "full_joint_validated": False,
    "theory_validated": False, "human_outcome_unexposed_claimed": False,
}
SCIENTIFIC_FILES = (
    "criterion-mu0001.1.md", "sources.json", "source-methods.md", "primary.py", "schema.py", "test_primary.py",
    "invariant_independent.py", "test_invariant_independent.py", "verify.py", "test_verify.py",
    "format-repair-mu0001.1.json",
)


def unsigned_bytes(value):
    require(type(value) is int and value > 0, "nonpositive_exact_integer")
    return value.to_bytes((value.bit_length() + 7) // 8, "big")


def fraction_encoding(value):
    numerator, denominator = unsigned_bytes(value.numerator), unsigned_bytes(value.denominator)
    return len(numerator).to_bytes(8, "big") + numerator + len(denominator).to_bytes(8, "big") + denominator


def exact_summary(value):
    require(isinstance(value, Fraction) and value > 0, "nonpositive_exact_fraction")
    numerator, denominator = value.numerator, value.denominator
    exponent = numerator.bit_length() - denominator.bit_length()
    below_power = numerator < denominator << exponent if exponent >= 0 else numerator << -exponent < denominator
    if below_power:
        exponent -= 1
    shift = 48 - exponent
    scaled_numerator = numerator << shift if shift >= 0 else numerator
    scaled_denominator = denominator if shift >= 0 else denominator << -shift
    lower, remainder = divmod(scaled_numerator, scaled_denominator)
    return {
        "numerator_sha256": hashlib.sha256(unsigned_bytes(numerator)).hexdigest(),
        "denominator_sha256": hashlib.sha256(unsigned_bytes(denominator)).hexdigest(),
        "numerator_bits": numerator.bit_length(), "denominator_bits": denominator.bit_length(),
        "dyadic": {"lower_mantissa": lower, "upper_mantissa": lower + (remainder != 0),
                   "exponent": exponent - 48},
    }


class Predictor:
    def __init__(self):
        self.counts = {key: [0, 0] for key in itertools.product(range(2), repeat=4)}
        self.joints = {key: [0, 0, 0, 0] for key in itertools.product(range(2), repeat=3)}
        self.evalue = Fraction(1)
        self.joint_e, self.alice_e, self.bob_e = Fraction(1), Fraction(1), Fraction(1)
        self.pooled_a, self.pooled_b = [0, 0], [0, 0]
        self.trials = 0

    def step(self, trial):
        require(trial.row == self.trials + 1, "nonoriginal_pair_order", row=trial.row)
        require(all(type(bit) is int and bit in (0, 1) for bit in
                    (trial.h, trial.a, trial.b, trial.x, trial.y)), "nonbinary_trial", row=trial.row)
        base = (trial.h, trial.a, trial.b)
        # Both parity bets are fixed from past counts before the current outcome is used.
        predictions = []
        for parity in (0, 1):
            n0, n1 = self.counts[base + (parity,)]
            predictions.append((Fraction(2 * n0 + 1, 2 * (n0 + n1) + 2),
                                Fraction(2 * n1 + 1, 2 * (n0 + n1) + 2)))
        alice_predictions = tuple(Fraction(2 * count + 1, 2 * sum(self.pooled_a) + 2) for count in self.pooled_a)
        bob_predictions = tuple(Fraction(2 * count + 1, 2 * sum(self.pooled_b) + 2) for count in self.pooled_b)
        parity = trial.x ^ trial.y
        self.joint_e *= 2 * predictions[parity][trial.x]
        self.alice_e *= 2 * alice_predictions[trial.x]
        self.bob_e *= 2 * bob_predictions[trial.y]
        self.evalue = (self.joint_e + self.alice_e + self.bob_e) / 3
        self.counts[base + (parity,)][trial.x] += 1
        self.joints[base][2 * trial.x + trial.y] += 1
        self.pooled_a[trial.x] += 1
        self.pooled_b[trial.y] += 1
        self.trials += 1
        return self.evalue


def exact_prefixes(trials):
    predictor = Predictor()
    for trial in trials:
        yield predictor.step(trial)


def score_run(admitted):
    predictor = Predictor()
    digest = hashlib.sha256()
    maximum, maximum_prefix, first_crossing, first_crossing_value = Fraction(1), 0, None, None
    for trial in admitted.trials:
        value = predictor.step(trial)
        digest.update(fraction_encoding(value))
        if value > maximum:
            maximum, maximum_prefix = value, trial.row
        if first_crossing is None and value >= THRESHOLD:
            first_crossing = trial.row
            first_crossing_value = value
    require(sum(sum(counts) for counts in predictor.counts.values()) == len(admitted.trials) and
            sum(sum(counts) for counts in predictor.joints.values()) == len(admitted.trials),
            "score_accounting", run=admitted.run)
    status = "rejected" if first_crossing is not None else ("not_rejected" if predictor.trials else "inconclusive")
    return {
        "run": admitted.run, "trials": predictor.trials,
        "contexts": [dict(zip(("h", "a", "b", "c"), key), counts=counts)
                     for key, counts in sorted(predictor.counts.items())],
        "four_outcomes": [dict(zip(("h", "a", "b"), key), counts=counts)
                          for key, counts in sorted(predictor.joints.items())],
        "terminal_e": exact_summary(predictor.evalue), "max_e": exact_summary(maximum),
        "components": {"joint": exact_summary(predictor.joint_e), "alice": exact_summary(predictor.alice_e),
                       "bob": exact_summary(predictor.bob_e)},
        "pooled_counts": {"alice": predictor.pooled_a, "bob": predictor.pooled_b},
        "max_prefix": maximum_prefix, "first_crossing": first_crossing,
        "first_crossing_e": exact_summary(first_crossing_value) if first_crossing_value is not None else None,
        "prefix_e_sha256": digest.hexdigest(), "alpha": "1/40", "threshold": "40", "status": status,
        "token_dictionaries": admitted.token_dictionaries, "local_audit": admitted.audit,
        "all_pair_records_scored": predictor.trials == admitted.audit["pair_records"],
    }


def adjudicate(admitted_runs):
    require(set(admitted_runs) == set(RUNS), "complete_run_inventory")
    require(all(admitted_runs[run].run == run for run in RUNS), "run_identity")
    results = [score_run(admitted_runs[run]) for run in RUNS]
    statuses = {result["status"] for result in results}
    verdict = "rejected" if "rejected" in statuses else ("inconclusive" if "inconclusive" in statuses else "not_rejected")
    return {
        "schema": "stage10-munich-balanced-complement-primary/v1", "version": PROTOCOL["version"],
        "admission": "admitted", "scientific_verdict": verdict, "runs": results,
        "familywise_alpha": "1/20", "pair_records_scored": sum(result["trials"] for result in results),
        "all_pair_records_scored": all(result["all_pair_records_scored"] for result in results),
        "scientific_adjudication_completed": True,
        "real_instrument_empirical_verdict_executed": all(result["trials"] > 0 for result in results),
        "scope": {"contract": PROTOCOL["null"], "nominal_instrument_transport_included": True,
                  "hardware_identity_validated": False, "full_joint_validated": False,
                  "theory_validated": False, "controller_advance": False},
    }


def strict_json(raw):
    def object_pairs(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, "duplicate_json_key", field=key)
            result[key] = value
        return result
    try:
        return json.loads(raw, object_pairs_hook=object_pairs)
    except (UnicodeError, json.JSONDecodeError):
        raise AdmissionError("json_encoding_or_schema") from None


def committed_snapshot():
    discovery = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=BASE,
                               capture_output=True, text=True, check=False)
    require(discovery.returncode == 0 and bool(discovery.stdout.strip()), "scientific_repository_root")
    root = Path(discovery.stdout.strip()).resolve()
    def git(*arguments):
        result = subprocess.run(["git", *arguments], cwd=root, capture_output=True, text=True, check=False)
        require(result.returncode == 0, "uncommitted_scientific_paths")
        return result.stdout.strip()
    paths = [str((BASE / name).resolve().relative_to(root)) for name in SCIENTIFIC_FILES]
    require(git("status", "--porcelain", "--", *paths) == "", "dirty_scientific_paths")
    blobs = {path: git("rev-parse", "HEAD:" + path) for path in paths}
    for path, blob in blobs.items():
        require(git("hash-object", "--no-filters", "--", path) == blob,
                "scientific_current_bytes_not_head", field=path)
    last_commit = git("log", "-1", "--format=%H", "--", *paths)
    require(bool(last_commit), "missing_scientific_path_commit")
    return {"execution_head": git("rev-parse", "HEAD"), "scientific_path_git_blobs": blobs,
            "last_scientific_path_commit": last_commit}


def load_frozen_inputs():
    raw_sources = (BASE / "sources.json").read_bytes()
    sources = strict_json(raw_sources)
    validate_bindings(sources)
    authority = sources.get("theory_authority", {})
    for key, value in (("source", "positiveSmoothUnifiedSource"), ("root_visit", 10), ("current_tick", 16),
                       ("next_tick", 17), ("controller_advance", False), ("source_theorem_changed", False),
                       ("probability_declaration", "SaturationMonoid.PhysicsCore.Stage10.Bell.probability"),
                       ("runtime_declaration", "SaturationMonoid.PhysicsCore.Stage10.Bell.sameOccurrenceBellPrediction"),
                       ("original_certification_commit", "79efabda45")):
        require(authority.get(key) == value, "theory_authority_identity", field=key)
    theory_bindings = authority.get("bindings", ())
    expected_paths = (
        "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/Runtime.lean",
        "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/Probabilities.lean",
        "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/Source.lean",
        "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/Herald.lean",
        "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/Operators.lean",
        "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/Effects.lean",
        "Lean/SaturationMonoid/PhysicsCore/Stage9C/Material/SpinPair/Spinor.lean",
        "Lean/SaturationMonoid/PhysicsCore/Stage9DEF/Source/Coefficients.lean",
        "Lean/SaturationMonoid/PhysicsCore/Stage10/Runtime/Occurrence.lean",
        "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/TheoryBlind.lean",
        "Verification/physics/stage10/independent-bell/theory-blind/Certification.lean",
        "Verification/physics/stage10/independent-bell/theory-blind/verification.json",
        "Verification/physics/stage10/independent-bell/theory-blind/kernel-certification-first.json",
    )
    require(len(theory_bindings) == 13 and {item.get("path") for item in theory_bindings} == set(expected_paths),
            "theory_binding_inventory")
    repo = BASE.parents[4]
    for binding in theory_bindings:
        require(hashlib.sha256((repo / binding["path"]).read_bytes()).hexdigest() == binding.get("sha256"),
                "theory_binding_bytes", field=binding["path"])
    raw_repair = (BASE / "format-repair-mu0001.1.json").read_bytes()
    repair = strict_json(raw_repair)
    require(repair.get("schema") == "munich-mu0001.1-format-repair/v1" and
            repair.get("parent_scientific_freeze") == "fc4305fe13" and
            repair.get("parent_first_admission") == "failed_without_statistical_verdict", "format_repair_lineage")
    for key in ("physics_prediction_changed", "e_process_changed", "alpha_changed", "pairs_denominator_changed"):
        require(repair.get(key) is False, "format_repair_scientific_invariance", field=key)
    observations = repair.get("observations", ())
    require(len(observations) == 2, "format_repair_inventory")
    for observation, spec in zip(observations, ARCHIVES):
        require(observation.get("run") == spec.run and observation.get("member") == spec.local2 and
                observation.get("header_fields") == 7 and observation.get("first_record_fields") == 6 and
                observation.get("row_model_values_reported") == 0 and observation.get("statistics_computed") == 0,
                "format_repair_observation", run=spec.run)
    criterion_path = BASE / "criterion-mu0001.1.md"
    criterion = criterion_path.read_text(encoding="utf-8")
    begin, end = "<!-- MUNICH-MU0001.1-FROZEN-BEGIN -->", "<!-- MUNICH-MU0001.1-FROZEN-END -->"
    require(criterion.count(begin) == 1 and criterion.count(end) == 1, "criterion_frozen_block")
    block = criterion.split(begin, 1)[1].split(end, 1)[0].strip()
    require(block.startswith("```json\n") and block.endswith("\n```"), "criterion_json_block")
    require(strict_json(block[8:-4]) == PROTOCOL, "criterion_protocol_mismatch")
    bindings = {
        "sources_json_sha256": hashlib.sha256(raw_sources).hexdigest(),
        "criterion_sha256": hashlib.sha256(criterion_path.read_bytes()).hexdigest(),
        "format_repair_sha256": hashlib.sha256(raw_repair).hexdigest(),
        "archive_bindings": sources["archives"], "header_bindings": sources["headers"],
        "readme_sha256": README_SHA256, "metadata_access_commit": sources["metadata_access_commit"],
        "header_access_commit": sources["header_access_commit"],
        "theory_authority": authority,
    }
    return bindings


def exclusive_json(path, value):
    with Path(path).open("x", encoding="utf-8") as stream:
        json.dump(value, stream, indent=2, sort_keys=True, ensure_ascii=False)
        stream.write("\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive-dir", type=Path, default=Path.home() / "Downloads",
                        help="Location of both byte-identical fixed archives; no selection override.")
    arguments = parser.parse_args()
    first = BASE / "primary-first-mu0001.1.json"
    attempt_path = BASE / "primary-attempt-mu0001.1.json"
    try:
        require(not first.exists() and not attempt_path.exists(), "first_attempt_already_reserved")
        provenance = committed_snapshot()
        bindings = load_frozen_inputs()
        # Reserve this version before any result-bearing member is decoded.
        attempt = {"schema": "stage10-munich-primary-attempt/v1", "version": PROTOCOL["version"],
                   "started_utc": datetime.now(timezone.utc).isoformat(), "source_bindings": bindings,
                   "provenance": provenance, "event_records_decoded_at_reservation": 0}
        exclusive_json(attempt_path, attempt)
    except (AdmissionError, OSError) as error:
        detail = error.detail if isinstance(error, AdmissionError) else {"code": "preexecution_filesystem"}
        print(json.dumps({"admission": "not_started", "scientific_verdict": "not_executed", "failure": detail}))
        return 2
    score_started = False
    access = {}
    try:
        admitted = {spec.run: admit_archive(arguments.archive_dir, spec, access) for spec in ARCHIVES}
        score_started = True
        receipt = adjudicate(admitted)
    except AdmissionError as error:
        receipt = {"schema": "stage10-munich-balanced-complement-primary/v1", "version": PROTOCOL["version"],
                   "admission": "admission_failed", "scientific_verdict": "not_executed", "failure": error.detail,
                   "scientific_adjudication_completed": False, "score_execution_started": score_started,
                   "real_instrument_empirical_verdict_executed": False}
    except Exception as error:
        receipt = {"schema": "stage10-munich-balanced-complement-primary/v1", "version": PROTOCOL["version"],
                   "admission": "execution_failed", "scientific_verdict": "not_executed",
                   "failure": {"code": "execution_error", "type": type(error).__name__},
                   "scientific_adjudication_completed": False, "score_execution_started": score_started,
                   "real_instrument_empirical_verdict_executed": False}
    receipt.update({"source_bindings": bindings, "provenance": provenance,
                    "attempt_sha256": hashlib.sha256(attempt_path.read_bytes()).hexdigest(),
                    "record_access": {
                        "members": [access[key] for key in sorted(access)],
                        "record_lines_in_read_csv_payloads": sum(item["record_lines_in_payload"] for item in access.values()),
                        "event_record_lines_decoded": sum(item["record_lines_decoded"] for item in access.values()),
                        "decoded_csv_members_in_full": sum(item["fully_decoded"] for item in access.values()),
                        "decoded_pairs_members_in_full": sum(item["fully_decoded"] and item["role"] == "pairs"
                                                             for item in access.values()),
                    }})
    exclusive_json(first, receipt)
    print(json.dumps({"admission": receipt["admission"], "scientific_verdict": receipt["scientific_verdict"],
                      "pair_records_scored": receipt.get("pair_records_scored", 0)}))
    return 0 if receipt["admission"] == "admitted" else 2


if __name__ == "__main__":
    raise SystemExit(main())
