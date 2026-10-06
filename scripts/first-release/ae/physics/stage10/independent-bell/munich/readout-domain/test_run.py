"""Synthetic records and mocked optimizer controls; no official archive is opened."""
import contextlib
import copy
from fractions import Fraction
import io
from itertools import product
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import run as driver
from model import Effect, Instrument, encode
from primary import polar_effects


def admitted(run=driver.RUNS[0], bits=None):
    bits = tuple(product((0, 1), repeat=5)) if bits is None else bits
    trials = tuple(SimpleNamespace(row=number, time_ms=Fraction(1000 + number),
                                   h=h, a=a, b=b, x=x, y=y, row_a=number, row_b=number)
                   for number, (h, a, b, x, y) in enumerate(bits, 1))
    audit = {"pair_records": len(trials), "original_pair_order_preserved": True,
             "all_pairs_joined": True, "additional_outcome_selection": False,
             "local1": {"unpaired_original_rows_rle": [[99, 101]]},
             "pairs_original_bytes_sha256": "synthetic_pair_payload"}
    return SimpleNamespace(run=run, trials=trials, audit=audit,
                           token_dictionaries={key: ["0", "1"] for key in ("h", "a", "b", "x", "y")})


def flat_primitive():
    effect = Effect(0, 0, 0)
    return encode(Instrument((effect, effect), (effect, effect)))


def candidate(document=None):
    return {"primitive": flat_primitive() if document is None else document,
            "approximate_terminal_log_e": 0., "optimizer_success": False,
            "numerical_verdict_certified": False, "all_prefix_checked": False}


def old_firsts(family):
    results = []
    for item in family.values():
        summary = driver.summarize(item)
        results.append({"run": item.run, "trials": summary["trials"],
                        "four_outcomes": summary["four_outcomes"], "pooled_counts": summary["pooled_counts"],
                        "local_audit": copy.deepcopy(item.audit),
                        "token_dictionaries": copy.deepcopy(item.token_dictionaries),
                        "all_pair_records_scored": True, "prefix_e_sha256": "0" * 64})
    return [{"runs": copy.deepcopy(results)} for _ in range(2)]


class DriverControls(unittest.TestCase):
    def test_root_and_fixed_complete_search_declaration(self):
        self.assertEqual(driver.ROOT, driver.BASE.parents[5])
        starts = driver.search_starts()
        self.assertEqual(starts, driver.search_starts())
        self.assertEqual(len(starts), 35)
        self.assertEqual(driver.SEARCH_DECLARATION["starts_count"], 35)
        self.assertEqual(driver.PRECISIONS, (80, 160, 320))
        for point in starts:
            self.assertEqual(len(polar_effects(point)), 4)

    def test_positive_exact_source_all_prefixes_without_optimizer_verdict(self):
        item = admitted()
        with patch.object(driver, "search_terminal", return_value=(candidate(),)) as search:
            result = driver.certify_run(item, driver.summarize(item))
        self.assertEqual(search.call_count, 35)
        self.assertEqual(result["searchcount"]["checked_candidates"], 1)
        self.assertEqual(result["status"], "all_prefix_witness_verified")
        self.assertTrue(result["all_prefixes_below_threshold_certified"])
        self.assertEqual(result["prefix_check"]["trials"], 32)
        self.assertEqual(len(result["source_probabilities"]), 32)
        self.assertEqual({row["q"] for row in result["source_probabilities"]}, {"1/4"})
        self.assertFalse(result["candidate_checks"][0]["optimizer_success"])

    def test_source_like_target_probability_and_noncanonical_primitives_fail(self):
        point = flat_primitive()
        self.assertEqual(encode(driver.validate_candidate(point)), point)
        for field in ("targetq", "probabilities", "visibility"):
            with self.assertRaises(driver.DriverError):
                driver.validate_candidate({**point, field: []})
        for value in ("0/1", 0, .0, "0.0"):
            wrong = copy.deepcopy(point)
            wrong["alice"][0]["mu"] = value
            with self.assertRaises((driver.DriverError, ValueError, TypeError)):
                driver.validate_candidate(wrong)

    def test_boundary_precision_escalates_without_guessing(self):
        item = admitted()
        def check(trials, table, precision):
            return {"status": "numerical_boundary_unresolved" if precision < 320 else "all_prefix_witness_verified",
                    "trials": len(trials), "all_prefixes_checked": True, "numerical_precision": precision}
        with patch.object(driver, "check_prefixes", side_effect=check):
            result = driver.check_candidate(item, flat_primitive())
        self.assertEqual(result["precision_attempts"], [80, 160, 320])
        self.assertEqual(result["prefix_check"]["status"], "all_prefix_witness_verified")

    def test_zero_probability_point_excluded_without_epsilon(self):
        pole = Effect(0, 0, 1)
        document = encode(Instrument((pole, pole), (pole, pole)))
        with patch.object(driver, "check_prefixes") as checker:
            result = driver.check_candidate(admitted(), document)
        checker.assert_not_called()
        self.assertEqual(result["prefix_check"]["status"], "zero_model_probability_observed")
        self.assertEqual(result["prefix_check"]["first_zero_model_probability_prefix"], 1)

    def test_all_points_excluded_is_unresolved_not_global_no_go(self):
        item = admitted(bits=[(0, 0, 0, 0, 0)] * 40)
        with patch.object(driver, "search_starts", return_value=((0., 0., 0.) * 4,)), \
                patch.object(driver, "search_terminal", return_value=(candidate(),)):
            result = driver.certify_run(item, driver.summarize(item))
        self.assertEqual(result["status"], "unresolved")
        self.assertEqual(result["candidate_checks"][0]["prefix_check"]["status"], "point_excluded")
        self.assertEqual(result["candidate_checks"][0]["prefix_check"]["trials"], 40)
        self.assertFalse(result["global_domain_rejection_claimed"])

    def test_search_failure_is_unresolved_and_remaining_starts_are_attempted(self):
        item = admitted()
        with patch.object(driver, "search_terminal", side_effect=RuntimeError("synthetic optimizer failure")) as search:
            result = driver.certify_run(item, driver.summarize(item))
        self.assertEqual(search.call_count, 35)
        self.assertEqual(result["status"], "unresolved")
        self.assertEqual(len(result["search_attempts"]), 35)
        self.assertFalse(result["global_domain_rejection_claimed"])

    def test_full_legacy_audit_dictionary_and_counts_are_checked(self):
        item = admitted()
        firsts = old_firsts({item.run: item})
        summary = driver.summarize(item)
        self.assertTrue(driver.legacy_cross(item, summary, firsts)["full_local_audit_checked"])
        for field in ("local_audit", "token_dictionaries", "four_outcomes", "pooled_counts"):
            changed = copy.deepcopy(firsts)
            changed[1]["runs"][0][field] = {}
            with self.assertRaises(driver.DriverError):
                driver.legacy_cross(item, summary, changed)

    def test_changed_original_order_rejected_before_search(self):
        item = admitted()
        item.trials[0].row = 2
        with self.assertRaises(driver.DriverError):
            driver.summarize(item)

    def test_dirty_guard_is_scoped_to_declared_scientific_paths(self):
        def git(*args):
            return b"fakehead\n" if args[0] == "rev-parse" else b" M owned.py\n"
        with patch.object(driver, "git", side_effect=git) as command:
            with self.assertRaisesRegex(driver.DriverError, "dirty_scientific_paths"):
                driver.committed_snapshot("synthetic-freeze")
        status_args = command.call_args_list[-1].args
        self.assertEqual(status_args[:3], ("status", "--porcelain", "--"))
        self.assertTrue(all(path.startswith("Verification/physics/stage10/independent-bell/munich/") or
                            path.startswith("Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/")
                            for path in status_args[3:]))

    def test_worktree_bytes_must_equal_head_without_filter_conversion(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            path = root / "pure.py"
            path.write_bytes(b"same\r\n")
            with patch.object(driver, "ROOT", root), patch.object(driver, "git", return_value=b"same\n"):
                with self.assertRaisesRegex(driver.DriverError, "scientific_input_not_frozen"):
                    driver.frozen_bytes(path)

    def test_lookalike_archive_name_does_not_admit_wrong_bytes(self):
        parser = driver.load_module(driver.PARENT / "schema.py", "_readout_synthetic_parser_control", driver.PARSER_SHA256)
        with tempfile.TemporaryDirectory() as directory:
            spec = parser.ARCHIVES[0]
            (Path(directory) / spec.name).write_bytes(b"PK synthetic non-source archive")
            with self.assertRaisesRegex(parser.AdmissionError, "archive_bytes_mismatch"):
                parser.admit_archive(Path(directory), spec)

    def test_cli_default_and_explicit_archive_directory_override(self):
        report = {"status": "not_started", "scientific_verdict": "not_executed", "source_point_certified": False}
        with patch.object(driver, "execute", return_value=(report, 2)) as execute, contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(driver.main(["--freeze-commit", "frozen"]), 2)
            self.assertEqual(execute.call_args.args, (Path.home() / "Downloads", "frozen"))
            self.assertEqual(driver.main(["--freeze-commit", "frozen", "--archive-dir", "/synthetic/location"]), 2)
            self.assertEqual(execute.call_args.args, (Path("/synthetic/location"), "frozen"))

    def fixture(self, output, admission_error=None):
        family = {run: admitted(run) for run in driver.RUNS}
        archives = tuple(SimpleNamespace(run=run, name=f"synthetic-{run}.zip") for run in driver.RUNS)
        seen = []
        def admit(directory, spec, access):
            attempt = json.loads((output / "primary-attempt.json").read_bytes())
            self.assertEqual(attempt["event_records_decoded_at_reservation"], 0)
            seen.append((directory, spec.run))
            if admission_error is not None:
                raise admission_error
            return family[spec.run]
        inputs = {"parser": SimpleNamespace(ARCHIVES=archives, admit_archive=admit),
                  "legacy_firsts": old_firsts(family), "legacy_first_bindings": [],
                  "bindings": {"parent": {"archive_bindings": []}, "kernel_receipt_bindings": []}}
        snapshot = {"freeze_commit": "synthetic-freeze", "execution_head": "synthetic-head", "program_bindings": []}
        return inputs, snapshot, seen

    def test_success_reserves_before_decode_and_writes_primitive_only_witness(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            inputs, snapshot, seen = self.fixture(output)
            with patch.object(driver, "committed_snapshot", return_value=snapshot), \
                    patch.object(driver, "load_frozen_inputs", return_value=inputs), \
                    patch.object(driver, "solver_environment", return_value={"python": "synthetic", "numpy": "synthetic", "scipy": "1.13.1"}), \
                    patch.object(driver, "search_terminal", return_value=(candidate(),)):
                report, status = driver.execute(Path("/synthetic/archives"), "synthetic-freeze", output_dir=output)
            self.assertEqual(status, 0)
            self.assertTrue(report["source_point_certified"])
            self.assertEqual(seen, [(Path("/synthetic/archives"), run) for run in driver.RUNS])
            witness = json.loads((output / "primitive-witness.json").read_bytes())
            self.assertEqual(set(witness), {"schema", "version", "runs"})
            self.assertEqual(witness["schema"], driver.WITNESS_SCHEMA)
            self.assertEqual([entry["run"] for entry in witness["runs"]], list(driver.RUNS))
            self.assertTrue(all(set(entry) == {"run", "primitive"} for entry in witness["runs"]))
            self.assertEqual(report["witness_sha256"], driver.digest((output / "primitive-witness.json").read_bytes()))
            self.assertEqual(report["attempt_sha256"], driver.digest((output / "primary-attempt.json").read_bytes()))
            self.assertEqual(json.loads((output / "primary-first.json").read_bytes()), report)

    def test_preexecution_failure_saved_without_decode_or_attempt(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            with patch.object(driver, "committed_snapshot", side_effect=driver.DriverError("dirty_scientific_paths")), \
                    patch.object(driver, "load_frozen_inputs") as inputs:
                report, status = driver.execute(Path("/synthetic"), "synthetic-freeze", output_dir=output)
            inputs.assert_not_called()
            self.assertEqual(status, 2)
            self.assertEqual(report["status"], "not_started")
            self.assertFalse((output / "primary-attempt.json").exists())
            self.assertEqual(report["record_access"]["event_record_lines_decoded"], 0)
            self.assertEqual(json.loads((output / "primary-first.json").read_bytes()), report)

    def test_admission_failure_preserves_reserved_attempt_and_first(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            inputs, snapshot, _ = self.fixture(output, driver.DriverError("archive_bytes_mismatch"))
            with patch.object(driver, "committed_snapshot", return_value=snapshot), \
                    patch.object(driver, "load_frozen_inputs", return_value=inputs), \
                    patch.object(driver, "solver_environment", return_value={"python": "synthetic", "numpy": "synthetic", "scipy": "1.13.1"}), \
                    patch.object(driver, "search_terminal") as search:
                report, status = driver.execute(Path("/synthetic"), "synthetic-freeze", output_dir=output)
            search.assert_not_called()
            self.assertEqual(status, 1)
            self.assertEqual(report["failure"]["code"], "archive_bytes_mismatch")
            self.assertFalse(report["source_point_certified"])
            self.assertTrue((output / "primary-attempt.json").exists())
            self.assertTrue((output / "primary-first.json").exists())

    def test_first_attempt_and_witness_are_never_overwritten(self):
        for filename in ("primary-first.json", "primary-attempt.json", "primitive-witness.json"):
            with self.subTest(filename=filename), tempfile.TemporaryDirectory() as directory:
                output = Path(directory)
                original = b"previous once-only evidence\n"
                (output / filename).write_bytes(original)
                with patch.object(driver, "committed_snapshot") as guard:
                    report, status = driver.execute(Path("/synthetic"), "synthetic-freeze", output_dir=output)
                guard.assert_not_called()
                self.assertEqual(status, 2)
                self.assertEqual(report["failure"]["code"], "first_attempt_already_reserved")
                self.assertEqual((output / filename).read_bytes(), original)
                self.assertEqual(len(list(output.iterdir())), 1)


if __name__ == "__main__":
    unittest.main()
