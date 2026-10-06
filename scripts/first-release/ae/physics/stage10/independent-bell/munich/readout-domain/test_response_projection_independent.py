"""Synthetic exact-probability and full-parent-CS projection controls."""
from decimal import Decimal, localcontext
from fractions import Fraction
import copy
import itertools
from pathlib import Path
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import response_projection_independent as checker


def rows(counts=(7, 3, 4, 6)):
    return [{"h": h, "a": a, "b": b, "counts": list(counts)} for h, a, b in checker.CONTEXTS]


def beta_probability(counts):
    seen, result, total = [0] * 4, Fraction(1), 0
    for event, n in enumerate(counts):
        for _ in range(n):
            result *= Fraction(2 * seen[event] + 1, 2 * total + 4)
            seen[event] += 1
            total += 1
    return result


def exact_profile(original, context, p):
    numerator, likelihood = Fraction(1), Fraction(1)
    for row in original:
        counts, total = row["counts"], sum(row["counts"])
        numerator *= beta_probability(counts)
        key = tuple(row[k] for k in ("h", "a", "b"))
        even, odd = counts[0] + counts[3], counts[1] + counts[2]
        for event, n in enumerate(counts):
            if n:
                q = Fraction(n, total)
                if key == context:
                    q = p * Fraction(n, even) if event in (0, 3) else (1 - p) * Fraction(n, odd)
                likelihood *= q ** n
    return numerator / likelihood


def envelope(original, key, low=Fraction(1, 1 << 80), high=1 - Fraction(1, 1 << 80)):
    return checker.FullProfile(original, bits=160).certify(key, [str(low), str(high)])


def biases(alice=(Fraction(1, 10), Fraction(1, 5)), bob=(Fraction(3, 20), Fraction(1, 4))):
    return [{"side": side, "setting": setting, "mu_outer_interval": list(map(str, alice if side == "alice" else bob))}
            for side, setting in checker.ROLES]


def correlation_rows(original, interval=(Fraction(-7, 10), Fraction(-3, 5))):
    return [{**row, "correlation_outer_interval": list(map(str, interval))} for row in original]


class ProfileControls(unittest.TestCase):
    def assert_log_encloses_exact(self, profile, actual_interval, exact):
        with localcontext() as context:
            context.prec = 100
            actual = (Decimal(exact.numerator) / Decimal(exact.denominator)).ln()
            scale = Decimal(profile.arithmetic.scale)
            self.assertLessEqual(Decimal(actual_interval.lo) / scale, actual)
            self.assertGreaterEqual(Decimal(actual_interval.hi) / scale, actual)

    def test_integer_log_matches_sequential_Jeffreys_and_constrained_likelihood(self):
        original, key = rows(), (0, 1, 0)
        profile = checker.FullProfile(original, bits=160)
        for p in (Fraction(1, 100), profile.mle(key), Fraction(99, 100)):
            self.assert_log_encloses_exact(profile, profile.at(key, p), exact_profile(original, key, p))
        self.assertLess(profile.mle_log.hi, 0)

    def test_profile_is_below_actual_full_component_with_same_parity(self):
        original, key, p = rows(), (1, 0, 1), Fraction(1, 4)
        optimum = exact_profile(original, key, p)
        numerator, likelihood = Fraction(1), Fraction(1)
        for row in original:
            numerator *= beta_probability(row["counts"])
            same = tuple(row[k] for k in ("h", "a", "b")) == key
            q = (p / 2, (1 - p) / 2, (1 - p) / 2, p / 2) if same else (Fraction(1, 4),) * 4
            likelihood *= product(q[i] ** n for i, n in enumerate(row["counts"]))
        self.assertLessEqual(optimum, numerator / likelihood)

    def test_both_endpoints_pay_entire_outside_intervals_without_receipt_IO(self):
        original, key = rows(), (0, 0, 0)
        supplied = envelope(original, key)
        with patch.object(Path, "read_bytes", side_effect=AssertionError("source IO")):
            checked = checker.verify_correlation_envelope(original, key, supplied, bits=160)
        self.assertTrue(checked["entire_outside_intervals_excluded"])
        self.assertEqual(checked["component_threshold"], "80")
        self.assertFalse(checked["new_confidence_budget_spent"])
        profile = checker.FullProfile(original, bits=160)
        self.assertLess(profile.derivative_sign_numerator(key, supplied["p_outer_interval"][0]), 0)
        self.assertGreater(profile.derivative_sign_numerator(key, supplied["p_outer_interval"][1]), 0)

    def test_narrow_or_wrong_coordinate_or_new_budget_rejected(self):
        original, key = rows(), (0, 0, 0)
        supplied = envelope(original, key)
        for changes in ({"p_outer_interval": ["1/2", "7/10"]},
                        {"correlation_outer_interval": ["-1", "1"]},
                        {"new_confidence_budget_spent": True}, {"component_threshold": "40"},
                        {"counts": [True, 3, 4, 6]}, {"h": True}, {"parity_counts": [12, 8]}):
            candidate = dict(supplied, **changes)
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                checker.verify_correlation_envelope(original, key, candidate, bits=160)

    def test_observed_zero_parity_has_infinite_profile_without_epsilon(self):
        profile = checker.FullProfile(rows(), bits=160)
        self.assertIsNone(profile.at((0, 0, 0), 0))
        self.assertIsNone(profile.at((0, 0, 0), 1))
        boundary = checker.FullProfile(rows((0, 3, 2, 0)), bits=160)
        self.assertIsNotNone(boundary.at((0, 0, 0), 0))
        self.assertIsNone(boundary.at((0, 0, 0), 1))
        with self.assertRaises(ValueError):
            boundary.certify((0, 0, 0), ["0", "1"])

    def test_missing_duplicate_negative_and_boolean_original_counts_rejected(self):
        original = rows()
        for bad in (original[:7], original[:7] + [original[0]],
                    [{**original[0], "counts": [-1, 3, 4, 6]}] + original[1:],
                    [{**original[0], "a": False}] + original[1:]):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                checker.FullProfile(bad, bits=160)


def product(values):
    answer = Fraction(1)
    for value in values:
        answer *= value
    return answer


class ResponseControls(unittest.TestCase):
    def test_four_corner_bias_products_and_all_four_contexts_pay_gain_errors(self):
        original = rows()
        result = checker.response_envelopes(original, correlation_rows(original), biases())
        self.assertEqual(len(result), 4)
        for row in result:
            self.assertEqual(len(row["source_contributions"]), 4)
            self.assertEqual(row["canonical_gain"][0], "123/200")
            self.assertEqual(row["source_contributions"][0]["bias_product_outer_interval"], ["3/200", "1/20"])
            self.assertEqual(row["source_contributions"][0]["centered_correlation_outer_interval"], ["-3/4", "-123/200"])
            self.assertFalse(row["actual_ideal_label_identity_selected"])
        self.assertEqual(result[0]["canonical_gain"], ["123/200", "9/10"])
        self.assertEqual(result[0]["canonical_e0"], ["0", "57/400"])
        self.assertEqual(result[0]["canonical_e1"], ["1/10", "117/400"])

    def test_centered_interval_crossing_zero_cannot_fabricate_gain(self):
        original = rows()
        result = checker.response_envelopes(original, correlation_rows(original, (Fraction(-1, 5), Fraction(1, 5))),
                                            biases((Fraction(-1, 10), Fraction(1, 10)), (Fraction(-1, 10), Fraction(1, 10))))
        self.assertTrue(all(row["canonical_gain"] == ["0", "1"] for row in result))

    def test_maximum_uses_every_herald_and_remote_setting(self):
        original = rows()
        correlations = correlation_rows(original, (Fraction(-1, 10), Fraction(1, 10)))
        correlations[-1]["correlation_outer_interval"] = ["4/5", "9/10"]
        result = checker.response_envelopes(original, correlations,
                                            biases((Fraction(0), Fraction(0)), (Fraction(0), Fraction(0))))
        self.assertEqual([row["canonical_gain"][0] for row in result], ["0", "4/5", "0", "4/5"])

    def test_false_context_counts_bias_role_or_source_cone_rejected(self):
        original, correlations, bounds = rows(), correlation_rows(rows()), biases()
        wrong_counts = copy.deepcopy(correlations)
        wrong_counts[0]["counts"][0] += 1
        wrong_role = copy.deepcopy(bounds)
        wrong_role[0]["setting"] = False
        cone = biases((Fraction(9, 10), Fraction(19, 20)), (Fraction(9, 10), Fraction(19, 20)))
        for corr, bias in ((correlations[:7], bounds), (wrong_counts, bounds), (correlations, wrong_role), (correlations, cone)):
            with self.subTest(corr=corr, bias=bias), self.assertRaises(ValueError):
                checker.response_envelopes(original, corr, bias)


def synthetic_reports():
    original = rows()
    bounds = biases((Fraction(-1, 10), Fraction(1, 10)), (Fraction(-1, 10), Fraction(1, 10)))
    profile = checker.FullProfile(original)
    epsilon = Fraction(1, 1 << 80)
    correlations = [profile.certify(key, [str(epsilon), str(1 - epsilon)]) for key in checker.CONTEXTS]
    responses = checker.response_envelopes(original, correlations, bounds)
    primary = {"schema": checker.PRIMARY_SCHEMA, "version": checker.VERSION,
               "status": "generated_parent_confidence_response_envelopes",
               "whole_empirical_confidence_set_bounds": True, "simultaneous_necessary_outer_projections": True,
               "parent_confidence_budget": "1/20", "new_confidence_budget_spent": False,
               "fixed_law_point_used_as_confidence_bound": False, "hardware_parameter_uniqueness_certified": False,
               "trial_event_files_read": 0, "optimizer_executed": False, "new_statistical_fit_executed": False,
               "full_component_threshold": "80", "runs": []}
    counted = {"schema": "stage10-munich-readout-primary-point/v1", "version": "stage10-munich-readout-rd0001", "runs": []}
    biased = {"schema": "stage10-munich-readout-identification-primary/v1", "version": "stage10-munich-readout-id0001", "runs": []}
    for index, run in enumerate(checker.source.RUNS):
        factor = ("01" if index == 0 else "02") * 32
        primary["runs"].append({"run": run, "correlation_envelopes": copy.deepcopy(correlations),
                                "response_envelopes": copy.deepcopy(responses), "bias_envelopes": copy.deepcopy(bounds),
                                "parent_trials": 160, "parent_factor_sequence_sha256": factor})
        counted["runs"].append({"run": run, "four_outcomes": copy.deepcopy(original), "trials": 160,
                                "prefix_check": {"factor_sequence_sha256": factor}})
        biased["runs"].append({"run": run, "bias_envelopes": copy.deepcopy(bounds)})
    return primary, counted, biased


class ReportControls(unittest.TestCase):
    def test_entire_ordered_two_run_report_has_32_endpoint_checks_without_IO(self):
        reports = synthetic_reports()
        with patch.object(Path, "read_bytes", side_effect=AssertionError("receipt IO")):
            result = checker.verify_report(*reports)
        self.assertTrue(result["evidence_valid"])
        self.assertEqual(result["correlation_envelopes_checked"], 16)
        self.assertEqual(result["correlation_endpoints_checked"], 32)
        self.assertEqual(result["response_envelopes_checked"], 8)
        self.assertFalse(result["source_optimizer_executed"])
        self.assertEqual(tuple(row["run"] for row in result["runs"]), checker.source.RUNS)

    def test_partial_family_boolean_literal_and_lookalike_report_rejected(self):
        for field, value in (("schema", "stage10-munich-readout-response-projection-primary/v2"),
                             ("trial_event_files_read", False), ("parent_confidence_budget", "1/10"),
                             ("whole_empirical_confidence_set_bounds", 1)):
            primary, counted, biased = synthetic_reports()
            primary[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                checker.verify_report(primary, counted, biased)
        primary, counted, biased = synthetic_reports()
        primary["runs"].pop()
        with self.assertRaises(ValueError):
            checker.verify_report(primary, counted, biased)

    def test_disjoint_log_changed_response_bias_factor_and_context_order_rejected(self):
        mutations = (
            lambda run: run["correlation_envelopes"][0].update(lower_endpoint_log_e={"lower": "1000", "upper": "1001"}),
            lambda run: run["response_envelopes"][0].update(canonical_gain=["0", "1/2"]),
            lambda run: run["bias_envelopes"][0].update(mu_outer_interval=["-1/2", "1/2"]),
            lambda run: run.update(parent_factor_sequence_sha256="ff" * 32),
            lambda run: run["correlation_envelopes"].reverse())
        for change in mutations:
            primary, counted, biased = synthetic_reports()
            change(primary["runs"][0])
            with self.subTest(change=change), self.assertRaises(ValueError):
                checker.verify_report(primary, counted, biased)

    def test_program_and_first_attempt_binding_guard_is_independent_of_real_files(self):
        names = [str((checker.BASE / name).relative_to(checker.ROOT)) for name in (*checker.FILES, *checker.INPUTS)]
        names.append(str(checker.MODULE.relative_to(checker.ROOT)))
        bindings = [{"path": name, "sha256": f"{index:064x}"} for index, name in enumerate(names)]
        inventory = {row["path"]: row["sha256"] for row in bindings}
        primary = {"source_bindings": bindings, "freeze_commit": "frozen-cp", "execution_head": "science-head",
                   "kernel_sha256": inventory[str((checker.BASE / "response-bounds-certification-first.json").relative_to(checker.ROOT))],
                   "parent_identification_sha256": inventory[str((checker.BASE / "identification-verification.json").relative_to(checker.ROOT))]}
        attempt = {"version": checker.VERSION, "freeze_commit": "frozen-cp", "execution_head": "science-head",
                   "source_bindings": bindings, "event_files_read_at_reservation": 0}
        raw = checker.source.canonical(attempt).encode()
        primary["attempt_sha256"] = checker.source.digest(raw)
        provenance = {"freeze_commit": "frozen-cp", "execution_head": "intake-head"}
        with patch.object(checker.source, "frozen_bytes", return_value=raw), \
                patch.object(checker.source.subprocess, "run", return_value=SimpleNamespace(returncode=0)):
            checker.primary_provenance(primary, bindings, provenance)
            primary["attempt_sha256"] = "changed-attempt"
            with self.assertRaises(ValueError):
                checker.primary_provenance(primary, bindings, provenance)
        with patch.object(checker.source, "frozen_bytes", side_effect=lambda path, commit="HEAD":
                          b"mutated-program" if commit == "HEAD" else b"frozen-program"):
            with self.assertRaises(ValueError):
                checker.frozen_bindings("frozen-cp")


if __name__ == "__main__":
    unittest.main()
