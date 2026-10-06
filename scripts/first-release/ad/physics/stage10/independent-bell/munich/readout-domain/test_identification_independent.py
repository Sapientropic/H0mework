"""Synthetic source/gauge and confidence-projection controls; no receipt input."""
from decimal import Decimal, localcontext
from fractions import Fraction
import itertools
import math
from pathlib import Path
import unittest
from unittest.mock import patch

import identification_independent as checker


def point():
    effect = checker.source.Effect
    return {"alice": (effect(Fraction(1, 10), Fraction(1, 4), Fraction(1, 5)),
                      effect(Fraction(-1, 10), Fraction(1, 5), Fraction(-1, 4))),
            "bob": (effect(Fraction(1, 8), Fraction(1, 5), Fraction(1, 6)),
                    effect(Fraction(-1, 8), Fraction(-1, 6), Fraction(1, 5)))}


class SourceFiberControls(unittest.TestCase):
    def test_actual_8D_law_is_unchanged_for_both_scales_and_signs(self):
        original = point()
        for s, t in ((Fraction(21, 20), Fraction(21, 20)),
                     (Fraction(21, 20), Fraction(19, 20)), (Fraction(-1), Fraction(1))):
            alternative = checker.encode_point(checker.scaled_point(original, s, t))
            with self.subTest(s=s, t=t), patch.object(Path, "read_bytes", side_effect=AssertionError("source IO")):
                result = checker.check_alternative(original, alternative, s, t)
            self.assertEqual(result["probabilities_compared"], 32)
            self.assertTrue(result["all_8D_generated_probabilities_unchanged"])
            if s > 0:
                self.assertTrue(result["changed_canonical_channel_settings"])

    def test_isotropic_gain_changes_without_axis_change(self):
        original = point()
        scaled = checker.scaled_point(original, checker.HIGH, checker.HIGH)
        for side in ("alice", "bob"):
            for old, new in zip(original[side], scaled[side]):
                self.assertEqual(old.u * new.z, old.z * new.u)
                self.assertNotEqual(old.u ** 2 + old.z ** 2, new.u ** 2 + new.z ** 2)

    def test_complete_rectangle_has_four_monotone_slacks(self):
        result = checker.rectangle(point())
        self.assertEqual(len(result["constraints"]), 4)
        self.assertTrue(all(Fraction(row["slack"]) > 0 for row in result["constraints"]))
        self.assertFalse(result["finite_samples_used_as_coverage"])
        with self.assertRaises(ValueError):
            checker.rectangle(point(), Fraction(1, 100), Fraction(100))

    def test_wrong_scale_zero_scale_illegal_effect_or_extra_target_rejected(self):
        with self.assertRaises(ValueError):
            checker.scaled_point(point(), 0, 1)
        with self.assertRaises(ValueError):
            checker.scaled_point(point(), 100, 1)
        wrong = checker.encode_point(point())
        with self.assertRaises(ValueError):
            checker.check_alternative(point(), wrong, checker.HIGH, checker.HIGH)
        wrong["probabilities"] = ["1/4"] * 32
        with self.assertRaises(ValueError):
            checker.check_alternative(point(), wrong, 1, 1)

    def test_observables_recovered_only_from_full_Born_table(self):
        original = point()
        quotient = checker.recover_observables(checker.source.born_table(original))
        self.assertEqual(quotient["alice_bias"], [str(e.mu) for e in original["alice"]])
        self.assertEqual(quotient["X"][0][0], str(original["alice"][0].u * original["bob"][0].u))
        self.assertEqual(quotient["Z"][0][0], str(original["alice"][0].z * original["bob"][0].z))
        descriptor = checker.regular_description(original, quotient)
        self.assertEqual(len(descriptor["sign_branches"]), 4)
        self.assertFalse(descriptor["fixed_generated_law_is_actual_empirical_probability"])
        incomplete = checker.source.born_table(original)
        incomplete.pop(next(iter(incomplete)))
        with self.assertRaises(ValueError):
            checker.recover_observables(incomplete)


class ProjectionControls(unittest.TestCase):
    def test_full_context_counts_project_to_own_settings(self):
        rows = [{"h": h, "a": a, "b": b, "counts": [2, 3, 5, 7]}
                for h, a, b in itertools.product((0, 1), repeat=3)]
        expected = {"alice": [[20, 48], [20, 48]], "bob": [[28, 40], [28, 40]]}
        self.assertEqual(checker.own_setting_counts(rows), expected)
        rows[0]["counts"][0] = True
        with self.assertRaises(ValueError):
            checker.own_setting_counts(rows)

    def test_duplicate_context_missing_context_and_boolean_setting_rejected(self):
        rows = [{"h": h, "a": a, "b": b, "counts": [1] * 4}
                for h, a, b in itertools.product((0, 1), repeat=3)]
        rows[-1] = rows[0]
        with self.assertRaises(ValueError):
            checker.own_setting_counts(rows)
        with self.assertRaises(ValueError):
            checker.own_setting_counts(rows[:7])
        with self.assertRaises(ValueError):
            checker.Profile([[40, 60], [55, 45]], False)

    def test_integer_profile_matches_independent_exact_probability_oracle(self):
        counts = [[40, 60], [55, 45]]
        profile = checker.Profile(counts, 0, bits=160)
        pooled = [95, 105]
        beta = Fraction(math.prod(range(1, 2 * pooled[0], 2)) * math.prod(range(1, 2 * pooled[1], 2)),
                        2 ** sum(pooled) * math.factorial(sum(pooled)))
        other = Fraction(55, 100) ** 55 * Fraction(45, 100) ** 45
        for p in (Fraction(1, 20), Fraction(2, 5), Fraction(19, 20)):
            exact = beta / (p ** 40 * (1 - p) ** 60 * other)
            interval = profile.at(p)
            with localcontext() as context:
                context.prec = 100
                actual = (Decimal(exact.numerator) / Decimal(exact.denominator)).ln()
                self.assertLessEqual(Decimal(interval.lo) / Decimal(profile.arithmetic.scale), actual)
                self.assertGreaterEqual(Decimal(interval.hi) / Decimal(profile.arithmetic.scale), actual)

    def test_both_entire_outside_intervals_are_excluded_without_new_alpha(self):
        profile = checker.Profile([[40, 60], [55, 45]], 0, bits=160)
        result = profile.certify(Fraction(1, 20), Fraction(19, 20), parent_mu=Fraction(-1, 5))
        self.assertTrue(result["entire_outside_intervals_excluded"])
        self.assertFalse(result["new_confidence_budget_spent"])
        self.assertEqual(result["component_threshold"], "240")
        self.assertLess(profile.derivative_sign_numerator(Fraction(1, 20)), 0)
        self.assertGreater(profile.derivative_sign_numerator(Fraction(19, 20)), 0)
        with self.assertRaises(ValueError):
            profile.certify(Fraction(3, 10), Fraction(7, 10))

    def test_zero_support_does_not_use_epsilon_and_other_empty_MLE_is_exact(self):
        profile = checker.Profile([[40, 60], [0, 0]], 0, bits=160)
        self.assertIsNone(profile.at(0))
        self.assertIsNone(profile.at(1))
        self.assertEqual(profile.other_mle, Fraction(1, 2))
        self.assertTrue(profile.certify(0, 1)["entire_outside_intervals_excluded"])
        with self.assertRaises(ValueError):
            checker.Profile([[0, 0], [0, 0]], 0)


class FrozenReceiptControls(unittest.TestCase):
    def test_primary_program_and_first_attempt_are_bound_without_receipt_IO(self):
        bindings = [{"path": str((checker.BASE / name).relative_to(checker.ROOT)), "sha256": str(index)}
                    for index, name in enumerate((*checker.PRIMARY_FILES, *checker.PARENT_FILES))]
        hashes = {row["path"]: row["sha256"] for row in bindings}
        attempt = {"version": checker.VERSION, "freeze_commit": "frozen-science",
                   "source_bindings": bindings, "event_files_read_at_reservation": 0}
        raw = checker.canonical(attempt).encode()
        primary = {"freeze_commit": "frozen-science", "source_bindings": bindings,
                   "parent_certificate_sha256": hashes[str((checker.BASE / "verification.json").relative_to(checker.ROOT))],
                   "identification_kernel_sha256": hashes[str((checker.BASE / "identification-certification-first.json").relative_to(checker.ROOT))],
                   "attempt_sha256": checker.source.digest(raw)}
        with patch.object(checker.source, "frozen_bytes", return_value=raw):
            checker.primary_provenance(primary, bindings, "frozen-science")
            with self.assertRaises(ValueError):
                checker.primary_provenance(primary, bindings, "different-science")
            primary["source_bindings"] = bindings[:-1]
            with self.assertRaises(ValueError):
                checker.primary_provenance(primary, bindings, "frozen-science")
            primary["source_bindings"] = bindings
            primary["attempt_sha256"] = "different-first-attempt"
            with self.assertRaises(ValueError):
                checker.primary_provenance(primary, bindings, "frozen-science")


if __name__ == "__main__":
    unittest.main()
