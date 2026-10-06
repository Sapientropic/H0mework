"""Shared response uses all four contexts and exactly one global numerator."""
from fractions import Fraction
import math
import unittest

import shared_response as producer


def rows():
    return [{"h": h, "a": a, "b": b, "counts": [45, 5, 5, 45]} for h, a, b in producer.CONTEXTS]


def biases():
    return [{"side": side, "setting": setting, "mu_outer_interval": ["0", "0"]} for side, setting in producer.ROLES]


class SharedResponseTests(unittest.TestCase):
    def setUp(self):
        self.full = producer.FullProfile(rows())
        self.profile = producer.SharedProfile(self.full, biases(), "alice", 0)

    def test_clipped_mle_and_all_four_contexts(self):
        result = self.profile.at(Fraction(1, 2))
        self.assertEqual(len(result["contexts"]), 4)
        self.assertEqual([row["context"] for row in result["contexts"]], [[0, 0, 0], [0, 0, 1], [1, 0, 0], [1, 0, 1]])
        for row in result["contexts"]:
            self.assertEqual(row["allowed_even_probability"], ["1/4", "3/4"])
            self.assertEqual(row["maximizing_even_probability"], "3/4")

    def test_global_numerator_appears_once(self):
        gain = Fraction(1, 2)
        counts = [45, 5, 5, 45]
        numerator = Fraction(1, math.factorial(101))
        for n in counts:
            numerator *= Fraction(math.factorial(2 * n), 4 ** n * math.factorial(n))
        q_selected = (Fraction(3, 8), Fraction(1, 8), Fraction(1, 8), Fraction(3, 8))
        q_other = tuple(Fraction(n, 100) for n in counts)
        likelihood = math.prod(q ** n for q, n in zip(q_selected, counts)) ** 4 * \
                     math.prod(q ** n for q, n in zip(q_other, counts)) ** 4
        direct = self.full.arithmetic.logarithm(numerator ** 8 / likelihood)
        actual = self.profile.at(gain)["interval"]
        self.assertLessEqual(direct.lower, actual.upper)
        self.assertLessEqual(actual.lower, direct.upper)

    def test_nested_gain_bands_make_profile_nonincreasing(self):
        values = [self.profile.at(Fraction(i, 4))["interval"] for i in range(5)]
        for left, right in zip(values[:-1], values[1:]):
            self.assertGreater(left.lower, right.upper)
        plateau = self.profile.at(Fraction(9, 10))["interval"]
        self.assertLessEqual(plateau.lower, values[4].upper)
        self.assertLessEqual(values[4].lower, plateau.upper)

    def test_rejected_low_gain_range_and_certified_threshold_bracket(self):
        result = self.profile.bounds("0")
        lo, hi = map(Fraction, result["shared_profile_threshold_bracket"])
        self.assertLessEqual(hi - lo, producer.BRACKET)
        self.assertGreaterEqual(self.profile.at(lo)["interval"].lower, self.full.threshold.upper)
        self.assertLess(self.profile.at(hi)["interval"].upper, self.full.threshold.lower)
        self.assertTrue(result["entire_low_response_interval_excluded"])
        self.assertFalse(result["actual_gain_extremum_sharpness_claimed"])

    def test_bob_uses_all_herald_and_alice_settings(self):
        profile = producer.SharedProfile(self.full, biases(), "bob", 1)
        self.assertEqual([row["context"] for row in profile.at(0)["contexts"]], [[0, 0, 1], [0, 1, 1], [1, 0, 1], [1, 1, 1]])

    def test_invalid_roles_and_duplicate_bias_rejected(self):
        with self.assertRaises(ValueError):
            producer.SharedProfile(self.full, biases(), "alice", True)
        invalid = biases()
        invalid[-1] = invalid[0]
        with self.assertRaises(ValueError):
            producer.SharedProfile(self.full, invalid, "alice", 0)

    def test_observed_zero_mass_is_infinite_without_epsilon(self):
        changed = biases()
        for row in changed:
            row["mu_outer_interval"] = ["1", "1"]
        result = producer.SharedProfile(self.full, changed, "alice", 0).at(0)
        self.assertEqual(result["log_e"], {"infinite": True})


if __name__ == "__main__":
    unittest.main()
