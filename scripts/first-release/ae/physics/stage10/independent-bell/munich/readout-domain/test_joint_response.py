"""Joint gain-product constraints preserve one global likelihood numerator."""
from fractions import Fraction
import math
import unittest

import joint_response as producer


def rows():
    return [{"h": h, "a": a, "b": b, "counts": [45, 5, 5, 45]} for h, a, b in producer.CONTEXTS]


def biases():
    return [{"side": side, "setting": setting, "mu_outer_interval": ["0", "0"]} for side, setting in producer.ROLES]


class JointResponseTests(unittest.TestCase):
    def setUp(self):
        self.full = producer.FullProfile(rows())
        self.profile = producer.JointProfile(self.full, biases())

    def test_gain_product_and_all_eight_contexts(self):
        result = self.profile.at([Fraction(1, 2), Fraction(3, 4), Fraction(2, 3), Fraction(1, 4)])
        self.assertEqual(len(result["contexts"]), 8)
        for row in result["contexts"]:
            _, a, b = row["context"]
            radius = (Fraction(1, 2), Fraction(3, 4))[a] * (Fraction(2, 3), Fraction(1, 4))[b]
            self.assertEqual(row["gain_product_cap"], str(radius))
            self.assertEqual(row["allowed_even_probability"], list(map(str, ((1 - radius) / 2, (1 + radius) / 2))))

    def test_exact_full_likelihood_once(self):
        count = [45, 5, 5, 45]
        numerator = Fraction(1, math.factorial(101))
        for n in count:
            numerator *= Fraction(math.factorial(2 * n), 4 ** n * math.factorial(n))
        probabilities = [Fraction(5, 16), Fraction(3, 16), Fraction(3, 16), Fraction(5, 16)]
        likelihood = math.prod(q ** n for q, n in zip(probabilities, count)) ** 8
        direct = self.full.arithmetic.logarithm(numerator ** 8 / likelihood)
        actual = self.profile.at([Fraction(1, 2)] * 4)["interval"]
        self.assertLessEqual(direct.lower, actual.upper)
        self.assertLessEqual(actual.lower, direct.upper)

    def test_each_cap_increase_expands_joint_domain(self):
        original = self.profile.at([Fraction(1, 2)] * 4)
        for index in range(4):
            proposed = [Fraction(1, 2)] * 4
            proposed[index] = Fraction(3, 4)
            result = self.profile.at(proposed)
            self.assertGreater(original["interval"].lower, result["interval"].upper)
            for old, new in zip(original["contexts"], result["contexts"]):
                left, right = map(Fraction, old["allowed_even_probability"])
                lo, hi = map(Fraction, new["allowed_even_probability"])
                self.assertLessEqual(lo, left)
                self.assertLessEqual(right, hi)

    def test_three_rays_certify_full_orthant_and_bracket(self):
        for ray in producer.RAYS:
            entry = self.profile.bounds(ray)
            low, high = map(Fraction, entry["profile_threshold_bracket"])
            self.assertLessEqual(high - low, producer.BRACKET)
            self.assertGreaterEqual(self.profile.at(entry["lower_caps"])["interval"].lower, self.full.threshold.upper)
            self.assertLess(self.profile.at(entry["upper_caps"])["interval"].upper, self.full.threshold.lower)
            self.assertTrue(entry["entire_lower_orthant_excluded"])

    def test_pass_is_necessary_only_and_zero_is_excluded(self):
        self.assertEqual(self.profile.control("point", [1] * 4)["status"], "necessary_profile_not_excluded")
        self.assertEqual(self.profile.control("zero", [0] * 4)["status"], "entire_lower_orthant_excluded")

    def test_original_primitive_gain_rounded_outwards(self):
        effects = {side: [{"mu": "0", "u": "1/3", "z": "1/4"}] * 2 for side in ("alice", "bob")}
        for value in producer.witness_caps(effects):
            self.assertGreaterEqual(value * value, Fraction(25, 144))
            self.assertLess((value - Fraction(1, 1 << 48)) ** 2, Fraction(25, 144))

    def test_missing_caps_bool_and_duplicate_bias_rejected(self):
        for invalid in ([1, 1, 1], [True, 1, 1, 1], [-1, 1, 1, 1], [2, 1, 1, 1]):
            with self.assertRaises(ValueError):
                self.profile.at(invalid)
        invalid = biases()
        invalid[-1] = invalid[0]
        with self.assertRaises(ValueError):
            producer.JointProfile(self.full, invalid)


if __name__ == "__main__":
    unittest.main()
