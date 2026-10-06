"""Inherited component likelihood and whole-CS response projections on synthetic counts."""
from fractions import Fraction
import itertools
import math
import unittest

from likelihood import Directed
import response_projection as producer


def rows(counts=(7, 1, 2, 6)):
    return [{"h": h, "a": a, "b": b, "counts": list(counts)}
            for h, a, b in itertools.product((0, 1), repeat=3)]


class CorrelationProjectionTests(unittest.TestCase):
    def test_profile_is_lower_than_actual_full_component(self):
        counts = (7, 1, 2, 6)
        q = tuple(map(Fraction, ("2/5", "1/10", "1/10", "2/5")))
        numerator = Fraction(1, math.factorial(sum(counts) + 1))
        for n in counts:
            numerator *= Fraction(math.factorial(2 * n), (4 ** n) * math.factorial(n))
        e_full = (numerator / math.prod(p ** n for p, n in zip(q, counts))) ** 8
        full = producer.FullProfile(rows())
        profile = full.correlation((0, 0, 0)).at(q[0] + q[3])
        direct = Directed(80).logarithm(e_full)
        self.assertLess(profile.upper, direct.lower)

    def test_within_parity_and_other_context_mle_attains_profile(self):
        counts = (7, 1, 2, 6)
        n = sum(counts)
        p = Fraction(3, 4)
        full = producer.FullProfile(rows())
        q = (p * Fraction(7, 13), (1 - p) * Fraction(1, 3),
             (1 - p) * Fraction(2, 3), p * Fraction(6, 13))
        numerator = Fraction(1, math.factorial(n + 1))
        for k in counts:
            numerator *= Fraction(math.factorial(2 * k), (4 ** k) * math.factorial(k))
        numerator **= 8
        mle = tuple(Fraction(k, n) for k in counts)
        denominator = math.prod(v ** k for v, k in zip(q, counts)) * math.prod(v ** k for v, k in zip(mle, counts)) ** 7
        value = Directed(80).logarithm(numerator / denominator)
        projected = full.correlation((0, 0, 0)).at(p)
        self.assertLessEqual(value.lower, projected.upper)
        self.assertLessEqual(projected.lower, value.upper)

    def test_outer_endpoints_and_monotone_exclusion(self):
        full = producer.FullProfile(rows())
        profile = full.correlation((0, 0, 0))
        saved = profile.bounds()
        lo, hi = map(Fraction, saved["p_outer_interval"])
        self.assertLess(lo, profile.mle)
        self.assertLess(profile.mle, hi)
        self.assertGreaterEqual(profile.at(lo / 2).lower, full.threshold.upper)
        self.assertGreaterEqual(profile.at((hi + 1) / 2).lower, full.threshold.upper)
        self.assertEqual(saved["component_threshold"], "80")

    def test_empty_or_duplicate_source_contexts_rejected(self):
        for invalid in (rows()[:-1], rows()[:-1] + [rows()[0]]):
            with self.assertRaises(ValueError):
                producer.FullProfile(invalid)
        with self.assertRaises(ValueError):
            producer.FullProfile(rows((1, 0, 0, 1))).correlation((0, 0, 0))

    def test_zero_cells_are_valid_when_both_parities_present(self):
        self.assertEqual(producer.FullProfile(rows((1, 0, 1, 0))).correlation((0, 0, 0)).mle, Fraction(1, 2))

    def test_response_bound_uses_all_contexts_and_both_biases(self):
        correlations = [{"h": h, "a": a, "b": b, "correlation_outer_interval": ["1/2", "3/5"]}
                        for h, a, b in producer.CONTEXTS]
        biases = [{"side": side, "setting": setting, "mu_outer_interval": ["-1/10", "1/5"]}
                  for side, setting in itertools.product(("alice", "bob"), (0, 1))]
        envelopes = producer.response_envelopes(correlations, biases)
        self.assertEqual(len(envelopes), 4)
        for row in envelopes:
            self.assertEqual(row["canonical_gain"], ["23/50", "1"])
            self.assertEqual(row["canonical_e0"], ["0", "8/25"])
            self.assertEqual(row["canonical_e1"], ["0", "37/100"])
            self.assertFalse(row["fixed_law_point_used_as_confidence_bound"])

    def test_negative_correlation_and_zero_crossing(self):
        biases = [{"side": side, "setting": setting, "mu_outer_interval": ["0", "0"]}
                  for side, setting in itertools.product(("alice", "bob"), (0, 1))]
        for interval, expected in ((["-3/5", "-1/2"], "1/2"), (["-1/2", "1/2"], "0")):
            correlations = [{"h": h, "a": a, "b": b, "correlation_outer_interval": interval}
                            for h, a, b in producer.CONTEXTS]
            self.assertEqual(producer.response_envelopes(correlations, biases)[0]["canonical_gain"][0], expected)


if __name__ == "__main__":
    unittest.main()
