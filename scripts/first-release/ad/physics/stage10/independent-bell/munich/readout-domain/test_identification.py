"""Quotient/fiber and confidence-projection controls without empirical records."""
from fractions import Fraction
import itertools
import unittest

from identification import (Profile, fixed_law_fiber, own_counts, positive_rectangle,
                            quotient, recover_quotient, recover_scales, scale)
from model import Effect, Instrument, source_joint


def point():
    return Instrument((Effect("1/50", "1/8", "3/4"), Effect("-1/40", "3/4", "1/8")),
                      (Effect("-1/30", "1/2", "1/2"), Effect("1/35", "-1/2", "1/2")))


def table(instrument):
    return {key: source_joint(instrument, *key) for key in itertools.product((0, 1), repeat=5)}


class IdentificationControls(unittest.TestCase):
    def test_all_q_recover_exact_observable_quotient(self):
        self.assertEqual(recover_quotient(table(point())), quotient(point()))

    def test_two_nonzero_signed_scales_preserve_complete_joint(self):
        for s, t in itertools.product((Fraction(-21, 20), Fraction(19, 20)), repeat=2):
            transformed = scale(point(), s, t)
            self.assertEqual(table(transformed), table(point()))
            self.assertEqual(recover_scales(point(), transformed), (s, t))

    def test_isotropic_family_preserves_axes_and_changes_channel_gain(self):
        transformed = scale(point(), Fraction(21, 20), Fraction(21, 20))
        for side in ("alice", "bob"):
            for original, other in zip(getattr(point(), side), getattr(transformed, side)):
                self.assertEqual(original.u * other.z, original.z * other.u)
                self.assertNotEqual(original.u ** 2 + original.z ** 2, other.u ** 2 + other.z ** 2)

    def test_continuous_rectangle_uses_all_four_worst_case_cones(self):
        result = positive_rectangle(point())
        self.assertEqual(len(result["constraints"]), 4)
        self.assertTrue(result["entire_continuous_rectangle_legal"])
        self.assertFalse(result["finite_samples_used_as_coverage"])
        with self.assertRaises(ValueError):
            positive_rectangle(point(), Fraction(1, 2), Fraction(2))

    def test_regular_complete_fiber_and_shape_failures(self):
        self.assertEqual(len(fixed_law_fiber(point())["constraints"]), 4)
        zero = Instrument((Effect(0, 0, 0),) * 2, (Effect(0, 0, 0),) * 2)
        with self.assertRaises(ValueError):
            fixed_law_fiber(zero)
        with self.assertRaises(ValueError):
            scale(point(), 0, 1)
        with self.assertRaises(ValueError):
            recover_scales(point(), zero)
        with self.assertRaises(ValueError):
            recover_quotient({})

    def test_own_setting_counts_use_all_contexts(self):
        rows = [{"h": h, "a": a, "b": b, "counts": [1, 2, 3, 4]}
                for h, a, b in itertools.product((0, 1), repeat=3)]
        self.assertEqual(own_counts(rows), {"alice": [[12, 28], [12, 28]], "bob": [[16, 24], [16, 24]]})
        rows[1]["h"], rows[1]["a"], rows[1]["b"] = 0, 0, 0
        with self.assertRaises(ValueError):
            own_counts(rows)

    def test_profile_encloses_mle_and_certifies_both_excluded_sides(self):
        profile = Profile([[70, 30], [35, 65]], 0)
        result = profile.bounds()
        lo, hi = map(Fraction, result["p_outer_interval"])
        self.assertLess(lo, Fraction(7, 10))
        self.assertGreater(hi, Fraction(7, 10))
        for p in (lo / 2, lo, hi, (1 + hi) / 2):
            self.assertGreaterEqual(profile.at(p).lower, profile.threshold.upper)
        self.assertFalse(result["new_confidence_budget_spent"])
        self.assertFalse(result["point_witness_used_as_confidence_bound"])

    def test_profile_closed_form_is_the_existing_pooled_numerator(self):
        profile = Profile([[3, 2], [1, 4]], 0)
        n0, n1 = 4, 6
        beta = Fraction(__import__('math').factorial(2 * n0) * __import__('math').factorial(2 * n1),
                        (1 << (2 * (n0 + n1))) * __import__('math').factorial(n0) *
                        __import__('math').factorial(n1) * __import__('math').factorial(n0 + n1))
        p = Fraction(2, 3)
        other_mle = Fraction(1, 5) * Fraction(4, 5) ** 4
        exact = beta / (p ** 3 * (1 - p) ** 2 * other_mle)
        expected = profile.arithmetic.logarithm(exact)
        actual = profile.at(p)
        self.assertLessEqual(actual.lower, expected.upper)
        self.assertGreaterEqual(actual.upper, expected.lower)

    def test_source_boundary_is_not_epsilon_smoothed(self):
        with self.assertRaises(ValueError):
            Profile([[0, 5], [1, 2]], 0)
        with self.assertRaises(ValueError):
            Profile([[3, 2], [1, 4]], 0).at(0)


if __name__ == "__main__":
    unittest.main()
