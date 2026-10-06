"""Independent source-effect realizer controls with synthetic response boxes."""
from fractions import Fraction as Q
from itertools import product
import inspect
import unittest

import pulse_realization_independent as check
from detector_fiber_independent import Effect


class PulseRealizationIndependentTests(unittest.TestCase):
    def test_distinct_responses_restore_same_effect(self):
        point = Effect(Q(1, 10), Q(3, 10), Q(2, 5))
        for b, r in ((Q(9, 10), Q(1, 10)), (Q(4, 5), Q(1, 5))):
            result = check.realize_box(point, (b, b), (r, r))
            self.assertTrue(result["whole_response_box_realizes_source_effect"])
            k = Q(1, 2) / (b - r)
            d = (1 - point.mu - k * (b + r)) / 2
            eta = k / (1 - d)
            self.assertEqual(result["detection_interval"], [str(k)] * 2)
            self.assertEqual(result["background_interval"], [str(d)] * 2)
            self.assertEqual(result["fragment_efficiency_interval"], [str(eta)] * 2)
            self.assertEqual(1 - 2 * d - k * (b + r), point.mu)
            self.assertEqual(-k * (b - r) * (-point.u / Q(1, 2)), point.u)
            self.assertEqual(-k * (b - r) * (-point.z / Q(1, 2)), point.z)

    def test_midpoint_does_not_pay_whole_box(self):
        point = Effect(Q(0), Q(4, 5), Q(0))
        self.assertTrue(check.feasible(point, Q(9, 10), Q(1, 10))[0])
        result = check.realize_box(point, (Q(3, 4), Q(1)), (Q(0), Q(1, 4)))
        self.assertEqual(result["status"], "undetermined_response_box")
        self.assertFalse(result["whole_response_box_realizes_source_effect"])

    def test_entire_infeasible_response_box(self):
        result = check.realize_box(Effect(0, Q(4, 5), 0), (Q(1, 2), Q(3, 5)), (Q(1, 5), Q(1, 4)))
        self.assertEqual(result["status"], "whole_response_box_excluded_for_source_effect")

    def test_all_box_points_and_detector_coordinates_enclosed(self):
        accepted = 0
        for gain, mu, bright, dark in product((Q(1, 4), Q(1, 2), Q(3, 4)), (Q(-1, 5), Q(0), Q(1, 10)),
                                             ((Q(3, 5), Q(9, 10)), (Q(4, 5), Q(1))),
                                             ((Q(0), Q(1, 10)), (Q(1, 10), Q(1, 5)))):
            point = Effect(mu, gain * Q(3, 5), gain * Q(4, 5))
            report = check.realize_box(point, bright, dark)
            b_values = (bright[0], sum(bright) / 2, bright[1])
            r_values = (dark[0], sum(dark) / 2, dark[1])
            if report["whole_response_box_realizes_source_effect"]:
                accepted += 1
                for b, r in product(b_values, r_values):
                    self.assertTrue(check.feasible(point, b, r)[0])
                    k = gain / (b - r)
                    d = (1 - mu - k * (b + r)) / 2
                    eta = k / (1 - d)
                    self.assertTrue(0 <= d < 1 and 0 < eta <= 1)
                    for name, value in (("detection_interval", k), ("background_interval", d),
                                        ("fragment_efficiency_interval", eta)):
                        lo, hi = map(Q, report[name])
                        self.assertLessEqual(lo, value)
                        self.assertLessEqual(value, hi)
            elif report["status"] == "whole_response_box_excluded_for_source_effect":
                self.assertTrue(all(not check.feasible(point, b, r)[0] for b, r in product(b_values, r_values)))
            else:
                self.assertFalse(check.feasible(point, bright[0], dark[1])[0])
                self.assertTrue(check.feasible(point, bright[1], dark[0])[0])
        self.assertGreater(accepted, 0)

    def test_feasible_boundary_exact_zero_background_eta_one(self):
        result = check.realize_box(Effect(0, Q(4, 5), 0), (Q(9, 10), Q(9, 10)), (Q(1, 10), Q(1, 10)))
        self.assertEqual(result["background_interval"], ["0", "0"])
        self.assertEqual(result["fragment_efficiency_interval"], ["1", "1"])

    def test_irrational_gain_symbolic_axis_and_outward_interval(self):
        point = Effect(0, Q(1, 10), Q(1, 5))
        result = check.realize_box(point, (Q(4, 5), Q(9, 10)), (Q(1, 10), Q(1, 5)))
        self.assertTrue(result["whole_response_box_realizes_source_effect"])
        self.assertTrue(result["normalized_axis_is_symbolic"])
        self.assertEqual(result["generator_definition"]["gain_squared"], "1/20")
        lower, upper = check.square_root_interval(Q(1, 20))
        self.assertLessEqual(lower ** 2, Q(1, 20))
        self.assertGreaterEqual(upper ** 2, Q(1, 20))

    def test_perfect_square_root_and_tiny_nonzero_gain(self):
        for value in (Q(0), Q(9, 25), Q(1, 1 << 600)):
            lo, hi = check.square_root_interval(value)
            self.assertEqual(lo, hi)
            self.assertEqual(lo * lo, value)
        point = Effect(0, Q(1, 1 << 300), 0)
        self.assertTrue(check.realize_box(point, (Q(1), Q(1)), (Q(0), Q(0)))["whole_response_box_realizes_source_effect"])

    def test_zero_gain_and_equal_spectrum_rejected(self):
        with self.assertRaises(ValueError):
            check.feasible(Effect(0, 0, 0), 1, 0)
        for b, r in ((0, 0), (Q(1, 2), Q(1, 2)), (Q(1, 2), Q(3, 4)), (2, 0)):
            with self.assertRaises(ValueError):
                check.feasible(Effect(0, Q(1, 2), 0), b, r)

    def test_no_uniform_gap_is_not_promoted(self):
        result = check.realize_box(Effect(0, Q(1, 2), 0), (Q(1, 4), Q(3, 4)), (Q(1, 4), Q(1, 2)))
        self.assertEqual(result["status"], "response_gap_not_uniformly_positive")
        self.assertFalse(result["whole_response_box_realizes_source_effect"])

    def test_response_separation_requires_disjoint_interval(self):
        first = {"p_bright": ["4/5", "9/10"], "p_dark": ["1/10", "1/5"]}
        self.assertFalse(check.responses_separated(first, first))
        overlap = {"p_bright": ["17/20", "1"], "p_dark": ["1/10", "1/5"]}
        self.assertFalse(check.responses_separated(first, overlap))
        separated = {"p_bright": ["19/20", "1"], "p_dark": ["1/10", "1/5"]}
        self.assertTrue(check.responses_separated(first, separated))

    def test_primary_and_forward_producers_not_imported(self):
        source = inspect.getsource(check)
        self.assertNotIn("import pulse_realization\n", source)
        self.assertNotIn("from pulse_realization import", source)
        self.assertNotIn("import atomic_forward", source)


if __name__ == "__main__":
    unittest.main()
