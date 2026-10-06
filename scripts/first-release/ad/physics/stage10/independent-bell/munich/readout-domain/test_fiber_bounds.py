"""Synthetic continuous-fiber certificates and meaningful rejection controls."""
import copy
from fractions import Fraction
import unittest

import fiber_bounds as fiber


PRIMITIVE = {side: [{"mu": "0", "u": "3/10", "z": "2/5"},
                    {"mu": "0", "u": "2/5", "z": "3/10"}] for side in ("alice", "bob")}
MINIMUM = {"multipliers": {"upper": ["0", "0"], "reciprocal": ["1/16", "0"]},
           "sqrt_lower": ["9/400", "1/25"], "primal_squared_scales": ["1/4", "1/4"]}
MAXIMUM = {"multipliers": {"upper": ["1", "0"], "reciprocal": ["0", "0"]},
           "sqrt_lower": ["0", "0"], "primal_squared_scales": ["4", "4"]}


class FiberTests(unittest.TestCase):
    def test_exact_attaining_dual_covers_continuum(self):
        lo = fiber.check_endpoint(PRIMITIVE, "alice", 0, "minimum", MINIMUM)
        hi = fiber.check_endpoint(PRIMITIVE, "alice", 0, "maximum", MAXIMUM)
        self.assertEqual(Fraction(lo["gain_squared_bound"]), Fraction(1, 16))
        self.assertEqual(Fraction(hi["gain_squared_bound"]), 1)
        self.assertEqual(lo["optimality_gap"], "0")
        ranges = fiber.channel_ranges(PRIMITIVE, "alice", 0, lo, hi)
        self.assertEqual(ranges["canonical_gain"], ["1/4", "1"])
        self.assertEqual(ranges["canonical_e0"], ["0", "3/8"])
        self.assertFalse(ranges["whole_empirical_confidence_set_bounds"])

    def test_bob_reciprocal_coordinate_contract(self):
        lo = fiber.check_endpoint(PRIMITIVE, "bob", 0, "minimum", MINIMUM)
        hi = fiber.check_endpoint(PRIMITIVE, "bob", 0, "maximum", MAXIMUM)
        self.assertEqual(fiber.channel_ranges(PRIMITIVE, "bob", 0, lo, hi)["coordinates"],
                         "bob_reciprocal_squared_scales")

    def test_irrational_root_is_outward_exact(self):
        for value in (Fraction(2), Fraction(2, 3), Fraction(0), Fraction(1, 16)):
            lo, hi = fiber.sqrt_bracket(value)
            self.assertLessEqual(lo * lo, value)
            self.assertGreaterEqual(hi * hi, value)

    def test_oversized_root_rejected(self):
        forged = copy.deepcopy(MINIMUM)
        forged["sqrt_lower"][0] = "1/10"
        with self.assertRaises(ValueError):
            fiber.check_endpoint(PRIMITIVE, "alice", 0, "minimum", forged)

    def test_negative_weight_rejected(self):
        forged = copy.deepcopy(MINIMUM)
        forged["multipliers"]["upper"][0] = "-1"
        with self.assertRaises(ValueError):
            fiber.check_endpoint(PRIMITIVE, "alice", 0, "minimum", forged)

    def test_infeasible_attaining_point_rejected(self):
        forged = copy.deepcopy(MINIMUM)
        forged["primal_squared_scales"] = ["1/5", "1/5"]
        with self.assertRaises(ValueError):
            fiber.check_endpoint(PRIMITIVE, "alice", 0, "minimum", forged)

    def test_loose_valid_dual_is_not_accepted_as_sharp(self):
        forged = copy.deepcopy(MINIMUM)
        forged["sqrt_lower"] = ["0", "0"]
        with self.assertRaises(ValueError):
            fiber.check_endpoint(PRIMITIVE, "alice", 0, "minimum", forged)

    def test_target_table_cannot_replace_primitive(self):
        forged = copy.deepcopy(PRIMITIVE)
        forged["alice"][0]["probabilities"] = ["1/4"] * 4
        with self.assertRaises(ValueError):
            fiber.check_endpoint(forged, "alice", 0, "minimum", MINIMUM)

    def test_no_degenerate_coefficients_silently_accepted(self):
        forged = copy.deepcopy(PRIMITIVE)
        forged["alice"][0]["u"] = "0"
        with self.assertRaises(ValueError):
            fiber.check_endpoint(forged, "alice", 0, "minimum", MINIMUM)


if __name__ == "__main__":
    unittest.main()
