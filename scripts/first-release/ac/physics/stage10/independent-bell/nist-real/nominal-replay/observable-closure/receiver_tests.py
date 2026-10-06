"""Independent exact polynomial controls for angular second jets and fixed-source updates."""
from fractions import Fraction as F
import unittest

import primary
import receiver
import angular_jet


class ReceiverTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        primary.frozen(__file__)
        cls.config, _, cls.g, _, _, _ = receiver.load()

    def test_polynomial_cross_hessian(self):
        J, I = angular_jet.Jet, self.g.I
        x, y = J.variable(0, I.point(2)), J.variable(1, I.point(3))
        f = x*x*y+3*x*y*y
        self.assertTrue(f.value.contains(66))
        self.assertTrue(f.gradient[0].contains(39))
        self.assertTrue(f.gradient[1].contains(40))
        self.assertTrue(f.hessian[0][0].contains(6))
        self.assertTrue(f.hessian[1][1].contains(12))
        self.assertTrue(f.hessian[0][1].contains(22))
        self.assertTrue(f.hessian[1][0].contains(22))

    def test_reciprocal_hessian(self):
        x = angular_jet.Jet.variable(0, self.g.I.point(2))
        f = 1/x
        self.assertTrue(f.value.contains(F(1, 2)))
        self.assertTrue(f.gradient[0].contains(-F(1, 4)))
        self.assertTrue(f.hessian[0][0].contains(F(1, 4)))

    def test_sine_cosine_degree_identity_at_zero(self):
        angle = angular_jet.Jet.variable(0, self.g.I.point(0))
        s, c = receiver.sine_cosine(angle, self.config, self.g)
        pi = self.g.I(*map(F, self.config["pi"]))
        self.assertTrue(s.value.contains(0) and c.value.contains(1))
        self.assertTrue(s.gradient[0].lo <= (pi/180).lo <= s.gradient[0].hi)
        self.assertTrue(c.gradient[0].contains(0))
        expected = -(pi/180).square()
        self.assertLessEqual(c.hessian[0][0].lo, expected.lo)
        self.assertGreaterEqual(c.hessian[0][0].hi, expected.hi)

    def test_original_mirror_coordinates_remain_available(self):
        self.assertEqual(self.config["directions"]["mirror0"], [1, 0, -1, 0])
        self.assertEqual(self.config["directions"]["mirror1"], [0, 1, 0, -1])
        self.assertEqual(self.config["receiver_rounding_half_width_degree"], "1/20")
        self.assertEqual(self.config["strict_improvement_lower_bound"], "1/10000000000")
        self.assertTrue(self.config["training_phase_held_fixed_under_receiver_update"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
