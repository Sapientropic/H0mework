"""Full matrix controls for the independent atomic forward enclosure."""
from fractions import Fraction
import inspect
import unittest

import atomic_forward_independent as check


class AtomicIndependentTests(unittest.TestCase):
    def pulse(self, **overrides):
        fields = dict(duration=Fraction(1, 100), omega_r=Fraction(2), omega_c=Fraction(3), ion_rate=Fraction(1, 2))
        fields.update(overrides)
        return check.Pulse(**fields)

    def test_raw_inputs_reject_target_efficiencies_and_floats(self):
        for record in ({"duration": "1", "omega_r": "2", "omega_c": "3", "ion_rate": "1", "f0": "1/2"},
                       {"duration": 0.1, "omega_r": "2", "omega_c": "3", "ion_rate": "1"}):
            with self.assertRaises(ValueError):
                check.Pulse.parse(record)

    def test_negative_raw_controls(self):
        for fields in ({"duration": Fraction(-1)}, {"ion_rate": Fraction(-1)},
                       {"omega_r": Fraction(-1)}, {"omega_c": Fraction(-1)}):
            with self.assertRaises(ValueError):
                self.pulse(**fields)

    def test_sqrt_integer_bounds(self):
        for root in (1, 3, 6):
            lo, hi = check.sqrt_enclosure(root)
            self.assertLessEqual(lo * lo, root)
            self.assertGreaterEqual(hi * hi, root)
            self.assertLessEqual(hi - lo, Fraction(1, 1 << check.BITS))

    def test_exact_source_jump_count_and_outgoing_rates(self):
        generator = check.Generator(self.pulse())
        self.assertEqual(len(check.NATURAL_JUMPS), 18)
        self.assertEqual(len(generator.jumps), 25)
        for label in (2, 7, 8, 9, 10, 12):
            self.assertEqual(generator.outgoing[label - 1], Fraction(3, 2))
        self.assertEqual(generator.outgoing[5], check.D2_RATE + Fraction(1, 2))
        self.assertEqual(generator.outgoing[check.ION], 0)

    def test_all_144_complex_matrix_units_preserve_trace(self):
        self.assertEqual(check.Generator(self.pulse()).check_all_matrix_units(), 288)

    def test_full_action_preserves_hermiticity(self):
        generator = check.Generator(self.pulse())
        for left in range(check.DIMENSION):
            for right in range(left, check.DIMENSION):
                for value in ((1, 0), (0, 1)):
                    if left == right and value[1]:
                        continue
                    matrix = {(left, right): value, (right, left): (value[0], -value[1])}
                    self.assertTrue(check._hermitian(generator.integer_action(matrix)))

    def test_ion_absorbing_and_offdiag_response_structurally_zero(self):
        generator = check.Generator(self.pulse())
        self.assertEqual(generator.action({(check.ION, check.ION): (1, 0)}), {})
        bright_block, dark_block = set((0, 1, 8)), set((3, 6, 11))
        matrix = {(check.BRIGHT, check.DARK): (1, 0)}
        for _ in range(7):
            matrix = generator.action(matrix)
            self.assertTrue(all(row in bright_block and column in dark_block for row, column in matrix))
            self.assertNotIn((check.ION, check.ION), matrix)

    def test_entry_norm_action_bound_full_basis(self):
        generator = check.Generator(self.pulse())
        for row in range(check.DIMENSION):
            for column in range(check.DIMENSION):
                for value in ((1, 0), (0, 1)):
                    output = generator.action({(row, column): value})
                    norm = sum(abs(real) + abs(imag) for real, imag in output.values())
                    self.assertLessEqual(norm, generator.norm_bound)

    def test_zero_time_exact_probability(self):
        output = check.propagate([self.pulse(duration=Fraction(0))])
        self.assertEqual(output["p_bright"], ["0", "0"])
        self.assertEqual(output["p_dark"], ["0", "0"])
        self.assertEqual(output["steps"], 0)

    def test_zero_ion_and_zero_readout_controls(self):
        for pulse in (self.pulse(ion_rate=Fraction(0)), self.pulse(omega_r=Fraction(0))):
            output = check.propagate([pulse])
            self.assertEqual(output["probability_centers"], ["0", "0"])
            self.assertTrue(all(Fraction(row[0]) <= 0 <= Fraction(row[1]) for row in (output["p_bright"], output["p_dark"])))

    def test_full_forward_nonzero_and_bounded(self):
        output = check.propagate([self.pulse()])
        for name in ("p_bright", "p_dark"):
            lo, hi = map(Fraction, output[name])
            self.assertTrue(0 < lo < hi < 1)
            self.assertLess(hi - lo, Fraction(1, 10 ** 60))
        self.assertTrue(output["full_144_complex_liouvillian"])

    def test_constant_generator_segment_composition(self):
        whole = check.propagate([self.pulse()])
        split = check.propagate([self.pulse(duration=Fraction(1, 200)), self.pulse(duration=Fraction(1, 200))])
        self.assertTrue(check.verify_intersection(whole, split))

    def test_rounding_antisymmetric_and_error(self):
        for denominator in range(1, 10):
            for numerator in range(-20, 21):
                value = check.round_nearest(numerator, denominator)
                self.assertEqual(value, -check.round_nearest(-numerator, denominator))
                self.assertLessEqual(abs(value - Fraction(numerator, denominator)), Fraction(1, 2))

    def test_tail_geometric_ratio_condition(self):
        with self.assertRaises(ValueError):
            check.propagate([self.pulse()], order=16, norm_cap=Fraction(18))

    def test_explicit_step_budget(self):
        with self.assertRaises(ValueError):
            check.propagate([self.pulse(duration=Fraction(1))], max_steps=1)

    def test_verifier_rejects_disjoint_enclosures(self):
        a = {name: ["0", "1/4"] for name in ("p_bright", "p_dark", "trace_j")}
        b = {name: ["1/2", "1"] for name in a}
        with self.assertRaises(ValueError):
            check.verify_intersection(a, b)

    def test_verifier_preserves_outward_zero_boundary_and_requires_physical_intersection(self):
        outward = {name: ["-1/1000", "1/1000"] for name in ("p_bright", "p_dark", "trace_j")}
        physical = {name: ["0", "1/1000"] for name in outward}
        self.assertTrue(check.verify_intersection(outward, physical))
        for interval in (["-2", "-1"], ["3", "4"]):
            outside = {name: interval for name in outward}
            with self.assertRaises(ValueError):
                check.verify_intersection(outside, outside)

    def test_primary_producer_not_imported(self):
        source = inspect.getsource(check)
        self.assertNotIn("import atomic_forward\n", source)
        self.assertNotIn("from atomic_forward import", source)


if __name__ == "__main__":
    unittest.main()
