import unittest
from fractions import Fraction

import independent_born as born


class IndependentBornControls(unittest.TestCase):
    def test_exact_field_order_and_inverse(self):
        sqrt = born.SQRT2
        self.assertEqual(sqrt * sqrt, born.Q2(2))
        self.assertEqual((3 + 2 * sqrt) * (3 - 2 * sqrt), born.ONE)
        self.assertEqual((3 - 2 * sqrt).sign(), 1)
        self.assertEqual((1 - sqrt).sign(), -1)
        self.assertEqual((-1 + sqrt).sign(), 1)
        self.assertEqual((-3 + 2 * sqrt).sign(), -1)
        with self.assertRaises(TypeError):
            born.Q2(0.5)
        with self.assertRaises(ZeroDivisionError):
            born.ZERO.inverse()

    def test_original_eight_dimensional_coefficients(self):
        expected = (0, 1, -1, 0, 0, 1, -1, 0)
        vector = born.source_vector()
        self.assertEqual(vector, tuple(born.C2(born.Q2(Fraction(x, 2))) for x in expected))
        self.assertEqual(born.inner(vector, vector), born.C2(born.ONE))
        truncated = tuple(value if index < 4 else born.C2() for index, value in enumerate(vector))
        self.assertEqual(born.inner(truncated, truncated), born.C2(born.ONE / 2))
        with self.assertRaises(ValueError):
            born.source_vector(born.C2(born.Q2(2)), born.C2(born.ONE))

    def test_color_z_only_changes_color_one(self):
        original = born.prepared_vector(False)
        prepared = born.prepared_vector(True)
        self.assertEqual(prepared, tuple((-value if index % 2 else value)
                                        for index, value in enumerate(original)))
        alice, bob = born.fixed_axes()
        left = born.tensor(born.spin_axis(*alice[1]), born.identity(2))
        right = born.tensor(born.identity(4), born.axis(*bob[0]))
        self.assertEqual(born.matmul(left, right), born.matmul(right, left))

    def test_malformed_spectral_and_source_inputs_rejected(self):
        alice, bob = born.fixed_axes()
        projection = born.joint_projection(alice[0], bob[0], False, False)
        with self.assertRaises(ValueError):
            born.certify_projection(born.scale(2, projection))
        with self.assertRaises(ValueError):
            born.axis(1, 1)
        with self.assertRaises(TypeError):
            born.outcome_sign(1)
        vector = tuple(value / 2 for value in born.source_vector())
        with self.assertRaises(ValueError):
            born.born(vector, projection)

    def test_full_distribution_and_marginals(self):
        raw = born.table()
        born.check_distribution(raw)
        self.assertEqual(len(raw), 32)
        self.assertTrue(all(value.sign() >= 0 and (born.ONE - value).sign() >= 0
                            for value in raw.values()))
        incomplete = dict(raw)
        incomplete.pop((True, 1, 1, True, True))
        with self.assertRaises(ValueError):
            born.check_distribution(incomplete)
        modified = dict(raw)
        modified[(True, 1, 1, True, True)] += born.ONE / 100
        with self.assertRaises(ValueError):
            born.check_distribution(modified)

    def test_herald_frame_is_corrected_by_the_declared_operation(self):
        raw = born.table()
        first = born.correlations(raw, False)
        second = born.correlations(raw, True)
        self.assertEqual(first[(0, 0)], second[(0, 0)])
        self.assertEqual(first[(1, 0)], -second[(1, 0)])
        self.assertEqual(born.corrected_chsh(second, False), born.ZERO)
        score = born.corrected_chsh(second, True)
        self.assertEqual(score * score, born.Q2(8))
        self.assertEqual((score - 2).sign(), 1)
        self.assertEqual(score, born.corrected_chsh(first, False))
        aligned = born.aligned_table(raw)
        born.check_distribution(aligned)
        for a in (0, 1):
            for b in (0, 1):
                for x in (False, True):
                    for y in (False, True):
                        self.assertEqual(aligned[(False, a, b, x, y)], aligned[(True, a, b, x, y)])

    def test_nontrivial_unit_phases_cancel_in_the_complete_carrier(self):
        controls = born.phase_controls()
        self.assertEqual(len(controls), 4)
        self.assertTrue(all(row["full_32_probabilities_equal_point_zero"] for row in controls))
        upper = born.C2(born.ZERO, born.ONE)
        lower = born.C2(born.Q2(Fraction(3, 5)), born.Q2(Fraction(4, 5)))
        self.assertEqual(born.table(upper, lower), born.table())

    def test_receipt_preserves_raw_and_aligned_identities(self):
        receipt = born.generate()
        self.assertEqual(receipt["dimension"], 8)
        self.assertEqual(len(receipt["raw_records"]), 32)
        self.assertEqual(len(receipt["aligned_records"]), 32)
        keys = {(row["herald"], row["setting_a"], row["setting_b"],
                 row["outcome_a"], row["outcome_b"]) for row in receipt["raw_records"]}
        self.assertEqual(len(keys), 32)
        for row in receipt["raw_records"]:
            self.assertEqual(row["aligned_outcome_a"], row["outcome_a"] ^ (
                row["herald"] and row["setting_a"] == 1))
            self.assertEqual(set(row["probability"]), {"r", "s"})
        self.assertFalse(receipt["scope"]["source_phase_uniform_proof_supplied_by_finite_controls"])
        self.assertFalse(receipt["scope"]["real_instrument_empirical_verdict_executed"])
        self.assertEqual(receipt["scope"]["trial_event_files_read"], 0)


if __name__ == "__main__":
    unittest.main()
