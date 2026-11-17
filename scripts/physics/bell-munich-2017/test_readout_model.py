"""Unit tests for the Munich 2017 symmetric vs. asymmetric readout audit."""
from __future__ import annotations

from fractions import Fraction
import itertools
import math
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import readout_model as m  # noqa: E402


class MunichReadoutModelTests(unittest.TestCase):
    def test_ideal_symmetric_balanced_complement_for_all_angles_and_visibility(self) -> None:
        """Any Psi+/- state with depolarizing noise and symmetric readout satisfies P00=P11, P01=P10."""
        for h_plus in (False, True):
            for ga in (-2.4, -0.7, 0.0, math.pi / 4, 1.9):
                for gb in (-1.8, -math.pi / 8, math.pi / 8, 2.7):
                    for vis in (0.0, 0.65, 0.92, 1.0):
                        p00, p01, p10, p11 = m.ideal_symmetric_joint(h_plus, ga, gb, vis, 0.96, 0.91)
                        self.assertAlmostEqual(p00, p11, places=14)
                        self.assertAlmostEqual(p01, p10, places=14)
                        self.assertAlmostEqual(p00 + p01, 0.5, places=14)
                        self.assertAlmostEqual(p00 + p10, 0.5, places=14)
                        self.assertAlmostEqual(p00 + p01 + p10 + p11, 1.0, places=14)

    def test_exact_conditional_martingale_property(self) -> None:
        """Past-only Jeffreys factors have exact conditional expectation 1 under any balanced law."""
        proc = m.BalancedComplementProcess()
        sample_stream = [
            (0, 0, 1, 0, 1),
            (1, 1, 0, 1, 1),
            (0, 0, 1, 1, 0),
            (0, 0, 1, 0, 0),
            (1, 0, 0, 0, 1),
        ]
        for step_bits in sample_stream:
            proc.step(*step_bits)

        # Test arbitrary balanced conditional law: P(0,0)=P(1,1)=m0/2, P(0,1)=P(1,0)=m1/2
        for h, a, b in itertools.product((0, 1), repeat=3):
            for m0 in (Fraction(0), Fraction(1, 7), Fraction(3, 5), Fraction(1)):
                m1 = 1 - m0
                probs = {
                    (0, 0): m0 / 2,
                    (1, 1): m0 / 2,
                    (0, 1): m1 / 2,
                    (1, 0): m1 / 2,
                }
                exp_j = Fraction(0)
                exp_a = Fraction(0)
                exp_b = Fraction(0)
                exp_mix = Fraction(0)
                for (x, y), p_xy in probs.items():
                    fj, fa, fb = proc.step_factors(h, a, b, x, y)
                    exp_j += p_xy * fj
                    exp_a += p_xy * fa
                    exp_b += p_xy * fb
                    exp_mix += p_xy * (proc.joint_e * fj + proc.alice_e * fa + proc.bob_e * fb) / 3
                self.assertEqual(exp_j, Fraction(1))
                self.assertEqual(exp_a, Fraction(1))
                self.assertEqual(exp_b, Fraction(1))
                self.assertEqual(exp_mix, proc.evalue)

    def test_exact_32_binary_label_map_invariance(self) -> None:
        """All 2^5 = 32 global binary relabelings of (h, a, b, x, y) yield identical prefix E_t."""
        raw_seq = [
            (0, 0, 0, 0, 1),
            (1, 0, 1, 1, 1),
            (0, 1, 0, 0, 1),
            (0, 0, 0, 1, 0),
            (1, 1, 1, 0, 1),
            (1, 0, 1, 0, 0),
            (0, 1, 0, 0, 1),
            (1, 1, 0, 1, 1),
        ]

        def run_seq(seq: list[tuple[int, int, int, int, int]]) -> list[Fraction]:
            p = m.BalancedComplementProcess()
            return [p.step(*bits) for bits in seq]

        baseline = run_seq(raw_seq)
        for mask in itertools.product((0, 1), repeat=5):
            relabeled = [tuple(bit ^ mbit for bit, mbit in zip(row, mask)) for row in raw_seq]  # type: ignore[misc]
            self.assertEqual(run_seq(relabeled), baseline, f"Failed invariance for mask {mask}")

    def test_2d_inverse_scale_fiber_preserves_all_32_probabilities(self) -> None:
        """Rescaling (u_A, z_A) -> (s*u_A, t*z_A), (u_B, z_B) -> (u_B/s, z_B/t) keeps joint law identical."""
        for run_name, inst in m.WITNESS_INSTRUMENTS.items():
            base_table = m.full_joint_table(inst)
            for h, a, b in itertools.product((0, 1), repeat=3):
                row = base_table[(h, a, b)]
                self.assertEqual(sum(row), Fraction(1))
                self.assertTrue(all(q > 0 for q in row))

            # Every point in [0.95, 1.05]^2 (and sign-flipped branches) preserves all 32 cells identically
            for s in (Fraction(19, 20), Fraction(1), Fraction(21, 20), Fraction(-1)):
                for t in (Fraction(19, 20), Fraction(1), Fraction(21, 20), Fraction(-1)):
                    alt = m.scale_fiber(inst, s, t)
                    self.assertEqual(
                        m.full_joint_table(alt),
                        base_table,
                        f"Joint table changed on {run_name} for (s, t) = ({s}, {t})",
                    )

            # Verify that individual station canonical error rates genuinely shift along the fiber
            alt_hi = m.scale_fiber(inst, Fraction(21, 20), Fraction(21, 20))
            g_base, e0_base, _ = inst.bob[0].canonical_gain_and_errors()
            g_alt, e0_alt, _ = alt_hi.bob[0].canonical_gain_and_errors()
            self.assertNotAlmostEqual(g_base, g_alt, places=4)
            self.assertNotAlmostEqual(e0_base, e0_alt, places=4)

    def test_csv_schema_lab2_trailing_semicolon_and_zero_based_row_join(self) -> None:
        """Parser handles lab_2 7-header / 6-data column mismatch and 0-based pair row indices."""
        raw_l1 = (
            m.HEADERS["local1"]
            + b"1460729997751;0;0;877019185934879;Psi-;no; \n"
            + b"1460730010000;1;1;877019999999999;Psi+;yes;laser unlock\n"
            + b"1460730051637;1;1;877021880802081;Psi+;no; \n"
        )
        raw_l2 = (
            m.HEADERS["local2"]
            + b"1460729997750;0;1;682563060370852;no; \n"
            + b"1460730051638;1;0;682565755227956;no; \n"
        )
        # Note 0-based indices after header: pair 2 joins lab_1 index 2 (row 3) with lab_2 index 1 (row 2)
        raw_pairs = (
            m.HEADERS["pairs"]
            + b"1460729997751\tPsi-\t0\t0\t0\t1\t0\t0\n"
            + b"1460730051637\tPsi+\t1\t1\t1\t0\t2\t1\n"
        )
        admitted = m.admit_run_bytes("2016-04-15", raw_l1, raw_l2, raw_pairs)
        self.assertEqual(len(admitted.trials), 2)
        self.assertEqual(admitted.schema_audit["lab2_header_fields"], 7)
        self.assertEqual(admitted.schema_audit["lab2_six_field_data_rows"], 2)
        self.assertEqual(admitted.schema_audit["unpaired_local1"], 1)
        self.assertEqual(admitted.schema_audit["unpaired_local2"], 0)

    def test_empirical_chsh_and_biases_formula(self) -> None:
        """Verify event-ready CHSH combination and marginal bias accounting on a synthetic 4-context sample."""
        trials = (
            # (0,0) Psi-: different -> corr = -1 -> -E00 = +1
            m.Trial(1, Fraction(1), 1, 0, 0, 0, 1, 1, 1),
            # (0,1) Psi+: different -> corr = -1 -> -E01 = +1
            m.Trial(2, Fraction(2), 0, 0, 1, 1, 0, 2, 2),
            # (1,0) Psi+: different -> prod = -1, flipped for (h=0, a=1) -> +1 -> +E10 = +1
            m.Trial(3, Fraction(3), 0, 1, 0, 0, 1, 3, 3),
            # (1,1) Psi-: different -> corr = -1 -> -E11 = +1
            m.Trial(4, Fraction(4), 1, 1, 1, 1, 0, 4, 4),
        )
        emp = m.empirical_chsh_and_biases(trials)
        self.assertAlmostEqual(float(emp["chsh_s"]), 4.0, places=12)
        self.assertAlmostEqual(float(emp["biases"]["Alice 0"]["mu_hat"]), 0.0, places=12)
        self.assertAlmostEqual(float(emp["biases"]["Bob 0"]["mu_hat"]), -1.0, places=12)


if __name__ == "__main__":
    unittest.main()
