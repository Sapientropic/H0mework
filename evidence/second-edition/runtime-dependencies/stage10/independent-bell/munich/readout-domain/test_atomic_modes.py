"""Residual witnesses are checked against raw dynamics, not their requested answer."""
from dataclasses import replace
from fractions import Fraction as Q
import cmath
import unittest

import atomic_dipole as dipole
import atomic_full_forward as full
import atomic_modes as code
from test_atomic_full_forward import segment


class ModeControls(unittest.TestCase):
    def test_scalar_exponential_complex_phase_and_precision_override(self):
        for real, imag in ((-2, 3), (0, 12000), (Q(1, 4), -1000)):
            for bits in (96, 160):
                value, error = code.complex_exponential(real, imag, bits=bits)
                expected = cmath.exp(complex(float(real), float(imag)))
                self.assertLess(abs(complex(float(value[0]), float(value[1])) - expected), 1e-12)
                self.assertLess(error, Q(1, 10 ** 15))

    def test_adjoint_action_has_exact_hilbert_schmidt_duality(self):
        generator = full.Generator(segment(general=True), 128)
        x = {(i, j): ((7 * i + 3 * j) % 11 - 5, (2 * i + 5 * j) % 13 - 6)
             for i in range(full.DIMENSION) for j in range(full.DIMENSION)}
        y = {(i, j): ((5 * i + 2 * j) % 17 - 8, (3 * i + 7 * j) % 19 - 9)
             for i in range(full.DIMENSION) for j in range(full.DIMENSION)}
        def pairing(a, b):
            return (sum(ar * b.get(key, (0, 0))[0] + ai * b.get(key, (0, 0))[1] for key, (ar, ai) in a.items()),
                    sum(ar * b.get(key, (0, 0))[1] - ai * b.get(key, (0, 0))[0] for key, (ar, ai) in a.items()))
        self.assertEqual(pairing(x, generator.integer_action(y)), pairing(code.adjoint_integer_action(generator, x), y))

    def test_exact_absorbing_curve_generates_full_ground_effect(self):
        raw = segment(drive=False)
        excited = full.EXCITED[0]
        raw = replace(raw, gammas=dict.fromkeys(full.WIDTHS, 0), ion_rates={state: 3 if state == excited else 0 for state in full.EXCITED})
        q, e, ion = 1 << 60, dipole.INDEX[excited], dipole.ION
        modes = [{"lambda": [0, 0], "matrix": [[ion, ion, q, 0], [e, e, q, 0]]},
                 {"lambda": [-3 * q, 0], "matrix": [[e, e, -q, 0]]}]
        report = code.certify(raw, modes)
        self.assertEqual(Q(report["initial_operator_error"]), 0)
        self.assertEqual(Q(report["residual_operator_error"]), 0)
        self.assertLess(Q(report["operator_error_bound"]), Q(1, 10 ** 40))
        self.assertEqual(len(report["ground_F1_ion_effect"]), 3)
        wrong = [{"lambda": [0, 0], "matrix": [[ion, ion, q, 0]]}]
        self.assertGreater(Q(code.certify(raw, wrong)["residual_operator_error"]), 0)

    def test_target_and_same_shape_bad_modes_cannot_mint_a_small_error(self):
        raw, q, ion = segment(drive=False), 1 << 60, dipole.ION
        bad = [{"lambda": [0, 0], "matrix": [[0, 0, q, 0]]}]
        self.assertGreaterEqual(Q(code.certify(raw, bad)["operator_error_bound"]), 2)
        for modes in ([{"lambda": [0, 0], "matrix": [[ion, ion, q, 0]], "J": [1]}],
                      [{"lambda": [20 * q, 0], "matrix": [[ion, ion, q, 0]]}],
                      [{"lambda": [0, 0], "matrix": [[33, 33, q, 0]]}]):
            with self.assertRaises(ValueError):
                code.certify(raw, modes)


if __name__ == "__main__":
    unittest.main()
