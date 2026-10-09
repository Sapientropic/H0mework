"""Exact controls for angular emission, physical optics and BSM contraction."""
from fractions import Fraction as Q
import unittest

import atomic_dipole as angular
import atom_photon_source as code


def scale_matrix(matrix, factor):
    return tuple(tuple(angular.complex_exact(value) * factor for value in row) for row in matrix)


def outer(vector):
    return {(i, j): a * b.conjugate() for i, a in vector.items() for j, b in vector.items() if a and b}


def source_bell_density(sign):
    basis = angular.source_qubit_bridge()
    ux, dx = basis["u_x"], basis["d_x"]
    vector = {}
    half = angular.sqrt_rational(Q(1, 2))
    for a in code.ATOM_BASIS:
        for b in code.ATOM_BASIS:
            value = (ux.get(a, angular.ComplexRadical()) * dx.get(b, angular.ComplexRadical()) +
                     sign * dx.get(a, angular.ComplexRadical()) * ux.get(b, angular.ComplexRadical())) * half
            if value:
                vector[code.PAIR_INDEX[a, b]] = value
    return outer(vector)


def purity(density):
    return code.density_trace(angular.matrix_product(density, density))


class AtomPhotonSourceTests(unittest.TestCase):
    def assert_density(self, density):
        self.assertEqual(density, angular.matrix_adjoint(density))
        self.assertEqual(code.density_trace(density), angular.Radical(1))
        self.assertGreaterEqual(code.radical_sign(1 - purity(density)), 0)

    def test_full_emission_retains_photon_and_exact_selection_rules(self):
        emission = code.emission_amplitudes()
        self.assertEqual(len(emission), 3)
        self.assertEqual({q for _, q in emission}, {-1, 0, 1})
        self.assertEqual({index for index, _ in emission}, set(code.ATOM_BASIS))
        for (index, q), amplitude in emission.items():
            state = angular.STATES[index]
            self.assertEqual(state.m + q, 0)
            self.assertEqual(amplitude, angular.ComplexRadical(
                angular.clebsch_gordan(1, state.m, 1, q, 0, 0)))
        norm = sum((a * a.conjugate() for a in emission.values()), angular.ComplexRadical())
        self.assertEqual(norm, angular.ComplexRadical(1))
        for m in range(-2, 3):
            for q in code.Q_COMPONENTS:
                self.assertFalse(angular.dipole_coefficient("D2", 2, m, 0, 0, q))

    def test_literal_public_detector_patterns_and_balanced_amplitudes(self):
        bras = code.bsm_bras()
        self.assertEqual(tuple((bra.herald, bra.detectors) for bra in bras), code.HERALD_PATTERNS)
        hp, ph = ("perp", "parallel"), ("parallel", "perp")
        half = angular.ComplexRadical(Q(1, 2))
        imaginary = angular.ComplexRadical(0, Q(1, 2))
        self.assertEqual(bras[0].coefficients, {hp: half, ph: -half})
        self.assertEqual(bras[1].coefficients, {ph: half, hp: -half})
        self.assertEqual(bras[2].coefficients, {hp: imaginary, ph: imaginary})
        self.assertEqual(bras[3].coefficients, {hp: imaginary, ph: imaginary})

    def test_ideal_collection_generates_source_bell_states_and_absolute_rates(self):
        optical = code.ideal_collection()
        collected = code.collected_amplitudes(optical)
        norm = sum((a * a.conjugate() for a in collected.values()), angular.ComplexRadical())
        self.assertEqual(norm, angular.ComplexRadical(Q(2, 3)))
        heralds = code.prepare_heralds(optical, optical)
        for herald, sign in (("Psi-", -1), ("Psi+", 1)):
            state = heralds[herald]
            self.assertEqual(state.conditional, source_bell_density(sign))
            self.assertEqual(state.probability, angular.Radical(Q(1, 9)))
            self.assertEqual([branch.probability for branch in state.branches],
                             [angular.Radical(Q(1, 18))] * 2)
            self.assertEqual(purity(state.conditional), angular.Radical(1))
            self.assert_density(state.conditional)
        self.assertEqual(sum((state.probability for state in heralds.values()), angular.Radical()),
                         angular.Radical(Q(2, 9)))

    def test_explicit_collection_override_changes_rate_without_target_rho_input(self):
        first = scale_matrix(code.ideal_collection(), Q(1, 2))
        heralds = code.prepare_heralds(first, code.ideal_collection())
        for herald, sign in (("Psi-", -1), ("Psi+", 1)):
            self.assertEqual(heralds[herald].probability, angular.Radical(Q(1, 36)))
            self.assertEqual(heralds[herald].conditional, source_bell_density(sign))

    def test_exact_irrational_herald_normalization(self):
        factor = (angular.Radical(1) + angular.sqrt_rational(2)) / 4
        first = scale_matrix(code.ideal_collection(), factor)
        heralds = code.prepare_heralds(first, code.ideal_collection())
        expected = (angular.Radical(3) + 2 * angular.sqrt_rational(2)) / 144
        for herald, sign in (("Psi-", -1), ("Psi+", 1)):
            self.assertEqual(heralds[herald].probability, expected)
            self.assertEqual(heralds[herald].conditional, source_bell_density(sign))
            self.assert_density(heralds[herald].conditional)

    def test_pi_leakage_retains_m0_in_generated_density(self):
        collection = ((Q(1, 2), Q(1, 2), 0), (0, 0, Q(1, 2)))
        heralds = code.prepare_heralds(collection, collection)
        zero = angular.INDEX[angular.State("ground", 1, 0)]
        for state in heralds.values():
            self.assert_density(state.conditional)
            leaked = sum((value.real for (i, j), value in state.conditional.items()
                          if i == j and zero in code.PAIR_BASIS[i]), angular.Radical())
            self.assertGreater(code.radical_sign(leaked), 0)
            self.assertNotEqual(state.conditional, source_bell_density(1))
            self.assertNotEqual(state.conditional, source_bell_density(-1))

    def test_raw_complex_collection_phase_changes_conditional_state(self):
        imaginary = angular.ComplexRadical(0, 1)
        first = tuple(tuple(value * (imaginary if column == 0 else 1)
                            for column, value in enumerate(row)) for row in code.ideal_collection())
        heralds = code.prepare_heralds(first, code.ideal_collection())
        for herald, sign in (("Psi-", -1), ("Psi+", 1)):
            self.assert_density(heralds[herald].conditional)
            self.assertNotEqual(heralds[herald].conditional, source_bell_density(sign))
            self.assertTrue(any(value.imag for value in heralds[herald].conditional.values()))

    def test_unbalanced_raw_splitter_generates_mixed_coarse_herald(self):
        splitter = ((Q(3, 5), (0, Q(4, 5))), ((0, Q(4, 5)), Q(3, 5)))
        heralds = code.prepare_heralds(code.ideal_collection(), code.ideal_collection(),
                                     beam_splitter=splitter)
        for state in heralds.values():
            self.assert_density(state.conditional)
        self.assertLess(code.radical_sign(purity(heralds["Psi-"].conditional) - 1), 0)
        self.assertEqual(purity(heralds["Psi+"].conditional), angular.Radical(1))
        self.assertNotEqual(heralds["Psi-"].conditional, source_bell_density(-1))

    def test_zero_herald_is_undefined_and_keeps_pattern_records(self):
        zero = ((0, 0, 0), (0, 0, 0))
        for state in code.prepare_heralds(zero, code.ideal_collection()).values():
            self.assertFalse(state.probability)
            self.assertEqual(state.subnormalized, {})
            self.assertIsNone(state.conditional)
            self.assertEqual(len(state.branches), 2)
            self.assertTrue(all(not branch.amplitudes and not branch.probability for branch in state.branches))

    def test_same_shape_nonphysical_transfer_and_wrong_field_types_rejected(self):
        for matrix in (((2, 0, 0), (0, 0, 0)),
                       ((Q(3, 5), Q(3, 5), 0), (Q(3, 5), Q(3, 5), 0))):
            with self.assertRaisesRegex(ValueError, "nonphysical"):
                code.prepare_heralds(matrix, code.ideal_collection())
        for matrix in (((0, 0), (0, 0)), ((True, 0, 0), (0, 0, 0)),
                       ((0.5, 0, 0), (0, 0, 0))):
            with self.assertRaises((ValueError, TypeError)):
                code.collection_matrix(matrix)
        with self.assertRaisesRegex(ValueError, "unitary"):
            code.bsm_bras(((1, 1), (0, 1)))

    def test_radical_order_inverse_and_model_scope(self):
        value = 2 + angular.sqrt_rational(2) + angular.sqrt_rational(3)
        self.assertEqual(value * code.radical_inverse(value), angular.Radical(1))
        self.assertEqual(code.radical_sign(1 - angular.sqrt_rational(2)), -1)
        self.assertEqual(code.radical_sign(2 - angular.sqrt_rational(2)), 1)
        self.assertEqual(code.radical_sign(0), 0)
        with self.assertRaises(ZeroDivisionError):
            code.radical_inverse(0)
        metadata = code.model_metadata()
        self.assertEqual(len(metadata["pair_basis"]), 9)
        for flag in ("actual_preparation_identified", "actual", "controller_advance",
                     "herald_token_mapping_asserted", "propagation_performed"):
            self.assertFalse(metadata[flag])


if __name__ == "__main__":
    unittest.main()
