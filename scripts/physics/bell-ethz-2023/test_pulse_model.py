"""Independent algebra and convention tests. No experimental data is loaded."""

from dataclasses import replace
import itertools
import math
import unittest

import pulse_model as m


class PulseModelTests(unittest.TestCase):
    def assert_vector_close(self, first, second):
        self.assertEqual(len(first), len(second))
        for a, b in zip(first, second):
            self.assertAlmostEqual(abs(a - b), 0, places=12)

    def test_eq14_gamma_sign_from_pauli_tensor(self):
        for gamma in (0, .43, -1.17, math.pi / 2):
            state = m.source_state(gamma)
            observed = tuple(m.expectation(state, m.tensor(a, b)) for a, b in
                             ((m.X, m.X), (m.X, m.Y), (m.Y, m.X), (m.Y, m.Y), (m.Z, m.Z)))
            self.assert_vector_close(observed, (math.cos(gamma), -math.sin(gamma),
                                               math.sin(gamma), math.cos(gamma), -1))
            for alpha, beta in ((.3, -.7), (-.4, 1.2)):
                def axis(t):
                    return tuple(tuple(math.cos(t) * m.X[i][j] + math.sin(t) * m.Y[i][j]
                                       for j in range(2)) for i in range(2))
                self.assertAlmostEqual(m.expectation(state, m.tensor(axis(alpha), axis(beta))).real,
                                       m.equatorial_correlation(gamma, alpha, beta), places=12)

    def test_all_signed_handed_quarter_sequences(self):
        for fa, oa, ha, fb, ob, hb in itertools.product((-1, 1), repeat=6):
            alice = m.quarter_station(.17, fixed_sign=fa, optional_sign=oa, optional_handedness=ha)
            bob = m.quarter_station(-.61, fixed_sign=fb, optional_sign=ob, optional_handedness=hb)
            expected = m.quarter_correlations(.37, .17, -.61, fa=fa, oa=oa, ha=ha, fb=fb, ob=ob, hb=hb)
            self.assert_vector_close(m.correlations(.37, alice, bob), expected)
            for (a, b), correlation in zip(m.SETTINGS, expected):
                self.assert_vector_close(m.joint_probabilities(.37, alice, bob, a, b),
                                         tuple((1 + x*y*correlation) / 4 for x, y in m.OUTCOMES))

    def test_source_phase_and_bob_axis_shift_are_indistinguishable(self):
        alice = m.Station(m.Pulse(.12, .9), m.Pulse(1.9, -1.3))
        bob = m.Station(m.Pulse(-.35, 1.7), m.Pulse(.92, .4), order="optional_then_fixed")
        shift = .58
        moved = replace(bob, fixed=replace(bob.fixed, phase=bob.fixed.phase-shift),
                        optional=replace(bob.optional, phase=bob.optional.phase-shift))
        for a, b in m.SETTINGS:
            self.assert_vector_close(m.joint_probabilities(.21, alice, bob, a, b),
                                     m.joint_probabilities(.21+shift, alice, moved, a, b))

    def test_two_cell_sign_patterns_have_distinct_possible_origins(self):
        theta = -.63
        alice, bob = m.quarter_station(0), m.quarter_station(theta)
        base = m.correlations(0, alice, bob)
        opposite_off_diagonal = (base[0], -base[1], -base[2], base[3])
        candidates = (
            m.correlations(0, alice, m.quarter_station(-theta)),
            m.correlations(-2*theta, alice, bob),
            m.correlations(0, m.quarter_station(0, optional_sign=-1),
                           m.quarter_station(theta, optional_sign=-1)),
            m.correlations(0, replace(alice, setting_xor=1), replace(bob, setting_xor=1)),
            m.correlations(0, replace(alice, output_signs=(1, -1)), replace(bob, output_signs=(1, -1))))
        for candidate in candidates:
            self.assert_vector_close(candidate, opposite_off_diagonal)
        global_reverse = m.correlations(0, m.quarter_station(0, fixed_sign=-1, optional_sign=-1),
                                       m.quarter_station(theta, fixed_sign=-1, optional_sign=-1))
        self.assert_vector_close(global_reverse, base)
        self.assert_vector_close(m.correlations(0, replace(alice, output_signs=(-1, -1)),
                                                replace(bob, output_signs=(-1, -1))), base)

    def test_order_reversal_removes_quarter_setting_distinction(self):
        alice = m.quarter_station(.1, order="optional_then_fixed")
        bob = m.quarter_station(-.4, order="optional_then_fixed")
        values = m.correlations(.2, alice, bob)
        self.assert_vector_close(values, (math.cos(-.3),) * 4)

    def test_complete_complex_conjugation_is_a_convention_change(self):
        alice = m.Station(m.Pulse(.2, .8), m.Pulse(1.2, 1.7))
        bob = m.Station(m.Pulse(-.5, 1.1), m.Pulse(.7, -.9))
        def conjugate(station):
            return replace(station, fixed=m.Pulse(-station.fixed.phase, -station.fixed.angle),
                           optional=m.Pulse(-station.optional.phase, -station.optional.angle))
        for a, b in m.SETTINGS:
            self.assert_vector_close(m.joint_probabilities(.48, alice, bob, a, b),
                                     m.joint_probabilities(-.48, conjugate(alice), conjugate(bob), a, b))

    def test_drive_handedness_changes_both_pulse_axes(self):
        for h in (-1, 1):
            alice = m.drive_station(0, zero_phase=0, phase_handedness=h)
            bob = m.drive_station(-.63, zero_phase=0, phase_handedness=h)
            self.assert_vector_close(m.correlations(0, alice, bob),
                                     m.quarter_correlations(0, 0, -.63))

    def test_chsh_phase_is_relative_to_its_sign_functional(self):
        for delta in (-1.1, -.2, .7):
            c = m.quarter_correlations(delta, 0, 0)
            self.assertAlmostEqual(m.chsh(c, (1, -1, 1, 1)),
                                   2*math.sqrt(2)*math.cos(delta-math.pi/4), places=12)
            self.assertAlmostEqual(m.chsh(c, (1, 1, -1, 1)),
                                   2*math.sqrt(2)*math.cos(delta+math.pi/4), places=12)

    def test_legacy_nominal_table_fails_official_optimality_closure(self):
        c = m.correlations(0, m.quarter_station(0), m.quarter_station(-math.pi/4))
        self.assert_vector_close(c, tuple(s/math.sqrt(2) for s in (1, 1, -1, 1)))
        official_s = m.chsh(c, m.OFFICIAL_CHSH_SIGNS)
        self.assertAlmostEqual(official_s, 0, places=12)
        self.assertGreater(abs(official_s - 2*math.sqrt(2)), 2.8)

    def test_assignment_formula_matches_full_forward_channel(self):
        v, fa, fb = .81, (.93, .98), (.9, .97)
        eta_a, eta_b = fa[0]-fa[1], fb[0]-fb[1]
        kappa_a, kappa_b = sum(fa)-1, sum(fb)-1
        for a, b in m.SETTINGS:
            p = m.joint_probabilities(.28, m.quarter_station(0), m.quarter_station(-.7), a, b)
            correlation = sum(x*y*q for (x, y), q in zip(m.OUTCOMES, p))
            expected = tuple((1+x*eta_a+y*eta_b+x*y*(eta_a*eta_b+kappa_a*kappa_b*v*correlation))/4
                             for x, y in m.OUTCOMES)
            self.assert_vector_close(m.depolarize_and_assign(p, v, fa, fb), expected)

    def test_visibility_and_assignment_do_not_repair_zero_ideal_chsh(self):
        alice, bob = m.quarter_station(0), m.quarter_station(-math.pi/4)
        for v, fa, fb in ((0, (.9, .98), (.93, .96)), (.7, (.97, .99), (.94, .98)),
                          (1, (1, 1), (1, 1))):
            values = []
            for a, b in m.SETTINGS:
                joint = m.depolarize_and_assign(m.joint_probabilities(0, alice, bob, a, b), v, fa, fb)
                values.append(sum(x*y*p for (x, y), p in zip(m.OUTCOMES, joint)))
            self.assertAlmostEqual(m.chsh(values, m.OFFICIAL_CHSH_SIGNS),
                                   2*(fa[0]-fa[1])*(fb[0]-fb[1]), places=12)

    def test_invalid_control_and_probability_inputs_fail(self):
        for operation in (lambda: m.Pulse(float("nan"), 1), lambda: m.source_state(float("inf")),
                          lambda: m.quarter_station(0, optional_handedness=0),
                          lambda: m.Station(m.Pulse(0, 1), m.Pulse(1, 1), setting_xor=2),
                          lambda: m.chsh((1, 1, 1, 1), (1, 1, 1, 1)),
                          lambda: m.depolarize_and_assign((.4, .4, .4, .4), 1, (1, 1), (1, 1))):
            with self.assertRaises(ValueError):
                operation()


if __name__ == "__main__":
    unittest.main()
