"""Anchor inversion uses signed response information and covers nominal coordinate poles."""
from fractions import Fraction as Q
import itertools
import unittest

import hardware_anchors as h
from identification import scale
from model import Effect, Instrument


def generic():
    return Instrument((Effect(0, Q(2, 5), Q(1, 2)), Effect(Q(1, 10), Q(-1, 3), Q(1, 2))),
                      (Effect(Q(-1, 10), Q(1, 2), Q(-1, 3)), Effect(0, Q(-2, 5), Q(2, 5))))


def poles():
    return Instrument((Effect(0, 0, Q(4, 5)), Effect(Q(1, 10), Q(-3, 4), 0)),
                      (Effect(0, Q(1, 2), Q(1, 2)), Effect(Q(-1, 10), Q(-3, 5), Q(3, 5))))


class AnchorTests(unittest.TestCase):
    def test_two_probe_source_constructor_without_reference_effect_inputs(self):
        point = generic()
        probes = (h.Probe(0, 1, 0), h.Probe(0, 0, 1))
        chart = h.AnchorChart(h.quotient(point), probes)
        means = [h.response(point.alice[p.setting], p) for p in probes]
        self.assertEqual(chart.recover(means), point)

    def test_coordinate_poles_use_different_source_product_anchors(self):
        point = poles()
        probes = (h.Probe(1, 1, 0), h.Probe(0, 0, 1))
        chart = h.AnchorChart(h.quotient(point), probes)
        self.assertEqual(chart.pivots, [(1, 0), (0, 0)])
        self.assertEqual(chart.recover([h.response(point.alice[p.setting], p) for p in probes]), point)

    def test_equal_rational_encodings_and_caller_mutation_do_not_change_law(self):
        point = generic()
        law = h.quotient(point)
        law['alice_bias'][0] = 0
        law['bob_bias'][1] = '0/3'
        probes = (h.Probe(0, 1, 0), h.Probe(0, 0, 1))
        chart = h.AnchorChart(law, probes)
        law['X'][0][0] = '1'
        self.assertEqual(chart.recover([h.response(point.alice[p.setting], p) for p in probes]), point)

    def test_independent_signed_probes_resolve_all_four_scale_sign_branches(self):
        point = generic()
        probes = (h.Probe(0, Q(3, 5), Q(4, 5)), h.Probe(1, Q(4, 5), Q(-3, 5)))
        chart = h.AnchorChart(h.quotient(point), probes)
        for first, second in itertools.product((-1, 1), repeat=2):
            other = scale(point, Q(first * 21, 20), Q(second * 19, 20))
            self.assertEqual(chart.recover([h.response(other.alice[p.setting], p) for p in probes]), other)
            self.assertEqual(h.quotient(other), h.quotient(point))

    def test_opposite_probe_pair_does_not_fix_second_scale(self):
        for point, probes in ((generic(), (h.Probe(0, 1, 0), h.Probe(0, -1, 0))),
                              (poles(), (h.Probe(0, 1, 0), h.Probe(0, 0, 1)))):
            with self.assertRaisesRegex(ValueError, "independently"):
                h.AnchorChart(h.quotient(point), probes)

    def test_interval_response_uncertainty_is_exact_affine_projection(self):
        point = generic()
        probes = (h.Probe(0, Q(3, 5), Q(4, 5)), h.Probe(1, Q(4, 5), Q(-3, 5)))
        chart = h.AnchorChart(h.quotient(point), probes)
        means = [h.response(point.alice[p.setting], p) for p in probes]
        error = Q(1, 1000)
        intervals = [(mean - error, mean + error) for mean in means]
        bounds = chart.interval_coordinates(intervals)
        vertices = [chart.anchor_coordinates(pair) for pair in itertools.product(*intervals)]
        for i, (low, high) in enumerate(bounds):
            self.assertEqual((low, high), (min(v[i] for v in vertices), max(v[i] for v in vertices)))
            self.assertEqual(high - low, 2 * error * chart.sensitivity()[i])
            self.assertGreater(high, low)

    def test_rank_one_changed_probabilities_or_nonphysical_response_rejected(self):
        law = h.quotient(generic());law['X'][1][1] = '1'
        with self.assertRaises(ValueError): h.AnchorChart(law, (h.Probe(0, 1, 0), h.Probe(0, 0, 1)))
        chart = h.AnchorChart(h.quotient(generic()), (h.Probe(0, 1, 0), h.Probe(0, 0, 1)))
        for means in ((2, 0), (0, 0), (1, 1)):
            with self.assertRaises(ValueError): chart.recover(means)

    def test_invalid_probe_state_and_float_input_rejected(self):
        for operation in (lambda: h.Probe(True, 1, 0), lambda: h.Probe(0, 1, 1), lambda: h.Probe(0, .5, 0)):
            with self.assertRaises((ValueError, TypeError)): operation()


class SelfCalibrationTests(unittest.TestCase):
    def test_atomic_forward_effects_and_law_biases_recover_detector_without_correctness_targets(self):
        atoms = [{'trace': Q(9, 10), 'x': Q(1, 5), 'z': Q(3, 5)},
                 {'trace': Q(6, 5), 'x': Q(-1, 2), 'z': Q(1, 5)}]
        background, efficiency = Q(1, 50), Q(19, 20)
        factor = (1 - background) * efficiency
        biases = [1 - 2 * background - factor * atom['trace'] for atom in atoms]
        result = h.self_calibrate_atom_response(biases, atoms)
        self.assertEqual(result['background'], background)
        self.assertEqual(result['fragment_efficiency'], efficiency)
        for effect, atom in zip(result['effects'], atoms):
            self.assertEqual(effect.u, -factor * atom['x'])
            self.assertEqual(effect.z, -factor * atom['z'])

    def test_equal_trace_lookalike_and_nonphysical_atomic_effect_rejected(self):
        same = [{'trace': 1, 'x': Q(1, 2), 'z': 0}] * 2
        with self.assertRaisesRegex(ValueError, 'Equal atomic traces'):
            h.self_calibrate_atom_response((0, 0), same)
        bad = [{'trace': Q(1, 2), 'x': 1, 'z': 0}, {'trace': 1, 'x': 0, 'z': 0}]
        with self.assertRaises(ValueError): h.self_calibrate_atom_response((0, 0), bad)
        atoms = [{'trace': Q(1, 2), 'x': 0, 'z': 0}, {'trace': 1, 'x': 0, 'z': 0}]
        with self.assertRaises(ValueError): h.self_calibrate_atom_response((-1, 1), atoms)


if __name__ == '__main__':
    unittest.main()
