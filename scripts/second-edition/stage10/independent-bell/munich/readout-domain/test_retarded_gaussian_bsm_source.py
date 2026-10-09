"""Retarded source clocks, exact Gram cancellation and original first flux."""
from fractions import Fraction as Q
from functools import lru_cache
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import retarded_gaussian_bsm_source as code
from test_gaussian_atomic_pulse_source import parent

NS = Q(1, 10**9)


@lru_cache(maxsize=4)
def fixture(flights=(NS, 2*NS), gate_start=0):
    pulses = tuple(code.gaussian.GaussianAtomicPulseSource(parent(), side,
        sigma_squared_seconds=(5*NS)**2, centre_seconds=10*NS, duration_seconds=20*NS) for side in (0, 1))
    source = code.driven.DrivenGaussianFieldSource(*pulses, flight_seconds=flights,
                    emission_origins_seconds=(0, 0), gate_start_seconds=gate_start)
    return code.RetardedGaussianBSMSource(source)


def matrix():
    g = code.dipole.INDEX[code.dipole.State('ground', 1, 0)]
    e = code.dipole.INDEX[code.dipole.State('D2', 2, 0)]
    a, b = code.joint.atom_pair_index(g, e), code.joint.atom_pair_index(e, g)
    return {(a, a): code.dipole.ComplexRadical(Q(1, 2)),
            (b, b): code.dipole.ComplexRadical(Q(1, 2)),
            (a, b): code.dipole.ComplexRadical(Q(1, 7), Q(1, 5)),
            (b, a): code.dipole.ComplexRadical(Q(1, 7), Q(-1, 5))}


def forget(state):
    result = {}
    for (mark, i, j), value in state.items():
        code._add(result, {(i, j): value})
    return result


class RetardedLawControls(unittest.TestCase):
    def test_detected_and_loss_Gram_forget_to_both_original_baths_on_complete_complex_input(self):
        source = fixture(); state = matrix(); time = 3*NS
        times = source.local_times(time)
        unobserved, _ = source._unobserved(state, times, 160)
        combined = dict(unobserved)
        for port in range(4):
            code._add(combined, source._detected(state, times, port))
        original, _ = source.independent_atomic_action(time, state)
        self.assertEqual(combined, original)
        marked, error = source.marked_action(time, {(code.bsm.INITIAL, i, j):v for (i, j), v in state.items()})
        self.assertEqual(forget(marked), original)
        self.assertEqual(code.joint._trace(original), code.dipole.ComplexRadical())
        self.assertGreaterEqual(error, 0)
        self.assertFalse(source.record()['physical_time_atom_state_claimed'])

    def test_original_pending_mark_generates_strictly_positive_first_receipt_flux(self):
        source = fixture(); state = matrix()
        mark = code.bsm.BSMSource.target(source._gate, code.bsm.INITIAL, 0)
        report = source.pending_action_and_flux(3*NS, {(mark, i, j):v for (i, j), v in state.items()})
        total = code.dipole.Radical()
        for matrix_ in report['four_pattern_retarded_flux']:
            total += code.joint._trace(matrix_).real
        centre, scalar_error = code.full.radical_midpoint(total, 160)
        self.assertGreater(centre-scalar_error, 0)
        self.assertEqual(len(report['four_pattern_retarded_flux']), 4)
        self.assertTrue(all(m.receipt is None for m, _, _ in report['pending_generator']))
        total_trace = code.joint._trace(forget(report['pending_generator'])).real+total
        self.assertFalse(total_trace)
        absorbed = code.bsm.BSMSource.target(source._gate, mark, 3)
        with self.assertRaisesRegex(ValueError, 'pending mother'):
            source.pending_action_and_flux(3*NS, {(absorbed, 0, 0):1})

    def test_actual_flight_override_changes_each_source_clock_and_keeps_inactive_arm_dark(self):
        first, other = fixture(), fixture((2*NS, NS))
        self.assertEqual(first.local_times(3*NS), (2*NS, NS))
        self.assertEqual(other.local_times(3*NS), (NS, 2*NS))
        self.assertNotEqual(first.independent_atomic_action(3*NS, matrix())[0],
                            other.independent_atomic_action(3*NS, matrix())[0])
        at_start = fixture().local_times(NS/2)
        drift, error = fixture()._drift(matrix(), at_start, 160)
        self.assertEqual(drift, {})
        self.assertEqual(error, 0)
        self.assertTrue(all(not fixture()._detected(matrix(), at_start, p) for p in range(4)))
        late, _ = first.independent_atomic_action(30*NS, matrix())
        self.assertTrue(late)
        self.assertFalse(code.joint._trace(late))
        self.assertTrue(first.record()['instantaneous_law_keeps_Gaussian_past_operator_certification_horizon'])

    def test_same_shape_callback_and_optical_alias_cannot_change_the_source(self):
        source = fixture()
        with self.assertRaisesRegex(ValueError, 'closed same-owner'):
            code.RetardedGaussianBSMSource(SimpleNamespace(record=lambda:source.record()))
        with patch.object(code, '_recycle', lambda *args:{}), self.assertRaisesRegex(ValueError, 'execution closure changed'):
            source.record()
        old = source._transfer
        source._transfer = tuple(list(old))
        try:
            with self.assertRaisesRegex(ValueError, 'optical transfer'):
                source.record()
        finally:
            source._transfer = old
        source.record()

    def test_original_gate_restricts_marked_law_and_keeps_pre_gate_source_transport(self):
        source = fixture(gate_start=3*NS)
        state = {(code.bsm.INITIAL, i, j):v for (i,j),v in matrix().items()}
        for time in (2*NS, 124*NS):
            with self.assertRaisesRegex(ValueError, 'fixed detector gate'):
                source.marked_action(time, state)
        self.assertTrue(source.independent_atomic_action(2*NS, matrix())[0])
        source.marked_action(3*NS, state)


if __name__ == '__main__':
    unittest.main()
