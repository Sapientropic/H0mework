from copy import deepcopy
from fractions import Fraction as Q
from math import factorial
from types import SimpleNamespace
import unittest

import retarded_registered_duhamel_rha0031 as code
import registered_duhamel_independent_rha0031 as independent
from test_retarded_gaussian_trajectory_source import fixture, matrix, NS


class RegisteredDuhamelControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original = fixture(); cls.source = code.RetardedRegisteredDuhamelSource(cls.original)

    def test_all_complete_mark_components_reproduce_original_generator(self):
        self.source.record(); _, active = self.original._clock(3*NS)
        for mark in self.original._marks:
            state = {(mark, i, j): value for (i, j), value in matrix().items()}
            for component in code.trajectory.COMPONENTS:
                expected = self.original._component(component, self.original._blocks(state), active)
                actual = code._free_component(self.original, component, self.original._blocks(state), active)
                code.trajectory._add(actual, code._registered_component(self.original, component, self.original._blocks(state), active))
                self.assertEqual(actual, expected)
        self.assertGreater(self.source.coefficient_identity()['complete_resolved_recycle_coefficient_identities'], 0)

    def test_original_flight_activation_and_receipt_counterflow(self):
        for time in (NS/2, 3*NS/2, 5*NS/2):
            state = {(code.bsm.INITIAL, i, j): value for (i, j), value in matrix().items()}
            for component in code.trajectory.COMPONENTS:
                actual = self.source.free_component_action(component, state, slice_start=time)
                code.trajectory._add(actual, self.source.registered_component_action(component, state, slice_start=time))
                self.assertEqual(actual, self.original.component_action(component, state, slice_start=time))
        absorbed = next(m for m in self.original._marks if m.receipt is not None)
        state = {(absorbed, i, j): value for (i, j), value in matrix().items()}
        self.assertFalse(self.source.registered_component_action('quiet', state, slice_start=3*NS))
        self.assertEqual(self.source.free_component_action('quiet', state, slice_start=3*NS),
                         self.original.component_action('quiet', state, slice_start=3*NS))

    def test_free_and_registered_parts_separately_preserve_trace(self):
        state = {(code.bsm.INITIAL, i, j): value for (i, j), value in matrix().items()}
        free = self.source.free_component_action('quiet', state, slice_start=3*NS)
        registered = self.source.registered_component_action('quiet', state, slice_start=3*NS)
        def trace(raw):
            return sum((v for (_, i, j), v in raw.items() if i == j), code.dipole.ComplexRadical())
        self.assertFalse(trace(free)); self.assertFalse(trace(registered))

    def test_tail_majorizes_every_tested_finite_suffix(self):
        for a in (Q(0), Q(1, 10), Q(1), Q(3)):
            for n in (2, 4, 8):
                bound = code.finite_tail(a, n)
                actual = sum((a**j/factorial(j) for j in range(n+1, n+31)), Q(0))
                self.assertLessEqual(actual, Q(bound['whole_instrument_operator_tail_upper']))
        with self.assertRaises(ValueError): code.finite_tail(4, 2)
        with self.assertRaises(ValueError): code.finite_tail(-Q(1, 1 << 256), 2)

    def test_zero_interval_and_explicit_time_override(self):
        raw = self.original.record()['retarded_source']['gate_seconds']; begin, end = map(Q, raw)
        self.assertEqual(self.source.tail_budget(8, interval=(begin, begin))['whole_instrument_operator_tail_upper'], '0')
        short = self.source.tail_budget(8, interval=(begin, (begin+end)/2))
        whole = self.source.tail_budget(8)
        self.assertLess(Q(short['whole_instrument_operator_tail_upper']), Q(whole['whole_instrument_operator_tail_upper']))
        with self.assertRaises(ValueError): self.source.tail_budget(8, interval=(begin, end+NS))

    def test_lookalike_source_and_changed_activity_rejected(self):
        with self.assertRaises(ValueError): code.RetardedRegisteredDuhamelSource(SimpleNamespace(record=self.original.record))
        old = deepcopy(self.source._value)
        self.source._value['interaction_norm_per_second_upper'] = '0'
        try:
            with self.assertRaises(ValueError): self.source.record()
        finally: self.source._value = old

    def test_independent_complete_scalar_and_transfer_checker(self):
        raw = self.source.record(); activity = raw['complete_activity_source']; facts = activity['source_activity']
        g0, g1 = map(Q, activity['fixed_gate_seconds']); branches = {}
        rates = sum(map(Q, facts['complete_Gamma_family_natural_loss_operator_norms_per_second']), Q(0))
        noise = sum(map(Q, facts['four_source_BG_rate_upper_per_second']), Q(0)); error = Q(1, 1000)
        for label, kappa in (('current_optical_member', Q(facts['registered_optical_operator_norm_square_upper'])),
                            ('whole_objective_transfer_domain', Q(facts['source_objective_operator_norm_square_upper']))):
            rate = kappa*rates+noise; a = 2*rate*(g1-g0); rows = []
            for n in (0, 2, 4, 6, 8, 10, 12, 16):
                if code.upper(a) >= n+2:
                    rows.append({'retained_order': n, 'geometric_ratio_valid': False}); continue
                row = code.finite_tail(a, n); price = code.upper(Q(row['whole_instrument_operator_tail_upper']))
                rows.append({**row, 'geometric_ratio_valid': True, 'source_mass_times_tail_upper': str(price),
                             'tail_below_old_input_error': price < error})
            branches[label] = {'registered_activity_upper_per_second': str(rate),
                'interaction_variation_upper': str(a), 'tail_budgets': rows}
        report = {'schema': 'stage10-registered-Duhamel-full-gate-budget-first/rha0031',
            'source_identity': {'source': 'positiveSmoothUnifiedSource', 'root_visit': 10, 'current_tick': 16, 'next_tick': 17},
            'free_flow_is_complete_local_TP': True, 'physical_receipt_coimage_stays_frozen': True,
            'inverse_TP_flow_used': False, 'large_atomic_H_norm_enters_interaction_tail': False,
            'detector_interval_seconds': list(map(str, (g0, g1))), 'source_positive_mass_upper': '1',
            'old_input_trace_norm_error_once': str(error), 'variation_domains': branches,
            'free_flow_and_quadrature_residuals_already_paid': False, 'full_gate_trajectory_generated': False,
            'actual_hardware_member_asserted': False, 'actual_hardware_uniquely_identified': False, 'controller_advance': False}
        self.assertTrue(independent.check(report, self.original._law.record(), activity)['factorial_recurrence_tail_checked'])
        report['variation_domains']['current_optical_member']['interaction_variation_upper'] = '0'
        with self.assertRaises(ValueError): independent.check(report, self.original._law.record(), activity)


if __name__ == '__main__': unittest.main()
