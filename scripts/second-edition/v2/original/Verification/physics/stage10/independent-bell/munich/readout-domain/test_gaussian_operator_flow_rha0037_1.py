from copy import deepcopy
from fractions import Fraction as Q
from pathlib import Path
from types import SimpleNamespace
import gzip
import json
import tempfile
import unittest

import numpy as np
import gaussian_operator_flow_rha0037_1 as flow
import gaussian_operator_independent_rha0037_1 as independent
import gaussian_operator_proposal_rha0037_1 as proposal
import gaussian_operator_check_rha0037_1 as checker
import gaussian_operator_bank_rha0037_1 as bank
from test_gaussian_atomic_pulse_source import source as pulse_fixture

NS = Q(1, 10**9)


class GaussianOperatorFlowControls(unittest.TestCase):
    def test_original_source_transpose_and_scalar_reflection(self):
        pulse = pulse_fixture(); forward = flow.GaussianOperatorFlow(pulse, 3*NS, 5*NS)
        reverse = flow.GaussianOperatorFlow(pulse, 3*NS, 5*NS, direction='reverse_right')
        self.assertEqual(forward.record()['original_Gaussian_source'], reverse.record()['original_Gaussian_source'])
        self.assertEqual(reverse._quiet, flow.transpose(forward._quiet))
        self.assertEqual(reverse._drive, flow.transpose(forward._drive))
        raw = pulse.record()
        for u in (Q(0), NS/7, NS, 2*NS):
            physical = 5*NS-u
            self.assertEqual((physical-Q(raw['centre_seconds']))**2,
                             (u-Q(reverse._view['centre_seconds']))**2)

    def test_complete_detector_plans_extend_certification_horizon_without_new_pulse(self):
        pulse = pulse_fixture(); original = pulse.record()
        current = SimpleNamespace(record=lambda: {
            'retarded_detector_law': {'gate_seconds': [str(NS), str(121*NS)]},
            'actual_retarded_local_cuts_seconds': [str(NS), str(NS)]},
            _law=SimpleNamespace(_field=SimpleNamespace(_pulses=(pulse, pulse)), local_times=lambda t:(t,t)))
        _, plans = bank.plans(current)
        self.assertEqual([(s,r) for s,r,_ in plans], [(s,r) for s in (0,1) for r in bank.ROLES])
        self.assertEqual([x.record()['source_interval_seconds'] for _,_,x in plans[:3]],
                         [[str(NS),str(61*NS)], [str(NS),str(61*NS)], [str(61*NS),str(121*NS)]])
        for _,_,source in plans:
            raw=source.record()
            self.assertEqual(raw['original_Gaussian_source'], original)
            self.assertEqual(raw['original_operator_certification_horizon_seconds'], str(20*NS))
            self.assertFalse(raw['Gaussian_field_truncated'])

    def test_nonzero_tail_beyond_old_horizon_has_its_own_full_residual(self):
        pulse = pulse_fixture(); original=pulse.record()
        self.assertLess(Q(original['duration_seconds']), 21*NS)
        physical=flow.gaussian._matrix(pulse.generator(21*NS)['complete_K'])
        self.assertTrue(any(flow.gaussian.dipole.STATES[i].family=='D2' and
                            flow.gaussian.dipole.STATES[j].family=='ground' for i,j in physical))
        for direction in flow.DIRECTIONS:
            source=flow.GaussianOperatorFlow(pulse,21*NS,169*NS/8,direction=direction)
            handoff={'schema':flow.SCHEMA+'/handoff','flow_source':source.record()}
            with tempfile.TemporaryDirectory() as directory:
                path=Path(directory)/'curve.gz'
                proposal.propose(handoff,path,degree=32,allow_float64=True)
                result=checker.certify(source,path,Path(directory)/'checked',allow_float64=True)
                self.assertTrue(result['registered_accuracy_passed'])
                self.assertEqual(source.record()['original_Gaussian_source'],original)
                self.assertNotEqual(flow.gaussian._matrix(result['complete_physical_endpoint']),
                                    {(i,i):flow.gaussian.dipole.ComplexRadical(1) for i in range(33)})

    def test_full33_nonHermitian_operator_columns_match_independently(self):
        for direction in flow.DIRECTIONS:
            source = flow.GaussianOperatorFlow(pulse_fixture(), 3*NS, 5*NS, direction=direction)
            record = source.record(); columns = flow.IntegerColumns(source)
            k, ek, v, ev = independent.parts(record); quantum = 1 << columns.bits
            for name, operator, error in (('quiet', k, ek), ('drive', v, ev)):
                own_error = source._parts[1 if name == 'quiet' else 3]
                for i in range(33):
                    for j in range(33):
                        matrix = {(i, j): (1, 0)}
                        actual = {key: (Q(a, quantum), Q(b, quantum)) for key, (a, b) in columns.action(name, matrix).items()}
                        expected = independent.multiply(operator, {(i, j): (Q(1), Q(0))})
                        for key in set(actual)|set(expected):
                            a, b = actual.get(key, (0, 0)); c, d = expected.get(key, (0, 0))
                            self.assertLessEqual(abs(a-c)+abs(b-d), 2*(error+own_error))

    def test_spectator_carrier_keeps_full_D1_without_optical_step_scale(self):
        source = flow.GaussianOperatorFlow(pulse_fixture(), 3*NS, 5*NS)
        self.assertTrue(source.record()['D1_and_D2_optical_frames_retained_exactly'])
        self.assertNotEqual(Q(source.record()['D1_frame_frequency_per_second']), 0)
        self.assertLess(max(abs(a)+abs(b) for a, b in source._quiet.values()), 10**12)
        d1 = [i for i, state in enumerate(flow.gaussian.dipole.STATES) if state.family == 'D1']
        self.assertTrue(all((i, i) in source._quiet for i in d1))

    def test_default_forward_role_and_explicit_coflow_override(self):
        pulse = pulse_fixture(); a = flow.GaussianOperatorFlow(pulse, 3*NS, 5*NS)
        b = flow.GaussianOperatorFlow(pulse, 3*NS, 5*NS, direction='reverse_right')
        rows = [(0, 'early_forward', a), (0, 'early_reverse_right', b)]
        self.assertIs(bank.choose(rows)[2], a)
        self.assertIs(bank.choose(rows, role='early_reverse_right')[2], b)
        with self.assertRaises(ValueError): bank.choose(rows, side=1)
        with self.assertRaises(ValueError): bank.choose(rows, role='inverse')

    def test_source_lookalikes_view_mutation_and_invalid_intervals_rejected(self):
        pulse = pulse_fixture()
        with self.assertRaises(ValueError): flow.GaussianOperatorFlow(SimpleNamespace(record=pulse.record), 3*NS, 5*NS)
        with self.assertRaises(ValueError): flow.GaussianOperatorFlow(pulse, 5*NS, 3*NS)
        with self.assertRaises(ValueError): flow.GaussianOperatorFlow(pulse, -NS, 3*NS)
        with self.assertRaises(ValueError): flow.GaussianOperatorFlow(pulse, 3*NS, 5*NS, direction='inverse')
        source = flow.GaussianOperatorFlow(pulse, 3*NS, 5*NS); source._view['centre_seconds'] = '0'
        with self.assertRaises(ValueError): source.record()
        source = flow.GaussianOperatorFlow(pulse, 3*NS, 5*NS); source._quiet[0, 0] = (Q(0), Q(0))
        with self.assertRaises(ValueError): source.record()

    def test_driven_complete_operator_curve_and_rational_residual(self):
        for direction in flow.DIRECTIONS:
            source = flow.GaussianOperatorFlow(pulse_fixture(), 3*NS, 13*NS/4, direction=direction)
            handoff = {'schema': flow.SCHEMA+'/handoff', 'flow_source': source.record()}
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory)/'curve.gz'
                proposal.propose(handoff, path, degree=32, allow_float64=True)
                result = checker.certify(source, path, Path(directory)/'checked', allow_float64=True)
                self.assertTrue(result['registered_accuracy_passed'])
                self.assertFalse(result['operator_Hermitian_projected'])
                endpoint = flow.gaussian._matrix(result['complete_physical_endpoint'])
                self.assertNotEqual(endpoint, flow.gaussian.dipole.matrix_adjoint(endpoint))
                with gzip.open(path, 'rt') as handle:
                    header, value = json.loads(next(handle)), json.loads(next(handle))
                initial = {(i, i): (Q(1), Q(0)) for i in range(33)}
                first = flow.piece(source, flow.IntegerColumns(source), value, initial, Q(0), header['mode_bits'])
                second = independent.piece(source.record(), value, initial, Q(0), header['mode_bits'])
                self.assertEqual(first[:2], second[:2]); self.assertLess(abs(first[2]-second[2]), Q(1, 1 << 80))

    def test_numeric_precision_default_and_wrong_direction_rejected(self):
        source = flow.GaussianOperatorFlow(pulse_fixture(), 3*NS, 13*NS/4)
        handoff = {'schema': flow.SCHEMA+'/handoff', 'flow_source': source.record()}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'curve.gz'
            if np.finfo(np.longdouble).nmant+1 < 64:
                with self.assertRaises(ValueError): proposal.propose(handoff, path)
            proposal.propose(handoff, path, degree=32, allow_float64=True)
            with gzip.open(path, 'rt') as handle: lines = [json.loads(line) for line in handle]
            lines[0]['direction'] = 'reverse_right'; bad = Path(directory)/'bad.gz'
            with gzip.open(bad, 'wt') as handle:
                for line in lines: handle.write(json.dumps(line)+'\n')
            with self.assertRaises(ValueError): checker.certify(source, bad, Path(directory)/'bad-check', allow_float64=True)


if __name__ == '__main__':
    unittest.main()
