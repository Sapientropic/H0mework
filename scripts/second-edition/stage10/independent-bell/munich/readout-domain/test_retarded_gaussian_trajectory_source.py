"""Full source chart, relative carrier and stopped physical coimage controls."""
from fractions import Fraction as Q
from functools import lru_cache
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import retarded_gaussian_trajectory_source as code
from test_retarded_gaussian_bsm_source import fixture as law_fixture, matrix, forget

NS = Q(1,10**9)


@lru_cache(maxsize=1)
def fixture():
    return code.RetardedGaussianTrajectorySource(law_fixture())


def blocks_norm(state):
    return code._norm(code.bsm.BSMSource.blocks(fixture()._law._gate,state),192)


class SourceTrajectoryControls(unittest.TestCase):
    def test_complete_rotation_recovers_original_lab_generator_and_trace(self):
        source = fixture(); time = 3*NS; law = source._law
        original = {(code.bsm.INITIAL,i,j):v for (i,j),v in matrix().items()}
        rotated,e0 = source.frame(time,original,inverse=True)
        action,error = source.action(time,rotated)
        _,active = source._clock(time)
        for mark,state in source._blocks(rotated).items():
            code._mark(action,mark,source._counter(state,active),-1)
        restored,ef = source.frame(time,action)
        actual,ea = law.marked_action(time,original,bits=192)
        difference = dict(restored); code._add(difference,actual,-1)
        raw = law.record()['complete_driven_field_source']['Gaussian_source_legs']
        operator_bound = Q(0)
        for leg in raw:
            operator_bound += 4*(code.gaussian._norm(code.gaussian._matrix(leg['complete_static_H_per_second']),192)+
                code.gaussian._norm(code.gaussian._matrix(leg['source_raising_operator_per_second']),192)+
                code.gaussian._norm(code.gaussian._matrix(leg['complete_natural_R_per_second']),192)+
                abs(Q(leg['carrier_angular_frequency_per_second'])))
        operator_bound += 2*sum(map(Q,law.record()['BG_source']['BG_rates_per_second']),Q(0))
        self.assertLessEqual(blocks_norm(difference),error+ef+ea+e0*operator_bound)
        self.assertFalse(code.joint._trace(forget(actual)))
        rotated_action,_ = source.action(time,rotated)
        self.assertFalse(code.joint._trace(forget(rotated_action)))
        self.assertGreater(len(source.record()['generated_stopped_marks']), 11)
        self.assertTrue(source.record()['complete_mark_counts_not_binary_coarsened'])

    def test_absorbed_frame_counterflow_freezes_its_physical_retarded_coimage(self):
        source = fixture(); gate = source._law._gate
        one = code.bsm.BSMSource.target(gate,code.bsm.INITIAL,0)
        absorbed = code.bsm.BSMSource.target(gate,one,3)
        self.assertIsNotNone(absorbed.receipt)
        original = {(absorbed,i,j):v for (i,j),v in matrix().items()}
        rotated,_ = source.frame(3*NS,original,inverse=True)
        action,error = source.action(3*NS,rotated)
        _,active = source._clock(3*NS)
        expected = {}; code._mark(expected,absorbed,source._counter(source._blocks(rotated)[absorbed],active))
        self.assertEqual(action,expected)
        self.assertEqual(error,0)
        self.assertFalse(source.record()['full_field_and_queue_reset'])

    def test_flight_override_leaves_its_relative_phase_and_partitions_true_activation(self):
        source = fixture(); raw = source.slice_components(5*NS/2,3*NS)
        cross = [d for d in raw['components'] if isinstance(d['component'],list) and d['component'][0]=='cross']
        self.assertEqual(len(cross),2)
        self.assertTrue(all(d['exact_frequency_per_second']=='0' for d in cross))
        self.assertNotEqual(cross[0]['polynomial_coefficients'][0],['1','0'])
        with self.assertRaisesRegex(ValueError,'activation boundary'):
            source.slice_components(0,3*NS)
        with self.assertRaisesRegex(ValueError,'fixed original detector gate'):
            source.slice_components(119*NS,121*NS)

    def test_lookalike_callback_and_nested_operator_alias_do_not_change_source_columns(self):
        with self.assertRaisesRegex(ValueError,'closed original retarded'):
            code.RetardedGaussianTrajectorySource(SimpleNamespace())
        with patch.object(code,'_mark',lambda *args:None),self.assertRaisesRegex(ValueError,'components changed'):
            fixture().record()
        source = fixture(); original = dict(source._parts[0][0])
        source._parts[0][0].clear()
        try:
            with self.assertRaisesRegex(ValueError,'trajectory columns changed'):
                source.record()
        finally:
            source._parts[0][0].update(original)
        source.record()


if __name__ == '__main__':
    unittest.main()
