"""Whole-domain pulse-area cuts consume response bounds rather than fitted values."""
from fractions import Fraction as Q
import unittest

import atomic_dose as producer


class AtomicDoseTests(unittest.TestCase):
    def test_root_is_exact_outward_and_whole_low_area_domain_excluded(self):
        gain = Q(2, 5)
        square = 4 * gain / 7
        lower = producer.square_root_lower(square)
        self.assertLessEqual(lower * lower, square)
        self.assertGreater((lower + Q(1, 1 << 80)) ** 2, square)
        self.assertLess(Q(7, 4) * Q(1, 10) ** 2, gain)

    def test_area_uses_raw_rabi_duration_and_is_segment_additive(self):
        pulses = [{'duration': '1/2', 'omega_r': '3'}, {'duration': '1/4', 'omega_r': '2'}]
        self.assertEqual(producer.area(pulses), 2)
        with self.assertRaises(ValueError): producer.area([{'duration': '1', 'omega_r': -1}])

    def test_all_roles_and_all_joint_maxima_are_consumed(self):
        shared = {'shared_response_envelopes': [{'side': side, 'setting': setting, 'canonical_gain': ['2/5', '1']}
                                              for side, setting in producer.ROLES]}
        joint = {'joint_response_rays': [{'ray': ray, 'profile_threshold_bracket': ['3/5', '7/10'],
                                         'entire_lower_orthant_excluded': True} for ray in ('uniform', 'alice', 'bob')]}
        result = producer.bounds(shared, joint)
        self.assertEqual(len(result['individual_exposures']), 4)
        self.assertEqual(len(result['joint_maximum_exposures']), 3)
        self.assertEqual(result['individual_exposures'][0]['readout_rabi_area_squared_lower'], '8/35')
        self.assertFalse(result['new_confidence_budget_spent'])
        self.assertFalse(result['actual_raw_controls_uniquely_identified'])
        joint['joint_response_rays'][0]['entire_lower_orthant_excluded'] = False
        with self.assertRaises(ValueError): producer.bounds(shared, joint)


if __name__ == '__main__':
    unittest.main()
