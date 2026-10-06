"""Independent elimination handles signed branches, coordinate poles and singular anchors."""
from fractions import Fraction as Q
import unittest

import hardware_anchor_check as checker
from model import Effect, Instrument


LAW = {'alice_bias': ['0', '1/10'], 'bob_bias': ['0', '-1/10'],
       'X': [['0', '0'], ['-3/8', '9/20']], 'Z': [['2/5', '12/25'], ['0', '0']]}
PROBES = ({'setting': 1, 'x': '1', 'z': '0'}, {'setting': 0, 'x': '0', 'z': '1'})


class IndependentAnchorTests(unittest.TestCase):
    def test_independent_split_setting_recovery_and_row_swap(self):
        expected = Instrument((Effect(0, 0, Q(4, 5)), Effect(Q(1, 10), Q(-3, 4), 0)),
                              (Effect(0, Q(1, 2), Q(1, 2)), Effect(Q(-1, 10), Q(-3, 5), Q(3, 5))))
        self.assertEqual(checker.recover(LAW, PROBES, ('-13/20', '4/5')), expected)
        self.assertEqual(checker.recover(LAW, PROBES[::-1], ('4/5', '-13/20')), expected)

    def test_independent_zero_product_and_dependent_probe_rejected(self):
        with self.assertRaises(ValueError): checker.recover(LAW, (PROBES[0], PROBES[0]), ('-13/20', '-13/20'))
        invalid = dict(LAW, X=[['0', '0'], ['0', '0']])
        with self.assertRaises(ValueError): checker.recover(invalid, PROBES, ('-13/20', '4/5'))

    def test_target_coordinates_and_wrong_signed_means_rejected(self):
        with self.assertRaises(ValueError): checker.recover(LAW, (dict(PROBES[0], target_u='-3/4'), PROBES[1]), ('-13/20', '4/5'))
        with self.assertRaises(ValueError): checker.recover(LAW, PROBES, ('-13/20', '0'))

    def test_extra_law_fields_or_bias_slots_cannot_be_ignored(self):
        with self.assertRaises(ValueError): checker.recover(dict(LAW, target_effects=[]), PROBES, ('-13/20', '4/5'))
        with self.assertRaises(ValueError): checker.recover(dict(LAW, alice_bias=['0', '1/10', '0']), PROBES, ('-13/20', '4/5'))


if __name__ == '__main__':
    unittest.main()
