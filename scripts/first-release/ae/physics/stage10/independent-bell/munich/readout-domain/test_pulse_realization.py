import unittest
from fractions import Fraction as Q

from model import Effect
import pulse_realization as p


class PulseRealizerTests(unittest.TestCase):
    def test_two_distinct_physical_spectra_realize_one_effect(self):
        effect=Effect(Q(1,10),Q(3,10),Q(4,10))
        for b,r in ((Q(9,10),Q(1,10)),(Q(4,5),Q(1,5))):
            self.assertTrue(p.feasible(effect,b,r)[0])
            result=p.realize_box(effect,[b,b],[r,r])
            self.assertTrue(result['source_effect_restored_exactly'])
            self.assertTrue(result['normalized_axis_is_symbolic'])

    def test_midpoint_pass_does_not_pay_the_whole_box(self):
        effect=Effect(0,Q(4,5),0)
        self.assertTrue(p.feasible(effect,Q(9,10),Q(1,10))[0])
        box=p.realize_box(effect,[Q(3,4),1],[0,Q(1,4)])
        self.assertFalse(box['whole_response_box_realizes_source_effect'])
        self.assertEqual(box['status'],'undetermined_response_box')

    def test_entire_bad_response_box_is_rejected(self):
        result=p.realize_box(Effect(0,Q(4,5),0),[Q(1,2),Q(3,5)],[Q(1,5),Q(1,4)])
        self.assertEqual(result['status'],'whole_response_box_excluded_for_source_effect')

    def test_feasible_boundary_retains_zero_background_and_eta_one(self):
        effect=Effect(0,Q(4,5),0)
        result=p.realize_box(effect,[Q(9,10),Q(9,10)],[Q(1,10),Q(1,10)])
        self.assertEqual(result['background_interval'],['0','0'])
        self.assertEqual(result['fragment_efficiency_interval'],['1','1'])

    def test_worst_corner_pays_all_four_vertices(self):
        effect=Effect(0,Q(1,2),0)
        result=p.realize_box(effect,[Q(4,5),Q(9,10)],[Q(1,10),Q(1,5)])
        self.assertTrue(result['whole_response_box_realizes_source_effect'])
        for b in (Q(4,5),Q(9,10)):
            for r in (Q(1,10),Q(1,5)): self.assertTrue(p.feasible(effect,b,r)[0])

    def test_only_raw_difference_does_not_certify_response_difference(self):
        a={'p_bright':['4/5','9/10'],'p_dark':['1/10','1/5']}
        self.assertFalse(p.responses_separated(a,a))
        self.assertTrue(p.responses_separated(a,{'p_bright':['19/20','1'],'p_dark':['1/10','1/5']}))

    def test_numerical_gain_is_outward_exact(self):
        lo,hi=p.square_root_interval(Q(2,3))
        self.assertLessEqual(lo*lo,Q(2,3)); self.assertGreaterEqual(hi*hi,Q(2,3))
        self.assertEqual(p.square_root_interval(Q(9,25)),(Q(3,5),Q(3,5)))

    def test_zero_and_nonphysical_spectra_rejected(self):
        for b,r in ((0,0),(Q(1,2),Q(1,2)),(Q(1,2),Q(3,4)),(2,0)):
            with self.assertRaises(ValueError): p.feasible(Effect(0,Q(1,2),0),b,r)
        with self.assertRaises(ValueError): p.feasible(Effect(0,0,0),1,0)


if __name__=='__main__': unittest.main()
