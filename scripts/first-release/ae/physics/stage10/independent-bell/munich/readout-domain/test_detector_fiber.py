import unittest
from fractions import Fraction as Q
from itertools import product

from model import Effect
import detector_fiber as d


class DetectorTests(unittest.TestCase):
    def test_raw_atom_detector_forward_and_inverse(self):
        for trace, x, z in ((Q(1),Q(3,5),Q(4,5)), (Q(4,5),Q(1,4),Q(-1,3)), (Q(0),Q(0),Q(0))):
            atom=d.AtomicEffect(trace,x,z)
            for background,eta in product((Q(0),Q(1,10)), (Q(1,2),Q(1))):
                effect=d.forward(atom,background,eta)
                k=(1-background)*eta
                self.assertTrue(d.admits(effect,background,k))
                self.assertEqual(d.inverse(effect,background,k)['atom'],atom)

    def test_complete_fiber_includes_boundary_and_rejects_fake_J(self):
        effect=Effect(Q(1,10),Q(3,10),Q(4,10))
        m,M=Q(1,5),Q(7,10)
        for background,k in product((Q(0),m,Q(3,10)), (Q(1,2),Q(7,10),Q(1))):
            expected=0<=background<=m and M-background<=k<=1-background
            self.assertIs(d.admits(effect,background,k),expected)
            if expected: self.assertEqual(d.forward(d.inverse(effect,background,k)['atom'],background,k/(1-background)),effect)
            else:
                with self.assertRaises(ValueError): d.inverse(effect,background,k)

    def test_zero_factor_stratum_is_explicit(self):
        for background in (Q(0),Q(1,2),Q(1)):
            self.assertTrue(d.admits(Effect(1-2*background,0,0),background,0))
        self.assertFalse(d.admits(Effect(0,Q(1,2),0),Q(1,2),0))
        with self.assertRaises(ValueError): d.inverse(Effect(0,0,0),Q(1,2),0)

    def test_product_bound_attained_at_distinct_eta_and_atomic_responses(self):
        effect=Effect(Q(1,10),Q(1,2),0)
        h=Q(5,8)
        for k in (Q(1,2),Q(4,5)):
            inverse=d.inverse(effect,Q(1,5),k)
            atom=inverse['atom']
            lam=(atom.trace+abs(atom.x))/2
            self.assertEqual(inverse['fragment_efficiency']*lam,h)

    def test_polarity_free_bounds_and_outward_area(self):
        result=d.necessary_bounds(Q(2,5),[Q(-1,10),Q(1,5)])
        reverse=d.necessary_bounds(Q(2,5),[Q(-1,5),Q(1,10)])
        self.assertEqual(result['eta_times_lambda_max_lower'],'1/2')
        self.assertEqual(result['dark_background_upper'],'2/5')
        self.assertEqual(result['eta_times_area_squared_lower'],'2/7')
        self.assertLessEqual(Q(result['area_lower'])**2,Q(result['area_lower_squared']))
        for name in result:
            if name!='bias_interval': self.assertEqual(result[name],reverse[name])

    def test_default_constraints_retain_both_click_polarities(self):
        result=d.atomic_detector_polygons(Q(2,5),[Q(-1,10),Q(1,10)],[Q(4,5),Q(4,5)],[Q(1,20),Q(1,20)])
        self.assertFalse(result['entire_atomic_response_box_excluded'])
        self.assertEqual([r['polarity'] for r in result['branches']],[1,-1])
        for row in result['branches']:
            self.assertTrue(row['vertices'])
            for point in row['vertices']:
                background,k=map(Q,point)
                self.assertTrue(all(Q(a)*background+Q(b)*k<=Q(c) for a,b,c in row['constraints']))

    def test_complete_response_boxes_rejected_for_both_polarities(self):
        for bright,dark in (([0,0],[0,0]), ([Q(1,10),Q(1,5)],[Q(1,10),Q(1,5)])):
            result=d.atomic_detector_polygons(Q(2,5),[Q(-1,10),Q(1,10)],bright,dark)
            self.assertTrue(result['entire_atomic_response_box_excluded'])

    def test_degenerate_polygon_faces_survive(self):
        result=d.atomic_detector_polygons(1,[0,0],[1,1],[0,0])
        self.assertEqual(result['branches'][0]['vertices'],[['0','1']])
        self.assertFalse(result['entire_atomic_response_box_excluded'])

    def test_efficiency_and_area_common_cap(self):
        self.assertEqual(d.hardware_gain_cap(Q(1,2),Q(4,7),Q(1,5)),Q(2,5))
        self.assertEqual(d.hardware_gain_cap(1,0,Q(1,5)),0)
        self.assertEqual(d.hardware_gain_cap(1,1,Q(1,5)),1)
        self.assertLess(d.hardware_gain_cap(Q(1,2),Q(1,7),Q(1,5)),Q(1,2))

    def test_nonphysical_inputs_are_rejected(self):
        for args in ((0,[-1,1]),(Q(2),[0,0]),(Q(1,2),[1,0])):
            with self.assertRaises(ValueError): d.necessary_bounds(*args)
        for args in ((2,1,0),(1,-1,0),(1,1,2)):
            with self.assertRaises(ValueError): d.hardware_gain_cap(*args)
        with self.assertRaises(ValueError): d.AtomicEffect(1,1,1)

    def test_group_bias_uses_own_side_and_strict_old_ray(self):
        roles=(('alice',0),('alice',1),('bob',0),('bob',1))
        shared={'run':'control','shared_response_envelopes':[
            {'side':s,'setting':i,'canonical_gain':['2/5','1']} for s,i in roles]}
        bias={'run':'control','bias_envelopes':[{'side':s,'setting':i,'mu_outer_interval':
              ['-1/10','1/10'] if s=='alice' else ['-1/5','1/5']} for s,i in roles]}
        joint={'run':'control','joint_response_rays':[{'ray':r,'profile_threshold_bracket':['1/2','3/5'],
              'entire_lower_orthant_excluded':True} for r in ('uniform','alice','bob')]}
        result=d.confidence_domain(shared,bias,joint)
        rays=result['joint_hardware_constraints']
        self.assertGreater(Q(rays[1]['maximum_area_strict_lower']),Q(rays[2]['maximum_area_strict_lower']))
        self.assertEqual(rays[0]['group_bias_absolute_upper'],'1/5')
        joint['joint_response_rays'][0]['entire_lower_orthant_excluded']=False
        with self.assertRaises(ValueError): d.confidence_domain(shared,bias,joint)
        joint['run']='different-control'
        with self.assertRaises(ValueError): d.confidence_domain(shared,bias,joint)


if __name__=='__main__': unittest.main()
