from fractions import Fraction as Q
import copy
import unittest
import late_registered_run_rha0038 as code


class LateRegisteredRunControls(unittest.TestCase):
    def test_default_cover_and_explicit_piece_override(self):
        rows=[{'piece_index':i} for i in range(60)]
        self.assertIs(code.select(rows),rows[0]);self.assertIs(code.select(rows,59),rows[-1])
        for value in (60,-1,False):
            with self.assertRaises(ValueError):code.select(rows,value)
        with self.assertRaises(ValueError):code.select(rows+[rows[0]])

    def test_source_readout_pays_old_input_once_for_whole_mean(self):
        q=1 << code.integral.B
        ports=[{'port':p,'same_arm_A':[[0,0,q//4,0]],'same_arm_B':[],
            'source_background_identity_coefficient':'1/10','coherent_cross_kernels':[],
            'whole_operator_error_upper':'1/500'} for p in range(4)]
        programme={'source_late_detector_interval_seconds':['0','1'],'registered_total_activity_upper_per_second':'2'}
        midpoint={'old_whole_input_error_once':'1/100','whole_new_free_midpoint_error':'1/1000','source_positive_mass_upper':'1',
            'source_factor_ids':[['a','b']],'rows':[{'side':s,'factor_id':name,'physical_matrix':[[0,0,'1','0']]} for s,name in enumerate(('a','b'))]}
        report=code.readout(ports,programme,midpoint)
        self.assertEqual(Q(report['whole_four_port_mean_centre']),Q(7,5))
        expected=2*Q(11,1000)+4*Q(1,500)*Q(1011,1000)
        self.assertEqual(Q(report['whole_four_port_scalar_error']),expected)
        self.assertTrue(report['old_input_error_paid_once_for_whole_readout'])
        self.assertFalse(report['first_receipt_probability_generated'])

    def test_impossible_source_bound_and_noncanonical_rows_rejected(self):
        with self.assertRaises(ValueError):code._read_rows([[0,0,1,0],[0,0,2,0]],33)
        with self.assertRaises(ValueError):code._read_rows([[0,0,1.0,0]],33)
        q=1 << code.integral.B
        ports=[{'port':p,'same_arm_A':[[0,0,q,0]],'same_arm_B':[],
            'source_background_identity_coefficient':'0','coherent_cross_kernels':[],'whole_operator_error_upper':'0'} for p in range(4)]
        programme={'source_late_detector_interval_seconds':['0','1'],'registered_total_activity_upper_per_second':'1'}
        midpoint={'old_whole_input_error_once':'0','whole_new_free_midpoint_error':'0','source_positive_mass_upper':'1',
            'source_factor_ids':[['a','b']],'rows':[{'side':s,'factor_id':name,'physical_matrix':[[0,0,'1','0']]} for s,name in enumerate(('a','b'))]}
        with self.assertRaises(ValueError):code.readout(ports,programme,midpoint)


if __name__=='__main__':unittest.main()
