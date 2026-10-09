from fractions import Fraction as Q
import copy
import unittest
import zero_count_run_rha0039 as code


class ZeroCountRunControls(unittest.TestCase):
    def test_default_all_query_and_explicit_polarization_override(self):
        rows=[{'query':q,'side':s} for q in code.source.PORT_SETS for s in (0,1)]
        self.assertIs(code.select(rows),rows[4]);self.assertIs(code.select(rows,'perp',1),rows[1])
        for q,s in (('Psi+',0),('all',False),('all',2)):
            with self.assertRaises(ValueError):code.select(rows,q,s)
        with self.assertRaises(ValueError):code.select(rows+[rows[4]])

    def test_complete_any_herald_inclusion_exclusion_and_whole_input_error_once(self):
        d=code.source.dipole;c=code.source.channel
        def matrix(value):return c._input_record({(0,0):d.ComplexRadical(Q(value))})
        initial={'source_factor_ids':[['a','b']],'checked_local_density_inventories':[
            [{'factor_id':'a','complete_retarded_local_endpoint':matrix(1)}],[{'factor_id':'b','complete_retarded_local_endpoint':matrix(1)}]],
            'whole_retarded_gate_input_error':'1/1000','source_positive_mass_upper':'1'}
        clock={'Gamma_numerical_centre':'1','angular_Gamma_enclosure_per_second':['1','1']}
        law={'gate_seconds':['0','1'],'complete_driven_field_source':{'reference_clock':clock},'BG_source':{'BG_rates_per_second':['0']*4}}
        reports=[{'query':q,'side':s,'report':{'complete_physical_effect':matrix(value if s==0 else 1),'whole_new_operator_error':'1/10000','coflow_source':{'side':s}}}
            for q,value in (('perp','3/4'),('parallel','2/3'),('all','1/2')) for s in (0,1)]
        result=code.probability_from_effects(reports,initial,law)
        self.assertEqual(Q(result['any_first_receipt_mass_centre']),Q(1,12))
        expected=Q(1,1000)+3*(2*Q(1,10000)+Q(1,10000)**2)*Q(1001,1000)
        self.assertGreaterEqual(Q(result['whole_first_receipt_error']),expected)
        self.assertLess(Q(result['whole_first_receipt_error']),expected+Q(1,10**40))
        self.assertFalse(result['old_input_error_repeated_for_three_no_count_queries'])
        self.assertTrue(result['source_event_is_complete_first_receipt'])

    def test_wrong_event_effect_sign_is_rejected(self):
        d=code.source.dipole;c=code.source.channel;one=c._input_record({(0,0):d.ComplexRadical(1)})
        initial={'source_factor_ids':[['a','b']],'checked_local_density_inventories':[[{'factor_id':'a','complete_retarded_local_endpoint':one}],[{'factor_id':'b','complete_retarded_local_endpoint':one}]],
            'whole_retarded_gate_input_error':'0','source_positive_mass_upper':'1'}
        law={'gate_seconds':['0','1'],'complete_driven_field_source':{'reference_clock':{'Gamma_numerical_centre':'1','angular_Gamma_enclosure_per_second':['1','1']}},
            'BG_source':{'BG_rates_per_second':['0']*4}}
        reports=[{'query':q,'side':s,'report':{'complete_physical_effect':one if q!='all' else [],'whole_new_operator_error':'0','coflow_source':{'side':s}}}
            for q in code.source.PORT_SETS for s in (0,1)]
        with self.assertRaises(ValueError):code.probability_from_effects(reports,initial,law)


if __name__=='__main__':unittest.main()
