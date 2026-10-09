from fractions import Fraction as Q
import copy
import unittest

import zero_count_primal_run_rha0041 as code


def fixture():
    matrix=code.source.channel._input_record({(0,0):code.source.dipole.ComplexRadical(1)})
    initial={'checked_local_density_inventories':[[{'factor_id':'A','complete_retarded_local_endpoint':matrix}],
        [{'factor_id':'B','complete_retarded_local_endpoint':matrix}]],'source_factor_ids':[['A','B']],
        'whole_retarded_gate_input_error':'1/1000','source_positive_mass_upper':'1'}
    law={'gate_seconds':['0','1/1000000000'],'BG_source':{'BG_rates_per_second':['0']*4},
        'complete_driven_field_source':{'reference_clock':{'Gamma_numerical_centre':'1',
                                                        'angular_Gamma_enclosure_per_second':['1','1']}}}
    rows=[]
    for query,value in (('perp',Q(4,5)),('parallel',Q(7,10)),('all',Q(3,5))):
        for side,name in ((0,'A'),(1,'B')):
            endpoint=code.source.channel._input_record({(0,0):code.source.dipole.ComplexRadical(value)})
            raw={'factor_id':name,'side':side,'query':query,'source_initial_physical_matrix':matrix}
            rows.append({'query':query,'side':side,'factor_index':0,'factor_id':name,
                'report':{'original_primal_source':raw,'complete_physical_endpoint':endpoint,
                    'whole_new_endpoint_trace_norm_error':'1/1000000000000','initial_entry_norm_upper':'1'}})
    return initial,law,rows


class CompletePrimalBankControls(unittest.TestCase):
    def test_default_override_and_complete_original_incidence(self):
        initial,_,rows=fixture();code.require_cover(rows,initial)
        self.assertEqual(code.select(rows)['query'],'all');self.assertEqual(code.select(rows)['side'],0)
        self.assertEqual(code.select(rows,'parallel',1)['factor_id'],'B')
        with self.assertRaises(ValueError):code.select(rows,'parallel',True)
        for bad in (rows[:-1],rows+[rows[-1]],list(reversed(rows))):
            with self.assertRaisesRegex(ValueError,'source order'):code.require_cover(bad,initial)
        bad=copy.deepcopy(rows);bad[0]['factor_id']='unknown'
        with self.assertRaisesRegex(ValueError,'identity'):code.require_cover(bad,initial)

    def test_complete_endpoint_query_and_whole_input_error_paid_once(self):
        initial,law,rows=fixture();report=code.endpoint_readout(rows,initial,law)
        self.assertEqual(Q(report['any_first_receipt_mass_centre']),Q(23,100))
        self.assertEqual(Q(report['whole_first_receipt_error'])-Q(report['whole_new_effect_and_arithmetic_price']),Q(1,1000))
        self.assertFalse(report['old_input_error_repeated_for_three_no_count_queries'])
        self.assertFalse(report['signed_factor_positivity_assumed'])
        self.assertFalse(report['CEM_time_mother_issued'])
        bad=copy.deepcopy(rows);bad[0]['report']['original_primal_source']['source_initial_physical_matrix']=[]
        with self.assertRaisesRegex(ValueError,'original inlet'):code.endpoint_readout(bad,initial,law)

    def test_independent_duality_requires_the_same_current_and_new_prices(self):
        initial,law,rows=fixture();first=code.endpoint_readout(rows,initial,law)
        other=copy.deepcopy(first);check=code.compare_adjoint(first,other)
        self.assertEqual(Q(check['centre_difference']),0)
        self.assertFalse(check['old_input_error_needed_for_numerical_duality_check'])
        other['any_first_receipt_mass_centre']=str(Q(first['any_first_receipt_mass_centre'])+Q(1,10**6))
        with self.assertRaisesRegex(ValueError,'disagree'):code.compare_adjoint(first,other)
        other=copy.deepcopy(first);other['original_current_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'same initial'):code.compare_adjoint(first,other)


if __name__=='__main__':unittest.main()
