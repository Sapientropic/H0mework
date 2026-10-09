from fractions import Fraction as Q
import copy
import unittest
import zero_count_probability_price_rha0039_1 as code


def fixture():
    raw={'gate_seconds':['1','2']};bound,arithmetic=code.activity._poisson_cap(Q(1,10),2,192)
    cap={'schema':code.activity.SCHEMA+'/first-receipt-cap','source_record':{'retarded_source_record':raw,'fixed_gate_seconds':raw['gate_seconds'],
        'scalar_bits':192,'source_activity':{'registered_total_activity_upper_per_second':'1/10'}},
        'receipt_time_restriction_seconds':['1','2'],'input_detector_clock_seconds':'1','activity_horizon_seconds':'1','source_Poisson_mean_upper':'1/10',
        'pending_mark_bounds':[{'original_mark_counts':[0]*4,'original_mark_receipt':None,'minimum_future_registered_arrivals':2,
            'first_receipt_instrument_input_contraction_upper':str(bound),'tail_arithmetic':arithmetic}],
        'whole_first_receipt_input_contraction_upper':str(bound)}
    first={'schema':code.source.SCHEMA+'/complete-any-first-receipt-probability','source_detector_interval_seconds':['1','2'],
        'old_whole_input_error_once':'1/1000','whole_new_effect_and_arithmetic_price':'1/100000','whole_first_receipt_error':'101/100000',
        'any_first_receipt_mass_centre':'1/100','source_positive_mass_upper':'1','physical_any_first_receipt_mass_interval':['899/100000','1101/100000'],
        'source_event_is_complete_first_receipt':True,'old_input_error_repeated_for_three_no_count_queries':False}
    return first,cap,raw,bound


class ZeroCountPriceControls(unittest.TestCase):
    def test_same_source_receipt_cap_refines_old_input_price_once(self):
        first,cap,raw,bound=fixture();r=code.contract(first,cap,raw)
        expected=bound*Q(1,1000)+Q(1,100000)
        self.assertEqual(Q(r['whole_first_receipt_error']),expected)
        self.assertEqual(list(map(Q,r['physical_any_first_receipt_mass_interval'])),[Q(1,100)-expected,Q(1,100)+expected])
        self.assertFalse(r['new_curve_or_source_generation']);self.assertTrue(r['strictly_positive_complete_normalizer'])

    def test_explicit_same_source_copy_and_lookalike_source_rejected(self):
        first,cap,raw,_=fixture();self.assertEqual(code.contract(first,copy.deepcopy(cap),copy.deepcopy(raw)),code.contract(first,cap,raw))
        bad=copy.deepcopy(raw);bad['other_parent']='lookalike'
        with self.assertRaises(ValueError):code.contract(first,cap,bad)
        bad=copy.deepcopy(cap);bad['receipt_time_restriction_seconds']=['1','3/2']
        with self.assertRaises(ValueError):code.contract(first,bad,raw)

    def test_wrong_Mark_or_unpaid_cap_override_rejected(self):
        first,cap,raw,_=fixture();bad=copy.deepcopy(cap);bad['pending_mark_bounds'][0]['minimum_future_registered_arrivals']=1
        with self.assertRaises(ValueError):code.contract(first,bad,raw)
        bad=copy.deepcopy(cap);bad['whole_first_receipt_input_contraction_upper']='0'
        with self.assertRaises(ValueError):code.contract(first,bad,raw)
        bad=copy.deepcopy(first);bad['old_input_error_repeated_for_three_no_count_queries']=True
        with self.assertRaises(ValueError):code.contract(bad,cap,raw)


if __name__=='__main__':unittest.main()
