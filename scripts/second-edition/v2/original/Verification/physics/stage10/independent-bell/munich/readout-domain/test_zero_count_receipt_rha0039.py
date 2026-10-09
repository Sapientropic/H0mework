from fractions import Fraction as Q
from types import SimpleNamespace
import copy
import unittest
import zero_count_receipt_rha0039 as code
from test_retarded_gaussian_bsm_source import fixture


class ZeroCountReceiptControls(unittest.TestCase):
    def test_original_first_receipt_queries_and_three_complete_no_count_faces(self):
        source=code.ZeroCountReceiptSource(fixture(gate_start=3*Q(1,10**9)))
        raw=source.record();self.assertEqual([r['query'] for r in raw['complete_queries']],['perp','parallel','all'])
        self.assertEqual(source.query()['ports'],[0,1,2,3])
        self.assertEqual(source.query('perp')['ports'],[0,2])
        self.assertTrue(all(r['cross_arm_Gram_zero_checked'] for r in raw['complete_queries']))
        self.assertEqual(len(raw['complete_Mark_restrictions']),3)
        for row in raw['complete_Mark_restrictions']:self.assertGreater(row['original_Mark_port_transitions_checked'],0)
        self.assertFalse(raw['specific_Psi_label_probability_claimed'])

    def test_no_count_identity_generates_negative_same_detected_effect(self):
        source=code.ZeroCountReceiptSource(fixture(gate_start=3*Q(1,10**9)))
        raw=source.record()['original_retarded_source'];identity={(i,i):(Q(1),Q(0)) for i in range(33)}
        for query in code.PORT_SETS:
            for side in (0,1):
                coflow=code.LocalNoCountCoflow(source,side,query=query);columns=code.Columns(coflow)
                got,error=columns.action('quiet',identity);expected={}
                for group,rate,modes in source._original._groups:
                    for port in code.PORT_SETS[query]:
                        j={}
                        for mu,(s,matrix) in modes:
                            if s==side:code.gaussian.field._add(j,matrix,source._original._transfer[port][mu])
                        code.gaussian.field._add(expected,code.dipole.matrix_product(code.dipole.matrix_adjoint(j),j),-rate)
                rational,prices=code.gaussian.full._midpoint_matrix(expected,192)
                difference=code.operator.basis.density.fourier._difference(got,rational)
                self.assertLessEqual(difference,error+sum(prices.values(),Q(0)))
                self.assertEqual(columns.action('drive',identity)[0],{})

    def test_closed_owner_invalid_query_and_inactive_source_rejected(self):
        with self.assertRaises(ValueError):code.ZeroCountReceiptSource(SimpleNamespace(record=fixture().record))
        source=code.ZeroCountReceiptSource(fixture(gate_start=3*Q(1,10**9)))
        with self.assertRaises(ValueError):source.query('Psi+')
        with self.assertRaises(ValueError):code.LocalNoCountCoflow(source,False)
        with self.assertRaises(ValueError):code.LocalNoCountCoflow(source,0,start=0)
        initial=code.ZeroCountReceiptSource(fixture())
        with self.assertRaises(ValueError):code.LocalNoCountCoflow(initial,1)
        source._value['specific_Psi_label_probability_claimed']=True
        with self.assertRaises(ValueError):source.record()


if __name__=='__main__':unittest.main()
