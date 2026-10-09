from fractions import Fraction as Q
from functools import lru_cache
from types import SimpleNamespace
import unittest

import first_receipt_flux_source_rha0040 as source
from test_retarded_gaussian_bsm_source import fixture,matrix,NS


@lru_cache(maxsize=1)
def parent():return source.FirstReceiptFluxSource(fixture(gate_start=3*NS))


class FirstReceiptFluxControls(unittest.TestCase):
    def test_complete_original_pending_quantum_flux_and_priority(self):
        owner=parent();raw=owner.record();original=owner._original
        self.assertEqual(len(raw['complete_no_count_queries']),7)
        self.assertEqual(sum(q['requires_coupled_no_count_flow'] for q in raw['complete_no_count_queries']),4)
        state={}
        for index,mark in enumerate(source.base._marks(original)):
            if mark.receipt is None:
                for (i,j),z in matrix().items():state[mark,i,j]=z*Q(index+1,1000)
        coimages=owner.project_pending(state);actual=original.pending_action_and_flux(3*NS,state)
        self.assertEqual(owner.contract(3*NS,coimages),actual['four_pattern_retarded_flux'])
        self.assertFalse(raw['CEM_time_mother_issued_here'])
        self.assertFalse(raw['whole_hardware_domain_local_factorization_claimed'])

    def test_priority_is_read_from_the_original_source_and_cannot_be_guessed(self):
        original=parent()._original;mark=source.base.bsm.INITIAL
        for port in (1,3):mark=source.base.bsm.BSMSource.target(original._gate,mark,port)
        coimages=parent().project_pending({(mark,i,j):z for (i,j),z in matrix().items()})
        flux=parent().contract(3*NS,coimages)
        self.assertTrue(flux[0]);self.assertFalse(flux[2])
        all_only={q:m for q,m in coimages.items() if q in source.base.PORT_SETS}
        with self.assertRaisesRegex(ValueError,'source-issued coimages'):parent().contract(3*NS,all_only)

    def test_source_lookalike_wrong_clock_and_receipt_latch_are_rejected(self):
        with self.assertRaisesRegex(ValueError,'closed original'):source.FirstReceiptFluxSource(SimpleNamespace(record=lambda:parent().record()))
        mark=source.base.bsm.INITIAL
        for port in (0,3):mark=source.base.bsm.BSMSource.target(parent()._original._gate,mark,port)
        with self.assertRaisesRegex(ValueError,'pending'):parent().project_pending({(mark,0,0):source.base.dipole.ComplexRadical(1)})
        coimages=parent().project_pending({})
        with self.assertRaisesRegex(ValueError,'original clock'):parent().contract(2*NS,coimages)


if __name__=='__main__':unittest.main()
