from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
from types import SimpleNamespace
import gzip
import json
import tempfile
import unittest
import numpy as np

import zero_count_primal_source_rha0040 as source
import zero_count_primal_independent_rha0040 as independent
import zero_count_primal_proposal_rha0040 as proposal
import zero_count_primal_check_rha0040 as checker
from test_prepared_retarded_gaussian_inlet import fixture,NS


@lru_cache(maxsize=1)
def parents():
    # Admit the paid pump certificates through their original constructors.
    source.paid.paid.restore_prepared()
    current=fixture(Q(0));return current,source.base.ZeroCountReceiptSource(current._law)


def flow(side=0,index=0,query='all'):
    current,parent=parents();start=Q(current._law.record()['gate_seconds'][0])
    return source.LocalNoCountPrimalFlow(current,parent,side,index,query=query,stop=start+NS/8)


class PrimalNoCountControls(unittest.TestCase):
    def test_source_inlet_default_override_and_independent_raw_bath(self):
        current,parent=parents();original=current._law.record()
        first=flow();self.assertEqual(first.record()['source_clock'],'local_a+u')
        self.assertEqual(first.record()['query'],'all')
        other=flow(1,2,'perp');self.assertEqual(other.record()['side'],1)
        self.assertEqual(other.record()['factor_index'],2)
        self.assertEqual(other.record()['factor_id'],current.record()['checked_local_density_inventories'][1][2]['factor_id'])
        self.assertFalse(other.record()['caller_initial_matrix_used'])
        for query,ports in source.base.PORT_SETS.items():
            for side in (0,1):
                self.assertEqual(parent.query(query)['complete_unobserved_local_recycling'][side],
                                 independent.local_recycling(original,side,ports))
        with self.assertRaisesRegex(ValueError,'source-issued'):source.LocalNoCountPrimalFlow(SimpleNamespace(),parent)
        with self.assertRaisesRegex(ValueError,'inventory'):flow(index=100)

    def test_all_complete_complex_columns_are_independent_and_dual_to_paid_adjoint(self):
        primal=source.Columns(flow(query='perp'));secondary=independent.Columns(primal.raw)
        adjoint=source.base.Columns(primal.flow._coflow);dual={name:{} for name in ('quiet','drive')}
        for k in range(33):
            for l in range(33):
                for name in dual:
                    primary,ep=primal.column(name,(k,l));other,eo=secondary.column(name,(k,l))
                    self.assertLessEqual(source.fourier._difference(primary,other),ep+eo)
                    for (m,n),value in primal.exact_column(name,(k,l)).items():
                        dual[name].setdefault((n,m),{})[l,k]=value
        for i in range(33):
            for j in range(33):
                for name in dual:self.assertEqual(dual[name].get((i,j),{}),adjoint.exact_column(name,(i,j)))

    def test_source_issued_driven_primal_and_independent_full_residual(self):
        original=flow(index=2,query='perp');handoff={'schema':source.SCHEMA+'/handoff','primal_source':original.record()}
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'primal.gz';proposal.propose(handoff,path,degree=32,allow_float64=True)
            report=checker.certify(original,path,Path(directory)/'checked',allow_float64=True)
            self.assertTrue(report['registered_accuracy_passed'])
            self.assertTrue(report['source_Hermitian_TNI_contraction_used'])
            self.assertFalse(report['old_inlet_error_reapplied_per_factor'])
            self.assertFalse(report['signed_factor_positivity_assumed'])
            self.assertGreater(Q(report['mathematical_Gamma_price']),0)
            self.assertEqual(len(report['independent_source_prefixes']),1)

    def test_default_precision_wrong_factor_and_wrong_clock_counterexamples(self):
        original=flow();handoff={'schema':source.SCHEMA+'/handoff','primal_source':original.record()}
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'primal.gz'
            if np.finfo(np.longdouble).nmant+1<64:
                with self.assertRaisesRegex(ValueError,'mantissa'):proposal.propose(handoff,path)
            proposal.propose(handoff,path,degree=32,allow_float64=True)
            with gzip.open(path,'rt') as f:lines=[json.loads(line) for line in f]
            lines[0]['source_factor_id']='unissued';bad=Path(directory)/'wrong-factor.gz'
            with gzip.open(bad,'wt') as f:
                for line in lines:f.write(json.dumps(line)+'\n')
            with self.assertRaisesRegex(ValueError,'factor'):checker.certify(original,bad,Path(directory)/'bad-check',allow_float64=True)
            raw=original.record();raw['source_clock']='local_b-u'
            with self.assertRaisesRegex(ValueError,'primal'):independent.Columns(raw)
        fake={'duration_seconds':str(NS/8),'chebyshev_coefficients':[[[0,1,1,0]]]}
        with self.assertRaises(ValueError):checker.integer.piece(source.Columns(original),independent.scalar(original.record()),fake,{},Q(0),96,20)


if __name__=='__main__':unittest.main()
