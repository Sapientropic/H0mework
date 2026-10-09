from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import copy
import gzip
import json
import tempfile
import unittest
import numpy as np

import zero_count_receipt_rha0039 as source
import zero_count_independent_rha0039 as independent
import zero_count_proposal_rha0039 as proposal
import zero_count_check_rha0039 as checker
from test_retarded_gaussian_bsm_source import fixture

NS=Q(1,10**9)


@lru_cache(maxsize=1)
def parent():return source.ZeroCountReceiptSource(fixture(gate_start=3*NS))


class ZeroCountCoflowControls(unittest.TestCase):
    def test_independent_raw_transfer_and_complete_complex_columns(self):
        original=parent();raw=original.record()['original_retarded_source']
        for query in source.PORT_SETS:
            for side in (0,1):
                self.assertEqual(original.query(query)['complete_unobserved_local_recycling'][side],
                                 independent.local_recycling(raw,side,source.PORT_SETS[query]))
        coflow=source.LocalNoCountCoflow(original,0,query='perp',start=3*NS,stop=25*NS/8)
        primary=source.Columns(coflow);secondary=independent.Columns(coflow.record())
        for i in range(33):
            for j in range(33):
                for name in ('quiet','drive'):
                    a,ea=primary.column(name,(i,j));b,eb=secondary.column(name,(i,j))
                    self.assertLessEqual(source.operator.basis.density.fourier._difference(a,b),ea+eb)
                    adjoint,_=primary.column(name,(j,i))
                    self.assertEqual(a,{(q,p):(x,-y) for (p,q),(x,y) in adjoint.items()})

    def test_independent_cross_arm_nonzero_branch_is_not_factorized(self):
        raw=copy.deepcopy(parent().record()['original_retarded_source']);pack=raw['complete_driven_field_source']['working_common_optical_source']
        row=pack['generated_four_by_six_transfer'][0]
        pack['generated_four_by_six_transfer'][0]=[(source.channel._complex_record(z)*Q(1,2)).serialize() for z in row]
        with self.assertRaisesRegex(ValueError,'coupled generator'):
            independent.local_recycling(raw,0,source.PORT_SETS['perp'])

    def test_driven_reverse_coflow_with_explicit_query_and_independent_residual(self):
        for query in ('all','perp'):
            coflow=source.LocalNoCountCoflow(parent(),0,query=query,start=3*NS,stop=25*NS/8)
            handoff={'schema':source.SCHEMA+'/handoff','coflow_source':coflow.record()}
            with tempfile.TemporaryDirectory() as directory:
                path=Path(directory)/'curve.gz';proposal.propose(handoff,path,degree=32,allow_float64=True)
                report=checker.certify(coflow,path,Path(directory)/'checked',allow_float64=True)
                self.assertTrue(report['registered_accuracy_passed']);self.assertTrue(report['CP_subunital_operator_contraction_used'])
                self.assertFalse(report['input_error_applied_to_effect'])
                with gzip.open(path,'rt') as handle:header=json.loads(next(handle));value=json.loads(next(handle))
                primary=checker.arithmetic.piece(source.Columns(coflow),independent.scalar(coflow.record()),value,
                    {(i,i):(Q(1),Q(0)) for i in range(33)},Q(0),header['mode_bits'],20)
                secondary=independent.piece(coflow.record(),value,{(i,i):(Q(1),Q(0)) for i in range(33)},Q(0),header['mode_bits'],20)
                self.assertEqual(primary[:2],secondary[:2]);self.assertLess(abs(primary[2]-secondary[2]),Q(1,1 << 80))

    def test_default_precision_wrong_source_and_Hermitian_counterexamples(self):
        coflow=source.LocalNoCountCoflow(parent(),0,start=3*NS,stop=25*NS/8)
        handoff={'schema':source.SCHEMA+'/handoff','coflow_source':coflow.record()}
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'curve.gz'
            if np.finfo(np.longdouble).nmant+1<64:
                with self.assertRaises(ValueError):proposal.propose(handoff,path)
            proposal.propose(handoff,path,degree=32,allow_float64=True)
            with gzip.open(path,'rt') as f:lines=[json.loads(line) for line in f]
            lines[0]['coflow_source_sha256']='0'*64;bad=Path(directory)/'bad.gz'
            with gzip.open(bad,'wt') as f:
                for line in lines:f.write(json.dumps(line)+'\n')
            with self.assertRaises(ValueError):checker.certify(coflow,bad,Path(directory)/'bad-check',allow_float64=True)
            value={'duration_seconds':str(NS/8),'chebyshev_coefficients':[[[0,1,1,0]]]}
            with self.assertRaises(ValueError):checker.arithmetic.piece(source.Columns(coflow),independent.scalar(coflow.record()),value,{},Q(0),96,20)


if __name__=='__main__':unittest.main()
