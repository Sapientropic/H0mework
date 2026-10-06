"""Independent calibrated-count domain and read-only intake controls."""
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import verify as audit


class CalibratedAuditControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.m=audit.native();cls.spec,_=cls.m.configuration();cls.endpoints=cls.m.load_endpoints()
        cls.first,_=audit.load_first()

    def test_original_19_sources_and_72CI_scope(self):
        audit.candidate_scope(self.first,self.m);self.m.validate_endpoints(self.endpoints)

    def test_default_and_explicit_ENV_allocation(self):
        points,branches=self.m.source_inventory(self.spec)
        self.assertEqual(sum(p['included_in_default_source_box'] for p in points),17)
        self.assertEqual({b['source']['allocation'] for b in branches},{'symmetric','Alice_rank_one','Bob_rank_one'})

    def test_finite_points_cannot_imply_continuum(self):
        bad={**self.first,'finite_point_rejection_implies_continuum_rejection':True}
        with self.assertRaisesRegex(ValueError,'claim_inflation'):audit.candidate_scope(bad,self.m)

    def test_missing_original_CI_rejected(self):
        bad=deepcopy(self.endpoints);bad[0]['CI']['sA_cell'].pop()
        with self.assertRaisesRegex(ValueError,'72_CI'):self.m.validate_endpoints(bad)

    def test_whole_bound_independent_and_N1_not_rejected(self):
        proof,meaning=audit.continuous(self.spec,self.endpoints,self.m)
        self.assertTrue(meaning['bound_independent_of_all_finite_source_points'])
        self.assertLess(proof['single_pulse_click_upper'],F('0.00004'))
        self.assertEqual([w['endpoint'] for w in proof['strict_original_CI_witnesses']],['full_N3','full_N5','full_N7','full_N9','old_stop_N5'])
        self.assertEqual(proof['input_domain']['q'],[F('.0004')-F('1e-12'),F('.0006')+F('1e-12')])

    def test_no_strict_CI_gap_no_whole_rejection(self):
        broad=deepcopy(self.endpoints)
        for e in broad:e['CI']['sA_cell'][0]={'exact_lower':'0','exact_upper':'1'}
        proof,_=audit.continuous(self.spec,broad,self.m)
        self.assertFalse(proof['continuous_nominal_ENV_input_domain_rejected'])

    def test_matched_K_necessary_bound_directions_with_background_and_zero_loss(self):
        ba,bb=map(F,self.spec['background_per_pulse']);I=self.m.primary.I
        for n in (F(0),F('.0002'),F('.0003'),F(1)):
            for ta in (F(0),F('0.75'),F(1)):
                for tb in (F(0),F('0.76'),F(1)):
                    values=self.m.primary.raw_matched(I(n),I(ta),I(tb),ba,bb)
                    kb=(1+n)/(1-ba)*((1+2*n)*tb+bb)
                    ka=ba+(1-ba)*ta*(1-bb/values['single_B'].lo)
                    self.assertLessEqual(values['K_B'].hi,kb)
                    self.assertGreaterEqual(values['K_A'].lo,ka-F('1e-30'))

    def test_FOREIGN_EF_and_epoch_fields_rejected(self):
        source=self.first['source_branches'][0]['source']
        for key in ('lambda','source_epoch_identified'):
            with self.assertRaisesRegex(ValueError,'ENV_source_fields'):self.m.unpack_source({**source,key:True},'primary')

    def test_immutable_first_copy_and_lookalike(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'copy.gz';path.write_bytes((audit.HERE/'first.json.gz').read_bytes())
            report,_=audit.load_first(path);audit.candidate_scope(report,self.m)
            path.write_bytes(b'plausible different source report')
            with self.assertRaisesRegex(ValueError,'lookalike_calibrated_first'):audit.load_first(path)

    def test_NIST_absolute_default_copy_disable_and_lookalike_intake(self):
        driver=str(audit.HERE/'verify.py');first=audit.HERE/'verification.json'
        with tempfile.TemporaryDirectory() as directory:
            copied=Path(directory)/'copy.json';copied.write_bytes(first.read_bytes())
            bad=Path(directory)/'lookalike.json';value=json.loads(first.read_text());value['source_points_checked']=18;bad.write_text(json.dumps(value))
            cases=(([],0,True),(['--certificate',str(copied)],0,True),(['--certificate',str(bad)],1,False),
                   (['--disabled','--certificate',str(Path(directory)/'missing')],0,False))
            for flags,code,valid in cases:
                result=subprocess.run([sys.executable,driver,'--check-only',*flags],cwd=audit.HERE.parents[2],text=True,capture_output=True)
                self.assertEqual(result.returncode,code,result.stderr);row=json.loads(result.stdout)
                self.assertEqual(row['schema'],'public-calibrated-count-evidence/v1');self.assertIs(row['evidence_valid'],valid)
                self.assertIs(row['experimental_or_Born_law_rejected'],False)


if __name__ == '__main__':unittest.main()
