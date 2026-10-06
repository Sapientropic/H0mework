import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from fractions import Fraction as F
import consume as c


class Controls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cfg=json.loads((c.HERE/'criterion.md').read_text().split('```json')[1].split('```')[0])
        cls.inputs=json.loads((c.PUBLIC/'public-summaries/inputs.json').read_text())
        cls.cross=json.loads((c.MW/'cross-verification.json').read_text())

    def test_positive_full_public_family(self):
        r=c.consume();self.assertTrue(r['cut_free_public_family_source_signature_certified'])
        self.assertEqual(len(r['public_spacelike_family']),24);self.assertEqual(len(r['auxiliary_N9']),6)
        self.assertLess(F(r['selected_XOR3_N5']['public_24_family_p_upper']),F(1,20))
        self.assertEqual(r['selected_XOR3_N5']['original_all_mask_family_p_upper'],'1')

    def test_copy_override(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'copy.json';p.write_bytes((c.HERE/'certification.json').read_bytes())
            self.assertTrue(c.consume(p)['evidence_valid'])

    def test_disable_without_access(self):
        with patch.object(c,'frozen',side_effect=AssertionError('no disabled reads')):
            self.assertFalse(c.consume('/missing',True)['evidence_valid'])

    def test_private_tau_lookalike_rejected(self):
        r=json.loads((c.HERE/'certification.json').read_text());r['hidden_cut_log_required']=True;r['private_tau']='unpublished'
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'fake.json';p.write_text(json.dumps(r))
            with self.assertRaisesRegex(ValueError,'original-byte'):c.consume(p)

    def test_old_prefix_exposure_rejected(self):
        d=copy.deepcopy(self.inputs);b=next(b for b in d['diagnostic_workbooks'] if b['file']=='diag-xor3.xlsx')
        b['groups'][2]['complete_trials_literal_count_sum']=177358351
        with self.assertRaisesRegex(ValueError,'exposure'):c.signatures(d,self.cross,self.cfg)

    def test_wrong_pulse_mapping_rejected(self):
        d=copy.deepcopy(self.inputs);d['diagnostic_workbooks'][0]['groups'][0]['paper_pulse_numbers']=[5]
        with self.assertRaisesRegex(ValueError,'pulse mapping'):c.signatures(d,self.cross,self.cfg)

    def test_N9_Bell_promotion_rejected(self):
        d=copy.deepcopy(self.cross);next(r for r in d['local_count_review'] if r['N']==9)['four_window_spacelike_scope']=True
        with self.assertRaisesRegex(ValueError,'Bell scope'):c.signatures(self.inputs,d,self.cfg)

    def test_missing_family_member_rejected(self):
        d=copy.deepcopy(self.cross);d['local_count_review'].pop()
        with self.assertRaises(ValueError):c.signatures(self.inputs,d,self.cfg)

    def test_global_bound_rewrite_rejected(self):
        d=copy.deepcopy(self.cross);next(r for r in d['local_count_review'] if r['workbook']=='diag-xor3.xlsx' and r['N']==5)['all_6_times_32767_p_upper']='1/100'
        with self.assertRaisesRegex(ValueError,'old family bound'):c.signatures(self.inputs,d,self.cfg)

    def test_private_cut_in_source_rejected(self):
        d=copy.deepcopy(self.inputs);d['diagnostic_workbooks'][0]['groups'][0]['training_Nchi']=999
        with self.assertRaisesRegex(ValueError,'private cut'):c.signatures(d,self.cross,self.cfg)

    def test_reciprocal_bound_and_cap(self):
        self.assertEqual(c.bound(F(1000),24),F(3,125))
        self.assertEqual(c.bound(F(1,2),24),F(1))
        with self.assertRaises(ValueError):c.bound(F(0),24)


if __name__=='__main__':unittest.main()
