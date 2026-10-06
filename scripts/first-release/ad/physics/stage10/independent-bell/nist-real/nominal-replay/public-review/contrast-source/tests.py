"""Focused source-certificate intake controls; no Lean or numerical solver rerun."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import certify as c


class IntakeControls(unittest.TestCase):
    def test_original_positive(self):
        row=c.fastconsume()
        self.assertTrue(row['evidence_valid'])
        self.assertTrue(row['source_generated_probability_law_all_N'])
        self.assertTrue(row['source_negative_CH_implies_original_binomial_threshold'])
        self.assertTrue(row['source_negative_CH_fixed_bet_expected_value_bound'])
        self.assertFalse(row['new_stochastic_process_or_Ville_kernel'])
        self.assertFalse(row['actual_source_epoch_or_hardware_identified'])

    def test_immutable_copy_override(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'copy.json';p.write_bytes((c.HERE/'certification.json').read_bytes())
            self.assertTrue(c.fastconsume(p)['evidence_valid'])

    def test_disabled_override(self):
        with patch.object(c,'frozen',side_effect=AssertionError('disabled must not inspect files')):
            row=c.fastconsume('/missing',True)
        self.assertFalse(row['evidence_valid'])
        self.assertFalse(row['source_generated_probability_law_all_N'])

    def test_lookalike_false_process_claim_rejected(self):
        data=json.loads((c.HERE/'certification.json').read_text())
        data['kernel_claims']['new_stochastic_process_or_Ville_kernel']=True
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'lookalike.json';p.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError,'original-byte'):
                c.fastconsume(p)

    def test_lookalike_unauthorized_axiom_rejected(self):
        data=json.loads((c.HERE/'certification.json').read_text())
        data['authorized_axioms'].append('FalseOracle')
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'lookalike.json';p.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError,'original-byte'):
                c.fastconsume(p)

    def test_wrong_loss_labels_rejected(self):
        data=json.loads((c.HERE/'certification.json').read_text())
        data['mouth_scope']['one_step']='swap 01.onlyA with 01.onlyB'
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'wrong-labels.json';p.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError,'original-byte'):
                c.fastconsume(p)

    def test_source_changed_rejected(self):
        original=c.digest
        def changed(p):
            return '0'*64 if p.name=='ContrastSource.lean' else original(p)
        with patch.object(c,'digest',side_effect=changed):
            with self.assertRaises(ValueError):
                c.fastconsume()


if __name__=='__main__':
    unittest.main()
