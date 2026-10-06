"""Atomic response evidence cannot become an actual parameter identity by relabelling."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import atomic_forward_verify as consumer


class AtomicEvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.receipts = [json.loads((consumer.BASE / name).read_text()) for name in consumer.FIRSTS]

    def test_complete_dual_response_and_generator_checks(self):
        self.assertIs(type(consumer.validate(*self.receipts)), bool)

    def test_raw_control_replacement_is_rejected(self):
        receipts = copy.deepcopy(self.receipts)
        receipts[0]['samples'][2]['raw_pulses'][0]['omega_r'] = '4'
        with self.assertRaises(ValueError): consumer.validate(*receipts)

    def test_actual_identity_or_extra_alpha_lookalike_is_rejected(self):
        for name in ('actual_hardware_uniquely_identified', 'actual_independent_anchor_inputs_available',
                     'theory_control_samples_used_as_actual_parameters', 'new_confidence_budget_spent'):
            receipts = copy.deepcopy(self.receipts)
            receipts[1][name] = True
            with self.subTest(field=name), self.assertRaises(ValueError): consumer.validate(*receipts)

    def test_disjoint_probability_and_wrong_restriction_are_rejected(self):
        receipts = copy.deepcopy(self.receipts)
        receipts[1]['samples'][2]['response']['p_bright'] = ['0', '0']
        with self.assertRaises(ValueError): consumer.validate(*receipts)
        receipts = copy.deepcopy(self.receipts)
        receipts[1]['samples'][0]['restriction_check']['exact_formal_coefficient_checks'] = 1
        with self.assertRaises(ValueError): consumer.validate(*receipts)

    def test_trace_anchor_must_be_generated_by_the_same_ionization_response(self):
        receipts = copy.deepcopy(self.receipts)
        receipts[1]['samples'][2]['response']['trace_j'] = ['1', '1']
        with self.assertRaises(ValueError): consumer.validate(*receipts)

    def test_receipt_location_override_and_tamper(self):
        path = consumer.BASE / 'atomic-forward-verification.json'
        receipt = json.loads(path.read_text())
        with tempfile.TemporaryDirectory() as directory, patch.object(consumer, 'generate', return_value=receipt):
            override = Path(directory) / 'copy.json'
            override.write_text(json.dumps(receipt))
            self.assertTrue(consumer.consume(override)['evidence_valid'])
            receipt = dict(receipt, actual_hardware_uniquely_identified=True)
            override.write_text(json.dumps(receipt))
            with self.assertRaises(ValueError): consumer.consume(override)


if __name__ == '__main__':
    unittest.main()
