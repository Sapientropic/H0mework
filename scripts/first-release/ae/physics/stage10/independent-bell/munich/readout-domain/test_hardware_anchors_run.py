"""Frozen constructor controls cannot be promoted to actual calibration or unique hardware."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import hardware_anchors_run as science


class HardwareAnchorEvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.path = science.BASE / 'hardware-anchors-first.json'
        cls.receipt = json.loads(cls.path.read_text())

    def test_actual_construction_controls(self):
        result = science.consume()
        self.assertTrue(result['conditional_signed_hardware_reconstruction_certified'])
        self.assertEqual(result['known_generated_law_controls_checked'], 34)
        self.assertFalse(result['actual_hardware_uniquely_identified'])

    def test_location_override_preserves_exact_input_identity(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'copy.json'
            path.write_text(json.dumps(self.receipt))
            self.assertTrue(science.consume(path)['evidence_valid'])

    def test_constructor_control_cannot_be_promoted_to_actual_input(self):
        for name in ('actual_hardware_uniquely_identified', 'actual_independent_anchor_inputs_available',
                     'construction_controls_used_as_actual_calibration', 'atomic_response_forward_model_kernel_proved'):
            receipt = copy.deepcopy(self.receipt)
            receipt[name] = True
            with self.subTest(field=name), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / 'lookalike.json'
                path.write_text(json.dumps(receipt))
                with self.assertRaises(ValueError): science.consume(path)

    def test_changed_signed_probe_response_is_rejected(self):
        receipt = copy.deepcopy(self.receipt)
        receipt['runs'][0]['known_generated_law_controls'][0]['generated_test_response_means'][0] = '0'
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'changed.json'
            path.write_text(json.dumps(receipt))
            with self.assertRaises(ValueError): science.consume(path)


if __name__ == '__main__':
    unittest.main()
