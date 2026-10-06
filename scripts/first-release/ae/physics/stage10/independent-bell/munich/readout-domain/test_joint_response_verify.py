"""Joint qualification cannot be replaced by individual or identity look-alikes."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import joint_response_verify as consumer


BASE = Path(__file__).resolve().parent


class JointResponseIntakeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.receipts = [json.loads((BASE / name).read_text()) for name in
                        (*consumer.FIRSTS, "primary-first-c0002.json", "identification-first.json",
                         "shared-response-first.json", "primitive-witness-c0002.json")]

    def test_complete_dual_checked_endpoints(self):
        result = consumer.validate(*self.receipts)
        self.assertEqual(result["profile_brackets_checked"], 6)
        self.assertEqual(result["context_likelihood_checks"], 96)
        self.assertEqual(result["lawful_witness_controls_not_excluded"], 2)

    def test_individual_cap_cannot_replace_source_product(self):
        receipts = copy.deepcopy(self.receipts)
        receipts[0]["runs"][0]["joint_response_rays"][0]["profile_lower_endpoint"]["contexts"][0]["gain_product_cap"] = "1"
        with self.assertRaises(ValueError):
            consumer.validate(*receipts)

    def test_sharpness_uniqueness_and_extra_budget_rejected(self):
        for field in ("hardware_parameter_uniqueness_certified", "actual_gain_extremum_sharpness_claimed",
                      "new_confidence_budget_spent", "profile_pass_used_as_full_source_membership"):
            receipts = copy.deepcopy(self.receipts)
            receipts[0][field] = True
            with self.subTest(field=field), self.assertRaises(ValueError):
                consumer.validate(*receipts)

    def test_context_and_primitive_control_identity_required(self):
        receipts = copy.deepcopy(self.receipts)
        receipts[0]["runs"][1]["joint_response_rays"].pop()
        with self.assertRaises(ValueError):
            consumer.validate(*receipts)
        receipts = copy.deepcopy(self.receipts)
        receipts[0]["runs"][0]["controls"][0]["caps"][0] = "1"
        with self.assertRaises(ValueError):
            consumer.validate(*receipts)

    def test_same_byte_receipt_location_override_and_tamper(self):
        receipt = json.loads((BASE / "joint-response-verification.json").read_text())
        with tempfile.TemporaryDirectory() as directory, patch.object(consumer, "generate", return_value=receipt):
            path = Path(directory) / "copy.json"
            path.write_text(json.dumps(receipt))
            self.assertTrue(consumer.consume(path)["evidence_valid"])
            changed = copy.deepcopy(receipt)
            changed["hardware_parameter_uniqueness_certified"] = True
            path.write_text(json.dumps(changed))
            with self.assertRaises(ValueError):
                consumer.consume(path)


if __name__ == "__main__":
    unittest.main()
