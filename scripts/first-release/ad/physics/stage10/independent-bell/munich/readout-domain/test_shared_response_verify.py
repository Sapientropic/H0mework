"""Shared-profile consumer checks complete coverage and preserved scientific scope."""
import copy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import shared_response_verify as verifier
from test_shared_response_independent import synthetic_reports


class SharedIntakeTests(unittest.TestCase):
    def fixture(self):
        p, c, b, old = synthetic_reports()
        i = verifier.independent.verify_report(p, c, b, old)
        return p, i, c, b, old

    def test_full_four_context_source_profile_coverage(self):
        result = verifier.validate(*self.fixture())
        self.assertEqual(result["context_likelihood_checks"], 64)
        self.assertTrue(result["old_cp0001_envelopes_preserved_or_tightened"])

    def test_sharpness_identity_or_budget_promotion_rejected(self):
        p, i, c, b, old = self.fixture()
        for field in ("actual_gain_extremum_sharpness_claimed", "hardware_parameter_uniqueness_certified", "new_confidence_budget_spent"):
            forged = copy.deepcopy(i)
            forged[field] = True
            with self.subTest(field=field), self.assertRaises(ValueError):
                verifier.validate(p, forged, c, b, old)

    def test_one_missing_context_cannot_close_shared_response(self):
        p, i, c, b, old = self.fixture()
        p["runs"][0]["shared_response_envelopes"][0]["profile_lower_endpoint"]["contexts"].pop()
        with self.assertRaises(ValueError):
            verifier.validate(p, i, c, b, old)

    def test_lower_bound_must_be_generated_from_certified_endpoint(self):
        p, i, c, b, old = self.fixture()
        p["runs"][0]["shared_response_envelopes"][0]["canonical_gain"][0] = "99/100"
        with self.assertRaises(ValueError):
            verifier.validate(p, i, c, b, old)

    def test_override_is_same_evidence_relocation(self):
        result = {"schema": verifier.SCHEMA, "evidence_valid": True}
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory) / "receipt.json"
            p.write_text(verifier.parent.canonical(result))
            with patch.object(verifier, "generate", return_value=result):
                self.assertEqual(verifier.consume(p), result)
                p.write_text(verifier.parent.canonical({**result, "actual_gain_extremum_sharpness_claimed": True}))
                with self.assertRaises(ValueError):
                    verifier.consume(p)


if __name__ == "__main__":
    unittest.main()
