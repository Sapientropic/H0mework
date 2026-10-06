"""Immutable opposite-sign readout controls."""
from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import all_data_signs as signs


def witness(sign):
    value = "1/100" if sign == "positive" else "-1/100"
    return {"strict_sign": sign, "actual_positive_Fock_CH_N5": {"exact_lower": value, "exact_upper": value},
            "all_twelve_original_exact_CI_verified": True, "physical_bounds_verified": True}


def positive_header():
    return {"schema": signs.SCHEMA, "version": signs.VERSION, "status": "certified", "statistical_role": signs.base.ROLE,
            "evidence_valid": True, "readout_certified": True,
            "complete_public_CI_fibre_opposite_CH_signs_verified": True,
            "uniform_CH_N5_strictly_positive_refuted": True, "uniform_CH_N5_strictly_negative_refuted": True,
            "uniform_CH_N5_strictly_positive": False, "uniform_CH_N5_strictly_negative": False,
            "uniform_CH_N5_sign": "mixed_certified", "retrospective": True,
            **{key: False for key in signs.FALSE_SCOPE}, "bell_event_files_read": 0,
            "original_NIST_experiment_statistical_rejection_claimed": False,
            "foreign_source_fields_used_as_forward_inputs": False, "source_and_epoch_identifiability_paid": False,
            "base_certificate": {"sha256": signs.BASE_SHA}, "source_bindings": [], "execution_bindings": [],
            "concrete_CH_sign_witnesses": {kind: {sign: witness(sign) for sign in ("positive", "negative")}
                                          for kind in ("primary", "independent")}}


class ConcreteSignsControls(unittest.TestCase):
    def test_positive_opposite_sign_certificate(self):
        self.assertTrue(signs.validate_result(positive_header()))

    def test_strict_zero_is_unresolved(self):
        self.assertEqual(signs.strict_sign({"exact_lower": "0", "exact_upper": "1/100"}), "unresolved")
        self.assertEqual(signs.strict_sign({"exact_lower": "-1/100", "exact_upper": "0"}), "unresolved")

    def test_outer_crossing_is_not_concrete_negative(self):
        packet = positive_header()
        packet["concrete_CH_sign_witnesses"]["primary"]["negative"]["actual_positive_Fock_CH_N5"] = {
            "exact_lower": "-1/100", "exact_upper": "1/100"}
        with self.assertRaisesRegex(ValueError, "unsupported_concrete"):
            signs.validate_result(packet)

    def test_two_positive_sources_do_not_prove_opposite_signs(self):
        packet = positive_header()
        packet["concrete_CH_sign_witnesses"]["independent"]["negative"] = witness("positive")
        with self.assertRaisesRegex(ValueError, "unsupported_concrete"):
            signs.validate_result(packet)

    def test_missing_path_or_sign_rejected(self):
        for key in ("independent", "negative"):
            packet = positive_header()
            if key == "independent":
                del packet["concrete_CH_sign_witnesses"][key]
            else:
                del packet["concrete_CH_sign_witnesses"]["primary"][key]
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, "missing_CH"):
                signs.validate_result(packet)

    def test_unqualified_original_twelve_CI_rejected(self):
        packet = positive_header()
        packet["concrete_CH_sign_witnesses"]["primary"]["positive"]["all_twelve_original_exact_CI_verified"] = False
        with self.assertRaisesRegex(ValueError, "unsupported_concrete"):
            signs.validate_result(packet)

    def test_original_experiment_is_not_rejected_by_model_fibre(self):
        packet = positive_header(); packet["original_NIST_experiment_statistical_rejection_claimed"] = True
        with self.assertRaisesRegex(ValueError, "inflated"):
            signs.validate_result(packet)

    def test_hardware_identity_not_minted(self):
        packet = positive_header(); packet["source_mapping_identified"] = True
        with self.assertRaisesRegex(ValueError, "inflated"):
            signs.validate_result(packet)

    def test_wrong_base_certificate_rejected(self):
        packet = positive_header(); packet["base_certificate"]["sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "base_certificate_identity"):
            signs.validate_result(packet)

    def test_disable_is_immediate(self):
        with patch.object(signs.base, "consume", return_value={"evidence_valid": False, "reason": "explicit_disable"}) as caller:
            result = signs.consume(Path("/missing/signs.json"), disabled=True)
        caller.assert_called_once_with(disabled=True)
        self.assertFalse(result["evidence_valid"])

    def test_disabled_base_cannot_be_bypassed(self):
        with patch.object(signs.base, "consume", return_value={"evidence_valid": False, "reason": "base_failure"}):
            result = signs.consume()
        self.assertFalse(result["evidence_valid"])

    def test_byte_identical_certificate_copy_override(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "signs.json"; path.write_text(json.dumps(positive_header()))
            canonical = {"sha256": signs.base.sha(path.read_bytes())}
            base = {"evidence_valid": True, "readout_certified": True, "certificate": {"sha256": signs.BASE_SHA}}
            with patch.object(signs.base, "consume", return_value=base), patch.object(signs.base, "frozen", return_value=canonical), \
                 patch.object(signs.base, "check_bindings", return_value=True):
                result = signs.consume(path)
            self.assertTrue(result["complete_public_CI_fibre_opposite_CH_signs_verified"])
            self.assertEqual(result["uniform_CH_N5_sign"], "mixed_certified")

    def test_positive_flags_lookalike_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "signs.json"; path.write_text(json.dumps(positive_header()))
            with patch.object(signs.base, "consume", return_value={"evidence_valid": True}), \
                 patch.object(signs.base, "frozen", return_value={"sha256": "0" * 64}):
                result = signs.consume(path)
            self.assertFalse(result["evidence_valid"])
            self.assertIn("lookalike", result["reason"])


if __name__ == "__main__":
    unittest.main()
