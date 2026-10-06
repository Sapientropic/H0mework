"""Focused calibration provenance, semantic and actual readiness controls."""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
from fractions import Fraction as F

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import verify
sys.path.insert(0, str(HERE.parent.parent))


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


class CalibrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.primary = module("calibration_primary_controls", HERE/"calibration.py")
        cls.independent = module("calibration_count_controls", HERE/"independent_count.py")
        cls.readiness = module("calibration_actual_readiness", HERE.parent.parent/"readiness.py")

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        (self.directory/"certification.json").write_bytes((HERE/"certification.json").read_bytes())
        (self.directory/"verification.json").write_text(json.dumps(verify.assess()))

    def callback(self, **kwargs):
        return self.readiness.calibration_readout_investigation(report_dir=self.directory, **kwargs)

    def test_exact_snapshot_tail_bijection(self):
        audit = verify.numeric_audit()
        self.assertEqual((audit["exact_primary_rates_enclosed"], audit["exact_primary_Klyshko_enclosed"]), (36, 24))
        self.assertTrue(audit["twelve_branches_bijective"])
        self.assertTrue(audit["no_calibration_branch_selected"])

    def test_source_law_three_pair_quantities(self):
        values = self.primary.pair_quantities([F(1,4), F(0)])
        self.assertEqual((values["at_least_one"], values["exactly_one"], values["mean_pair"]), (F(1,4), F(3,16), F(1,3)))

    def test_public_percent_unit_is_probability_point_zero_zero_three(self):
        self.assertEqual(verify.numeric_audit()["public_efficiency_probability_half_width"], "0.003")
        original = verify.load
        def wrong_unit(path):
            result = original(path)
            if Path(path) == HERE/"sources.json":
                result["eta_probability_half_width"] = "0.3"
            return result
        with patch.object(verify, "load", side_effect=wrong_unit):
            with self.assertRaisesRegex(ValueError, "public_calibration_role_or_unit_changed"):
                verify.inputs()

    def test_zero_herald_is_undefined_on_both_paths(self):
        packet = {"geometric_ratio": [F(0), F(0)], "transmission_A": [F(1), F(1)], "transmission_B": [F(1), F(1)]}
        result = self.primary.native_bucket(packet, 1, (F(0), F(0)))
        for side in ("Alice", "Bob"):
            self.assertEqual(result["Klyshko"][side]["status"], "UNDEFINED_ZERO_HERALD")
            self.assertIsNone(result["Klyshko"][side]["value"])
        raw = self.independent.source_parameters([0,0], [1,1,1,1])
        own = self.independent.count_readout(raw, 1, [0,0])
        self.assertTrue(all(row["status"] == "UNDEFINED_ZERO_HERALD" and "interval" not in row for row in own["Klyshko"].values()))

    def test_bucket_efficiency_is_not_raw_transmission(self):
        value = self.primary.monomode_identity(F(1,10000), F(4,5), F(3,4))
        self.assertGreater(value, F(4,5))
        self.assertLessEqual(value-F(4,5), 2*F(1,9999))

    def test_no_prefix_renormalization(self):
        raw = self.independent.source_parameters([F(1,10000),0], [1,1,1,1])
        pulse = self.independent.pulse_prefix(raw)
        self.assertEqual(pulse["mass"]+pulse["tail"], 1)
        self.assertGreater(pulse["tail"], 0)
        self.assertNotEqual(pulse["prefix"]["A0"]/pulse["mass"], 1-F(1,10000))

    def test_missing_evidence_and_override(self):
        with tempfile.TemporaryDirectory() as temporary:
            self.assertEqual(verify.assess(temporary)["status"], "missing_calibration_evidence")
        self.assertEqual(verify.assess(enabled=False)["status"], "disabled_by_override")

    def test_actual_readiness_positive_override_lookalike(self):
        valid = self.callback()
        self.assertTrue(valid["evidence_valid"], valid)
        self.assertEqual(self.callback(enabled=False)["status"], "disabled_by_override")
        lookalike = {**verify.assess(), "evidence_valid": 1}
        with patch.object(self.readiness.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, json.dumps(lookalike), "")):
            bad = self.callback()
        self.assertFalse(bad["evidence_valid"])

    def test_each_unbound_flag_is_strict_false(self):
        good = verify.assess()
        self.assertTrue(good["evidence_valid"], good)
        for flag in verify.FLAGS:
            with self.subTest(flag=flag):
                fake = {**good, flag: 0}
                with patch.object(self.readiness.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, json.dumps(fake), "")):
                    self.assertFalse(self.callback()["evidence_valid"])

    def test_no_actual_failure_or_branch_selection(self):
        good = verify.assess()
        for key, value in (("actual_calibration_failure_claimed", True), ("no_calibration_branch_selected", False)):
            fake = {**good, key: value}
            with patch.object(self.readiness.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, json.dumps(fake), "")):
                self.assertFalse(self.callback()["evidence_valid"])

    def test_counterfeit_certificate_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary)/"certification.json"
            receipt = verify.load(HERE/"certification.json")
            receipt["status"] = "certified"
            receipt["source_audit"]["target_in_primitive"] = True
            path.write_text(json.dumps(receipt))
            result = verify.assess(temporary)
            self.assertEqual(result["status"], "invalid_calibration_evidence")
            self.assertFalse(result["evidence_valid"])


if __name__ == "__main__":
    unittest.main()
