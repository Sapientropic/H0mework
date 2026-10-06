#!/usr/bin/env python3
"""Focused source-family and evidence controls; changed reports stay temporary."""
import copy
from fractions import Fraction as F
import json
import math
from pathlib import Path
import sys
import tempfile
import unittest

import verify


class ObservableEvidenceControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        verify.program_freeze(Path(__file__))
        cls.config,_ = verify.scientific_inputs()
        cls.primary = json.loads((verify.HERE/verify.PRIMARY).read_text())
        cls.independent = json.loads((verify.HERE/verify.INDEPENDENT).read_text())
        cls.actual = verify.assess()
        if cls.actual["status"] != "verified":
            raise AssertionError(cls.actual)
        cls.main_program = verify.implementation(verify.HERE/"predict.py")

    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="p23-observable-controls-")
        self.addCleanup(directory.cleanup)
        self.directory = Path(directory.name)
        self.main,self.own = copy.deepcopy(self.primary),copy.deepcopy(self.independent)

    def write(self):
        path = self.directory/verify.PRIMARY
        path.write_text(json.dumps(self.main)+"\n")
        if "comparison" in self.own:
            self.own["bindings"][verify.relative(verify.HERE/verify.PRIMARY)] = verify.digest(path)
            self.own["comparison"]["primary_sha256"] = verify.digest(path)
            _,bindings = verify.scientific_inputs()
            bindings[verify.relative(verify.HERE/"predict.py")] = self.main["program_sha256"]
            self.own["comparison"]["primary_bindings"] = bindings
        (self.directory/verify.INDEPENDENT).write_text(json.dumps(self.own)+"\n")

    def rejected(self):
        self.write()
        result = verify.assess(self.directory)
        self.assertEqual(result["status"],"invalid_observable_evidence",result)
        self.assertFalse(result["evidence_valid"])
        self.assertTrue(all(result[k] is False for k in verify.IDENTITY))

    def row(self,report,model="S1_signal"):
        return next(row for row in report["rows"] if row["case_id"] == "all_collected/p1/ph0/a1/"+model)

    def test_positive_control_explicit_directory(self):
        self.write()
        (self.directory/"predict.py").write_text('raise RuntimeError("untrusted program")\n')
        (self.directory/"criterion.md").write_text('{}')
        result = verify.assess(self.directory)
        self.assertEqual(result["status"],"verified",result)
        self.assertEqual(result["source_controls"],336)
        self.assertEqual(tuple(result["models"]),verify.MODELS)
        self.assertTrue(result["source_full_mode_and_OR_branch_recomputed"])

    def test_explicit_disable_override(self):
        self.write()
        result = verify.assess(self.directory,enabled=False)
        self.assertEqual(result["status"],"disabled_by_override")
        self.assertFalse(result["evidence_valid"])

    def test_readiness_consumes_actual_reports_with_override_and_lookalike(self):
        self.write()
        (self.directory/"verification.json").write_text('{"status":"verified"}\n')
        sys.path.insert(0,str(verify.HERE.parent.parent))
        readiness = verify.implementation(verify.HERE.parent.parent/"readiness.py")
        result = readiness.observable_prediction_investigation(report_dir=self.directory)
        self.assertEqual(result["status"],"verified_research_source_observable_prediction",result)
        self.assertFalse(result["production_admitted"])
        result = readiness.observable_prediction_investigation(report_dir=self.directory,enabled=False)
        self.assertEqual(result["status"],"disabled_by_override",result)
        self.row(self.main)["rates"]["j"][2] += 1e-7
        self.write()
        result = readiness.observable_prediction_investigation(report_dir=self.directory)
        self.assertEqual(result["status"],"invalid_observable_prediction_evidence",result)
        self.assertFalse(result["evidence_valid"])

    def test_false_source_flag_cannot_be_zero(self):
        self.main["source_mapping_identified"] = 0
        self.rejected()

    def test_fake_production_identity_rejected(self):
        self.own["production_admitted"] = True
        self.rejected()

    def test_source_criterion_binding_rejected(self):
        self.main["criterion_sha256"] = "0"*64
        self.rejected()

    def test_missing_model_cannot_select_a_winner(self):
        self.main["rows"] = [r for r in self.main["rows"] if r["model"] != "named_M3"]
        self.rejected()

    def test_duplicate_case_cannot_hide_missing_source(self):
        self.main["rows"][-1] = copy.deepcopy(self.main["rows"][0])
        self.rejected()

    def test_wrong_coherence_is_rejected(self):
        self.row(self.main)["source_gram"]["X"] *= 2
        self.rejected()

    def test_held_out_mutation_keeps_training_and_changes_residual(self):
        row = self.row(self.primary)
        rates = copy.deepcopy(row["rates"])
        angles = [math.radians(float(F(x))) for x in self.config["angles_deg"][1]]
        background = [float(F(self.config["rates"][k])) for k in ("background_A","background_B")]
        before = self.main_program.inverse(rates,angles,"S1_signal",background)
        rates["j"][2] += 1e-7
        after = self.main_program.inverse(rates,angles,"S1_signal",background)
        self.assertEqual(before["gram"],after["gram"])
        self.assertEqual(before["held_out_prediction"],after["held_out_prediction"])
        self.assertAlmostEqual(after["held_out_residual"]-before["held_out_residual"],1e-7,places=16)

    def test_forged_held_out_residual_cannot_pass(self):
        self.row(self.main)["rates"]["j"][2] += 1e-7
        self.row(self.main)["reconstruction"]["held_out_residual"] = 0.
        self.rejected()

    def test_wrong_joint_marginal_singles_rejected_for_actual_source(self):
        row = self.row(self.main)
        row["signal"]["sA"][0] = row["signal"]["j"][0]
        row["rates"]["sA"][0] = row["signal"]["sA"][0]+float(F(self.config["rates"]["background_A"]))
        self.rejected()

    def test_same_joint_different_loss_inclusive_singles(self):
        rows = [next(r for r in self.primary["rows"] if r["case_id"] == f"{name}/p0/ph0/a1/S1_signal")
                for name in ("calibration_I","calibration_II")]
        self.assertLess(max(abs(x-y) for x,y in zip(rows[0]["signal"]["j"],rows[1]["signal"]["j"])),1e-12)
        self.assertGreater(max(abs(x-y) for side in ("sA","sB") for x,y in zip(rows[0]["signal"][side],rows[1]["signal"][side])),1e-8)

    def test_explicit_signal_override_has_distinct_M3_rates(self):
        signal,m3 = self.row(self.primary),self.row(self.primary,"named_M3")
        self.assertGreater(max(abs(x-y) for x,y in zip(signal["rates"]["j"],m3["rates"]["j"])),1e-12)
        self.assertLess(max(abs(x-y) for x,y in zip(signal["corrected_joint"],m3["corrected_joint"])),1e-12)

    def test_OR_scale_cannot_be_reset(self):
        self.row(self.main,"independent_OR")["reconstruction"]["scale"] = 1.
        self.rejected()

    def test_wrong_paired_update_body_rejected(self):
        self.row(self.main)["response"]["paired_gain_prediction"] += 1e-5
        self.rejected()

    def test_derivative_per_degree_cannot_replace_per_radian(self):
        self.row(self.main)["response"]["derivatives"][0] *= math.pi/180
        self.rejected()

    def test_json_one_is_not_success_control(self):
        self.main["controls"][next(iter(self.main["controls"]))] = 1
        self.rejected()

    def test_three_calibration_rows_and_certain_OR_are_not_identifiable(self):
        row = self.row(self.primary)
        angles = [math.radians(float(F(x))) for x in self.config["angles_deg"][1]]
        background = [float(F(self.config["rates"][k])) for k in ("background_A","background_B")]
        with self.assertRaisesRegex(ValueError,"NOT_IDENTIFIABLE"):
            self.main_program.inverse(row["rates"],[angles[0],angles[0],angles[2],angles[3]],"S1_signal",background)
        with self.assertRaisesRegex(ValueError,"NOT_IDENTIFIABLE"):
            self.main_program.inverse(row["rates"],angles,"independent_OR",[1.,background[1]])

    def test_percentage_rounding_has_correct_probability_unit(self):
        row = verify.printed_percentage("0.1234%")
        self.assertEqual(F(row["exact_center"]),F("0.001234"))
        self.assertEqual(F(row["rounding_half_width"]),F(1,2000000))
        self.assertEqual(F(row["exact_upper"])-F(row["exact_lower"]),F(1,1000000))
        self.assertIsNone(row["counts"])
        self.assertIsNone(row["denominator"])
        self.assertIsNone(row["statistical_verdict"])

    def test_printed_zero_is_not_an_exact_zero_count(self):
        row = verify.printed_percentage("0.0000%")
        self.assertEqual(F(row["exact_lower"]),-F(1,2000000))
        self.assertEqual(F(row["exact_upper"]),F(1,2000000))
        self.assertIsNone(row["counts"])

    def test_missing_receipts_are_not_green(self):
        result = verify.assess(self.directory)
        self.assertFalse(result["evidence_valid"])
        self.assertEqual(result["status"],"missing_observable_evidence",result)


if __name__ == "__main__":
    unittest.main(verbosity=2)
