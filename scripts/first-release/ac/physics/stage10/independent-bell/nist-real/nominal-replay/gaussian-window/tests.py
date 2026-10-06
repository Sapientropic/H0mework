#!/usr/bin/env python3
"""Focused geometric-source, coherent-sector, window and intake controls."""
import copy
from fractions import Fraction as F
import json
from pathlib import Path
import sys
import tempfile
import unittest

import verify


def receipt(lower, upper=None):
    lower = F(lower); upper = lower if upper is None else F(upper)
    return {"exact_lower":str(lower),"exact_upper":str(upper),"lower":float(lower),"upper":float(upper)}


class GaussianWindowControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        verify.program_freeze(Path(__file__))
        cls.spec,_,cls.seed,cls.confidence = verify.scientific_inputs()
        cls.primary = json.loads((verify.HERE/verify.PRIMARY).read_text())
        cls.independent = json.loads((verify.HERE/verify.INDEPENDENT).read_text())
        cls.actual = verify.assess()
        if cls.actual["status"] != "verified":
            raise AssertionError(cls.actual)

    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="p23-window-controls-")
        self.addCleanup(directory.cleanup)
        self.directory = Path(directory.name)
        self.main,self.own = copy.deepcopy(self.primary),copy.deepcopy(self.independent)

    def write(self):
        path = self.directory/verify.PRIMARY
        path.write_text(json.dumps(self.main)+"\n")
        if "comparison" in self.own:
            self.own["bindings"][verify.relative(verify.HERE/verify.PRIMARY)] = verify.digest(path)
            self.own["comparison"]["primary_report_sha256"] = verify.digest(path)
        (self.directory/verify.INDEPENDENT).write_text(json.dumps(self.own)+"\n")

    def rejected(self):
        self.write()
        result = verify.assess(self.directory)
        self.assertEqual(result["status"],"invalid_gaussian_window_evidence",result)
        self.assertFalse(result["evidence_valid"])
        self.assertTrue(all(result[k] is False for k in verify.IDENTITY))

    def test_positive_explicit_directory_ignores_untrusted_program(self):
        self.write()
        (self.directory/"gaussian.py").write_text('raise RuntimeError("untrusted program")\n')
        result = verify.assess(self.directory)
        self.assertEqual(result["status"],"verified",result)
        self.assertEqual(result["control_cells"],720)
        self.assertTrue(result["source_Born_matrices_recomputed"])
        self.assertTrue(result["unnormalized_sector_prefix_and_exact_tail_recomputed"])

    def test_explicit_disable_override(self):
        result = verify.assess(self.directory,enabled=False)
        self.assertEqual(result["status"],"disabled_by_override")
        self.assertFalse(result["evidence_valid"])

    def test_false_identity_is_not_json_zero(self):
        self.main["source_mapping_identified"] = 0
        self.rejected()

    def test_fake_actual_window_identity_rejected(self):
        self.own["actual_window_model_identified"] = True
        self.rejected()

    def test_fake_production_identity_rejected(self):
        self.main["production_admitted"] = True
        self.rejected()

    def test_stale_frozen_criterion_binding_rejected(self):
        self.main["criterion_sha256"] = "0"*64
        self.rejected()

    def test_unbound_interval_program_rejected(self):
        self.main["interval_source_sha256"] = "0"*64
        self.rejected()

    def test_loss_and_geometric_domain_are_checked(self):
        packet = verify.seed_packet(self.seed,self.spec["window_pulses"])
        packet["transmission_A"][0] = "1001/1000"
        with self.assertRaisesRegex(ValueError,"invalid_passive_loss"):
            verify.parameters(packet)
        packet = verify.seed_packet(self.seed,self.spec["window_pulses"])
        packet["geometric_ratio"][0] = "1"
        with self.assertRaisesRegex(ValueError,"invalid_geometric_ratio"):
            verify.parameters(packet)

    def test_source_phase_cannot_be_optimized_after_freeze(self):
        self.main["source_parameters"]["phase_cos"]["numerator"] = "0"
        self.rejected()

    def test_tail_omission_is_rejected(self):
        self.own["prefix"][0]["tail"] = "0"
        self.rejected()

    def test_finite_prefix_cannot_be_renormalized(self):
        prefix = self.own["candidate"]["pulse_noclick"][0]
        mass = F(prefix["mass"])
        for key,row in prefix["partial"].items():
            lo,hi = verify.interval(row)
            prefix["partial"][key] = receipt(lo/mass,hi/mass)
        self.rejected()

    def test_physical_sector_cutoff_cannot_replace_tail(self):
        self.own["arithmetic"]["source_pair_cutoff"] = 1
        self.rejected()

    def test_pulse_coincidences_cannot_be_summed_as_window(self):
        pulse = self.main["public_cells"][0]["pulse"]
        a,b,j = [verify.interval(pulse[key]) for key in ("no_click_A","no_click_B","no_click_AB")]
        lo,hi = verify.add(verify.add(verify.add((F(1),F(1)),verify.neg(a)),verify.neg(b)),j)
        self.main["public_cells"][0]["signal"]["j"] = receipt(5*lo,5*hi)
        self.rejected()

    def test_additive_background_cannot_replace_OR(self):
        lo,hi = verify.interval(self.main["public_cells"][0]["signal"]["sA"])
        background = 5*F(self.spec["background_per_pulse"][0])
        self.main["public_cells"][0]["observed"]["sA"] = receipt(lo+background,hi+background)
        self.rejected()

    def test_changed_public_interval_cannot_keep_green_verdict(self):
        upper = F(self.confidence["j"][2]["exact_upper"])
        self.main["public_probabilities"]["j"][2] = receipt(upper+F(1,10**6))
        self.rejected()

    def test_control_one_is_not_a_proof_boolean(self):
        name = next(iter(self.own["controls"]["checks"]))
        self.own["controls"]["checks"][name] = 1
        self.rejected()

    def test_missing_control_cannot_hide_model_branch(self):
        self.main["controls"].pop()
        self.rejected()

    def test_geometric_tail_has_original_probability_mass(self):
        t = F(1,10000)
        mass,budget = verify.tail((t,F(0)),6)
        self.assertEqual(budget,t**7)
        self.assertEqual(mass+budget,F(1))
        self.assertLess(mass,F(1))
        self.assertEqual(verify.tail((F(0),F(0)),6),(F(1),F(0)))

    def test_full_complex_phase_changes_same_sector_Born(self):
        packet = {"geometric_ratio":["1/10000","1/20000"],"transmission_A":["1","1"],
                  "transmission_B":["1","1"],"phase_cos":{"numerator":"1","sqrt_denominator":"1"}}
        coherent = verify.fock_prefix(packet,"21/5","-21/5",6)
        packet["phase_cos"]["numerator"] = "0"
        right_angle = verify.fock_prefix(packet,"21/5","-21/5",6)
        self.assertGreater(abs(coherent["P00"]-right_angle["P00"]),1e-9)
        self.assertLess(abs(coherent["P0A"]-right_angle["P0A"]),1e-12)

    def test_actual_H_V_reference_endpoints(self):
        for ratios,detecting,dark in ((["1/10000","0"],"90","0"),(["0","1/10000"],"0","90")):
            packet = {"geometric_ratio":ratios,"transmission_A":["1","1"],"transmission_B":["1","1"],
                      "phase_cos":{"numerator":"1","sqrt_denominator":"1"}}
            signal = verify.fock_prefix(packet,detecting,detecting,6)
            untouched = verify.fock_prefix(packet,dark,dark,6)
            self.assertAlmostEqual(signal["P0A"],1-1/10000,places=12)
            self.assertAlmostEqual(untouched["P0A"],1,places=12)

    def test_missing_receipts_are_not_green(self):
        result = verify.assess(self.directory)
        self.assertEqual(result["status"],"missing_gaussian_window_evidence",result)
        self.assertFalse(result["evidence_valid"])

    def test_readiness_positive_disable_and_lookalike(self):
        self.write()
        (self.directory/"verification.json").write_text('{"status":"verified"}\n')
        sys.path.insert(0,str(verify.HERE.parent.parent))
        readiness = verify.implementation(verify.HERE.parent.parent/"readiness.py")
        result = readiness.gaussian_window_investigation(report_dir=self.directory)
        self.assertEqual(result["status"],"verified_research_full_fock_window_member",result)
        self.assertTrue(result["evidence_valid"])
        result = readiness.gaussian_window_investigation(report_dir=self.directory,enabled=False)
        self.assertEqual(result["status"],"disabled_by_override")
        self.own["actual_window_model_identified"] = True
        self.write()
        result = readiness.gaussian_window_investigation(report_dir=self.directory)
        self.assertEqual(result["status"],"invalid_gaussian_window_evidence",result)
        self.assertFalse(result["evidence_valid"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
