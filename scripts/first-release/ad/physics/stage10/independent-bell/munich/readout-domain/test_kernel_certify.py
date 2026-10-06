"""Controls for evidence intake and source-only dependency certification."""

import copy
import importlib.util
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("readout_source_kernel", HERE / "kernel_certify.py")
cert = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cert)


class DependencyControls(unittest.TestCase):
    def inventory(self):
        declarations = [(module, item) for module in cert.CANDIDATE_MODULES
                        for item in cert.explicit_declarations(cert.candidate_path(module))]
        delta = [{"name": item["name"], "module": module,
                  "kind": {"structure": "inductive", "def": "definition", "theorem": "theorem"}[item["kind"]],
                  "dependencies": []} for module, item in declarations]
        consumer = "IndependentSourceConsumer"
        delta.append({"name": consumer, "module": "Certification", "kind": "theorem",
                      "dependencies": [cert.PUBLIC_MOUTH]})
        effect_mouth = "SaturationMonoid.PhysicsCore.Stage10.Bell.sameOccurrenceReadoutEffectPrediction"
        return {"candidate_modules": list(cert.CANDIDATE_MODULES), "closed_public_mouth": True,
                "closed_effect_mouth": True, "imported_modules": list(cert.CANDIDATE_MODULES),
                "owned_declarations": [item["name"] for _, item in declarations],
                "independent_consumers": [consumer], "dependency_delta": delta,
                "paid_boundary": [], "compiler_only_module_symbols": [],
                "public_mouths": [{"name": cert.PUBLIC_MOUTH,
                  "type": "SaturationMonoid.PhysicsCore.Stage10.Bell.SameOccurrenceReadoutPrediction"},
                  {"name": effect_mouth,
                   "type": "SaturationMonoid.PhysicsCore.Stage10.Bell.SameOccurrenceReadoutEffectPrediction"}]}

    def test_source_only_inventory_accepts(self):
        result = cert.validate_inventory(self.inventory(), {})
        self.assertEqual(len(result["explicit_declarations"]), 115)
        self.assertEqual(result["axiom_union"], [])

    def test_unauthorized_axiom_rejects(self):
        inventory = self.inventory()
        inventory["dependency_delta"][0]["dependencies"] = ["EmpiricalGoal"]
        inventory["dependency_delta"].append({"name": "EmpiricalGoal", "module": "ForeignModel",
                                             "kind": "axiom", "dependencies": []})
        with self.assertRaisesRegex(ValueError, "unauthorized axiom"):
            cert.validate_inventory(inventory, {})

    def test_unused_empirical_import_rejects(self):
        inventory = self.inventory()
        inventory["imported_modules"].append("SaturationMonoid.PhysicsCore.Stage10.Empirical.Contact")
        with self.assertRaisesRegex(ValueError, "empirical or scratch import"):
            cert.validate_inventory(inventory, {})

    def test_target_constant_empirical_dependency_rejects(self):
        inventory = self.inventory()
        inventory["dependency_delta"][0]["dependencies"] = ["ReleasedCounts"]
        inventory["dependency_delta"].append({"name": "ReleasedCounts", "module": "Verification.Data",
                                             "kind": "definition", "dependencies": []})
        with self.assertRaisesRegex(ValueError, "empirical declaration dependency"):
            cert.validate_inventory(inventory, {})

    def test_open_dependency_edge_rejects(self):
        inventory = self.inventory()
        inventory["dependency_delta"][0]["dependencies"] = ["MissingPrimitive"]
        with self.assertRaisesRegex(ValueError, "open edge"):
            cert.validate_inventory(inventory, {})

    def test_changed_paid_boundary_rejects(self):
        inventory = self.inventory()
        base = {"PaidSource": {"name": "PaidSource", "module": "OriginalSource", "kind": "definition",
                               "dependencies": []}}
        inventory["paid_boundary"] = [dict(base["PaidSource"], kind="axiom")]
        with self.assertRaisesRegex(ValueError, "base dependency identity changed"):
            cert.validate_inventory(inventory, base)

    def test_native_kernel_escape_rejects(self):
        inventory = self.inventory()
        inventory["dependency_delta"].append({"name": "Lean.ofReduceBool", "module": "Lean",
                                             "kind": "theorem", "dependencies": []})
        with self.assertRaisesRegex(ValueError, "trust escape"):
            cert.validate_inventory(inventory, {})

    def test_unsafe_primitive_rejects(self):
        inventory = self.inventory()
        inventory["dependency_delta"][1]["kind"] = "unsafe-definition"
        with self.assertRaisesRegex(ValueError, "unsafe owned"):
            cert.validate_inventory(inventory, {})

    def test_conditional_public_mouth_rejects(self):
        inventory = self.inventory()
        inventory["closed_public_mouth"] = False
        with self.assertRaisesRegex(ValueError, "closed Prop"):
            cert.validate_inventory(inventory, {})


class ReceiptControls(unittest.TestCase):
    def setUp(self):
        if not cert.DEFAULT_REPORT.is_file():
            self.skipTest("first source certificate has not been generated")
        import json
        self.report = json.loads(cert.DEFAULT_REPORT.read_text())

    def test_actual_source_receipt(self):
        cert.validate_payload(self.report)
        self.assertEqual(cert.consume(require_frozen=False), self.report)

    def test_boolean_cannot_replace_literal_trust_level(self):
        report = copy.deepcopy(self.report)
        report["focused_trust_level"] = False
        with self.assertRaisesRegex(ValueError, "literal"):
            cert.validate_payload(report)

    def test_empirical_verdict_promotion_rejects(self):
        report = copy.deepcopy(self.report)
        report["real_instrument_verdict_executed"] = True
        with self.assertRaisesRegex(ValueError, "scope was promoted"):
            cert.validate_payload(report)

    def test_omitted_image_coverage_rejects(self):
        report = copy.deepcopy(self.report)
        report["all_original_channels_and_axes_image_covered"] = False
        with self.assertRaisesRegex(ValueError, "lost an obligation"):
            cert.validate_payload(report)


if __name__ == "__main__":
    unittest.main()
