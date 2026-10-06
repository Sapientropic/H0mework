"""Read-only complete-law and regular-fiber certificate controls; no empirical replay."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("identification_kernel_certificate", HERE / "identification_certify.py")
cert = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cert)


class IdentificationReceiptControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report = json.loads(cert.DEFAULT_REPORT.read_text())

    def test_actual_receipt_and_frozen_source_intake(self):
        self.assertEqual(cert.consume(require_frozen=False), self.report)
        self.assertEqual(len(self.report["explicit_declarations"]), 46)

    def reject(self, mutate, message):
        value = copy.deepcopy(self.report)
        mutate(value)
        with self.assertRaisesRegex(ValueError, message):
            cert.validate_payload(value)

    def test_arbitrary_target_table_promotion_rejects(self):
        self.reject(lambda r: r.update(arbitrary_target_probability_table_used=True), "scope was promoted")

    def test_singular_source_scope_promotion_rejects(self):
        self.reject(lambda r: r.update(regular_anchor_required_for_complete_scale_fiber=False), "lost an obligation")

    def test_actual_q_identification_promotion_rejects(self):
        self.reject(lambda r: r.update(actual_empirical_probability_identified=True), "scope was promoted")

    def test_unique_hardware_promotion_rejects(self):
        self.reject(lambda r: r.update(actual_hardware_uniquely_identified=True), "scope was promoted")

    def test_boolean_trust_level_rejects(self):
        self.reject(lambda r: r.update(focused_trust_level=False), "invalid literal")

    def test_missing_source_transport_rejects(self):
        self.reject(lambda r: r.update(same_original_source_current_next_certified=False), "lost an obligation")

    def test_unauthorized_axiom_rejects(self):
        self.reject(lambda r: r.update(axiom_union=["ForeignTrialOracle"]), "unauthorized axioms")


class IdentificationDependencyControls(unittest.TestCase):
    def inventory(self):
        declarations = cert.source.explicit_declarations(cert.CANDIDATE)
        delta = [{"name": x["name"], "module": cert.MODULE,
                  "kind": {"structure": "inductive", "def": "definition", "theorem": "theorem"}[x["kind"]],
                  "dependencies": []} for x in declarations]
        delta.append({"name": "IndependentFiniteConsumer", "module": "IdentificationCertification", "kind": "theorem",
                      "dependencies": [cert.PUBLIC_MOUTH]})
        return {"candidate_modules": [cert.MODULE], "owned_declarations": [x["name"] for x in declarations],
                "independent_consumers": ["IndependentFiniteConsumer"], "dependency_delta": delta,
                "paid_boundary": [], "imported_modules": [cert.MODULE], "compiler_only_module_symbols": [],
                "closed_public_mouth": True,
                "public_mouths": [{"name": cert.PUBLIC_MOUTH,
                  "type": "SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutIdentification.SameOccurrenceIdentification"}]}

    def test_finite_source_only_graph_accepts(self):
        report = cert.validate_inventory(self.inventory(), {}, {"owned_declarations": []})
        self.assertEqual(len(report["explicit_declarations"]), 46)

    def test_empirical_import_rejects(self):
        inventory = self.inventory()
        inventory["imported_modules"].append("SaturationMonoid.PhysicsCore.Stage10.Empirical.Contact")
        with self.assertRaisesRegex(ValueError, "empirical or scratch"):
            cert.validate_inventory(inventory, {}, {"owned_declarations": []})

    def test_open_proof_dependency_rejects(self):
        inventory = self.inventory()
        inventory["dependency_delta"][0]["dependencies"] = ["MissingSourceTotal"]
        with self.assertRaisesRegex(ValueError, "open identification dependency"):
            cert.validate_inventory(inventory, {}, {"owned_declarations": []})

    def test_changed_paid_primitive_rejects(self):
        inventory = self.inventory()
        original = {"name": "PaidSourcePrimitive", "module": "OriginalSource", "kind": "theorem", "dependencies": []}
        inventory["paid_boundary"] = [dict(original, kind="axiom")]
        with self.assertRaisesRegex(ValueError, "paid base dependency identity"):
            cert.validate_inventory(inventory, {original["name"]: original}, {"owned_declarations": []})

    def test_source_boundary_owner_replacement_rejects(self):
        inventory = self.inventory()
        inventory["paid_boundary"] = [{"name": "PaidSourcePrimitive", "module": "ForeignRoot", "kind": "theorem", "dependencies": []}]
        with self.assertRaisesRegex(ValueError, "source boundary ownership"):
            cert.validate_inventory(inventory, {}, {"owned_declarations": [{"name": "PaidSourcePrimitive", "axioms": []}]})


if __name__ == "__main__":
    unittest.main()
