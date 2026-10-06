"""Read-only complete-law and regular-fiber certificate controls; no empirical replay."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("response_kernel_certificate", HERE / "response_bounds_certify.py")
cert = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cert)


class FiberReceiptControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report = json.loads(cert.DEFAULT_REPORT.read_text())

    def test_actual_receipt_and_frozen_source_intake(self):
        self.assertEqual(cert.consume(require_frozen=False), self.report)
        self.assertEqual(len(self.report["explicit_declarations"]), 22)

    def reject(self, mutate, message):
        value = copy.deepcopy(self.report)
        mutate(value)
        with self.assertRaisesRegex(ValueError, message):
            cert.validate_payload(value)

    def test_statistical_coverage_promotion_rejects(self):
        self.reject(lambda r: r.update(statistical_interval_coverage_proved_by_kernel=True), "scope was promoted")

    def test_missing_computed_gain_response_rejects(self):
        self.reject(lambda r: r.update(primitive_intervals_generate_gain_lower_bound_certified=False), "lost an obligation")

    def test_native_ideal_label_selection_rejects(self):
        self.reject(lambda r: r.update(actual_native_signed_gain_label_identity_selected=True), "scope was promoted")

    def test_missing_gain_to_error_consumer_rejects(self):
        self.reject(lambda r: r.update(computed_gain_lower_bound_consumed_by_canonical_error_consumer=False), "lost an obligation")

    def test_boolean_trust_level_rejects(self):
        self.reject(lambda r: r.update(focused_trust_level=False), "invalid literal")

    def test_missing_source_transport_rejects(self):
        self.reject(lambda r: r.update(same_original_source_current_next_certified=False), "lost an obligation")

    def test_unauthorized_axiom_rejects(self):
        self.reject(lambda r: r.update(axiom_union=["ForeignTrialOracle"]), "unauthorized axioms")


class FiberDependencyControls(unittest.TestCase):
    def inventory(self):
        declarations = cert.source.explicit_declarations(cert.CANDIDATE)
        delta = [{"name": x["name"], "module": cert.MODULE,
                  "kind": {"structure": "inductive", "def": "definition", "theorem": "theorem"}[x["kind"]],
                  "dependencies": []} for x in declarations]
        delta.append({"name": "IndependentFiniteConsumer", "module": "FiberCertification", "kind": "theorem",
                      "dependencies": [cert.PUBLIC_MOUTH]})
        return {"candidate_modules": [cert.MODULE], "owned_declarations": [x["name"] for x in declarations],
                "independent_consumers": ["IndependentFiniteConsumer"], "dependency_delta": delta,
                "paid_boundary": [], "imported_modules": [cert.MODULE], "compiler_only_module_symbols": [],
                "public_mouths": [{"name": cert.PUBLIC_MOUTH, "type": "generic all-feasible-point dual"},
                  {"name": "SaturationMonoid.PhysicsCore.Stage10.Bell.ResponseBoundsCertification.generalIntervalsGenerateCanonicalErrors",
                   "type": "same source scaled effect gain objective"}]}


    def test_finite_source_only_graph_accepts(self):
        report = cert.validate_inventory(self.inventory(), {}, {"owned_declarations": []})
        self.assertEqual(len(report["explicit_declarations"]), 22)

    def test_empirical_import_rejects(self):
        inventory = self.inventory()
        inventory["imported_modules"].append("SaturationMonoid.PhysicsCore.Stage10.Empirical.Contact")
        with self.assertRaisesRegex(ValueError, "empirical or scratch"):
            cert.validate_inventory(inventory, {}, {"owned_declarations": []})

    def test_open_proof_dependency_rejects(self):
        inventory = self.inventory()
        inventory["dependency_delta"][0]["dependencies"] = ["MissingSourceTotal"]
        with self.assertRaisesRegex(ValueError, "open fiber dependency"):
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
