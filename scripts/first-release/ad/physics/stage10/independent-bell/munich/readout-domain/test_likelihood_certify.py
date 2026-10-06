"""Read-only finite-step certificate controls; no trial or statistical replay."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("likelihood_kernel_certificate", HERE / "likelihood_certify.py")
cert = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cert)


class LikelihoodReceiptControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report = json.loads(cert.DEFAULT_REPORT.read_text())

    def test_actual_receipt_and_frozen_source_intake(self):
        self.assertEqual(cert.consume(require_frozen=False), self.report)
        self.assertEqual(len(self.report["explicit_declarations"]), 44)

    def reject(self, mutate, message):
        value = copy.deepcopy(self.report)
        mutate(value)
        with self.assertRaisesRegex(ValueError, message):
            cert.validate_payload(value)

    def test_full_and_conditional_weight_swap_rejects(self):
        self.reject(lambda r: r["fixed_mixture_weights"].update(full="1/6", conditional="1/2"), "weight order changed")

    def test_nonpositive_source_scope_promotion_rejects(self):
        self.reject(lambda r: r.update(strict_all_cell_source_positivity_required=False), "lost an obligation")

    def test_trial_law_promotion_rejects(self):
        self.reject(lambda r: r.update(trial_conditional_law_identified=True), "scope was promoted")

    def test_ville_process_promotion_rejects(self):
        self.reject(lambda r: r.update(Ville_probability_process_proved=True), "scope was promoted")

    def test_boolean_trust_level_rejects(self):
        self.reject(lambda r: r.update(focused_trust_level=False), "invalid literal")

    def test_missing_source_transport_rejects(self):
        self.reject(lambda r: r.update(same_original_source_current_next_certified=False), "lost an obligation")

    def test_unauthorized_axiom_rejects(self):
        self.reject(lambda r: r.update(axiom_union=["ForeignTrialOracle"]), "unauthorized axioms")


class LikelihoodDependencyControls(unittest.TestCase):
    def inventory(self):
        declarations = cert.source.explicit_declarations(cert.CANDIDATE)
        delta = [{"name": x["name"], "module": cert.MODULE,
                  "kind": {"structure": "inductive", "def": "definition", "theorem": "theorem"}[x["kind"]],
                  "dependencies": []} for x in declarations]
        delta.append({"name": "IndependentFiniteConsumer", "module": "LikelihoodCertification", "kind": "theorem",
                      "dependencies": [cert.PUBLIC_MOUTH]})
        return {"candidate_modules": [cert.MODULE], "owned_declarations": [x["name"] for x in declarations],
                "independent_consumers": ["IndependentFiniteConsumer"], "dependency_delta": delta,
                "paid_boundary": [], "imported_modules": [cert.MODULE], "compiler_only_module_symbols": [],
                "public_mouths": [{"name": cert.PUBLIC_MOUTH, "type": "registered finite normalizer"}]}

    def test_finite_source_only_graph_accepts(self):
        report = cert.validate_inventory(self.inventory(), {}, {"owned_declarations": []})
        self.assertEqual(len(report["explicit_declarations"]), 44)

    def test_empirical_import_rejects(self):
        inventory = self.inventory()
        inventory["imported_modules"].append("SaturationMonoid.PhysicsCore.Stage10.Empirical.Contact")
        with self.assertRaisesRegex(ValueError, "empirical or scratch"):
            cert.validate_inventory(inventory, {}, {"owned_declarations": []})

    def test_open_proof_dependency_rejects(self):
        inventory = self.inventory()
        inventory["dependency_delta"][0]["dependencies"] = ["MissingSourceTotal"]
        with self.assertRaisesRegex(ValueError, "open likelihood dependency"):
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
