"""Complete detector proof-closure and read-only certificate intake controls."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('detector_kernel_certificate', HERE / 'detector_certify.py')
cert = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cert)


def fixture_report():
    declarations = cert.source.explicit_declarations(cert.CANDIDATE)
    report = {key: True for key in cert.TRUE_FIELDS}
    report.update({key: False for key in cert.FALSE_FIELDS})
    report.update(schema=cert.SCHEMA, candidate_module=cert.MODULE,
                  focused_trust_level=0, lean_threads=1, trial_event_files_read=0,
                  new_statistical_tables_read=0, explicit_declarations=declarations,
                  owned_declarations=[{'name': row['name'], 'axioms': []} for row in declarations],
                  independent_consumers=[{'name': 'IndependentFiniteConsumer', 'axioms': []}],
                  axiom_union=[], source_bindings=[cert.source.binding(cert.CANDIDATE)],
                  toolchain_version=json.loads(cert.source.DEFAULT_REPORT.read_text())['toolchain_version'],
                  frozen_source_receipt={'sha256': cert.source.digest(cert.source.DEFAULT_REPORT.read_bytes())})
    return report


class DetectorReceiptControls(unittest.TestCase):
    def setUp(self):
        self.report = fixture_report()

    def reject(self, mutate, message):
        report = copy.deepcopy(self.report)
        mutate(report)
        with self.assertRaisesRegex(ValueError, message):
            cert.validate_payload(report)

    def test_valid_scope_accepts(self):
        cert.validate_payload(self.report)

    def test_unique_actual_hardware_promotion_rejects(self):
        self.reject(lambda r: r.update(actual_hardware_uniquely_identified=True), 'scope was promoted')

    def test_forward_kinetics_kernel_promotion_rejects(self):
        self.reject(lambda r: r.update(atomic_response_forward_model_kernel_proved=True), 'scope was promoted')

    def test_claimed_extra_confidence_coverage_rejects(self):
        self.reject(lambda r: r.update(new_statistical_interval_coverage_kernel_proved=True), 'scope was promoted')

    def test_click_dictionary_selection_rejects(self):
        self.reject(lambda r: r.update(both_click_polarities_retained=False), 'lost an obligation')

    def test_product_replaced_by_individual_bounds_rejects(self):
        self.reject(lambda r: r.update(joint_efficiency_atomic_response_lower_certified=False), 'lost an obligation')

    def test_missing_raw_cap_rejects(self):
        self.reject(lambda r: r.update(raw_control_gain_cap_certified=False), 'lost an obligation')

    def test_boolean_trust_level_rejects(self):
        self.reject(lambda r: r.update(focused_trust_level=False), 'invalid literal')

    def test_empty_consumer_rejects(self):
        self.reject(lambda r: r.update(independent_consumers=[]), 'declaration scope')

    def test_unauthorized_axiom_rejects(self):
        self.reject(lambda r: r.update(axiom_union=['ActualHardwareOracle']), 'unauthorized axioms')

    def test_receipt_override_and_source_hash_intake(self):
        with tempfile.TemporaryDirectory() as directory:
            canonical = Path(directory) / 'receipt.json'
            supplied = Path(directory) / 'relocated.json'
            canonical.write_text(json.dumps(self.report))
            supplied.write_bytes(canonical.read_bytes())
            with patch.object(cert, 'DEFAULT_REPORT', canonical):
                self.assertEqual(cert.consume(supplied, require_frozen=False), self.report)
                supplied.write_text('{}')
                with self.assertRaisesRegex(ValueError, 'override changes canonical'):
                    cert.consume(supplied, require_frozen=False)
                changed = copy.deepcopy(self.report)
                changed['source_bindings'][0]['sha256'] = '0' * 64
                canonical.write_text(json.dumps(changed))
                with self.assertRaisesRegex(ValueError, 'certified source changed'):
                    cert.consume(require_frozen=False)


class DetectorDependencyControls(unittest.TestCase):
    def inventory(self):
        declarations = cert.source.explicit_declarations(cert.CANDIDATE)
        delta = [{'name': row['name'], 'module': cert.MODULE,
                  'kind': {'structure': 'inductive', 'def': 'definition', 'theorem': 'theorem'}[row['kind']],
                  'dependencies': []} for row in declarations]
        delta.append({'name': 'IndependentFiniteConsumer', 'module': 'DetectorCertification',
                      'kind': 'theorem', 'dependencies': [cert.PUBLIC_MOUTH]})
        return {'candidate_modules': [cert.MODULE], 'owned_declarations': [row['name'] for row in declarations],
                'independent_consumers': ['IndependentFiniteConsumer'], 'dependency_delta': delta,
                'paid_boundary': [], 'imported_modules': [cert.MODULE], 'compiler_only_module_symbols': [],
                'public_mouths': [{'name': name, 'type': 'general detector source consequence'}
                                  for name in cert.REQUIRED_MOUTHS]}

    def test_source_only_complete_graph_accepts(self):
        report = cert.validate_inventory(self.inventory(), {}, {'owned_declarations': []})
        self.assertEqual(len(report['explicit_declarations']), len(cert.source.explicit_declarations(cert.CANDIDATE)))

    def test_empirical_import_rejects(self):
        value = self.inventory()
        value['imported_modules'].append('SaturationMonoid.PhysicsCore.Stage10.Empirical.ActualEffect')
        with self.assertRaisesRegex(ValueError, 'empirical or scratch'):
            cert.validate_inventory(value, {}, {'owned_declarations': []})

    def test_open_proof_edge_rejects(self):
        value = self.inventory()
        value['dependency_delta'][0]['dependencies'] = ['MissingRawPulseProof']
        with self.assertRaisesRegex(ValueError, 'open detector dependency'):
            cert.validate_inventory(value, {}, {'owned_declarations': []})

    def test_changed_paid_edge_rejects(self):
        value = self.inventory()
        paid = {'name': 'PaidSource', 'module': 'OriginalSource', 'kind': 'theorem', 'dependencies': []}
        value['paid_boundary'] = [dict(paid, kind='axiom')]
        with self.assertRaisesRegex(ValueError, 'paid base dependency identity'):
            cert.validate_inventory(value, {'PaidSource': paid}, {'owned_declarations': []})

    def test_foreign_source_boundary_rejects(self):
        value = self.inventory()
        value['paid_boundary'] = [{'name': 'PaidSource', 'module': 'ForeignRoot', 'kind': 'theorem', 'dependencies': []}]
        with self.assertRaisesRegex(ValueError, 'source boundary ownership'):
            cert.validate_inventory(value, {}, {'owned_declarations': [{'name': 'PaidSource', 'axioms': []}]})

    def test_missing_owned_declaration_rejects(self):
        value = self.inventory()
        value['owned_declarations'].pop()
        with self.assertRaisesRegex(ValueError, 'explicit declaration missed'):
            cert.validate_inventory(value, {}, {'owned_declarations': []})

    def test_duplicate_owned_declaration_rejects(self):
        value = self.inventory()
        value['owned_declarations'].append(value['owned_declarations'][0])
        with self.assertRaisesRegex(ValueError, 'duplicate detector audit'):
            cert.validate_inventory(value, {}, {'owned_declarations': []})


if __name__ == '__main__':
    unittest.main()
