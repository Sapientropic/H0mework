#!/usr/bin/env python3
"""Immutable statistics intake and final source-consumer payload controls."""
import copy
from fractions import Fraction as F
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import statistics_verify as statistics


def final_validator():
    path = statistics.HERE / 'verify.py'
    spec = importlib.util.spec_from_file_location('_sc_final_payload_validation', path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module.validate_statistics


class ImmutableStatisticsConsumer(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.canonical = statistics.HERE / 'statistics-cross-verification.json'
        cls.raw = cls.canonical.read_bytes()
        cls.report = statistics.consume()

    def reject_override(self, mutation):
        changed = copy.deepcopy(self.report)
        mutation(changed)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'changed-certificate.json'
            path.write_text(json.dumps(changed))
            with self.assertRaisesRegex(ValueError, 'lookalike_statistical_certificate'):
                statistics.consume(path)

    def test_actual_canonical_positive(self):
        report = statistics.consume()
        self.assertIs(report['evidence_valid'], True)
        self.assertTrue(all(report[name] is True for name in statistics.FLAGS))
        self.assertEqual(len(report['records']), 24)
        self.assertEqual(report['original_CI72'], statistics.original_CI72())
        b = report['budget']
        self.assertEqual(sum(F(b[k]) for k in ('old_CI_failure_upper', 'alpha_contrast', 'alpha_conditional')), F(1, 20))
        self.assertEqual(F(b['conditional_inverse_delta']) * F(b['alpha_conditional']), 24 * 4 * 6 * 40)
        for record in report['records']:
            self.assertEqual(record['total_trials'], sum(record['setting_trials']))
            for index, row in enumerate(record['conditional']):
                self.assertEqual(len(row), 6)
                for event in row:
                    self.assertIs(type(event['trials']), int)
                    self.assertEqual(event['trials'], record['setting_trials'][index])

    def test_same_byte_override(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'copy.json'
            path.write_bytes(self.raw)
            self.assertEqual(statistics.consume(path), self.report)

    def test_disabled_never_reads_input_or_provenance(self):
        def forbidden(*args, **kwargs):
            raise AssertionError('disabled consumer accessed a file or provenance')
        with patch.object(Path, 'read_bytes', side_effect=forbidden), \
             patch.object(Path, 'read_text', side_effect=forbidden), \
             patch.object(statistics.c, 'frozen', side_effect=forbidden), \
             patch.object(statistics.c, 'configuration', side_effect=forbidden), \
             patch.object(statistics, 'binding_check', side_effect=forbidden):
            report = statistics.consume('/does/not/exist/foreign.py', disabled=True)
        self.assertEqual(report['status'], 'disabled')
        self.assertIs(report['evidence_valid'], False)
        self.assertTrue(all(report[name] is False for name in statistics.FLAGS))

    def test_lookalike_bytes_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'same-content-different-bytes.json'
            path.write_bytes(self.raw + b'\n')
            with self.assertRaisesRegex(ValueError, 'lookalike_statistical_certificate'):
                statistics.consume(path)

    def test_foreign_script_never_executes(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / 'executed'
            path = Path(directory) / 'certificate.py'
            path.write_text('from pathlib import Path\nPath(' + repr(str(marker)) + ').write_text("executed")\n')
            with self.assertRaisesRegex(ValueError, 'lookalike_statistical_certificate'):
                statistics.consume(path)
            self.assertFalse(marker.exists())

    def test_missing_exposure_override_rejected(self):
        self.reject_override(lambda r: r['records'][0].pop('setting_trials'))

    def test_one_confidence_or_pulse_override_rejected(self):
        self.reject_override(lambda r: r['records'][0]['conditional'][0][0]['interval'].update(exact_lower='0'))
        self.reject_override(lambda r: r['records'][0]['identity'].update(pulse_count=9))

    def test_false_scope_override_rejected(self):
        self.reject_override(lambda r: r.update(controller_advance=True))

    def test_cross_accepts_different_certified_widths(self):
        narrow = {'exact_lower': '0', 'exact_upper': '1'}
        wide = {'exact_lower': str(-F(1, 10 ** 40)), 'exact_upper': str(1 + F(1, 10 ** 40))}
        hull = statistics.cross(narrow, wide)
        self.assertEqual(hull, wide)
        with self.assertRaisesRegex(ValueError, 'independent_interval_endpoints_changed'):
            statistics.cross(narrow, {'exact_lower': '0', 'exact_upper': str(1 + F(1, 10 ** 30))})
        with self.assertRaisesRegex(ValueError, 'independent_statistical_bounds_disjoint'):
            statistics.cross(narrow, {'exact_lower': '2', 'exact_upper': '3'})


class FinalStatisticsPayloadControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report = statistics.consume()
        cls.validate = staticmethod(final_validator())

    def rejected(self, mutation):
        changed = copy.deepcopy(self.report)
        mutation(changed)
        with self.assertRaises((ValueError, KeyError, TypeError, AssertionError)):
            self.validate(changed)

    def test_actual_payload_positive(self):
        self.validate(copy.deepcopy(self.report))

    def test_budget_cannot_exceed_joint_alpha(self):
        self.rejected(lambda r: r['budget'].update(alpha_contrast='1/20'))

    def test_full_family_unique_and_complete(self):
        self.rejected(lambda r: r['records'].__setitem__(1, copy.deepcopy(r['records'][0])))
        self.rejected(lambda r: r['records'].pop())
        self.rejected(lambda r: r['records'][0]['identity'].update(pulse_count=9))
        self.rejected(lambda r: r['records'][0]['identity'].update(pulse_indices=[4, 5, 6, 7, 8]))

    def test_count_total_and_setting_exposures_are_exact_integers(self):
        self.rejected(lambda r: r['records'][0].update(total_trials=float(r['records'][0]['total_trials'])))
        self.rejected(lambda r: r['records'][0]['setting_trials'].__setitem__(0, float(r['records'][0]['setting_trials'][0])))
        self.rejected(lambda r: r['records'][0]['conditional'][0][0].update(trials=float(r['records'][0]['setting_trials'][0])))
        self.rejected(lambda r: r['records'][0]['counts'][0].__setitem__(0, float(r['records'][0]['counts'][0][0])))
        self.rejected(lambda r: r['records'][0].update(total_trials=0))
        self.rejected(lambda r: r['records'][0]['setting_trials'].__setitem__(0, -1))
        self.rejected(lambda r: r['records'][0].pop('setting_trials'))

    def test_one_conditional_exposure_is_not_total_trial_exposure(self):
        self.rejected(lambda r: r['records'][0]['conditional'][0][0].update(trials=r['records'][0]['total_trials']))
        self.rejected(lambda r: r['records'][0]['conditional'][0].pop())

    def test_scope_flags_require_exact_booleans(self):
        self.rejected(lambda r: r.update(evidence_valid=1))
        self.rejected(lambda r: r.update(**{statistics.FLAGS[0]: 1}))
        self.rejected(lambda r: r.update(controller_advance=True))
        self.rejected(lambda r: r.update(controller_advance=0))
        self.rejected(lambda r: r.update(actual_hardware_identity_claimed=True))
        self.rejected(lambda r: r.update(source_tree_or_Fock_producers_executed=1))
        self.rejected(lambda r: r.update(source_tree_or_Fock_producers_executed=False))

    def test_old72_are_not_replaced_or_removed(self):
        self.rejected(lambda r: r['original_CI72'].pop())
        self.rejected(lambda r: r['original_CI72'][0]['interval'].update(exact_lower='0'))

    def test_probability_outer_is_intersected_with_physical_unit_domain(self):
        legal = copy.deepcopy(self.report)
        legal['records'][0]['conditional'][0][3]['interval']['exact_upper'] = str(1 + F(1, 10 ** 50))
        self.validate(legal)
        self.rejected(lambda r: r['records'][0]['conditional'][0][3]['interval'].update(
            exact_lower='2', exact_upper='3'))


if __name__ == '__main__':
    unittest.main()
