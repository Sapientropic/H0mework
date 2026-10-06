"""Bounded source witness and immutable intake controls; no tree or Fock generation."""
import copy
from fractions import Fraction as F
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import domain_verify as v


class DomainVerificationControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.d, _, _ = v.modules()
        cls.first = cls.d.load(v.HERE/'domain-first.json.xz')
        cls.canonical = (v.HERE/'domain-verification.json').read_bytes()
        cls.certificate = json.loads(cls.canonical)

    def test_default_source_certificate(self):
        result = v.consume()
        self.assertTrue(all(result[name] is True for name in v.POSITIVE))
        self.assertTrue(all(result[name] is False for name in v.NEGATIVE))
        self.assertGreater(F(result['uniform_CH_N5_lower_bound']), 0)

    def test_original_byte_copy_override(self):
        with tempfile.TemporaryDirectory(prefix='p23-sc-domain-copy-') as folder:
            path = Path(folder)/'copy.json'
            path.write_bytes(self.canonical)
            self.assertEqual(v.consume(path), v.consume())

    def test_disabled_never_reads_inputs(self):
        with patch.object(Path, 'read_bytes', side_effect=AssertionError('disabled read')):
            result = v.consume('/not/a/certificate', disabled=True)
        self.assertFalse(result['evidence_valid'])
        self.assertTrue(all(result[name] is False for name in v.POSITIVE))

    def test_lookalike_scope_certificate_rejected(self):
        with tempfile.TemporaryDirectory(prefix='p23-sc-domain-lookalike-') as folder:
            path = Path(folder)/'copy.json'
            fake = copy.deepcopy(self.certificate)
            fake['controller_advance'] = True
            path.write_text(json.dumps(fake))
            with self.assertRaises(ValueError): v.consume(path)

    def test_intake_never_calls_domain_solver_or_Fock(self):
        with (patch.object(self.d, 'refine', side_effect=AssertionError('refine')),
              patch.object(self.d, 'members', side_effect=AssertionError('members')),
              patch.object(self.d, 'generate', side_effect=AssertionError('generate')),
              patch.object(self.d.geometry, 'fock_readout', side_effect=AssertionError('Fock'))):
            self.assertTrue(v.consume()['evidence_valid'])

    def test_missing_old_source_root_rejected(self):
        fake = dict(self.first['cover'], roots=self.first['cover']['roots'][:-1])
        with self.assertRaises(ValueError): v.check_tree_structure(fake)

    def test_child_gap_and_scaled_integer_readout_rejected(self):
        for scaled in (False, True):
            cover = self.first['cover']
            parent = next(n for n in cover['nodes'] if n['status'] == 'split')
            child = copy.deepcopy(cover['nodes'][parent['children'][0]])
            axis = self.d.geometry.AXES.index(parent['split_axis'])
            packet = child['input_box'][axis]
            packet['exact_upper'] = str(F(packet['exact_upper'])*self.d.SCALE if scaled else F(packet['exact_upper'])-F(1, self.d.SCALE))
            fake_nodes = list(cover['nodes']); fake_nodes[child['id']] = child
            with self.assertRaises(ValueError): v.check_tree_structure(dict(cover, nodes=fake_nodes))

    def test_complete_phase_partition_cannot_drop_a_component(self):
        node = next(n for n in self.first['cover']['nodes'] if len(n.get('phase_partitions', [])) == 8)
        with self.assertRaises(ValueError):
            v.check_phase_partition(node['phase_partitions'][:-1], v.interval(node['common_k']))

    def test_false_cap_or_exclusion_summary_rejected(self):
        for name, value in (('retained_source_leaves', 313), ('excluded_source_nodes', 210)):
            fake = copy.deepcopy(self.certificate)
            fake['source_summary'][name] = value
            with self.assertRaises(ValueError): v.certificate_check(fake)

    def test_wrong_window_and_relevant_only_exposure_rejected(self):
        for wrong_window in (True, False):
            records = copy.deepcopy(self.first['records'])
            if wrong_window:
                records[2]['identity']['pulse_count'] = 9
            else:
                records[2]['total_trials'] = 6541+5898
            with self.assertRaises(ValueError): v.check_record_identities(records, self.first['records'])

    def test_phase_after_window_or_foreign_native_source_rejected(self):
        candidate = self.first['members'][0]
        sealed = {'source': candidate['source'], 'recipe': candidate['recipe'], 'windows': candidate['native_windows']}
        fake = copy.deepcopy(candidate)
        fake['native_windows']['5'][0]['j']['exact_upper'] = '1'
        with self.assertRaises(ValueError): v.check_member_identity(fake, sealed, candidate['reuse_identity'])

    def test_foreign_source_binding_rejected(self):
        with self.assertRaises(ValueError):
            v.binding_check({'path': '/tmp/foreign.json', 'commit': 'fixed', 'sha256': 'fixed'})

    def test_true_flag_and_uniform_bound_lookalikes_rejected(self):
        for name in ('controller_advance', 'new_full_Born_kernel_claim', 'original_CI_modified'):
            fake = copy.deepcopy(self.certificate); fake[name] = True
            with self.assertRaises(ValueError): v.certificate_check(fake)
        fake = copy.deepcopy(self.certificate); fake['uniform_CH_N5_lower_bound'] = '1'
        with self.assertRaises(ValueError): v.certificate_check(fake)


if __name__ == '__main__':
    unittest.main()
