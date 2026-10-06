"""Focused calibrated-source/complete-CI/source-identity controls."""
from copy import deepcopy
from fractions import Fraction as F
import gzip
import json
from pathlib import Path
import tempfile
import unittest

import review as m


def source_fixture():
    p = m.read_json(m.ENV/'calibration-primary.json')['points'][0]
    return deepcopy(next(b['source'] for b in p['branches'] if 'source' in b))


class CalibratedCountControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec, _ = m.configuration()
        cls.endpoints = m.load_endpoints()
        cls.source = source_fixture()

    def test_generated19_inventory_includes_two_explicit_overrides(self):
        points, branches = m.source_inventory(self.spec)
        self.assertEqual(len(points), 19); self.assertEqual(len(branches), 19)
        self.assertEqual(sum(p['included_in_default_source_box'] for p in points), 17)
        self.assertEqual({p['input']['allocation'] for p in points if not p['included_in_default_source_box']}, {'Alice_rank_one','Bob_rank_one'})

    def test_all72_CI_from_two_correct_exposures(self):
        m.validate_endpoints(self.endpoints)
        self.assertEqual(sum(len(e['CI'][f]) for e in self.endpoints for f in ('j','sA_cell','sB_cell')), 72)

    def test_missing_CI_is_not_lookalike_complete(self):
        endpoints = deepcopy(self.endpoints); endpoints[0]['CI']['j'].pop()
        with self.assertRaisesRegex(ValueError, '72_CI'):
            m.validate_endpoints(endpoints)

    def test_wrong_N_or_exposure_mapping_rejected(self):
        endpoints = deepcopy(self.endpoints); endpoints[0]['N'] = 5
        with self.assertRaisesRegex(ValueError, '72_CI'):
            m.validate_endpoints(endpoints)
        endpoints = deepcopy(self.endpoints); endpoints[-1]['exposure'] = 182137032
        with self.assertRaisesRegex(ValueError, 'exposure_mapping'):
            m.validate_endpoints(endpoints)

    def test_N9_cannot_gain_Bell_identity(self):
        endpoints = deepcopy(self.endpoints); endpoints[4]['spacelike_scope'] = True
        with self.assertRaisesRegex(ValueError, 'identity_inflated'):
            m.validate_endpoints(endpoints)

    def test_same_bytes_CI_override_and_lookalike(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d)/'copy.json.gz'; path.write_bytes(m.CANONICAL_CI.read_bytes())
            self.assertEqual(len(m.load_endpoints(path)), 6)
            raw = json.loads(gzip.decompress(path.read_bytes())); raw['publication_configuration_identified'] = True
            path.write_bytes(gzip.compress(json.dumps(raw).encode()))
            with self.assertRaisesRegex(ValueError, 'lookalike_or_changed'):
                m.load_endpoints(path)

    def test_foreign_EF_fields_cannot_be_ENV_inputs(self):
        source = deepcopy(self.source); source['lambda'] = '1/2'
        with self.assertRaisesRegex(ValueError, 'ENV_source_fields'):
            m.unpack_source(source, 'primary')

    def test_source_epoch_is_not_minted(self):
        source = deepcopy(self.source); source['source_epoch_identified'] = True
        with self.assertRaisesRegex(ValueError, 'ENV_source_fields'):
            m.unpack_source(source, 'independent')

    def test_root_midpoint_cannot_replace_generated_source(self):
        source = deepcopy(self.source); source['root_midpoints_used_as_source'] = True
        with self.assertRaisesRegex(ValueError, 'lookalike_calibrated_source'):
            m.unpack_source(source, 'primary')

    def test_environment_allocation_override_is_resolved_by_source(self):
        source = deepcopy(self.source); source['allocation'] = 'Alice_rank_one'
        p = m.unpack_source(source, 'independent')
        packet = m.independent.source_packet(p, 16)
        self.assertEqual((packet['xiA'].lo, packet['xiA'].hi), (1, 1))

    def test_same_source_forward_primary_determinant_and_actual_Gamma(self):
        endpoints = self.endpoints[:1]
        a, _ = m.primary_forward(self.source, self.spec, endpoints)
        b, actual, _ = m.independent_forward(self.source, self.spec, endpoints)
        result = m.compare_readouts([a,b,actual], endpoints)
        self.assertTrue(result['actual_strict_disjoint_certificates'] or result['all_72_CI_contained'] or result['verdict']=='CI_OVERLAP_UNRESOLVED')
        for row in range(4):
            self.assertLessEqual(max(x[0]['cells'][row]['j'].lo for x in [a,b,actual]), min(x[0]['cells'][row]['j'].hi for x in [a,b,actual]))

    def test_broad_CI_positive_control(self):
        endpoints = deepcopy(self.endpoints)
        for endpoint in endpoints:
            for field in ('j','sA_cell','sB_cell'):
                endpoint['CI'][field] = [{'exact_lower':'0','exact_upper':'1'}]*4
        a, _ = m.primary_forward(self.source, self.spec, endpoints)
        b, actual, _ = m.independent_forward(self.source, self.spec, endpoints)
        result = m.compare_readouts([a,b,actual], endpoints)
        self.assertEqual(result['verdict'], 'ALL_72_CI_CONTAINED')
        self.assertTrue(result['all_72_reads_and_96_outcomes_crossed'])

    def test_continuum_uses_a_single_domain_bound_not_finite_scan(self):
        proof = m.continuum_bound(self.spec, self.endpoints)
        self.assertTrue(proof['all_legal_environment_allocations_and_calibration_roots_covered'])
        self.assertFalse(proof['more_point_scans_performed'])
        self.assertGreater(proof['transmission_A_upper'], F(3,4))
        self.assertLess(proof['transmission_A_upper'], F(4,5))
        self.assertLess(proof['single_pulse_click_upper'], F(4,100000))


if __name__ == '__main__':
    unittest.main()
