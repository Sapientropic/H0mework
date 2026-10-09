import copy
import unittest

import source_reissue_rha0025 as code
from test_reference_atomic_clock_source import source_fixture


class SourceReissueControls(unittest.TestCase):
    def test_original_raw_primitive_reissues_identical_mathematical_source(self):
        source, _ = source_fixture(); old = source.record()
        fresh = code.fresh_reference_source(old)
        self.assertEqual(fresh.record(), old)
        self.assertIsNot(fresh, source)

    def test_old_executable_binding_override_does_not_change_new_source(self):
        source, _ = source_fixture(); old = copy.deepcopy(source.record())
        old['source_bindings'] = {'old-programme.py': '0'*64}
        old['normalized_native_assembler']['source_bindings'] = {'old-frame.py': '0'*64}
        fresh = code.fresh_reference_source(old)
        self.assertEqual(fresh.record(), source.record())
        self.assertNotEqual(fresh.record()['source_bindings'], old['source_bindings'])

    def test_same_shape_saved_endpoint_cannot_replace_source_primitive(self):
        source, _ = source_fixture(); old = copy.deepcopy(source.record())
        old['source_primitive_input'] = []
        with self.assertRaisesRegex(ValueError, 'primitive, action'):
            code.fresh_reference_source(old)

    def test_old_incoming_matrix_must_match_its_original_basis_recipe(self):
        source, _ = source_fixture(); old = copy.deepcopy(source.record())
        old['normalized_native_assembler']['original_PRM_source']['incoming_state']['quantum_centre'] = []
        with self.assertRaises(ValueError): code.fresh_reference_source(old)


if __name__ == '__main__':
    unittest.main()
