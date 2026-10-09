import copy
import hashlib
import unittest

import zero_count_primal_run_rha0041_1 as code


def fixture():
    current = {code.OPERATION_DOCUMENT: b'original operations',
               'physics/source.py': b'original physics', 'physics/criterion.md': b'original science'}
    expected = {p: hashlib.sha256(raw).hexdigest() for p, raw in current.items()}
    return expected, copy.deepcopy(expected), current


class FrozenPrimalConsumerControls(unittest.TestCase):
    def test_default_binds_old_document_and_explicit_strict_override(self):
        expected, issued, current = fixture()
        self.assertEqual(code.validate_bound_bytes(expected, issued, current), [])
        current[code.OPERATION_DOCUMENT] = b'new targeted cancellation instructions'
        changes = code.validate_bound_bytes(expected, issued, current)
        self.assertEqual(changes[0]['producer_frozen_sha256'], expected[code.OPERATION_DOCUMENT])
        self.assertFalse(changes[0]['executed_science'])
        with self.assertRaisesRegex(ValueError, 'science changed'):
            code.validate_bound_bytes(expected, issued, current, require_document_unchanged=True)

    def test_executable_and_scientific_lookalike_cannot_use_document_exception(self):
        for path in ('physics/source.py', 'physics/criterion.md'):
            expected, issued, current = fixture()
            current[path] += b'changed'
            with self.assertRaisesRegex(ValueError, 'science changed'):
                code.validate_bound_bytes(expected, issued, current)

    def test_complete_historical_document_and_science_binding_required(self):
        expected, issued, current = fixture()
        for path in expected:
            bad = copy.deepcopy(issued)
            bad.pop(path)
            with self.assertRaisesRegex(ValueError, 'complete original'):
                code.validate_bound_bytes(expected, bad, current)
        issued[code.OPERATION_DOCUMENT] = '0'*64
        with self.assertRaisesRegex(ValueError, 'complete original'):
            code.validate_bound_bytes(expected, issued, current)


if __name__ == '__main__':
    unittest.main()
