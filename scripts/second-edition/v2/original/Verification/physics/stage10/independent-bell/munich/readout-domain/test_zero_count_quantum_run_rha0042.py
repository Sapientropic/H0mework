from contextlib import ExitStack
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch
import hashlib
import unittest

import zero_count_quantum_run_rha0042 as code


class QuantumProgramBindingControls(unittest.TestCase):
    def fixture(self, temporary):
        root = Path(temporary)
        here = root/'physics'
        here.mkdir()
        frozen = {'physics/runner.py': b'import extra\n', 'physics/extra.py': b'import deep\n',
                  'physics/deep.py': b'VALUE=1\n'}
        for path, value in frozen.items():
            (root/path).write_bytes(value)
        stack = ExitStack()
        stack.enter_context(patch.object(code, 'ROOT', root))
        stack.enter_context(patch.object(code, 'HERE', here))
        stack.enter_context(patch.object(code, 'OWN', ('runner.py',)))
        stack.enter_context(patch.object(code, 'INPUTS', ()))
        stack.enter_context(patch.object(code.provenance, 'OWN', ()))
        stack.enter_context(patch.object(code.provenance, '_blob', side_effect=lambda freeze, path: frozen[path]))
        stack.enter_context(patch.object(code.subprocess, 'check_output', return_value='\n'.join(frozen).encode()))
        return root, here, frozen, stack

    def test_original_bindings_and_new_transitive_science_are_both_retained(self):
        with TemporaryDirectory() as directory:
            _, _, frozen, stack = self.fixture(directory)
            with stack:
                old = {'paid-source': 'old-hash'}
                result = code.consumer_bindings('freeze', old)
                self.assertEqual(result, {**old, **{p: hashlib.sha256(b).hexdigest() for p, b in frozen.items()}})
                self.assertEqual(old, {'paid-source': 'old-hash'})

    def test_changed_transitive_science_fails(self):
        with TemporaryDirectory() as directory:
            root, _, _, stack = self.fixture(directory)
            with stack:
                (root/'physics/deep.py').write_bytes(b'VALUE=2\n')
                with self.assertRaisesRegex(ValueError, 'science changed'):
                    code.consumer_bindings('freeze', {})

    def test_unfrozen_local_import_lookalike_fails(self):
        with TemporaryDirectory() as directory:
            root, _, frozen, stack = self.fixture(directory)
            with stack:
                frozen['physics/deep.py'] = b'import unregistered\n'
                (root/'physics/deep.py').write_bytes(frozen['physics/deep.py'])
                (root/'physics/unregistered.py').write_bytes(b'VALUE=1\n')
                with self.assertRaisesRegex(ValueError, 'unfrozen local'):
                    code.consumer_bindings('freeze', {})

