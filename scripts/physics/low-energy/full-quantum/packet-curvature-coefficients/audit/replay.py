#!/usr/bin/env python3
"""One isolated replay, retaining compact evidence rather than a duplicate table."""
from contextlib import redirect_stdout, redirect_stderr
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
CANDIDATE = HERE.parent
ROOT = CANDIDATE.parents[4]


def stable(value):
    if isinstance(value, dict):
        return {key: stable(item) for key, item in value.items() if key not in {'elapsed_seconds', 'input_sha256'}}
    if isinstance(value, list):
        return [stable(item) for item in value]
    return value


def main():
    frozen = json.loads((CANDIDATE/'construction.json').read_text())
    def verify():
        for name, digest in frozen['candidate_sha256'].items():
            assert hashlib.sha256((CANDIDATE/name).read_bytes()).hexdigest() == digest, name
    verify()
    output = HERE/'replay'
    output.mkdir(exist_ok=True)
    checks = []
    for name, result in [('compute', 'receipt.json'), ('controls', 'controls.json')]:
        spec = importlib.util.spec_from_file_location('audit_curvature_'+name, CANDIDATE/(name+'.py'))
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        module.HERE = output
        started = time.monotonic()
        with (output/(name+'.log')).open('w') as stream, redirect_stdout(stream), redirect_stderr(stream):
            module.main()
        generated = json.loads((output/result).read_text())
        assert stable(generated) == stable(json.loads((CANDIDATE/result).read_text())), result
        for key in ['source_sha256', 'source_inputs_sha256', 'input_sha256']:
            for path, digest in generated.get(key, {}).items():
                assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
        canonical = json.dumps(stable(generated), sort_keys=True, separators=(',', ':')).encode()
        checks.append({'program': name+'.py', 'exact_math_equal': True,
            'canonical_math_sha256': hashlib.sha256(canonical).hexdigest(),
            'seconds': round(time.monotonic()-started, 3)})
        print('PASS isolated', name, flush=True)
    verify()
    # The full table remains in the frozen source capsule. This duplicate is not
    # needed after exact comparison, provenance validation, and its digest.
    (output/'receipt.json').unlink()
    (HERE/'replay.json').write_text(json.dumps({'verdict': 'PASS', 'candidate_unchanged': True,
        'checks': checks, 'duplicate_table_removed_after_exact_comparison': True}, indent=2)+'\n')


if __name__ == '__main__':
    main()
