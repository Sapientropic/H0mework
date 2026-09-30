#!/usr/bin/env python3
"""Single isolated replay of the frozen thirteen source programs."""
import argparse
import gzip
import hashlib
import importlib.util
import inspect
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time
from types import ModuleType

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
CANDIDATE = HERE.parent
ROOT = CANDIDATE.parents[4]
OUT = HERE/'replayed'


def read(path):
    raw = path.read_bytes()
    return json.loads(gzip.decompress(raw) if path.suffix == '.gz' else raw)


def clean(value):
    if isinstance(value, dict):
        return {k: clean(v) for k, v in value.items()
                if k not in ['seconds', 'elapsed_seconds', 'input_sha256']}
    if isinstance(value, list):
        return list(map(clean, value))
    return value


def hashes():
    manifest = read(CANDIDATE/'construction.json')
    for name, digest in manifest['candidate_sha256'].items():
        assert hashlib.sha256((CANDIDATE/name).read_bytes()).hexdigest() == digest, name
    for key in ['source_inputs', 'source_sha256']:
        for name, digest in manifest[key].items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    packing = read(CANDIDATE/'radial-compression.json')
    decoded = gzip.decompress((CANDIDATE/packing['file']).read_bytes())
    assert hashlib.sha256(decoded).hexdigest() == packing['decoded_sha256']
    assert len(decoded) == packing['decoded_bytes']
    return manifest


def child(filename):
    sys.path.insert(0, str(CANDIDATE))
    spec = importlib.util.spec_from_file_location('certified_replay_'+filename.replace('-', '_'), CANDIDATE/filename)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    seen = set()
    def redirect(m):
        if id(m) in seen:
            return
        seen.add(id(m))
        path = getattr(m, '__file__', None)
        if not path or Path(path).resolve().parent != CANDIDATE:
            return
        if hasattr(m, 'HERE'):
            m.HERE = OUT
        for value in list(vars(m).values()):
            if isinstance(value, ModuleType):
                redirect(value)
    redirect(module)
    for m in list(sys.modules.values()):
        if isinstance(m, ModuleType):
            redirect(m)
    captured = []
    if filename == 'solution_series.py':
        original_norm = module.entry_norm
        def record_interval(value):
            frame = inspect.currentframe().f_back
            beta, n = frame.f_locals['beta'], frame.f_locals['n']
            if n+sum(beta) <= 4:
                rows = []
                for i in range(value.re.nrows()):
                    for j in [0, 4, 8]:
                        rows.append([i, j, str(int(value.re[i, j])), str(int(value.im[i, j])), str(int(value.rad[i, j]))])
                captured.append({'external': list(beta), 'radial_degree': n, 'rectangles': rows})
            return original_norm(value)
        module.entry_norm = record_interval
    module.main()
    if captured:
        raw = json.dumps({'precision_bits': module.inv.PRECISION, 'selected_profiles': [0, 4, 8],
                          'coefficient_rectangles': captured}, separators=(',', ':')).encode()
        (HERE/'captured-source-series.json.gz').write_bytes(gzip.compress(raw, mtime=0))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--child')
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    OUT.mkdir(exist_ok=True)
    if args.child:
        child(args.child)
        return
    manifest = hashes()
    stages = read(CANDIDATE/'focused.json')['checks']
    # Some receipts bind their local source file through HERE. The execution
    # still imports the frozen original; these copies pay that read-only hash.
    for path in CANDIDATE.glob('*.py'):
        shutil.copyfile(path, OUT/path.name)
    if not args.resume:
        for path in CANDIDATE.iterdir():
            if path.is_file() and (path.name.endswith('.json') or path.name.endswith('.json.gz')):
                shutil.copyfile(path, OUT/path.name)
    previous = read(HERE/'progress.json')['checks'] if args.resume and (HERE/'progress.json').exists() else []
    checks = []
    for stage in stages:
        name = stage['script']
        old = next((r for r in previous if r['script'] == name and r['exit_code'] == 0), None)
        if old is None:
            print('START', name, flush=True)
            started = time.monotonic()
            with (OUT/stage['log']).open('w') as log:
                result = subprocess.run([sys.executable, '-u', __file__, '--child', name], stdout=log, stderr=subprocess.STDOUT)
            assert result.returncode == 0, (name, result.returncode)
            seconds = round(time.monotonic()-started, 3)
        else:
            seconds = old['seconds']
        actual = clean(read(OUT/stage['receipt']))
        expected = clean(read(CANDIDATE/stage['receipt']))
        assert actual == expected, ('mathematical receipt mismatch', name)
        if name == 'axis.py':
            assert clean(read(OUT/'axis-source.json')) == clean(read(CANDIDATE/'axis-source.json'))
        if name == 'radial_inverse.py':
            packing = read(OUT/'radial-compression.json')
            decoded = gzip.decompress((OUT/packing['file']).read_bytes())
            assert hashlib.sha256(decoded).hexdigest() == packing['decoded_sha256']
        checks.append({'script': name, 'exit_code': 0, 'seconds': seconds,
            'full_mathematical_receipt_identical': True, 'resumed_completed_output': bool(old),
            'mathematical_sha256': hashlib.sha256(json.dumps(actual, sort_keys=True,
                separators=(',', ':')).encode()).hexdigest()})
        (HERE/'progress.json').write_text(json.dumps({'checks': checks}, indent=2)+'\n')
        print('PASS', name, seconds, flush=True)
    hashes()
    (HERE/'replay.json').write_text(json.dumps({'passed': True, 'candidate_files': len(manifest['candidate_sha256']),
        'candidate_unchanged': True, 'original_source_and_dependency_hashes_checked': True,
        'checks': checks}, indent=2)+'\n')


if __name__ == '__main__':
    main()
