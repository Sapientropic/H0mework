"""Bind a frozen nullary mathematical producer and save its first exact prediction."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import sysconfig

import capabilities

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
OWN = ('criterion.md', 'sources.json', 'constructor.py', 'capabilities.py',
       'test_constructor.py', 'produce.py')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def git_binding(path):
    relative = path.relative_to(ROOT).as_posix()
    blob = subprocess.check_output(['git', 'rev-parse', 'HEAD:' + relative], cwd=ROOT, timeout=30).decode().strip()
    original = subprocess.check_output(['git', 'cat-file', 'blob', blob], cwd=ROOT, timeout=30)
    current = path.read_bytes()
    if current != original:
        raise ValueError('unfrozen_scientific_input:' + relative)
    return {'path': relative, 'git_blob': blob, 'sha256': digest(current)}


def pure_constructor():
    source = (HERE / 'constructor.py').read_text()
    capability = capabilities.certify_constructor(source)
    spec = importlib.util.spec_from_file_location('theory_blind_constructor', HERE / 'constructor.py')
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    capabilities.require_nullary(module.build_prediction)
    stdlib = Path(sysconfig.get_paths()['stdlib']).resolve()
    runtime_sources = []
    for name in ('fractions', 'dataclasses'):
        path = Path(sys.modules[name].__file__).resolve()
        if path.parent != stdlib:
            raise ValueError('shadowed_standard_library:' + name)
        runtime_sources.append({'module': name, 'stdlib_file': path.name,
                                'sha256': digest(path.read_bytes())})
    return module, capability, runtime_sources


def generate():
    sources = json.loads((HERE / 'sources.json').read_text())
    if sources['criterion_sha256'] != digest((HERE / 'criterion.md').read_bytes()):
        raise ValueError('criterion_binding_changed')
    bindings = [git_binding(HERE / name) for name in OWN]
    for source in sources['sources']:
        path = ROOT / source['path']
        binding = git_binding(path)
        if binding['sha256'] != source['sha256']:
            raise ValueError('theory_source_changed:' + source['path'])
        bindings.append(binding)
    module, capability, runtime_sources = pure_constructor()
    return {
        'schema': 'stage10-theory-blind-first/v1',
        'status': 'generated_exact_theory_prediction',
        'prediction': module.build_prediction(), 'capability_check': capability,
        'source_bindings': bindings, 'stdlib_sources': runtime_sources,
        'new_public_statistical_tables_read': 0, 'trial_event_files_read': 0,
        'empirical_parameters_used': False, 'human_outcome_unexposed_claimed': False,
        'real_instrument_empirical_verdict_executed': False, 'controller_advance': False}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', default='prediction-first.json')
    args = parser.parse_args()
    output = (HERE / args.out).resolve()
    if output.parent != HERE or output.name in OWN:
        parser.error('new receipt must be a separate file in the theory-blind directory')
    result = generate()
    with output.open('x', encoding='utf-8') as stream:
        json.dump(result, stream, ensure_ascii=False, indent=2)
        stream.write('\n')
    print(json.dumps({'status': result['status'], 'records': len(result['prediction']['records']),
                      'receipt': output.name}, ensure_ascii=False))


if __name__ == '__main__':
    main()
