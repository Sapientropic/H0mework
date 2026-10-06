#!/usr/bin/env python3
"""Focused fresh kernel acceptance; no numerical producer is executed."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / '.git').exists())
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    sys.modules[name] = result
    spec.loader.exec_module(result)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--ct-cache', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    c = module('_sc_contract', HERE / 'compress.py')
    c.require(not args.output.exists(), 'kernel_certificate_already_exists')
    bindings = [c.frozen(HERE / name) for name in
                ('criterion.md', 'sources.json', 'NormalizedSourceBet.lean', 'CompressionCertification.lean', 'lean_certify.py')]
    ct = module('_sc_ct_certificate', HERE.parent / 'contrast-source/certify.py')
    old = ct.fastconsume()
    c.require(old.get('evidence_valid') is True, 'original_source_law_certificate_invalid')
    # The admitted CT cache is an import artifact of the unchanged, certified CT source.
    c.require((args.ct_cache / 'ContrastConsumer.olean').is_file(), 'missing_certified_CT_import')
    for p in (HERE / 'NormalizedSourceBet.lean', HERE / 'CompressionCertification.lean'):
        c.require(not re.search(r'\b(sorry|admit|axiom|native_decide)\b', p.read_text()), 'forbidden_proof_escape')
    with tempfile.TemporaryDirectory(prefix='p23-sc-kernel-') as temporary:
        fresh = Path(temporary)
        environment = dict(os.environ)
        environment['LEAN_PATH'] = os.pathsep.join((str(fresh), str(args.ct_cache), environment.get('LEAN_PATH', '')))
        logs, commands = [], []
        for name in ('NormalizedSourceBet', 'CompressionCertification'):
            cmd = ['lake', 'env', 'lean', '--trust=0', '-DwarningAsError=true', '--root=' + str(HERE),
                   '-o', str(fresh / (name + '.olean')), str(HERE / (name + '.lean'))]
            process = subprocess.run(cmd, cwd=ROOT / 'Lean', env=environment, capture_output=True, text=True, timeout=180)
            if process.returncode != 0:
                Path('/tmp/p23-sc-kernel-error.log').write_text(process.stdout + process.stderr)
                c.require(False, 'focused_kernel_gate_failed:' + process.stdout[:9000] + process.stderr[:1000])
            logs.append(process.stdout)
            commands.append({'module': name, 'trust': 0, 'warningAsError': True, 'exit_code': process.returncode,
                             'output_sha256': hashlib.sha256(process.stdout.encode()).hexdigest()})
        audit = logs[-1]
        rows = re.findall(r'SC_AXIOMS ([^\n|]+)\|\[([^\]]*)\]', audit)
        count = re.search(r'SC_OWNED (\d+)', audit)
        c.require(count is not None and int(count[1]) == len(rows) and len(rows) > 30, 'incomplete_owned_axiom_inventory')
        axioms = {}
        for name, values in rows:
            actual = {v.strip() for v in values.split(',') if v.strip()}
            c.require(actual <= ALLOWED, 'unauthorized_source_compression_axiom:' + name)
            axioms[name] = sorted(actual)
        dependencies = re.findall(r'SC_DEP (\S+)', audit)
        graph = re.search(r'SC_GRAPH (\d+)', audit)
        c.require(graph is not None and len(set(dependencies)) == len(dependencies) == int(graph[1]),
                  'incomplete_transitive_source_dependency_inventory')
    result = {'schema': 'p23-source-compression-kernel-certification/v1', 'version': c.VERSION,
              'evidence_valid': True, 'bindings': bindings, 'reused_CT_certificate': old,
              'fresh_compilations': commands, 'owned_declarations': len(axioms), 'authorized_axioms': sorted(ALLOWED),
              'all_owned_axioms': axioms, 'dependency_count': len(dependencies),
              'dependency_sha256': hashlib.sha256(json.dumps(sorted(dependencies)).encode()).hexdigest(),
              'support_is_exact_and_attained': True, 'all_N_source_normalized_bet_kernel_certified': True,
              'all_six_source_conditional_features_kernel_certified': True,
              'positive_cut_requires_generated_source_support': True,
              'new_stochastic_process_or_Ville_kernel': False, 'controller_advance': False,
              'numerical_producers_executed': 0}
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'output': str(args.output), 'owned_declarations': len(axioms),
                      'dependency_count': len(dependencies), 'evidence_valid': True}))


if __name__ == '__main__':
    main()
