"""Issue all original quantum query programs and their same-source inlet."""
from pathlib import Path
import argparse
import ast
import hashlib
import json
import subprocess

import zero_count_quantum_source_rha0042 as source
import zero_count_primal_run_rha0041_1 as provenance

bank, ROOT, HERE = provenance.bank, provenance.ROOT, provenance.HERE
PRODUCER_FREEZE = '065399a21dcf684b38fd34c791e9861fca95d5ea'
OWN = ('criterion-rha0042.md', 'NoCountQuantumGenerator.lean', 'no-count-quantum-generator-math-rha0042.json',
    'zero_count_quantum_source_rha0042.py', 'test_zero_count_quantum_source_rha0042.py',
    'zero_count_quantum_run_rha0042.py', 'test_zero_count_quantum_run_rha0042.py')
INPUTS = ('criterion-rha0034.md', 'RegisteredTensorAction.lean', 'registered-tensor-math-certification-rha0034.json')


def consumer_bindings(freeze, old_bound):
    bound = dict(old_bound)
    available = set(subprocess.check_output(['git', '-C', str(ROOT), 'ls-tree', '-r', '--name-only',
        freeze, '--', HERE.relative_to(ROOT).as_posix()]).decode().splitlines())
    pending = [HERE/name for name in (*OWN, *INPUTS, *provenance.OWN)]
    while pending:
        path = pending.pop()
        relative = path.relative_to(ROOT).as_posix()
        if relative in bound:
            continue
        raw = path.read_bytes()
        source.base.require(provenance._blob(freeze, relative) == raw, 'quantum query science changed after freeze: '+relative)
        bound[relative] = hashlib.sha256(raw).hexdigest()
        if path.suffix != '.py' or path.name.startswith('test_'):
            continue
        for node in ast.walk(ast.parse(raw)):
            names = ([r.name for r in node.names] if isinstance(node, ast.Import) else
                [node.module] if isinstance(node, ast.ImportFrom) and node.level == 0 and node.module else [])
            for name in names:
                candidate = HERE/(name.split('.')[0]+'.py')
                source.base.require(not candidate.is_file() or candidate.relative_to(ROOT).as_posix() in available,
                                    'unfrozen local quantum dependency: '+candidate.name)
                if candidate.relative_to(ROOT).as_posix() in available:
                    pending.append(candidate)
    return bound


def prepare(freeze, prepared, output):
    manifest = json.loads((Path(prepared)/'summary.json').read_text())
    source.base.require(manifest['schema'] == provenance.original.SCHEMA+'/prepared' and
        manifest['scientific_freeze_commit'] == PRODUCER_FREEZE, 'complete original source handoff required')
    old_bound, changes = provenance.producer_bindings(PRODUCER_FREEZE, manifest['source_bindings'])
    bound = consumer_bindings(freeze, old_bound)
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    provenance.previous.write(output/'attempt.json', {'phase': 'prepare', 'scientific_freeze_commit': freeze,
        'original_primal_producer_freeze': PRODUCER_FREEZE, 'source_bindings': bound,
        'operation_document_changes': changes})
    current = source.paid.restore()
    raw = current.record()
    source.base.require(source.base.digest(raw) == manifest['original_current_sha256'], 'original complete retarded inlet changed')
    provenance.original.require_cover(manifest['rows'], raw)
    trajectory = source.trajectory.RetardedGaussianTrajectorySource(current._law, bits=192)
    priority = source.flux.FirstReceiptFluxSource(current._law)
    source.base.require(priority.record() == json.loads(bank.artifact(manifest['complete_priority_flux_source']).read_text()),
                        'actual original priority or retarded law changed')
    rows = []
    for item in priority.record()['complete_no_count_queries']:
        quantum = source.NoCountQuantumSource(trajectory, priority, item['query'])
        inlet = source.NoCountPrimalInlet(current, quantum)
        source_record, inlet_record = quantum.record(), inlet.record()
        path = output/f'query-{item["query"]}.json'
        provenance.previous.write(path, {'schema': source.SCHEMA+'/source-handoff',
            'scientific_freeze_commit': freeze, 'source_bindings': bound,
            'original_quantum_query': source_record, 'source_issued_primal_inlet': inlet_record,
            'curve_or_CEM_mother_certified': False, 'actual_hardware_uniquely_identified': False})
        rows.append({'query': item['query'], 'coupled': item['requires_coupled_no_count_flow'],
            'source_handoff': bank.binding(path), 'quantum_source_sha256': source.base.digest(source_record),
            'primal_inlet_sha256': source.base.digest(inlet_record),
            'activation_component_program_count': sum(len(r['components']) for r in source_record['source_component_programs'])})
    result = {'schema': source.SCHEMA+'/complete-source-program-bank', 'scientific_freeze_commit': freeze,
        'original_primal_producer_freeze': PRODUCER_FREEZE, 'source_bindings': bound,
        'operation_document_changes': changes, 'rows': rows, 'original_current_sha256': source.base.digest(raw),
        'source_factor_ids': raw['source_factor_ids'], 'old_whole_input_error_once': raw['whole_retarded_gate_input_error'],
        'all_original_priority_queries_issued': True, 'complete_coupled_query_count': sum(r['coupled'] for r in rows),
        'source_quantum_curve_generated': False, 'new_pump_or_inlet_solves': 0,
        'CEM_time_mother_issued': False, 'actual_hardware_uniquely_identified': False, 'controller_advance': False}
    provenance.previous.write(output/'summary.json', result)
    print(json.dumps({'source_quantum_queries': len(rows), 'source_coupled_queries': result['complete_coupled_query_count'],
                      'source_inlet_preserved': True}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--freeze', required=True)
    parser.add_argument('--prepared', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    try:
        prepare(args.freeze, args.prepared, args.output)
    except Exception as error:
        if args.output.is_dir() and not (args.output/'failure.json').exists():
            provenance.previous.write(args.output/'failure.json', {'schema': source.SCHEMA+'/failed-attempt',
                'scientific_freeze_commit': args.freeze, 'reason': str(error),
                'actual_hardware_uniquely_identified': False, 'controller_advance': False})
        raise
