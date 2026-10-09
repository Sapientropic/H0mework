"""Check the frozen primal bank while retaining its original operation document."""
from pathlib import Path
import argparse
import ast
import hashlib
import json
import subprocess

import zero_count_primal_run_rha0041 as original

source, independent, checker = original.source, original.independent, original.checker
bank, HERE, ROOT = original.bank, original.HERE, original.ROOT
previous, flux, activity_price = original.previous, original.flux, original.activity_price
SCHEMA = 'stage10-complete-source-primal-zero-count-bank/rha0041.1'
OWN = ('criterion-rha0041.1.md', 'zero_count_primal_run_rha0041_1.py',
       'test_zero_count_primal_run_rha0041_1.py')
OPERATION_DOCUMENT = 'ComputeNode/README.md'


def _blob(freeze, relative):
    return subprocess.check_output(['git', '-C', str(ROOT), 'show', freeze+':'+relative])


def validate_bound_bytes(expected, issued, current, *, require_document_unchanged=False):
    source.base.require(type(require_document_unchanged) is bool and issued == expected and
                        set(current) == set(expected), 'complete original frozen source bindings required')
    changes = []
    for relative, frozen_hash in expected.items():
        current_hash = hashlib.sha256(current[relative]).hexdigest()
        if current_hash == frozen_hash:
            continue
        source.base.require(relative == OPERATION_DOCUMENT and not require_document_unchanged,
                            'primal source science changed after freeze: '+relative)
        changes.append({'path': relative, 'producer_frozen_sha256': frozen_hash,
                        'current_operation_sha256': current_hash, 'executed_science': False})
    return changes


def producer_bindings(freeze, issued, *, require_document_unchanged=False):
    # Recover the dependency closure from frozen imports, including a missing
    # working-tree dependency; caller-provided inventories cannot erase it.
    available = set(subprocess.check_output(['git', '-C', str(ROOT), 'ls-tree', '-r',
        '--name-only', freeze, '--', HERE.relative_to(ROOT).as_posix()]).decode().splitlines())
    paths = {HERE/n for n in (*original.OWN, *original.INPUTS)}
    pending = [p for p in paths if p.suffix == '.py' and not p.name.startswith('test_')]
    blobs = {}

    def load(path):
        relative = path.relative_to(ROOT).as_posix()
        if relative not in blobs:
            blobs[relative] = _blob(freeze, relative)
        return blobs[relative]

    while pending:
        path = pending.pop()
        for node in ast.walk(ast.parse(load(path))):
            names = ([r.name for r in node.names] if isinstance(node, ast.Import) else
                [node.module] if isinstance(node, ast.ImportFrom) and node.level == 0 and node.module else [])
            for name in names:
                candidate = HERE/(name.split('.')[0]+'.py')
                if candidate.relative_to(ROOT).as_posix() in available and candidate not in paths:
                    paths.add(candidate)
                    pending.append(candidate)
    paths |= {ROOT/OPERATION_DOCUMENT, HERE.parent/'schema.py',
              HERE.parent.parent/'theory-blind/independent_born.py'}
    expected = {p.relative_to(ROOT).as_posix(): hashlib.sha256(load(p)).hexdigest() for p in sorted(paths)}
    current = {p.relative_to(ROOT).as_posix(): p.read_bytes() for p in paths}
    changes = validate_bound_bytes(expected, issued, current,
                                  require_document_unchanged=require_document_unchanged)
    return expected, changes


def consumer_bindings(freeze):
    result = {}
    for name in OWN:
        path = HERE/name
        relative = path.relative_to(ROOT).as_posix()
        raw = path.read_bytes()
        source.base.require(_blob(freeze, relative) == raw, 'primal consumer changed after freeze: '+relative)
        result[relative] = hashlib.sha256(raw).hexdigest()
    return result


def check(producer_freeze, consumer_freeze, prepared, results, output, *, require_document_unchanged=False):
    prepared, results, output = map(Path, (prepared, results, output))
    manifest = json.loads((prepared/'summary.json').read_text())
    source.base.require(manifest['schema'] == original.SCHEMA+'/prepared' and
                        manifest['scientific_freeze_commit'] == producer_freeze,
                        'the original frozen source-owned primal handoff is required')
    bound, changes = producer_bindings(producer_freeze, manifest['source_bindings'],
                                      require_document_unchanged=require_document_unchanged)
    consumer_bound = consumer_bindings(consumer_freeze)
    provenance = {'scientific_freeze_commit': producer_freeze, 'source_bindings': bound,
                  'consumer_freeze_commit': consumer_freeze, 'consumer_bindings': consumer_bound,
                  'operation_document_changes': changes}
    output.mkdir(parents=True, exist_ok=False)
    previous.write(output/'attempt.json', {'phase': 'check', **provenance})
    current = source.paid.restore()
    raw = current.record()
    parent = source.base.ZeroCountReceiptSource(current._law)
    original.require_cover(manifest['rows'], raw)
    plans = original.inventory(current, parent)
    source.base.require(source.base.digest(raw) == manifest['original_current_sha256'] and
        json.loads(bank.artifact(manifest['complete_zero_count_source']).read_text()) == parent.record() and
        json.loads(bank.artifact(manifest['complete_priority_flux_source']).read_text()) ==
        flux.FirstReceiptFluxSource(current._law).record(),
        'original current, no-count law or source priority changed')
    rows, reports = [], []
    for row, (query, side, index, flow) in zip(manifest['rows'], plans):
        source.base.require(json.loads(bank.artifact(row['handoff']).read_text()) ==
            original.handoff(flow, producer_freeze, bound) and
            independent.local_recycling(current._law.record(), side, source.base.PORT_SETS[query]) ==
            flow.record()['complete_unobserved_local_recycling'],
            'original factor handoff or independent bath restriction changed')
        curve = results/row['node_unit_id']/f'primal-{query}-{side}-{index}.jsonl.gz'
        report = checker.certify(flow, curve, output/f'checked-{query}-{side}-{index}',
                                progress=lambda p: print(json.dumps(p), flush=True))
        record = flow.record()
        checked = output/f'checked-{query}-{side}-{index}/checked-primal.json'
        rows.append({'query': query, 'side': side, 'factor_index': index, 'factor_id': record['factor_id'],
            'primal_source_sha256': source.base.digest(record), 'curve': bank.binding(curve),
            'checked_primal': bank.binding(checked),
            'whole_new_uniform_trace_norm_error': report['whole_new_uniform_trace_norm_error'],
            'whole_new_endpoint_trace_norm_error': report['whole_new_endpoint_trace_norm_error'],
            'registered_accuracy_passed': report['registered_accuracy_passed']})
        reports.append({**row, 'report': report})
    first = original.endpoint_readout(reports, raw, current._law.record())
    adjoint = json.loads(source.paid.paid.frozen(HERE/'first-receipt-probability-first-rha0039.json'))
    first['independent_accepted_adjoint_readout'] = original.compare_adjoint(first, adjoint)
    previous.write(output/'primal-first-receipt.json', first)
    normalizer = json.loads(source.paid.paid.frozen(HERE/'retarded-normalizer-first-rha0028.json'))
    source.base.require(normalizer['source_bindings'] ==
        {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in normalizer['source_bindings']},
        'the paid same-source activity certificate changed')
    activity = json.loads(bank.artifact(normalizer['report']).read_text())['complete_source_activity_cap']
    ar = activity['source_record']
    source.base.require(ar['source_activity'] == activity_price.activity._facts(current._law.record(), ar['scalar_bits']) and
        activity['source_bindings'] == activity_price.activity._bindings(), 'original complete activity derivation changed')
    priced = activity_price.contract(first, activity, current._law.record())
    previous.write(output/'primal-first-receipt-priced.json', priced)
    result = {'schema': SCHEMA+'/complete', **provenance, 'rows': rows,
        'complete_source_factor_query_count': len(rows),
        'all_registered_accuracy_gates_passed': all(r['registered_accuracy_passed'] for r in rows),
        'complete_zero_count_source': manifest['complete_zero_count_source'],
        'complete_priority_flux_source': manifest['complete_priority_flux_source'],
        'source_primal_first_receipt': bank.binding(output/'primal-first-receipt.json'),
        'source_primal_first_receipt_priced': bank.binding(output/'primal-first-receipt-priced.json'),
        'independent_accepted_adjoint_readout': first['independent_accepted_adjoint_readout'],
        'full_CEM_time_mother_issued': False, 'specific_Psi_label_probability_claimed': False,
        'actual_hardware_uniquely_identified': False, 'controller_advance': False}
    previous.write(output/'summary.json', result)
    print(json.dumps({'complete_primal_flows': len(rows),
        'accuracy_passed': result['all_registered_accuracy_gates_passed'],
        'first_receipt_mass_interval': [float(original.Q(x)) for x in priced['physical_any_first_receipt_mass_interval']]}), flush=True)
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--producer-freeze', required=True)
    p.add_argument('--consumer-freeze', required=True)
    p.add_argument('--prepared', type=Path, required=True)
    p.add_argument('--results', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--require-operation-document-unchanged', action='store_true')
    args = p.parse_args()
    try:
        check(args.producer_freeze, args.consumer_freeze, args.prepared, args.results, args.output,
              require_document_unchanged=args.require_operation_document_unchanged)
    except Exception as error:
        if args.output.is_dir() and not (args.output/'failure.json').exists():
            previous.write(args.output/'failure.json', {'schema': SCHEMA+'/failed-attempt', 'phase': 'check',
                'scientific_freeze_commit': args.producer_freeze, 'consumer_freeze_commit': args.consumer_freeze,
                'reason': str(error), 'actual_hardware_uniquely_identified': False, 'controller_advance': False})
        raise
