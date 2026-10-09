"""Complete the original ten-factor free TP term without repeating paid pumps."""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import time

import free_density_check_rha0032_1 as previous
import retarded_gate_inlet_factors as factors

HERE, ROOT, core = previous.HERE, previous.ROOT, previous.core
checker, paid = previous.checker, previous.previous.paid
SCHEMA = 'stage10-complete-source-free-TP-bank/rha0033'
OWN = ('criterion-rha0033.md', 'free_density_bank_rha0033.py', 'test_free_density_bank_rha0033.py')
INPUTS = (*previous.OWN, *previous.INPUTS, 'criterion-rha0032.2.md',
    'chebyshev_density_proposal_rha0032_2.py', 'test_chebyshev_clock_rha0032_2.py',
    'free-density-first-rha0032.2.json')


def write(path, value):
    previous.previous.write(Path(path), value)


def binding(path):
    path = Path(path)
    with path.open('rb') as handle: sha = hashlib.file_digest(handle, 'sha256').hexdigest()
    return {'path': path.resolve().relative_to(ROOT).as_posix(), 'bytes': path.stat().st_size, 'sha256': sha}


def artifact(value):
    relative = Path(value['path'])
    core.require(not relative.is_absolute() and '..' not in relative.parts, 'bank artifact outside its workspace')
    path = ROOT/relative; core.require(binding(path) == value, 'free TP bank artifact changed')
    return path


def bindings(freeze):
    result = {}
    for name in dict.fromkeys((*OWN, *INPUTS)):
        path = HERE/name; relative = path.relative_to(ROOT).as_posix(); data = path.read_bytes()
        core.require(subprocess.check_output(['git', '-C', str(ROOT), 'show', freeze+':'+relative]) == data,
                     'free TP bank science changed after freeze: '+name)
        result[relative] = hashlib.sha256(data).hexdigest()
    return result


def inventory(raw):
    banks = raw['checked_local_density_inventories']
    parent = raw['source_issued_two_pump_source']['source_issued_two_pump_factor_inlets']
    core.require(len(banks) == len(parent) == 2, 'both source banks required')
    result = []
    for side, rows in enumerate(banks):
        ids = [row['factor_id'] for row in rows]
        core.require(ids == [row['factor_id'] for row in parent[side]] and len(ids) == len(set(ids)),
                     'every original retarded factor keeps its side and order')
        result.extend((side, index, value) for index, value in enumerate(ids))
    ids = [{row['factor_id'] for row in bank} for bank in banks]
    core.require(raw['source_factor_ids'] == raw['source_issued_two_pump_source']['source_tensor_factor_ids'] and
        all(left in ids[0] and right in ids[1] for left, right in raw['source_factor_ids']),
        'every original tensor incidence must be covered')
    return result


def choose(raw, side=0, index=0):
    core.require(type(side) is int and side in (0, 1) and type(index) is int and index >= 0,
                 'explicit original side and factor index required')
    rows = [row for row in inventory(raw) if row[:2] == (side, index)]
    core.require(len(rows) == 1, 'factor override is outside the original bank')
    return rows[0]


def tensor_price(terms, reports):
    total = Q(0); rows = []
    for left, right in terms:
        a, b = reports[0, left], reports[1, right]
        na, nb = Q(a['initial_entry_norm_upper']), Q(b['initial_entry_norm_upper'])
        ea, eb = Q(a['whole_new_trace_norm_error']), Q(b['whole_new_trace_norm_error'])
        core.require(min(na, nb, ea, eb) >= 0, 'nonnegative complete source prices required')
        value = ea*nb+eb*na+ea*eb
        total += value; rows.append({'factor_ids': [left, right], 'new_uniform_tensor_price': str(value)})
    return total, rows


def _handoff(current, raw, side, index, freeze, bound):
    _, _, factor = choose(raw, side, index)
    source = core.density.GaussianLocalDensitySource(current._law._field._pulses[side])
    initial = core.density.channel._read_input(raw['checked_local_density_inventories'][side][index]['complete_retarded_local_endpoint'], 33)
    start = Q(raw['actual_retarded_local_cuts_seconds'][side])
    field = raw['retarded_detector_law']['complete_driven_field_source']
    stop = Q(raw['retarded_detector_law']['gate_seconds'][1])-Q(field['flight_seconds'][side])-Q(field['emission_origins_seconds'][side])
    core.require(start == current._law.local_times(Q(raw['fixed_detector_gate_start_seconds']))[side] and
                 stop-start == Q(120, 10**9), 'both original local cuts and the full detector gate required')
    handoff = {'schema': 'stage10-source-issued-free-density-handoff/rha0032', 'source_record': source.record(),
        'complete_initial_matrix': core.density.channel._input_record(initial),
        'source_interval_seconds': [str(start), str(stop)], 'source_side': side, 'source_factor_index': index,
        'source_factor_id': factor, 'scientific_freeze_commit': freeze, 'source_bindings': bound,
        'old_whole_input_error_once': raw['whole_retarded_gate_input_error'], 'actual_hardware_member_asserted': False}
    return handoff, source, initial, start, stop


def prepare(freeze, output):
    bound = bindings(freeze); output = Path(output); output.mkdir(parents=True, exist_ok=False)
    first = json.loads(paid.paid.frozen(HERE/'free-density-first-rha0032.2.json'))
    core.require(first['registered_relative_accuracy_passed'] is True and first['free_term_only'] is True,
                 'the complete first factor must pass the unchanged relative accuracy gate')
    current = paid.restore(); raw = current.record(); factors.factor_terms(raw)
    entries = inventory(raw); core.require(len(entries) == 10, 'the completed current inlet has ten factors')
    write(output/'attempt.json', {'scientific_freeze_commit': freeze, 'source_bindings': bound})
    rows = []
    for side, index, factor in entries:
        handoff, _, _, _, _ = _handoff(current, raw, side, index, freeze, bound)
        path = output/f'handoff-{side}-{index}.json'; write(path, handoff)
        row = {'side': side, 'factor_index': index, 'factor_id': factor, 'handoff': binding(path)}
        if (side, index) == (0, 0):
            checked = json.loads(artifact(first['checked_curve']).read_text())
            core.require(first['source_factor_id'] == factor and
                checked['original_density_source'] == handoff['source_record'] and
                checked['stream_header']['initial_matrix_sha256'] == core.digest(handoff['complete_initial_matrix']) and
                checked['source_interval_seconds'] == handoff['source_interval_seconds'],
                'the paid first curve must be this exact original bank entry')
            row['reused_checked_curve'] = first['checked_curve']
        else:
            row['node_unit_id'] = f'free-density-bank-{side}-{index}@{row["handoff"]["sha256"][:16]}'
        rows.append(row)
        print(json.dumps({'prepared_factor': [side, index], 'factor_id': factor}), flush=True)
    report = {'schema': SCHEMA+'/handoff', 'scientific_freeze_commit': freeze, 'source_bindings': bound,
        'rows': rows, 'source_tensor_factor_ids': raw['source_factor_ids'],
        'old_whole_input_error_once': raw['whole_retarded_gate_input_error'],
        'source_positive_mass_upper': raw['source_positive_mass_upper'], 'new_pump_or_inlet_residuals': 0,
        'first_complete_curve_reused': True, 'actual_hardware_uniquely_identified': False, 'controller_advance': False}
    write(output/'summary.json', report)


def check(freeze, prepared, results, output):
    bound = bindings(freeze); prepared, results, output = map(Path, (prepared, results, output))
    manifest = json.loads((prepared/'summary.json').read_text())
    core.require(manifest['schema'] == SCHEMA+'/handoff' and manifest['scientific_freeze_commit'] == freeze and
                 manifest['source_bindings'] == bound, 'the same frozen bank handoff is required')
    output.mkdir(parents=True, exist_ok=False)
    write(output/'attempt.json', {'scientific_freeze_commit': freeze, 'source_bindings': bound})
    current = paid.restore(); raw = current.record(); expected = inventory(raw)
    core.require([(r['side'], r['factor_index'], r['factor_id']) for r in manifest['rows']] == expected and
        manifest['source_tensor_factor_ids'] == raw['source_factor_ids'] and
        manifest['old_whole_input_error_once'] == raw['whole_retarded_gate_input_error'], 'complete source bank coverage changed')
    reports = {}; receipts = []; started = time.monotonic()
    for row in manifest['rows']:
        side, index, factor = row['side'], row['factor_index'], row['factor_id']
        handoff, source, initial, start, stop = _handoff(current, raw, side, index, freeze, bound)
        core.require(json.loads(artifact(row['handoff']).read_text()) == handoff, 'a full handoff source or factor changed')
        if 'reused_checked_curve' in row:
            first = json.loads(paid.paid.frozen(HERE/'free-density-first-rha0032.2.json'))
            core.require((side, index) == (0, 0) and row['reused_checked_curve'] == first['checked_curve'], 'only the paid original first curve is reused')
            path = artifact(row['reused_checked_curve']); result = json.loads(path.read_text())
        else:
            directory = output/f'factor-{side}-{index}'
            result = checker.certify(source, initial, start, stop, results/row['node_unit_id']/'curve.jsonl.gz', directory,
                progress=lambda v: print(json.dumps({'side': side, 'factor_index': index, **v}), flush=True))
            path = directory/'checked-curve.json'
        core.require(result['original_density_source'] == handoff['source_record'] and
            result['stream_header']['initial_matrix_sha256'] == core.digest(handoff['complete_initial_matrix']) and
            result['source_interval_seconds'] == handoff['source_interval_seconds'], 'checked result is not the same full source flow')
        reports[side, factor] = result
        receipts.append({'side': side, 'factor_index': index, 'factor_id': factor, 'checked_curve': binding(path),
            'relative_accuracy_passed': result['registered_relative_accuracy_passed'],
            'whole_new_trace_norm_error': result['whole_new_trace_norm_error'], 'initial_entry_norm_upper': result['initial_entry_norm_upper']})
        write(output/f'factor-{side}-{index}-receipt.json', receipts[-1])
    new, prices = tensor_price(raw['source_factor_ids'], reports); old = Q(raw['whole_retarded_gate_input_error'])
    report = {'schema': SCHEMA+'/complete', 'scientific_freeze_commit': freeze, 'source_bindings': bound,
        'complete_local_residual_count': len(receipts), 'rows': receipts, 'source_tensor_prices': prices,
        'whole_new_uniform_free_tensor_error': str(core.density.field._price_upper(new, 192)),
        'old_whole_input_error_once': str(old), 'whole_free_term_error': str(core.density.field._price_upper(old+new, 192)),
        'all_local_relative_accuracy_gates_passed': all(r['relative_accuracy_passed'] for r in receipts),
        'new_uniform_tensor_error_below_old_input_error': new <= old,
        'free_term_only': True, 'natural_emissions_retained': True,
        'full_gate_instrument_or_response_anchor_certified': False, 'actual_hardware_uniquely_identified': False,
        'controller_advance': False, 'seconds': time.monotonic()-started}
    write(output/'summary.json', report)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('operation', choices=('prepare', 'check'))
    parser.add_argument('--freeze', required=True); parser.add_argument('--output', required=True)
    parser.add_argument('--prepared'); parser.add_argument('--results'); args = parser.parse_args()
    if args.operation == 'prepare': prepare(args.freeze, args.output)
    else: check(args.freeze, args.prepared, args.results, args.output)
