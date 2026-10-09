"""Prepare an issued full-gate factor and check its untrusted node curve."""
from pathlib import Path
from fractions import Fraction as Q
import argparse
import hashlib
import json
import subprocess

import completed_retarded_inlet_rha0028 as paid
import chebyshev_density_rha0032 as core
import chebyshev_density_check_rha0032 as checker

HERE, ROOT = paid.HERE, paid.ROOT
OWN = ('criterion-rha0032.md', 'ChebyshevDensityResidual.lean', 'chebyshev_density_rha0032.py',
    'chebyshev_basis_independent_rha0032.py', 'chebyshev_density_proposal_rha0032.py',
    'chebyshev_density_check_rha0032.py', 'free_density_run_rha0032.py', 'test_chebyshev_density_rha0032.py',
    'chebyshev-density-math-certification-rha0032.json')
INPUTS = ('retarded-inlet-first-rha0027.json', 'registered-duhamel-first-rha0031.json',
    'completed_retarded_inlet_rha0028.py', 'retarded_gate_inlet_factors.py', 'prepared_retarded_gaussian_inlet.py',
    'gaussian_density_exponential_writer.py', 'gaussian_local_density_source.py', 'gaussian_atomic_pulse_source.py',
    'fourier_local_phase_source.py', 'retarded_registered_duhamel_rha0031.py')


def bindings(freeze):
    result = {}
    for name in (*OWN, *INPUTS):
        path = HERE/name; relative = path.relative_to(ROOT).as_posix(); data = path.read_bytes()
        core.require(subprocess.check_output(['git', '-C', str(ROOT), 'show', freeze+':'+relative]) == data,
                     'free-density science changed after freeze: '+name)
        result[relative] = hashlib.sha256(data).hexdigest()
    return result


def write(path, value):
    with path.open('x') as handle: json.dump(value, handle, sort_keys=True); handle.write('\n')


def selection(current, side=0, factor_index=0):
    raw = current.record(); source = core.density.GaussianLocalDensitySource(current._law._field._pulses[side])
    row = raw['checked_local_density_inventories'][side][factor_index]
    initial = core.density.channel._read_input(row['complete_retarded_local_endpoint'], 33)
    start = Q(raw['actual_retarded_local_cuts_seconds'][side])
    field = raw['retarded_detector_law']['complete_driven_field_source']
    stop = Q(raw['retarded_detector_law']['gate_seconds'][1])-Q(field['flight_seconds'][side])-Q(field['emission_origins_seconds'][side])
    core.require(start == current._law.local_times(Q(raw['fixed_detector_gate_start_seconds']))[side] and stop-start == Q(120, 10**9),
                 'the issued factor must cover the original complete120ns detector gate')
    return source, initial, start, stop, row['factor_id'], raw


def prepare(freeze, output):
    bound = bindings(freeze); output = Path(output); output.mkdir(parents=True, exist_ok=False)
    write(output/'attempt.json', {'scientific_freeze_commit': freeze, 'source_bindings': bound, 'operation': 'prepare'})
    current = paid.restore(); source, initial, start, stop, factor, raw = selection(current)
    handoff = {'schema': 'stage10-source-issued-free-density-handoff/rha0032', 'source_record': source.record(),
        'complete_initial_matrix': core.density.channel._input_record(initial),
        'source_interval_seconds': list(map(str, (start, stop))), 'source_side': 0, 'source_factor_index': 0,
        'source_factor_id': factor, 'source_positive_mass_upper': raw['source_positive_mass_upper'],
        'old_whole_input_error_once': raw['whole_retarded_gate_input_error'],
        'scientific_freeze_commit': freeze, 'source_bindings': bound,
        'paid_current_inlet_sha256': hashlib.sha256((HERE/'retarded-inlet-first-rha0027.json').read_bytes()).hexdigest(),
        'numeric_endpoint_installed_as_new_source': False, 'actual_hardware_member_asserted': False}
    path = output/'handoff.json'; write(path, handoff)
    result = {'schema': 'stage10-issued-free-density-handoff-first/rha0032', 'scientific_freeze_commit': freeze,
        'source_bindings': bound, 'source_side': 0, 'source_factor_index': 0, 'source_factor_id': factor,
        'source_interval_seconds': handoff['source_interval_seconds'],
        'source_record_sha256': core.digest(handoff['source_record']),
        'initial_matrix_sha256': core.digest(handoff['complete_initial_matrix']),
        'handoff': {'path': path.resolve().relative_to(ROOT).as_posix(), 'bytes': path.stat().st_size,
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()},
        'new_pump_or_retarded_inlet_residuals': 0, 'untrusted_node_worker_issues_a_source': False,
        'actual_hardware_uniquely_identified': False, 'controller_advance': False}
    write(output/'summary.json', result); print(json.dumps(result), flush=True)


def check(freeze, prepared, curve, output):
    bound = bindings(freeze); prepared, curve, output = Path(prepared), Path(curve), Path(output)
    summary = json.loads((prepared/'summary.json').read_text()); handoff_path = prepared/'handoff.json'
    core.require(summary['scientific_freeze_commit'] == freeze and summary['source_bindings'] == bound and
        handoff_path.stat().st_size == summary['handoff']['bytes'] and
        hashlib.sha256(handoff_path.read_bytes()).hexdigest() == summary['handoff']['sha256'], 'issued source handoff changed')
    handoff = json.loads(handoff_path.read_text()); current = paid.restore()
    source, initial, start, stop, factor, raw = selection(current)
    core.require(factor == handoff['source_factor_id'] and source.record() == handoff['source_record'] and
        core.density.channel._input_record(initial) == handoff['complete_initial_matrix'] and
        [str(start), str(stop)] == handoff['source_interval_seconds'], 'same original closed source, factor and clock required')
    output.mkdir(parents=True, exist_ok=False)
    write(output/'attempt.json', {'scientific_freeze_commit': freeze, 'source_bindings': bound, 'operation': 'check'})
    try:
        result = checker.certify(source, initial, start, stop, curve, output/'complete-residual',
                                progress=lambda value: print(json.dumps(value), flush=True))
        report = {'schema': 'stage10-source-issued-free-density-checked-first/rha0032', 'scientific_freeze_commit': freeze,
            'source_bindings': bound, 'source_factor_id': factor, 'source_interval_seconds': [str(start), str(stop)],
            'whole_new_trace_norm_error': result['whole_new_trace_norm_error'],
            'initial_entry_norm_upper': result['initial_entry_norm_upper'],
            'registered_relative_accuracy_passed': result['registered_relative_accuracy_passed'],
            'checked_curve': {'path': (output/'complete-residual/checked-curve.json').resolve().relative_to(ROOT).as_posix(),
                'sha256': hashlib.sha256((output/'complete-residual/checked-curve.json').read_bytes()).hexdigest()},
            'same_issued_retarded_factor_and_entire_gate_checked': True, 'free_term_only': True,
            'full_gate_instrument_or_response_anchor_certified': False, 'actual_hardware_uniquely_identified': False,
            'controller_advance': False}
    except Exception as error:
        write(output/'summary.json', {'schema': core.SCHEMA+'/failed-check', 'status': 'check_failed',
            'reason': str(error), 'scientific_freeze_commit': freeze, 'source_bindings': bound}); raise
    write(output/'summary.json', report); print(json.dumps(report), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('operation', choices=('prepare', 'check'))
    parser.add_argument('--freeze', required=True); parser.add_argument('--output', required=True)
    parser.add_argument('--prepared'); parser.add_argument('--curve'); args = parser.parse_args()
    if args.operation == 'prepare': prepare(args.freeze, args.output)
    else: check(args.freeze, args.prepared, args.curve, args.output)
