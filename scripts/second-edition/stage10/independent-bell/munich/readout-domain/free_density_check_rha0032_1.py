"""Reuse the frozen issued handoff and node curve with integer source checking."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess

import free_density_run_rha0032 as previous
import chebyshev_density_check_rha0032_1 as checker

HERE, ROOT, core = previous.HERE, previous.ROOT, previous.core
OWN = ('criterion-rha0032.1.md', 'chebyshev_density_integer_rha0032_1.py',
       'chebyshev_density_check_rha0032_1.py', 'free_density_check_rha0032_1.py',
       'test_chebyshev_integer_rha0032_1.py')
INPUTS = (*previous.OWN, *previous.INPUTS, 'free-density-handoff-first-rha0032.json')


def bindings(freeze):
    result = {}
    for name in (*OWN, *INPUTS):
        path = HERE/name; relative = path.relative_to(ROOT).as_posix(); data = path.read_bytes()
        core.require(subprocess.check_output(['git', '-C', str(ROOT), 'show', freeze+':'+relative]) == data,
                     'integer density science changed after freeze: '+name)
        result[relative] = hashlib.sha256(data).hexdigest()
    return result


def execute(freeze, curve, output, *, rational=False):
    bound = bindings(freeze); curve, output = Path(curve), Path(output)
    summary = json.loads(previous.paid.paid.frozen(HERE/'free-density-handoff-first-rha0032.json'))
    handoff_path = ROOT/summary['handoff']['path']
    core.require(handoff_path.stat().st_size == summary['handoff']['bytes'] and
        hashlib.sha256(handoff_path.read_bytes()).hexdigest() == summary['handoff']['sha256'], 'original frozen handoff changed')
    handoff = json.loads(handoff_path.read_text()); current = previous.paid.restore()
    source, initial, start, stop, factor, _ = previous.selection(current)
    core.require(factor == handoff['source_factor_id'] and source.record() == handoff['source_record'] and
        core.density.channel._input_record(initial) == handoff['complete_initial_matrix'] and
        [str(start), str(stop)] == handoff['source_interval_seconds'], 'same original complete source factor and clock required')
    output.mkdir(parents=True, exist_ok=False)
    previous.write(output/'attempt.json', {'scientific_freeze_commit': freeze, 'source_bindings': bound,
        'operation': 'rational' if rational else 'integer'})
    try:
        result = checker.certify(source, initial, start, stop, curve, output/'complete-residual',
            strategy='rational' if rational else 'integer', progress=lambda v: print(json.dumps(v), flush=True))
        path = output/'complete-residual/checked-curve.json'
        report = {'schema': 'stage10-source-issued-free-density-checked-first/rha0032.1', 'scientific_freeze_commit': freeze,
            'source_bindings': bound, 'source_factor_id': factor, 'source_interval_seconds': [str(start), str(stop)],
            'whole_new_trace_norm_error': result['whole_new_trace_norm_error'],
            'initial_entry_norm_upper': result['initial_entry_norm_upper'],
            'registered_relative_accuracy_passed': result['registered_relative_accuracy_passed'],
            'checked_curve': {'path': path.resolve().relative_to(ROOT).as_posix(),
                'bytes': path.stat().st_size, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()},
            'residual_arithmetic': result['residual_arithmetic'], 'node_curve_regenerated': False,
            'same_issued_retarded_factor_and_entire_gate_checked': True, 'free_term_only': True,
            'full_gate_instrument_or_response_anchor_certified': False, 'actual_hardware_uniquely_identified': False,
            'controller_advance': False, 'seconds': result['seconds']}
    except Exception as error:
        previous.write(output/'summary.json', {'schema': core.SCHEMA+'/failed-integer-check', 'reason': str(error),
            'scientific_freeze_commit': freeze, 'source_bindings': bound}); raise
    previous.write(output/'summary.json', report); print(json.dumps(report), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--freeze', required=True)
    parser.add_argument('--curve', required=True); parser.add_argument('--output', required=True)
    parser.add_argument('--rational', action='store_true'); args = parser.parse_args()
    execute(args.freeze, args.curve, args.output, rational=args.rational)
