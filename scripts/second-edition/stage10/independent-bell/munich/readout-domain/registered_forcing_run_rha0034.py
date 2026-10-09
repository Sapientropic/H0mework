"""Freeze-bound first forcing compilation from the completed original free bank."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import time

import registered_forcing_rha0034 as primary
import registered_forcing_independent_rha0034 as independent

HERE, ROOT, bank = primary.HERE, primary.ROOT, primary.bank
OWN = ('criterion-rha0034.md', 'RegisteredTensorAction.lean', 'registered_tensor_action_rha0034.py',
    'test_registered_tensor_action_rha0034.py', 'registered_forcing_rha0034.py',
    'registered_forcing_independent_rha0034.py', 'registered_forcing_run_rha0034.py',
    'test_registered_forcing_rha0034.py', 'registered-tensor-math-certification-rha0034.json')
INPUTS = (*bank.OWN, *bank.INPUTS, 'free-density-bank-first-rha0033.json',
    'free-density-bank-proposals-first-rha0033.1.json', 'retarded_registered_duhamel_rha0031.py',
    'retarded_gaussian_trajectory_source.py', 'retarded_gaussian_bsm_source.py',
    'retarded_receipt_activity_envelope.py', 'factorized_local_phase_source.py', 'atomic_dipole.py')


def bindings(freeze):
    result = {}
    for name in dict.fromkeys((*OWN, *INPUTS)):
        path = HERE/name; relative = path.relative_to(ROOT).as_posix(); data = path.read_bytes()
        primary.source.require(subprocess.check_output(['git', '-C', str(ROOT), 'show', freeze+':'+relative]) == data,
                               'registered forcing science changed after freeze: '+name)
        result[relative] = hashlib.sha256(data).hexdigest()
    return result


def execute(freeze, output):
    bound = bindings(freeze); output = Path(output); output.mkdir(parents=True, exist_ok=False)
    bank.write(output/'attempt.json', {'scientific_freeze_commit': freeze, 'source_bindings': bound})
    started = time.monotonic(); current = primary.paid.restore()
    print('restored the same completed current inlet; no pump or free-curve solve', flush=True)
    report = primary.generate(current)
    completed = json.loads(primary.paid.paid.frozen(HERE/'free-density-bank-first-rha0033.json'))
    checked = independent.check(report, current._law, completed)
    bank.write(output/'forcing-DAG.json', report)
    result = {'schema': primary.SCHEMA+'/first', 'scientific_freeze_commit': freeze, 'source_bindings': bound,
        'source_identity': report['source_identity'], 'paid_free_bank_sha256': report['paid_free_bank_sha256'],
        'source_detector_interval_seconds': report['source_detector_interval_seconds'],
        'forcing_DAG': bank.binding(output/'forcing-DAG.json'), 'complete_free_curve_node_count': len(report['free_curve_nodes']),
        'complete_operator_node_count': len(report['operator_nodes']),
        'complete_registered_row_count': sum(len(p['rows']) for p in report['original_registered_component_programs']),
        'forcing_prices': report['forcing_prices'], 'independent_report': checked,
        'quantum_joint_matrix_expanded': False, 'first_registered_time_integral_evaluated': False,
        'full_gate_instrument_or_response_anchor_certified': False, 'actual_hardware_uniquely_identified': False,
        'controller_advance': False, 'seconds': time.monotonic()-started}
    bank.write(output/'summary.json', result)
    print(json.dumps({k: result[k] for k in ('forcing_prices', 'complete_operator_node_count', 'complete_registered_row_count', 'seconds')}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--freeze', required=True); parser.add_argument('--output', required=True)
    args = parser.parse_args(); execute(args.freeze, args.output)
