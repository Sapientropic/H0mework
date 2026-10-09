"""Six same-source propagators generate a separated two-arrival rectangle."""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json
import subprocess

import completed_retarded_inlet_rha0028 as paid
import free_density_bank_rha0033 as previous
import gaussian_operator_flow_rha0037_1 as flow
import gaussian_operator_check_rha0037_1 as checker

HERE, ROOT = previous.HERE, previous.ROOT
SCHEMA = 'stage10-source-two-arrival-no-jump-operator-bank/rha0037.1'
ROLES = ('early_forward', 'early_reverse_right', 'late_forward')
OWN = ('criterion-rha0037.1.md', 'GaussianCoflow.lean', 'gaussian-coflow-math-certification-rha0037.json',
    'gaussian_operator_flow_rha0037_1.py', 'gaussian_operator_proposal_rha0037_1.py',
    'gaussian_operator_independent_rha0037_1.py', 'gaussian_operator_check_rha0037_1.py',
    'gaussian_operator_bank_rha0037_1.py', 'test_gaussian_operator_flow_rha0037_1.py')
INPUTS = (*previous.OWN, *previous.INPUTS, 'criterion-rha0037.md',
    'gaussian-operator-first-rha0037.json', 'gaussian-operator-attempt-rha0037.json',
    'completed_retarded_inlet_rha0028.py',
    'gaussian_atomic_pulse_source.py', 'chebyshev_density_rha0032.py',
    'chebyshev_density_integer_rha0032_1.py', 'chebyshev_density_proposal_rha0032_2.py',
    'chebyshev_basis_independent_rha0032.py', 'ChebyshevDensityResidual.lean',
    'chebyshev-density-math-certification-rha0032.json', 'retarded-inlet-first-rha0027.json',
    'registered-forcing-first-rha0034.json')


def bindings(freeze):
    result = {}
    for name in dict.fromkeys((*OWN, *INPUTS)):
        path = HERE/name; relative = path.relative_to(ROOT).as_posix(); raw = path.read_bytes()
        flow.require(subprocess.check_output(['git', '-C', str(ROOT), 'show', freeze+':'+relative]) == raw,
                     'operator bank science changed after freeze: '+name)
        result[relative] = hashlib.sha256(raw).hexdigest()
    return result


def plans(current):
    raw = current.record(); g0, g1 = map(Q, raw['retarded_detector_law']['gate_seconds']); mid = (g0+g1)/2
    result = []
    for side, pulse in enumerate(current._law._field._pulses):
        start, middle, stop = (current._law.local_times(t)[side] for t in (g0, mid, g1))
        flow.require(start == Q(raw['actual_retarded_local_cuts_seconds'][side]) and stop-start == Q(120, 10**9),
                     'same original retarded cuts and whole detector gate required')
        for role, a, b, direction in (('early_forward', start, middle, 'forward'),
                ('early_reverse_right', start, middle, 'reverse_right'), ('late_forward', middle, stop, 'forward')):
            result.append((side, role, flow.GaussianOperatorFlow(pulse, a, b, direction=direction)))
    return raw, result


def choose(rows, side=0, role='early_forward'):
    flow.require(type(side) is int and side in (0, 1) and role in ROLES, 'registered side and explicit flow role required')
    selected = [item for item in rows if item[:2] == (side, role)]
    flow.require(len(selected) == 1, 'complete source operator role inventory required')
    return selected[0]


def handoff(source, side, role, freeze, bound):
    return {'schema': flow.SCHEMA+'/handoff', 'flow_source': source.record(), 'side': side, 'role': role,
        'scientific_freeze_commit': freeze, 'source_bindings': bound, 'initial_operator_supplied_by_caller': False,
        'actual_hardware_member_asserted': False}


def prepare(freeze, output):
    bound = bindings(freeze); output = Path(output); output.mkdir(parents=True, exist_ok=False)
    previous.write(output/'attempt.json', {'scientific_freeze_commit': freeze, 'source_bindings': bound})
    current = paid.restore(); raw, inventory = plans(current); rows = []
    for side, role, source in inventory:
        path = output/f'handoff-{side}-{role}.json'; previous.write(path, handoff(source, side, role, freeze, bound))
        binding = previous.binding(path)
        rows.append({'side': side, 'role': role, 'flow_source_sha256': flow.digest(source.record()), 'handoff': binding,
            'node_unit_id': f'operator-flow-{side}-{role}@{binding["sha256"][:16]}'})
        print(json.dumps({'prepared_operator': [side, role]}), flush=True)
    report = {'schema': SCHEMA+'/handoff', 'scientific_freeze_commit': freeze, 'source_bindings': bound, 'rows': rows,
        'original_inlet_source_sha256': flow.digest(raw), 'old_whole_input_error_once': raw['whole_retarded_gate_input_error'],
        'source_positive_mass_upper': raw['source_positive_mass_upper'],
        'source_detector_gate_seconds': raw['retarded_detector_law']['gate_seconds'],
        'selected_two_arrival_domain': 'g0<=first<=midpoint<=second<=g1; original Mark target applied at both arrivals',
        'new_pump_or_inlet_residuals': 0, 'inverse_propagator_used': False,
        'positive_two_arrival_integral_evaluated': False, 'actual_hardware_uniquely_identified': False, 'controller_advance': False}
    previous.write(output/'summary.json', report)


def check(freeze, prepared, results, output):
    bound = bindings(freeze); prepared, results, output = map(Path, (prepared, results, output))
    manifest = json.loads((prepared/'summary.json').read_text())
    flow.require(manifest['schema'] == SCHEMA+'/handoff' and manifest['scientific_freeze_commit'] == freeze and
                 manifest['source_bindings'] == bound, 'same frozen source operator handoff required')
    output.mkdir(parents=True, exist_ok=False); previous.write(output/'attempt.json', {'scientific_freeze_commit': freeze, 'source_bindings': bound})
    current = paid.restore(); raw, inventory = plans(current)
    flow.require(manifest['original_inlet_source_sha256'] == flow.digest(raw) and len(manifest['rows']) == len(inventory) == 6 and
                 [(r['side'], r['role']) for r in manifest['rows']] == [r[:2] for r in inventory], 'six complete original operator flows required')
    reports = []
    for row, (side, role, source) in zip(manifest['rows'], inventory):
        expected = handoff(source, side, role, freeze, bound)
        flow.require(json.loads(previous.artifact(row['handoff']).read_text()) == expected and
                     row['flow_source_sha256'] == flow.digest(source.record()), 'source operator handoff changed')
        curve = results/row['node_unit_id']/f'curve-{side}-{role}.jsonl.gz'
        report = checker.certify(source, curve, output/f'checked-{side}-{role}', progress=lambda p: print(json.dumps(p), flush=True))
        reports.append({'side': side, 'role': role, 'flow_source_sha256': row['flow_source_sha256'],
            'curve': previous.binding(curve), 'checked_curve': previous.binding(output/f'checked-{side}-{role}/checked-curve.json'),
            'whole_uniform_operator_error': report['whole_uniform_operator_error'],
            'registered_accuracy_passed': report['registered_accuracy_passed'],
            'independent_source_prefixes': report['independent_source_prefixes']})
    summary = {'schema': SCHEMA+'/checked-bank', 'scientific_freeze_commit': freeze, 'source_bindings': bound, 'rows': reports,
        'original_inlet_source_sha256': manifest['original_inlet_source_sha256'],
        'complete_operator_flow_count': len(reports), 'all_registered_accuracy_gates_passed': all(r['registered_accuracy_passed'] for r in reports),
        'old_inlet_error_reapplied_per_operator': False, 'inverse_propagator_used': False,
        'positive_two_arrival_integral_evaluated': False, 'actual_hardware_uniquely_identified': False, 'controller_advance': False}
    previous.write(output/'summary.json', summary)
    print(json.dumps({'complete_operator_flows': len(reports), 'all_accuracy_gates_passed': summary['all_registered_accuracy_gates_passed']}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('phase', choices=('prepare', 'check'))
    parser.add_argument('--freeze', required=True); parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', type=Path); parser.add_argument('--results', type=Path); args = parser.parse_args()
    try:
        if args.phase == 'prepare': prepare(args.freeze, args.output)
        else:
            flow.require(args.prepared is not None and args.results is not None, 'original prepared and proposal artifacts required')
            check(args.freeze, args.prepared, args.results, args.output)
    except Exception as error:
        if args.output.is_dir() and not (args.output/'failure.json').exists():
            previous.write(args.output/'failure.json', {'schema': SCHEMA+'/failed-attempt',
                'scientific_freeze_commit': args.freeze, 'phase': args.phase, 'reason': str(error),
                'actual_hardware_uniquely_identified': False, 'controller_advance': False})
        raise
