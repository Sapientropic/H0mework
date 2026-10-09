"""Freeze-bound split and whole-gate tail budget on the issued current source."""
from pathlib import Path
from fractions import Fraction as Q
import argparse
import hashlib
import json
import subprocess
import time

import completed_retarded_inlet_rha0028 as paid
import retarded_registered_duhamel_rha0031 as primary
import registered_duhamel_independent_rha0031 as independent

HERE, ROOT = paid.HERE, paid.ROOT
OWN = ('criterion-rha0031.md', 'RegisteredDuhamelTail.lean', 'retarded_registered_duhamel_rha0031.py',
       'registered_duhamel_independent_rha0031.py', 'registered_duhamel_run_rha0031.py',
       'test_registered_duhamel_rha0031.py', 'registered-duhamel-math-certification-rha0031.json')
INPUTS = ('completed_retarded_inlet_rha0028.py', 'retarded-normalizer-first-rha0028.json',
    'retarded-inlet-first-rha0027.json', 'retarded_receipt_activity_envelope.py',
    'retarded_gaussian_trajectory_source.py', 'retarded_gaussian_bsm_source.py', 'gaussian_local_density_source.py',
    'gaussian_atomic_pulse_source.py', 'aperture_collection_domain.py', 'atomic_dipole.py',
    'retarded_receipt_trajectory_certificate.py', 'retarded_integer_residual_certificate.py')
ORDERS = (0, 2, 4, 6, 8, 10, 12, 16)


def bindings(freeze):
    result = {}
    for name in (*OWN, *INPUTS):
        path = HERE/name; relative = path.relative_to(ROOT).as_posix(); data = path.read_bytes()
        primary.require(subprocess.check_output(['git', '-C', str(ROOT), 'show', freeze+':'+relative]) == data,
                        'registered Duhamel source changed after freeze: '+name)
        result[relative] = hashlib.sha256(data).hexdigest()
    return result


def write(path, value):
    with path.open('x') as handle:
        json.dump(value, handle, sort_keys=True, indent=2); handle.write('\n')


def execute(freeze, output):
    bound = bindings(freeze); output = Path(output)
    primary.require(not output.exists(), 'the first registered Duhamel receipt is immutable')
    write(output.with_name(output.stem+'-attempt.json'), {'scientific_freeze_commit': freeze, 'source_bindings': bound})
    started = time.monotonic()
    try:
        old = json.loads(paid.paid.frozen(HERE/'retarded-normalizer-first-rha0028.json'))
        completed = paid._artifact(old['report'], None)
        old_activity = completed['complete_source_activity_cap']['source_record']
        current = paid.restore(); print('restored the same completed current inlet; no new domain solve', flush=True)
        source = primary.trajectory.RetardedGaussianTrajectorySource(current._law, bits=old_activity['scalar_bits'])
        split = primary.RetardedRegisteredDuhamelSource(source); raw = split.record()
        primary.require(raw['complete_activity_source'] == old_activity,
                        'the split must consume the already paid current activity source')
        facts = old_activity['source_activity']; gate = tuple(map(Q, old_activity['fixed_gate_seconds']))
        mass = Q(completed['source_positive_mass_upper']); error = Q(completed['source_record']['whole_retarded_gate_input_error'])
        rates = sum(map(Q, facts['complete_Gamma_family_natural_loss_operator_norms_per_second']), Q(0))
        background = sum(map(Q, facts['four_source_BG_rate_upper_per_second']), Q(0)); domains = {}
        for label, kappa in (('current_optical_member', Q(facts['registered_optical_operator_norm_square_upper'])),
                            ('whole_objective_transfer_domain', Q(facts['source_objective_operator_norm_square_upper']))):
            activity = kappa*rates+background; variation = 2*activity*(gate[1]-gate[0]); budgets = []
            for n in ORDERS:
                if primary.upper(variation) >= n+2:
                    budgets.append({'retained_order': n, 'geometric_ratio_valid': False}); continue
                row = primary.finite_tail(variation, n); value = Q(row['whole_instrument_operator_tail_upper'])
                price = primary.upper(mass*value)
                budgets.append({**row, 'geometric_ratio_valid': True, 'source_mass_times_tail_upper': str(price),
                                'tail_below_old_input_error': price < error})
            domains[label] = {'registered_activity_upper_per_second': str(activity),
                'interaction_variation_upper': str(variation), 'tail_budgets': budgets}
        report = {'schema': 'stage10-registered-Duhamel-full-gate-budget-first/rha0031',
            'source_identity': {'source': 'positiveSmoothUnifiedSource', 'root_visit': 10, 'current_tick': 16, 'next_tick': 17},
            'scientific_freeze_commit': freeze, 'source_bindings': bound,
            'paid_current_inlet_sha256': hashlib.sha256((HERE/'retarded-inlet-first-rha0027.json').read_bytes()).hexdigest(),
            'paid_normalizer_report_binding': old['report'], 'complete_split_source_sha256': primary.digest(raw),
            'coefficient_identity': split.coefficient_identity(), 'detector_interval_seconds': list(map(str, gate)),
            'source_positive_mass_upper': str(mass), 'old_input_trace_norm_error_once': str(error),
            'variation_domains': domains, 'free_flow_is_complete_local_TP': True,
            'physical_receipt_coimage_stays_frozen': True, 'inverse_TP_flow_used': False,
            'large_atomic_H_norm_enters_interaction_tail': False, 'free_flow_and_quadrature_residuals_already_paid': False,
            'full_gate_trajectory_generated': False, 'actual_hardware_member_asserted': False,
            'actual_hardware_uniquely_identified': False, 'controller_advance': False}
        report['independent_report'] = independent.check(report, source._law.record(), old_activity)
        report['seconds'] = time.monotonic()-started
    except Exception as error:
        write(output, {'schema': primary.SCHEMA+'/failed-attempt', 'status': 'generation_or_check_failed',
            'reason': str(error), 'scientific_freeze_commit': freeze, 'source_bindings': bound})
        raise
    write(output, report)
    print(json.dumps({'independent_report': report['independent_report'], 'seconds': report['seconds']}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--freeze', required=True); parser.add_argument('--output', required=True)
    args = parser.parse_args(); execute(args.freeze, args.output)
