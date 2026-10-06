"""Frozen primary or independent atomic response, with original-CS raw dose bounds."""
import argparse
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import subprocess

import verify as parent
from run import exclusive_json


BASE, ROOT = parent.BASE, parent.ROOT
VERSION = 'stage10-munich-atomic-forward-af0001'
FILES = ('criterion-af0001.md', 'atomic_forward.py', 'atomic_forward_independent.py', 'atomic_forward_run.py', 'atomic_forward_verify.py',
         'test_atomic_forward.py', 'test_atomic_forward_independent.py', 'test_atomic_forward_verify.py', 'atomic_dose.py', 'test_atomic_dose.py',
         'atomic-forward-source.md', 'atomic-forward-source.json')
INPUTS = ('shared-response-first.json', 'joint-response-first.json', 'joint-response-verification.json')
SAMPLES = (('no_readout', ('1/5', '0', '4', '3')),
           ('weak_readout', ('1/5', '1/4', '25', '83/25')),
           ('response_0', ('1', '5', '25', '83/25')),
           ('response_1', ('1', '6', '25', '83/25')))
KEYS = ('duration', 'omega_r', 'omega_c', 'ion_rate')
MAX_WIDTH = Q(1, 10 ** 50)


def bindings(commit):
    result = []
    for name in (*FILES, *INPUTS):
        path = BASE / name
        raw = parent.frozen(path, commit)
        parent.require(raw == parent.frozen(path), 'atomic_forward_science_changed')
        result.append({'path': str(path.relative_to(ROOT)), 'sha256': parent.sha256(raw)})
    return result


def source_review():
    review = parent.strict_json(parent.frozen(BASE / 'atomic-forward-source.json'))
    parent.require(review['schema'] == 'stage10-munich-atomic-forward-source/v1' and
                   review['evidence_valid'] is True and review['uniform_raw_pulse_area_bound_reviewed'] is True and
                   review['actual_hardware_uniquely_identified'] is False and
                   review['atomic_response_forward_model_kernel_proved'] is False, 'atomic_model_source_review_changed')
    for entry in (*review['numerical_program_files_reviewed'], review['review_note']):
        parent.require(parent.sha256(parent.frozen(ROOT / entry['path'])) == entry['sha256'], 'atomic_source_review_binding_changed')
    return review


def validate_intervals(report, *, primary):
    expected_trace = tuple(a + b for a, b in zip(map(Q, report['p_bright']), map(Q, report['p_dark'])))
    parent.require(tuple(map(Q, report['trace_j'])) == expected_trace, 'atomic_trace_not_generated_from_probabilities')
    for name in ('p_bright', 'p_dark', 'trace_j'):
        lo, hi = map(Q, report[name])
        limit = 2 if name == 'trace_j' else 1
        width = 2 * MAX_WIDTH if name == 'trace_j' else MAX_WIDTH
        parent.require(lo <= hi and max(lo, Q(0)) <= min(hi, Q(limit)) and hi - lo <= width,
                       'atomic_response_interval_not_physical_or_precise')
    parent.require(report['generator_trace_preserving'] is True and report['ion_offdiagonal_zero'] is True,
                   'atomic_generator_structure_changed')
    if primary:
        for branch in ('bright', 'dark'):
            low, high = map(Q, report[branch]['trace_interval'])
            parent.require(low <= 1 <= high, 'atomic_trace_not_one')
            parent.require(0 <= Q(report[branch]['trace_norm_error_upper']) <= MAX_WIDTH, 'atomic_trace_norm_error_too_wide')
    else:
        parent.require(report['full_144_complex_liouvillian'] is True and report['hermitian_states_checked'] is True and
                       all(0 <= Q(value) <= MAX_WIDTH for value in report['error_bounds']), 'atomic_independent_error_too_wide')


def interval_gain(report):
    b0, b1 = map(Q, report['p_bright'])
    d0, d1 = map(Q, report['p_dark'])
    low, high = b0 - d1, b1 - d0
    return [str(max(Q(0), low, -high)), str(max(abs(low), abs(high)))]


def dose_reports(*, independent=False):
    import joint_response_verify
    admitted = joint_response_verify.consume()
    parent.require(admitted['whole_empirical_confidence_set_bounds'] is True and
                   admitted['parent_confidence_budget'] == '1/20', 'atomic_dose_parent_cs_changed')
    shared, joint = (parent.strict_json(parent.frozen(BASE / name)) for name in
                     ('shared-response-first.json', 'joint-response-first.json'))
    parent.require(tuple(row['run'] for row in shared['runs']) == tuple(row['run'] for row in joint['runs']) == parent.RUNS,
                   'atomic_dose_parent_runs_changed')
    if not independent:
        import atomic_dose
        return [{'run': previous['run'], **atomic_dose.bounds(previous, current)}
                for previous, current in zip(shared['runs'], joint['runs'])]
    # The independent side consumes the same source bounds with its own ratio and root check.
    output = []
    for previous, current in zip(shared['runs'], joint['runs']):
        def lower(gain):
            gain = Q(gain)
            parent.require(0 < gain <= 1, 'atomic_dose_positive_gain_required')
            squared = gain / Q(7, 4)
            scale = 2 ** 80
            root = Q(isqrt(squared.numerator * scale ** 2 // squared.denominator), scale)
            parent.require(root ** 2 <= squared < (root + Q(1, scale)) ** 2, 'atomic_dose_outward_root_failed')
            return str(squared), str(root)
        roles = (('alice', 0), ('alice', 1), ('bob', 0), ('bob', 1))
        parent.require(tuple((r['side'], r['setting']) for r in previous['shared_response_envelopes']) == roles,
                       'atomic_dose_original_roles_changed')
        individual, joint_bounds = [], []
        for row in previous['shared_response_envelopes']:
            squared, root = lower(row['canonical_gain'][0])
            individual.append({'side': row['side'], 'setting': row['setting'], 'source_gain_lower': row['canonical_gain'][0],
                               'readout_rabi_area_squared_lower': squared, 'readout_rabi_area_lower': root,
                               'whole_parent_confidence_set_necessary_bound': True})
        parent.require(tuple(r['ray'] for r in current['joint_response_rays']) == ('uniform', 'alice', 'bob'),
                       'atomic_dose_joint_rays_changed')
        for row in current['joint_response_rays']:
            parent.require(row['entire_lower_orthant_excluded'] is True, 'atomic_dose_original_joint_exclusion_lost')
            squared, root = lower(row['profile_threshold_bracket'][0])
            joint_bounds.append({'ray': row['ray'], 'source_max_gain_strict_lower': row['profile_threshold_bracket'][0],
                                 'maximum_readout_rabi_area_squared_strict_lower': squared,
                                 'maximum_readout_rabi_area_strict_lower': root})
        output.append({'run': previous['run'], 'individual_exposures': individual, 'joint_maximum_exposures': joint_bounds,
                       'area_definition': 'sum_dimensionless_readout_Rabi_times_dimensionless_duration=integral_Omega12_dt',
                       'source_inequality': 'gain<=min(1,7*area^2/4)',
                       'scope': 'registered_fixed_chart_12_state_ionization_model_intersected_with_original_parent_confidence_set',
                       'cycling_and_ion_rates_restricted_by_this_bound': False, 'new_confidence_budget_spent': False,
                       'actual_raw_controls_uniquely_identified': False})
    return output


def common_scope():
    return {'version': VERSION, 'evidence_valid': True, 'raw_control_atomic_response_certified': True,
            'whole_parent_cs_kinetic_dose_bounds_certified': True,
            'fixed_chart_12_state_model_required': True, 'parent_confidence_budget': '1/20',
            'actual_independent_anchor_inputs_available': False, 'actual_hardware_uniquely_identified': False,
            'theory_control_samples_used_as_actual_parameters': False,
            'nominal_atom_centers_used_as_actual_confidence_box': False,
            'atomic_response_forward_model_kernel_proved': False, 'new_confidence_budget_spent': False,
            'trial_event_files_read': 0, 'new_empirical_fit_executed': False, 'controller_advance': False}


def generate_primary():
    import atomic_forward as producer
    source_review()
    results = []
    for name, values in SAMPLES:
        pulse = producer.Pulse(*values)
        result = producer.propagate((pulse,))
        validate_intervals(result, primary=True)
        exact = producer.generator_coefficients(pulse)
        results.append({'id': name, 'raw_pulses': [dict(zip(KEYS, values))], 'response': result,
                        'generator_restrictions': [[[column, list(map(str, coefficient))] for column, coefficient in row]
                                                   for row in exact], 'spectral_gap_absolute_interval': interval_gain(result)})
    return {'schema': 'stage10-munich-atomic-forward-primary/v1',
            'status': 'generated_atomic_response_and_whole_cs_dose_bounds', **common_scope(),
            'samples': results, 'kinetic_dose_bounds': dose_reports()}


def generate_independent(primary):
    import atomic_forward_independent as checker
    source_review()
    parent.require(primary['schema'] == 'stage10-munich-atomic-forward-primary/v1' and
                   primary['version'] == VERSION and primary['evidence_valid'] is True,
                   'atomic_primary_receipt_identity')
    parent.require([row['id'] for row in primary['samples']] == [name for name, _ in SAMPLES], 'atomic_sample_inventory_changed')
    results = []
    for row, (name, values) in zip(primary['samples'], SAMPLES):
        expected = [dict(zip(KEYS, values))]
        parent.require(row['raw_pulses'] == expected, 'atomic_raw_controls_changed')
        restriction = checker.verify_restriction(expected[0], row['response']['basis'], row['generator_restrictions'])
        checked = checker.propagate(expected)
        validate_intervals(row['response'], primary=True)
        validate_intervals(checked, primary=False)
        checker.verify_intersection(row['response'], checked)
        # A detector contraction cannot increase the generated ionization spectral width.
        parent.require(row['spectral_gap_absolute_interval'] == interval_gain(row['response']), 'atomic_spectral_gap_changed')
        results.append({'id': name, 'raw_pulses': expected, 'response': checked, 'restriction_check': restriction,
                        'primary_interval_intersections_verified': True})
    old_dose = dose_reports(independent=True)
    parent.require(parent.canonical(primary['kinetic_dose_bounds']) == parent.canonical(old_dose), 'atomic_dose_projection_changed')
    left, right = (tuple(map(Q, results[i]['response']['trace_j'])) for i in (2, 3))
    separated = left[1] < right[0] or right[1] < left[0]
    return {'schema': 'stage10-munich-atomic-forward-independent/v1',
            'status': 'certified_atomic_response_and_whole_cs_dose_bounds', **common_scope(),
            'samples': results, 'kinetic_dose_bounds': old_dose, 'samples_checked': 4,
            'response_intersections_checked': 12, 'restriction_coefficient_checks': 12288,
            'whole_cs_individual_dose_bounds_checked': 8, 'whole_cs_joint_maximum_dose_bounds_checked': 6,
            'theory_unequal_trace_control_certified': separated,
            'unequal_trace_control_is_actual_response_anchor': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--freeze-commit', required=True)
    parser.add_argument('--implementation', choices=('primary', 'independent'), required=True)
    args = parser.parse_args()
    suffix = '' if args.implementation == 'primary' else '-independent'
    attempt, first = BASE / ('atomic-forward' + suffix + '-attempt.json'), BASE / ('atomic-forward' + suffix + '-first.json')
    try:
        parent.require(not attempt.exists() and not first.exists(), 'atomic_first_already_reserved')
        def git(*arguments):
            result = subprocess.run(['git', *arguments], cwd=ROOT, text=True, capture_output=True)
            parent.require(result.returncode == 0, 'atomic_freeze_not_ancestor')
            return result.stdout.strip()
        commit, head = git('rev-parse', '--verify', args.freeze_commit + '^{commit}'), git('rev-parse', 'HEAD')
        git('merge-base', '--is-ancestor', commit, head)
        science = bindings(commit)
        primary_raw = parent.frozen(BASE / 'atomic-forward-first.json') if suffix else None
        exclusive_json(attempt, {'version': VERSION, 'freeze_commit': commit, 'execution_head': head,
                                 'source_bindings': science, 'trial_events_read_at_reservation': 0})
    except (OSError, ValueError, TypeError, KeyError) as error:
        print(parent.canonical({'status': 'not_started', 'reason': str(error)}))
        return 2
    try:
        report = generate_primary() if primary_raw is None else generate_independent(parent.strict_json(primary_raw))
    except Exception as error:
        report = {'evidence_valid': False, 'status': 'execution_failed', 'reason': str(error), 'error_type': type(error).__name__}
    report.update(freeze_commit=commit, execution_head=head, source_bindings=science,
                  attempt_sha256=parent.sha256(attempt.read_bytes()))
    if primary_raw is not None:
        report['primary_receipt_sha256'] = parent.sha256(primary_raw)
    exclusive_json(first, report)
    print(parent.canonical({'status': report['status'], 'evidence_valid': report['evidence_valid']}))
    return 0 if report['evidence_valid'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
