"""Consume frozen atomic responses and whole-domain kinetic-dose constraints."""
import argparse
from fractions import Fraction as Q
from pathlib import Path
import subprocess

import atomic_forward_independent as independent
import atomic_forward_run as science
import verify as parent
from run import exclusive_json


BASE, ROOT = parent.BASE, parent.ROOT
SCHEMA = 'stage10-munich-atomic-forward-evidence/v1'
FIRSTS = ('atomic-forward-first.json', 'atomic-forward-independent-first.json')


def validate(primary, checked):
    parent.require(primary.get('schema') == 'stage10-munich-atomic-forward-primary/v1' and
                   checked.get('schema') == 'stage10-munich-atomic-forward-independent/v1' and
                   primary.get('status') == 'generated_atomic_response_and_whole_cs_dose_bounds' and
                   checked.get('status') == 'certified_atomic_response_and_whole_cs_dose_bounds', 'atomic_receipt_identity')
    for report in (primary, checked):
        for name, value in science.common_scope().items():
            parent.require(type(report.get(name)) is type(value) and report[name] == value, 'atomic_scope_changed')
        parent.require(tuple(row['id'] for row in report['samples']) == tuple(name for name, _ in science.SAMPLES),
                       'atomic_sample_coverage_changed')
    for row, other, (name, values) in zip(primary['samples'], checked['samples'], science.SAMPLES):
        raw = [dict(zip(science.KEYS, values))]
        parent.require(row['raw_pulses'] == other['raw_pulses'] == raw, 'atomic_raw_sample_changed')
        science.validate_intervals(row['response'], primary=True)
        science.validate_intervals(other['response'], primary=False)
        independent.verify_intersection(row['response'], other['response'])
        restriction = independent.verify_restriction(raw[0], row['response']['basis'], row['generator_restrictions'])
        parent.require(other['restriction_check'] == restriction and other['primary_interval_intersections_verified'] is True,
                       'atomic_full_generator_restriction_changed')
        parent.require(row['spectral_gap_absolute_interval'] == science.interval_gain(row['response']), 'atomic_spectral_gap_changed')
    parent.require(primary['kinetic_dose_bounds'] == checked['kinetic_dose_bounds'] and
                   tuple(row['run'] for row in checked['kinetic_dose_bounds']) == parent.RUNS, 'atomic_dose_scope_changed')
    for field, value in {'samples_checked': 4, 'response_intersections_checked': 12, 'restriction_coefficient_checks': 12288,
                         'whole_cs_individual_dose_bounds_checked': 8, 'whole_cs_joint_maximum_dose_bounds_checked': 6}.items():
        parent.require(type(checked.get(field)) is int and checked[field] == value, 'atomic_check_coverage_incomplete')
    left, right = (tuple(map(Q, checked['samples'][i]['response']['trace_j'])) for i in (2, 3))
    separated = left[1] < right[0] or right[1] < left[0]
    parent.require(checked['theory_unequal_trace_control_certified'] is separated and
                   checked['unequal_trace_control_is_actual_response_anchor'] is False, 'atomic_control_promoted_to_actual')
    return separated


def generate():
    science.source_review()
    primary, checked = (parent.strict_json(parent.frozen(BASE / name)) for name in FIRSTS)
    commit = primary['freeze_commit']
    binding = science.bindings(commit)
    for report, name in ((primary, 'atomic-forward-attempt.json'), (checked, 'atomic-forward-independent-attempt.json')):
        raw = parent.frozen(BASE / name)
        attempt = parent.strict_json(raw)
        parent.require(report['attempt_sha256'] == parent.sha256(raw) and
                       report['freeze_commit'] == attempt['freeze_commit'] == commit and
                       report['execution_head'] == attempt['execution_head'] and
                       report['source_bindings'] == attempt['source_bindings'] == binding, 'atomic_execution_identity_changed')
        ancestor = subprocess.run(['git', 'merge-base', '--is-ancestor', commit, report['execution_head']], cwd=ROOT, capture_output=True)
        parent.require(ancestor.returncode == 0, 'atomic_science_not_frozen_before_execution')
    parent.require(checked['primary_receipt_sha256'] == parent.sha256(parent.frozen(BASE / FIRSTS[0])), 'atomic_primary_identity_changed')
    separated = validate(primary, checked)
    # Already paid numerical executions are consumed; only exact dose arithmetic is rebuilt.
    dose = science.dose_reports(independent=True)
    parent.require(parent.canonical(dose) == parent.canonical(checked['kinetic_dose_bounds']), 'atomic_old_cs_dose_binding_changed')
    return {'schema': SCHEMA, 'criterion_version': science.VERSION, 'evidence_valid': True,
            'status': 'certified_raw_atomic_response_and_whole_cs_kinetic_dose', **science.common_scope(),
            'theory_unequal_trace_control_certified': separated, 'unequal_trace_control_is_actual_response_anchor': False,
            'samples_checked': 4, 'response_intersections_checked': 12, 'restriction_coefficient_checks': 12288,
            'whole_cs_individual_dose_bounds_checked': 8, 'whole_cs_joint_maximum_dose_bounds_checked': 6,
            'kinetic_dose_bounds': dose, 'trial_events_read_at_intake': 0, 'new_numerical_forward_executions_at_intake': 0,
            'source_bindings': [parent.binding(BASE / name) for name in
                                ('criterion-af0001.md', 'atomic_forward_verify.py', 'atomic-forward-source.json', *FIRSTS)]}


def consume(certificate=None):
    path = BASE / 'atomic-forward-verification.json' if certificate is None else Path(certificate)
    result = generate()
    parent.require(parent.canonical(result) == parent.canonical(parent.strict_json(path.read_bytes())), 'atomic_certificate_changed')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-only', action='store_true')
    parser.add_argument('--certificate', type=Path)
    args = parser.parse_args()
    try:
        report = consume(args.certificate) if args.check_only else generate()
        if not args.check_only:
            parent.require(args.certificate is None, 'atomic_override_is_consume_only')
            exclusive_json(BASE / 'atomic-forward-verification.json', report)
        print(parent.canonical(report))
        return 0
    except (OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError) as error:
        print(parent.canonical({'schema': SCHEMA, 'evidence_valid': False, 'reason': str(error)}))
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
