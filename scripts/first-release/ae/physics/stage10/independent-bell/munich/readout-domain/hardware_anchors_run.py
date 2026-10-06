"""Frozen mathematical controls for conditional instrument recovery, without calibration data."""
import argparse
from fractions import Fraction
from itertools import product
from pathlib import Path
import subprocess

import anchors_certify
import hardware_anchor_check as independent
import hardware_anchors as primary
import identification
from model import decode, encode, source_joint
import verify as parent
from run import exclusive_json


BASE, ROOT = parent.BASE, parent.ROOT
VERSION = 'stage10-munich-readout-ia0001'
MODULE = ROOT / 'Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/ReadoutAnchors.lean'
FILES = ('criterion-ia0001.md', 'hardware_anchors.py', 'hardware_anchor_check.py', 'hardware_anchors_run.py',
         'test_hardware_anchors.py', 'test_hardware_anchor_check.py', 'test_hardware_anchors_run.py', 'hardware-anchor-access.md',
         'hardware-anchor-sources.json', 'hardware-anchors-audit.md', 'hardware-anchors-program-audit.json',
         'AnchorsCertification.lean', 'anchors_certify.py', 'test_anchors_certify.py', 'anchors-certification-first.json')
INPUTS = ('primitive-witness-c0002.json', 'identification-first.json', 'model.py', 'identification.py',
          'identification-certification-first.json')


def bindings(commit):
    result = []
    for path in [*(BASE / name for name in (*FILES, *INPUTS)), MODULE]:
        raw = parent.frozen(path, commit)
        parent.require(raw == parent.frozen(path), 'hardware_anchor_science_changed')
        result.append({'path': str(path.relative_to(ROOT)), 'sha256': parent.sha256(raw)})
    return result


def controls():
    kernel = anchors_certify.consume()
    parent.require(kernel['all_four_effects_reconstructed_from_law_and_means_certified'] is True and
                   kernel['actual_hardware_uniquely_identified'] is False, 'hardware_anchor_kernel_scope_changed')
    review = parent.strict_json(parent.frozen(BASE / 'hardware-anchors-program-audit.json'))
    parent.require(review['evidence_valid'] is True, 'hardware_anchor_program_review_rejected')
    for entry in review['source_bindings']:
        parent.require(parent.sha256(parent.frozen(ROOT / entry['path'])) == entry['sha256'], 'hardware_anchor_review_source_changed')
    sources = parent.strict_json(parent.frozen(BASE / 'hardware-anchor-sources.json'))
    parent.require(sources['schema'] == 'munich-run-hardware-anchor-access/v1' and
                   sources['scope']['run_setting_aom_nominal_table_certified'] is True and
                   sources['scope']['actual_hardware_parameters_unique'] is False,
                   'hardware_control_scope_changed')
    witnesses, identified = (parent.strict_json(parent.frozen(BASE / name)) for name in
                             ('primitive-witness-c0002.json', 'identification-first.json'))
    parent.require(tuple(r['run'] for r in witnesses['runs']) == tuple(r['run'] for r in identified['runs']) == parent.RUNS,
                   'hardware_anchor_generated_law_family_changed')
    probes = (primary.Probe(0, Fraction(3, 5), Fraction(4, 5)), primary.Probe(1, Fraction(4, 5), Fraction(-3, 5)))
    probe_records = [{'setting': p.setting, 'x': str(p.x), 'z': str(p.z)} for p in probes]
    runs = []
    for original, law_record in zip(witnesses['runs'], identified['runs']):
        point = decode(original['primitive'])
        law = law_record['observable_quotient']
        parent.require(identification.quotient(point) == law, 'hardware_anchor_source_law_changed')
        chart = primary.AnchorChart(law, probes)
        scales = [(Fraction(1), Fraction(1)), *product((Fraction(-21, 20), Fraction(-19, 20),
                                                       Fraction(19, 20), Fraction(21, 20)), repeat=2)]
        samples = []
        for s, t in scales:
            other = identification.scale(point, s, t)
            means = [primary.response(other.alice[p.setting], p) for p in probes]
            recovered = chart.recover(means)
            checked = independent.recover(law, probe_records, means)
            parent.require(recovered == checked == other, 'hardware_anchor_constructor_or_independent_elimination_failed')
            old_q = tuple(source_joint(point, *key) for key in product((0, 1), repeat=5))
            new_q = tuple(source_joint(checked, *key) for key in product((0, 1), repeat=5))
            parent.require(old_q == new_q, 'hardware_anchor_reconstructed_source_law_changed')
            error = Fraction(1, 100000)
            intervals = [(max(Fraction(-1), value - error), min(Fraction(1), value + error)) for value in means]
            bounds = chart.interval_coordinates(intervals)
            vertices = [chart.anchor_coordinates(pair) for pair in product(*intervals)]
            parent.require(all((min(v[i] for v in vertices), max(v[i] for v in vertices)) == bound
                               for i, bound in enumerate(bounds)), 'hardware_anchor_interval_inverse_failed')
            samples.append({'scales': [str(s), str(t)], 'probes': probe_records,
                            'generated_test_response_means': list(map(str, means)), 'recovered_effects': encode(checked),
                            'all_32_source_probabilities_unchanged': True, 'both_constructions_agree': True,
                            'anchor_error_intervals': [list(map(str, row)) for row in intervals],
                            'coordinate_error_outer_intervals': [list(map(str, row)) for row in bounds],
                            'actual_calibration_inputs': False})
        runs.append({'run': original['run'], 'known_generated_law_controls': samples,
                     'law_derived_coefficient_determinant': str(chart.determinant),
                     'coordinate_lipschitz_constants': list(map(str, chart.sensitivity()))})
    return {'schema': 'stage10-munich-hardware-anchor-construction/v1', 'version': VERSION,
            'evidence_valid': True, 'status': 'certified_conditional_hardware_recovery_construction_controls',
            'source_kernel_sha256': parent.sha256(parent.frozen(BASE / 'anchors-certification-first.json')),
            'public_control_binding_sha256': parent.sha256(parent.frozen(BASE / 'hardware-anchor-sources.json')),
            'conditional_signed_hardware_reconstruction_certified': True,
            'nominal_two_run_setting_aom_identity_certified': True,
            'known_generated_law_controls_checked': 34, 'generated_probe_responses_checked': 68,
            'exact_source_probabilities_checked': 1088, 'all_four_signed_scale_branches_checked': True,
            'actual_independent_anchor_inputs_available': False, 'actual_hardware_uniquely_identified': False,
            'construction_controls_used_as_actual_calibration': False, 'actual_law_assumed_known_from_empirical_counts': False,
            'atomic_response_forward_model_kernel_proved': False, 'atomic_detector_self_calibration_kernel_proved': False,
            'new_confidence_budget_spent': False, 'trial_event_files_read': 0, 'new_statistical_tables_read': 0,
            'new_empirical_fit_executed': False, 'controller_advance': False, 'runs': runs}


def consume(certificate=None):
    path = BASE / 'hardware-anchors-first.json' if certificate is None else Path(certificate)
    report = parent.strict_json(path.read_bytes())
    attempt_raw = parent.frozen(BASE / 'hardware-anchors-attempt.json')
    attempt = parent.strict_json(attempt_raw)
    parent.require(report['attempt_sha256'] == parent.sha256(attempt_raw) and
                   report['freeze_commit'] == attempt['freeze_commit'] and
                   report['execution_head'] == attempt['execution_head'] and
                   report['source_bindings'] == attempt['source_bindings'] == bindings(report['freeze_commit']),
                   'hardware_anchor_first_identity_changed')
    ancestor = subprocess.run(['git', 'merge-base', '--is-ancestor', report['freeze_commit'], report['execution_head']],
                              cwd=ROOT, capture_output=True)
    parent.require(ancestor.returncode == 0, 'hardware_anchor_science_not_frozen')
    rebuilt = controls()
    rebuilt.update({name: report[name] for name in ('freeze_commit', 'execution_head', 'attempt_sha256', 'source_bindings')})
    parent.require(parent.canonical(rebuilt) == parent.canonical(report), 'hardware_anchor_construction_receipt_changed')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--freeze-commit')
    parser.add_argument('--check-only', action='store_true')
    parser.add_argument('--certificate', type=Path)
    args = parser.parse_args()
    if args.check_only:
        try:
            report = consume(args.certificate)
            print(parent.canonical({'status': report['status'], 'evidence_valid': True,
                                    'known_generated_law_controls_checked': report['known_generated_law_controls_checked'],
                                    'actual_hardware_uniquely_identified': False}))
            return 0
        except (OSError, ValueError, TypeError, KeyError) as error:
            print(parent.canonical({'evidence_valid': False, 'reason': str(error)}))
            return 1
    if not args.freeze_commit or args.certificate is not None:
        parser.error('generation requires a freeze commit; certificate override is check-only')
    attempt, first = BASE / 'hardware-anchors-attempt.json', BASE / 'hardware-anchors-first.json'
    try:
        parent.require(not attempt.exists() and not first.exists(), 'hardware_anchor_first_already_reserved')
        commit = subprocess.run(['git', 'rev-parse', '--verify', args.freeze_commit + '^{commit}'], cwd=ROOT,
                                text=True, capture_output=True, check=True).stdout.strip()
        head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True, capture_output=True, check=True).stdout.strip()
        subprocess.run(['git', 'merge-base', '--is-ancestor', commit, head], cwd=ROOT, check=True, capture_output=True)
        entries = bindings(commit)
        exclusive_json(attempt, {'version': VERSION, 'freeze_commit': commit, 'execution_head': head,
                                 'source_bindings': entries, 'trial_event_files_read': 0})
    except (OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError) as error:
        print(parent.canonical({'status': 'not_started', 'reason': str(error)}))
        return 2
    try:
        report = controls()
    except Exception as error:
        report = {'schema': 'stage10-munich-hardware-anchor-construction/v1', 'version': VERSION,
                  'evidence_valid': False, 'status': 'execution_failed', 'reason': str(error), 'error_type': type(error).__name__}
    report.update(freeze_commit=commit, execution_head=head, source_bindings=entries,
                  attempt_sha256=parent.sha256(attempt.read_bytes()))
    exclusive_json(first, report)
    print(parent.canonical({'status': report['status'], 'evidence_valid': report['evidence_valid']}))
    return 0 if report['evidence_valid'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
