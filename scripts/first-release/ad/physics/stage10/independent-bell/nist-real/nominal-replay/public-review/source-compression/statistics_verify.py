#!/usr/bin/env python3
"""Check immutable independent statistical witnesses, without repeating inversion."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import hashlib
import json
import lzma
from pathlib import Path
import subprocess

import compress as c

HERE = Path(__file__).resolve().parent
SCHEMA = 'p23-source-compression-statistical-cross/v1'
FLAGS = ('joint_95_coverage_budget_paid', 'all_24_complete_records_verified',
         'all_576_conditional_intervals_verified', 'all_23040_direction_bets_verified',
         'all_480_original_contrast_bets_verified', 'all_24_support_cut_brackets_verified',
         'all_72_original_CI_preserved')


def endpoints(value):
    lo, hi = F(value['exact_lower']), F(value['exact_upper'])
    c.require(lo <= hi, 'reversed_statistical_interval')
    return lo, hi


def cross(left, right):
    a, b = endpoints(left), endpoints(right)
    c.require(max(a[0], b[0]) <= min(a[1], b[1]), 'independent_statistical_bounds_disjoint')
    c.require(abs(a[0] - b[0]) < F(1, 10 ** 35) and abs(a[1] - b[1]) < F(1, 10 ** 35),
              'independent_interval_endpoints_changed')
    return {'exact_lower': str(min(a[0], b[0])), 'exact_upper': str(max(a[1], b[1]))}


def binding_check(row):
    path = (c.ROOT / row['path']).resolve()
    c.require(path.is_relative_to(c.ROOT) and c.sha(path) == row['sha256'], 'source_binding_changed')
    c.require(subprocess.check_output(['git', 'show', row['commit'] + ':' + row['path']], cwd=c.ROOT) == path.read_bytes(),
              'source_freeze_identity_changed')
    subprocess.run(['git', 'merge-base', '--is-ancestor', row['commit'], 'HEAD'], cwd=c.ROOT, check=True)


def load(name):
    path = HERE / name
    binding = c.frozen(path)
    raw = lzma.decompress(path.read_bytes())
    report = json.loads(raw)
    c.require(report['schema'] == 'p23-source-compression-statistics/v1' and report['version'] == c.VERSION,
              'wrong_statistical_first')
    for row in report['bindings']:
        binding_check(row)
    return report, binding, hashlib.sha256(raw).hexdigest()


def original_CI72():
    q = json.loads((c.MW / 'primary-first.json').read_text())
    run = next(r for r in q['runs'] if r['workbook'] == 'diag-xor3.xlsx')
    groups = [('full_N' + str(g['pulse_count']), g['common_mean_confidence']) for g in run['groups']]
    old = json.loads((HERE.parents[1] / 'observable-prediction/public-comparison-po0003.json').read_text())
    groups.append(('old_cut_N5', old['common_mean_confidence']))
    return [{'identity': name, 'field': field, 'row': i,
             'interval': {k: value[k] for k in ('exact_lower', 'exact_upper')}}
            for name, ci in groups for field in ('j', 'sA_cell', 'sB_cell') for i, value in enumerate(ci[field])]


def generate():
    allocation = {k: str(v) for k, v in c.budget().items()}
    primary, pb, psha = load('statistics-primary-first.json.xz')
    independent, ib, isha = load('statistics-independent-first.json.xz')
    c.require(primary['implementation'] == 'primary' and independent['implementation'] == 'independent', 'missing_independent_route')
    c.require(primary['budget'] == independent['budget'] == allocation, 'joint_budget_changed')
    c.require(independent['retained_old_CI72'] == original_CI72(), 'original_CI72_changed')
    c.require(len(primary['records']) == len(independent['records']) == 24, 'incomplete_public_family')
    imap = {(r['identity']['workbook'], r['identity']['pulse_count']): r for r in independent['records']}
    c.require(len(imap) == 24, 'repeated_independent_public_record')
    records, conditional_count, directional_count, base_count = [], 0, 0, 0
    expected_inputs = {(r['identity']['workbook'], r['identity']['pulse_count']): r for r in c.input_records()}
    for p in primary['records']:
        key = (p['identity']['workbook'], p['identity']['pulse_count'])
        i, original = imap[key], expected_inputs[key]
        for name in ('identity', 'counts', 'total_trials', 'setting_trials'):
            c.require(p[name] == i[name] == original[name], 'complete_count_or_pulse_identity_changed')
        conditional = []
        for setting in range(4):
            row = []
            c.require(len(p['conditional'][setting]) == len(i['conditional'][setting]) == 6, 'missing_outcome_or_single')
            values = c.conditional_events(p['counts'][setting])
            for f, name in enumerate(c.configuration()['conditional_features']):
                a, b = p['conditional'][setting][f], i['conditional'][setting][f]
                c.require(a['feature'] == b['feature'] == name and a['count'] == b['count'] == values[f]
                          and a['trials'] == b['trials'] == p['setting_trials'][setting], 'conditional_exposure_or_event_changed')
                ag = {F(v['lambda']): v for v in a['grid']}
                bg = {F(v['lambda']): v for v in b['grid40']}
                powers = {F(sign, 2 ** k) for k in range(1, 21) for sign in (-1, 1)}
                c.require(set(ag) == set(bg) == powers and len(a['grid']) == len(b['grid40']) == 40, 'direction_bet_family_changed')
                for lam in powers:
                    cross(ag[lam]['bound_expected_count'], bg[lam]['bound_expected_count'])
                row.append({'feature': name, 'count': a['count'], 'trials': a['trials'], 'interval': cross(a['interval'], b['interval'])})
                conditional_count += 1
                directional_count += 40
            conditional.append(row)
        pc, ic = p['contrast'], i['contrast']
        counts = p['counts']
        win, loss = counts[0][0], counts[1][1] + counts[2][2] + counts[3][0]
        eps = F(c.configuration()['epsilon'])
        lower, upper = ((1 - eps) / 2) ** 2, ((1 + eps) / 2) ** 2
        q0, rho = upper / (lower + upper), lower / upper
        c.require(pc['win_count'] == ic['win_count'] == win and pc['loss_count'] == ic['loss_count'] == loss
                  and F(pc['old_q0']) == F(ic['old_q0']) == q0, 'full_trial_contrast_changed')
        c.require(len(pc['fixed_bets']) == len(ic['fixed_bets20']) == 20, 'fixed_bet_count_changed')
        for power, (a, b) in enumerate(zip(pc['fixed_bets'], ic['fixed_bets20']), 1):
            c.require(a['power'] == b['power'] == power and F(a['a']) == F(b['a']) == 1 + rho / 2 ** power
                      and F(a['b']) == F(b['b']) == 1 - F(1, 2 ** power), 'original_fixed_bet_changed')
            cross(a['base_log_e'], b['base_log_e'])
            base_count += 1
        roots = [pc['h_bracket'], ic['h_bracket']]
        for root in roots:
            c.require(root['lower_rejected'] is True and root['upper_not_rejected'] is True
                      and -1 <= F(root['lower']) < F(root['upper']) <= 1, 'uncertified_inversion_endpoint')
            c.require(endpoints(root['log_e_at_lower'])[0] > endpoints(root['log_threshold'])[1]
                      and endpoints(root['log_e_at_upper'])[1] <= endpoints(root['log_threshold'])[0], 'inversion_endpoint_direction_changed')
        c.require(max(F(r['lower']) for r in roots) <= min(F(r['upper']) for r in roots), 'independent_cut_brackets_disjoint')
        h = {'lower': str(min(F(r['lower']) for r in roots)), 'upper': str(max(F(r['upper']) for r in roots)),
             'lower_rejected': True, 'upper_not_rejected': True}
        records.append({**original, 'conditional': conditional,
                        'contrast': {'win_count': win, 'loss_count': loss, 'old_q0': str(q0), 'h_bracket': h}})
    c.require((conditional_count, directional_count, base_count) == (576, 23040, 480), 'missing_statistical_witnesses')
    bindings = [c.frozen(HERE / name) for name in ('criterion.md', 'sources.json', 'statistics_verify.py', 'compress.py', 'independent.py')]
    return {'schema': SCHEMA, 'version': c.VERSION, 'evidence_valid': True, 'bindings': bindings + [pb, ib],
            'first_logical_sha256': {'primary': psha, 'independent': isha}, 'budget': allocation,
            'records': records, 'original_CI72': original_CI72(), **{name: True for name in FLAGS},
            'source_stationarity_is_named_condition': True, 'original_CI_modified': False,
            'actual_hardware_identity_claimed': False, 'controller_advance': False,
            'source_tree_or_Fock_producers_executed': 0}


def consume(certificate_path=None, disabled=False):
    empty = {'schema': SCHEMA, 'evidence_valid': False, **{name: False for name in FLAGS}}
    if disabled:
        return {**empty, 'status': 'disabled'}
    canonical = HERE / 'statistics-cross-verification.json'
    c.frozen(canonical)
    path = canonical if certificate_path is None else Path(certificate_path)
    c.require(path.read_bytes() == canonical.read_bytes(), 'lookalike_statistical_certificate')
    report = json.loads(path.read_text())
    c.require(report['schema'] == SCHEMA and report['version'] == c.VERSION and report['evidence_valid'] is True,
              'invalid_statistical_cross')
    c.configuration()
    for row in report['bindings']:
        binding_check(row)
    c.require(all(report[name] is True for name in FLAGS) and report['original_CI_modified'] is False
              and report['actual_hardware_identity_claimed'] is False, 'statistical_scope_or_true_flag_changed')
    return report


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check-only', action='store_true')
    parser.add_argument('--certificate', type=Path)
    parser.add_argument('--disabled', action='store_true')
    args = parser.parse_args()
    if args.check_only or args.disabled:
        result = consume(args.certificate, args.disabled)
        print(json.dumps({k: result[k] for k in ('schema', 'evidence_valid', *FLAGS)}, sort_keys=True))
    else:
        c.require(args.output is not None and not args.output.exists(), 'new_cross_output_required')
        result = generate()
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
        print(json.dumps({'output': str(args.output), 'evidence_valid': True, 'records': 24,
                          'conditional_intervals': 576, 'directional_bets_checked': 23040}))


if __name__ == '__main__':
    main()
