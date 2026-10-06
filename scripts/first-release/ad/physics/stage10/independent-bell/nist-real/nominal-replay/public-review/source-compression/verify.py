#!/usr/bin/env python3
"""Consume the certified joint source domain; never regenerate science at intake."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import importlib.util
import json
from pathlib import Path
import sys

import compress as c
import statistics_verify as stats

HERE = Path(__file__).resolve().parent
SCHEMA = 'p23-public-source-compression-evidence/v1'
POSITIVE = ('public_source_domain_compressed', 'joint_95_source_domain_certified',
            'joint_95_source_domain_nonempty', 'joint_95_source_domain_CH_N5_positive',
            'complete_continuous_source_outer_cover_certified')
NEGATIVE = ('apparatus_optimum_verified', 'original_CI_modified', 'actual_hardware_identity_claimed',
            'calibration_sigma_inserted_as_CI', 'global_all_mask_family_rejected',
            'new_external_data_dependency', 'controller_advance', 'new_stochastic_process_or_Ville_kernel')


def literal_int(value, minimum=0):
    c.require(type(value) is int and value >= minimum, 'nonliteral_integer_evidence')


def validate_statistics(report):
    c.require(report['schema'] == stats.SCHEMA and report['version'] == c.VERSION
              and report['evidence_valid'] is True and all(report[name] is True for name in stats.FLAGS),
              'invalid_exact_statistical_flags')
    for name in ('controller_advance', 'actual_hardware_identity_claimed', 'original_CI_modified'):
        c.require(report[name] is False, 'statistical_scope_changed')
    literal_int(report['source_tree_or_Fock_producers_executed'])
    c.require(report['source_tree_or_Fock_producers_executed'] == 0
              and report['source_stationarity_is_named_condition'] is True, 'conditional_source_law_changed')
    allocation = {k: str(v) for k, v in c.budget().items()}
    c.require(report['budget'] == allocation and report['original_CI72'] == stats.original_CI72(),
              'joint_budget_or_old_CI_changed')
    originals = {(r['identity']['workbook'], r['identity']['pulse_count']): r for r in c.input_records()}
    records = report['records']
    c.require(type(records) is list and len(records) == 24, 'public_family_incomplete')
    keys = [(r['identity']['workbook'], r['identity']['pulse_count']) for r in records]
    c.require(len(set(keys)) == 24 and set(keys) == set(originals), 'public_family_repeated_or_foreign')
    features = c.configuration()['conditional_features']
    for key, r in zip(keys, records):
        original = originals[key]
        literal_int(r['identity']['pulse_count'], 1)
        literal_int(r['total_trials'], 1)
        c.require(r['identity'] == original['identity'] and r['total_trials'] == original['total_trials']
                  and len(r['setting_trials']) == len(r['counts']) == len(r['conditional']) == 4,
                  'public_identity_or_complete_exposure_changed')
        for setting in range(4):
            literal_int(r['setting_trials'][setting], 1)
            c.require(len(r['counts'][setting]) == 4, 'four_outcomes_required')
            for count in r['counts'][setting]:
                literal_int(count)
            c.require(r['counts'][setting] == original['counts'][setting]
                      and r['setting_trials'][setting] == sum(r['counts'][setting]) == original['setting_trials'][setting]
                      and len(r['conditional'][setting]) == 6, 'setting_exposure_or_event_inventory_changed')
            events = c.conditional_events(r['counts'][setting])
            for j, feature in enumerate(r['conditional'][setting]):
                literal_int(feature['count'])
                literal_int(feature['trials'], 1)
                c.require(feature['feature'] == features[j] and feature['count'] == events[j]
                          and feature['trials'] == r['setting_trials'][setting], 'conditional_source_event_changed')
                packet = feature['interval']
                c.require(all(type(packet[name]) is str for name in ('exact_lower', 'exact_upper')),
                          'exact_rational_confidence_endpoints_required')
                lo, hi = stats.endpoints(packet)
                c.require(lo <= hi and lo <= 1 and hi >= 0, 'conditional_probability_domain_changed')
        contrast = r['contrast']
        literal_int(contrast['win_count'])
        literal_int(contrast['loss_count'])
        c.require(contrast['win_count'] == r['counts'][0][0]
                  and contrast['loss_count'] == r['counts'][1][1] + r['counts'][2][2] + r['counts'][3][0],
                  'contrast_outcome_mapping_changed')
        root = contrast['h_bracket']
        c.require(root['lower_rejected'] is True and root['upper_not_rejected'] is True
                  and -1 <= F(root['lower']) < F(root['upper']) <= 1, 'source_cut_qualification_changed')
    return report


def kernel_consume():
    path = HERE / 'kernel-certification-first.json'
    c.frozen(path)
    report = json.loads(path.read_text())
    c.require(report['schema'] == 'p23-source-compression-kernel-certification/v1'
              and report['version'] == c.VERSION and report['evidence_valid'] is True
              and all(report[name] is True for name in ('support_is_exact_and_attained',
                  'all_N_source_normalized_bet_kernel_certified', 'all_six_source_conditional_features_kernel_certified',
                  'positive_cut_requires_generated_source_support'))
              and report['new_stochastic_process_or_Ville_kernel'] is False
              and report['controller_advance'] is False and report['numerical_producers_executed'] == 0,
              'invalid_source_kernel_certificate')
    for row in report['bindings']:
        stats.binding_check(row)
    c.require(report['owned_declarations'] == len(report['all_owned_axioms'])
              and all(set(v) <= {'propext', 'Classical.choice', 'Quot.sound'} for v in report['all_owned_axioms'].values()),
              'source_kernel_axiom_inventory_changed')
    ct = c.module('_sc_reuse_CT', HERE.parent / 'contrast-source/certify.py')
    c.require(report['reused_CT_certificate'] == ct.fastconsume(), 'original_source_law_binding_changed')
    return report


def domain_consumer():
    return c.module('_sc_checked_domain', HERE / 'domain_verify.py').consume()


def generate():
    statistical = validate_statistics(stats.consume())
    kernel = kernel_consume()
    domain = domain_consumer()
    c.require(domain['evidence_valid'] is True and domain['complete_source_outer_cover_certified'] is True
              and domain['new_constraints_checked'] is True and domain['nonempty_source_fibre_exhibited'] is True
              and domain['all_72_original_CI_preserved'] is True and domain['uniform_CH_N5_lower_bound_certified'] is True,
              'source_domain_not_certified')
    bindings = [c.frozen(HERE / name) for name in ('criterion.md', 'sources.json', 'verify.py', 'statistics_verify.py',
        'statistics-cross-verification.json', 'kernel-certification-first.json', 'domain_verify.py', 'domain-verification.json')]
    return {'schema': SCHEMA, 'version': c.VERSION, 'evidence_valid': True,
            'status': 'certified_public_source_domain_compression', 'bindings': bindings,
            'budget': statistical['budget'], 'source_summary': domain['source_summary'],
            'uniform_CH_N5_lower_bound': domain['uniform_CH_N5_lower_bound'],
            'source_kernel_owned_declarations': kernel['owned_declarations'],
            **{name: True for name in POSITIVE}, **{name: False for name in NEGATIVE},
            'conditional_source_law_required': True, 'spacelike_public_family_size': 24,
            'bell_event_files_read': 0, 'new_science_executed_at_intake': 0}


def consume(certificate_path=None, disabled=False):
    empty = {'schema': SCHEMA, 'version': c.VERSION, 'evidence_valid': False,
             **{name: False for name in (*POSITIVE, *NEGATIVE)}, 'new_science_executed_at_intake': 0}
    if disabled:
        return {**empty, 'status': 'disabled'}
    canonical = HERE / 'source-compression-verification.json'
    c.frozen(canonical)
    path = canonical if certificate_path is None else Path(certificate_path)
    c.require(path.read_bytes() == canonical.read_bytes(), 'lookalike_source_compression_certificate')
    result = json.loads(path.read_text())
    for row in result['bindings']:
        stats.binding_check(row)
    c.require(result['schema'] == SCHEMA and result['version'] == c.VERSION and result['evidence_valid'] is True
              and all(result[name] is True for name in POSITIVE)
              and all(result[name] is False for name in NEGATIVE), 'source_compression_scope_changed')
    fresh = generate()
    c.require(fresh == result, 'source_compression_consumer_result_changed')
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check-only', action='store_true')
    parser.add_argument('--certificate', type=Path)
    parser.add_argument('--disabled', action='store_true')
    args = parser.parse_args()
    if args.check_only or args.disabled:
        result = consume(args.certificate, args.disabled)
    else:
        c.require(args.output is not None and not args.output.exists(), 'new_source_certificate_required')
        result = generate()
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
