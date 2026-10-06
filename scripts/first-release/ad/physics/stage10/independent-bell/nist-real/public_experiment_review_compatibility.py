#!/usr/bin/env python3
"""Consume frozen public science across certified independent library registrations."""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PUB = HERE / 'nominal-replay/public-review'
ROOT = next(p for p in HERE.parents if (p / '.git').exists())


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    sys.modules[name] = result
    spec.loader.exec_module(result)
    return result


legacy = load_module('_p23_frozen_public_intake', HERE / 'public_experiment_review.py')


def strict_equal(left, right):
    return json.dumps(left, sort_keys=True, separators=(',', ':'), allow_nan=False) == \
           json.dumps(right, sort_keys=True, separators=(',', ':'), allow_nan=False)


def validate_registry(profile, kind):
    common = {'registry_changed', 'independent_registrations',
              'non_registry_options_unchanged', 'original_registrations_unchanged'}
    extra = {'current_environment_fresh_kernel_check_claimed', 'current_lakefile_sha256',
             'historical_lakefile_binding', 'semantic_import_sources_unchanged'} if kind == 'heralding' else set()
    legacy.require(type(profile) is dict and set(profile) == common | extra, 'unknown_registry_attestation_fields')
    legacy.require(type(profile['registry_changed']) is bool
                   and profile['non_registry_options_unchanged'] is True
                   and profile['original_registrations_unchanged'] is True, 'unpaid_registry_noninterference')
    if kind == 'heralding':
        legacy.require(profile['current_environment_fresh_kernel_check_claimed'] is False
                       and profile['semantic_import_sources_unchanged'] is True
                       and type(profile['current_lakefile_sha256']) is str
                       and len(profile['current_lakefile_sha256']) == 64, 'changed_heralding_proof_environment_scope')
    registrations = profile['independent_registrations']
    legacy.require(type(registrations) is list, 'malformed_independent_registrations')
    legacy.require(profile['registry_changed'] is bool(registrations), 'inconsistent_registry_attestation')
    names = []
    for item in registrations:
        legacy.require(type(item) is dict and set(item) == {'name', 'srcDir', 'roots'}
                       and type(item['name']) is str and item['name']
                       and type(item['srcDir']) is str and item['srcDir']
                       and type(item['roots']) is list and item['roots']
                       and all(type(r) is str and r for r in item['roots'])
                       and len(set(item['roots'])) == len(item['roots']), 'malformed_independent_library')
        names.append(item['name'])
    legacy.require(len(set(names)) == len(names), 'repeated_independent_library')
    # The fixed CT/HB consumers pay actual source closure and registration noninterference.
    dynamic = {'independent_registrations'} | ({'current_lakefile_sha256'} if kind == 'heralding' else set())
    return {k: v for k, v in profile.items() if k not in dynamic}


def compare_registry(old, current, kind='contrast'):
    legacy.require(strict_equal(validate_registry(old, kind), validate_registry(current, kind)),
                   'historical_registry_or_proof_scope_changed')
    return current


def compare_source_kernel(old, current):
    legacy.require(type(old) is dict and type(current) is dict
                   and old.get('evidence_valid') is True and current.get('evidence_valid') is True,
                   'uncertified_current_source_kernel')
    attestation = compare_registry(old['lake_registry'], current['lake_registry'])
    legacy.require(strict_equal({k: v for k, v in old.items() if k != 'lake_registry'},
                                {k: v for k, v in current.items() if k != 'lake_registry'}),
                   'source_kernel_science_or_identity_changed')
    return attestation


def prefix_reader():
    module = load_module('_p23_prefix_library_compat', PUB / 'prefix_review.py')
    canonical = PUB / 'original-source-review.json'
    legacy.frozen(canonical)
    report = json.loads(canonical.read_text())
    original = report['source_contrast_kernel']
    current = module.kernel_review()
    attestation = compare_source_kernel(original, current)
    # Supply the same certified proof at its recorded environment; its live attestation is separate.
    module.kernel_review = lambda: original
    result = module.consume(certificate_path=canonical)
    legacy.require(result['evidence_valid'] is True, 'prefix_science_does_not_reverify')
    return {**result, 'name': 'original_source_statistical_review', 'review_completed': True}, attestation


def anytime_reader():
    module = load_module('_p23_anytime_library_compat', PUB / 'anytime-source/consume.py')
    canonical = PUB / 'anytime-source/certification.json'
    legacy.frozen(canonical)
    report = json.loads(canonical.read_text())
    original = report['source_law']
    current = module.source_law()
    attestation = compare_source_kernel(original, current)
    module.source_law = lambda: original
    result = module.consume(certificate_path=canonical)
    legacy.require(result['evidence_valid'] is True, 'anytime_science_does_not_reverify')
    return {**result, 'name': 'cut_free_public_source_signature', 'review_completed': True}, attestation


def consume(certificate_path=None, disabled=False):
    rejected = {'schema': 'p23-complete-public-experiment-review-evidence/v1', 'evidence_valid': False,
                'public_review_completed': False, 'public_statistical_source_signature_certified': False,
                'apparatus_optimum_verified': False, 'disabled': disabled}
    if disabled:
        return {**rejected, 'reason': 'explicitly_disabled'}
    try:
        canonical = PUB / 'complete-review-final.json'
        binding = legacy.frozen(canonical)
        candidate = canonical if certificate_path is None else Path(certificate_path)
        legacy.require(candidate.read_bytes() == canonical.read_bytes(), 'unbound_or_lookalike_public_review_certificate')
        report = json.loads(canonical.read_text())
        legacy.require(report['schema'] == 'p23-complete-public-experiment-review/v1'
                       and report['public_review_completed'] is True, 'historical_review_not_complete')
        for row in report['bindings'] + [report['public_source_roles']]:
            legacy.require(legacy.digest(ROOT / row['path']) == row['sha256'], 'completed_review_source_changed')
        legacy.require(strict_equal(legacy.verify_source_roles(), report['public_source_roles']), 'public_roles_changed')
        names = [name for name in legacy.READERS if name not in
                 {'original_source_statistical_review', 'cut_free_public_source_signature'}]
        with ThreadPoolExecutor(max_workers=3) as pool:
            current = dict(zip(names, pool.map(legacy.reader, names)))
        prefix, prefix_registry = prefix_reader()
        anytime, anytime_registry = anytime_reader()
        current.update(original_source_statistical_review=prefix, cut_free_public_source_signature=anytime)
        attestations = {'original_source_statistical_review': prefix_registry,
                        'cut_free_public_source_signature': anytime_registry}
        for name, row in current.items():
            expected = report['reviews'][name]
            if name == 'heralding_source_law':
                legacy.require(row.get('evidence_valid') is True, 'heralding_law_not_verified')
                attestations[name] = compare_registry(expected['lake_registry'], row['lake_registry'], 'heralding')
                row = {**row, 'lake_registry': expected['lake_registry']}
            legacy.require(strict_equal(row, expected), 'public_science_or_scope_changed:' + name)
        nominal = report['nominal_replay']
        legacy.verify_nominal_binding_tree(nominal['bindings'])
        legacy.verify_nominal_storage(nominal['bindings'])
        legacy.require(nominal['evaluator']['sha256'] == legacy.digest(HERE / 'nominal_environment_optimum.py')
                       and nominal['evidence_valid'] is True
                       and nominal['status'] == 'certified_deviation_exceeds_predeclared_band', 'nominal_verdict_changed')
        return {**rejected, 'evidence_valid': True, 'public_review_completed': True,
                'public_statistical_source_signature_certified': report['public_statistical_source_signature_certified'],
                'decision': report['decision'], 'source': binding, 'reviews': report['reviews'],
                'new_external_data_dependency': False, 'actual_hardware_identity_claimed': False,
                'original_CI_modified': False, 'hidden_cut_log_required_for_public_signature': False,
                'nominal_continuous_count_model_accepted': False,
                'reason': 'complete_source_driven_public_claim_review',
                'independent_registry_compatibility_verified': True,
                'current_registry_attestations': attestations,
                'compatibility_consumer': legacy.frozen(__file__),
                'new_source_solver_or_Fock_execution': False}
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        return {**rejected, 'reason': str(error)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check-only', action='store_true')
    parser.add_argument('--certificate', type=Path)
    parser.add_argument('--disabled', action='store_true')
    args = parser.parse_args()
    result = consume(args.certificate, args.disabled)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result['evidence_valid'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
