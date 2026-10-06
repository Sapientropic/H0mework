"""Consume the exact theory lock, kernel provenance, and two frozen mathematical firsts."""
import argparse
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import sys

import capabilities
import constructor
import kernel_certify

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
CERTIFICATE = HERE / 'verification.json'
SCHEMA = 'stage10-theory-blind-evidence/v1'
POSITIVE = ('evidence_valid', 'blind_by_construction_certified', 'blind_theory_prediction_certified',
            'complete_Born_probability_family_certified', 'same_original_source_current_next_certified',
            'uniform_XZ_Tsirelson_bound_certified', 'fixed_theory_settings_saturate_Tsirelson',
            'exact_full_source_matrix_cross_certified', 'exact_Qsqrt2_export_bridge_certified')
NEGATIVE = ('empirical_parameters_used', 'human_outcome_unexposed_claimed',
            'real_instrument_empirical_verdict_executed', 'actual_hardware_identity_claimed',
            'apparatus_optimum_verified', 'controller_advance')
COUNTS = ('constructor_empirical_argument_count', 'constructor_external_resource_count',
          'public_statistical_dependency_count', 'new_public_statistical_tables_read',
          'trial_event_files_read', 'new_science_executed_at_intake')
PROGRAMS = ('criterion.md', 'sources.json', 'constructor.py', 'capabilities.py', 'produce.py',
            'independent_born.py', 'test_independent_born.py', 'verify.py')


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False)


def frozen(path):
    relative = path.relative_to(ROOT).as_posix()
    payload = path.read_bytes()
    run = subprocess.run(['git', 'show', 'HEAD:' + relative], cwd=ROOT,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30, check=True)
    require(run.stdout == payload, 'unfrozen_input:' + relative)
    return payload


def binding(path):
    relative = path.relative_to(ROOT).as_posix()
    payload = frozen(path)
    blob = subprocess.check_output(['git', 'rev-parse', 'HEAD:' + relative], cwd=ROOT, timeout=30).decode().strip()
    return {'path': relative, 'git_blob': blob, 'sha256': digest(payload)}


def exact(value):
    require(type(value) is dict and set(value) == {'r', 's'}, 'quadratic_field_schema_changed')
    for key in ('r', 's'):
        require(type(value[key]) is str and str(Fraction(value[key])) == value[key],
                'noncanonical_or_inexact_coefficient')
    return constructor.Q2(Fraction(value['r']), Fraction(value['s']))


def table(records):
    require(type(records) is list and len(records) == 32, 'incomplete_probability_carrier')
    result = {}
    for row in records:
        require(type(row) is dict, 'invalid_probability_record')
        require(all(type(row.get(name)) is bool for name in ('herald', 'outcome_a', 'outcome_b')),
                'nonliteral_bit_label')
        require(all(type(row.get(name)) is int and row[name] in (0, 1)
                    for name in ('setting_a', 'setting_b')), 'nonliteral_setting_label')
        key = tuple(row[name] for name in ('herald', 'setting_a', 'setting_b', 'outcome_a', 'outcome_b'))
        require(key not in result, 'duplicate_probability_record')
        result[key] = exact(row['probability'])
    expected = set(itertools.product((False, True), (0, 1), (0, 1), (False, True), (False, True)))
    require(set(result) == expected, 'foreign_or_missing_probability_record')
    return result


def validate_firsts(primary, independent):
    require(primary.get('schema') == 'stage10-theory-blind-first/v1'
            and primary.get('status') == 'generated_exact_theory_prediction', 'primary_first_schema_changed')
    for name in ('empirical_parameters_used', 'human_outcome_unexposed_claimed',
                 'real_instrument_empirical_verdict_executed', 'controller_advance'):
        require(primary.get(name) is False, 'primary_scope_promoted:' + name)
    for name in ('new_public_statistical_tables_read', 'trial_event_files_read'):
        require(type(primary.get(name)) is int and primary[name] == 0, 'primary_access_count_changed')
    capability = capabilities.certify_constructor((HERE / 'constructor.py').read_text())
    capabilities.require_nullary(constructor.build_prediction)
    require(canonical(primary['capability_check']) == canonical(capability), 'constructor_capability_receipt_changed')
    require(canonical(primary['prediction']) == canonical(constructor.build_prediction()), 'primary_prediction_not_generated_by_constructor')
    for item in primary['source_bindings']:
        require(item == binding(ROOT / item['path']), 'primary_source_binding_changed')
    require(independent.get('schema') == 'stage10-theory-blind-independent-born/v1'
            and independent.get('status') == 'verified_full_source_spectral_contraction'
            and type(independent.get('dimension')) is int and independent['dimension'] == 8,
            'independent_full_source_schema_changed')
    scope = independent['scope']
    for name in ('mathematical_matrix_cross', 'fixed_setting_theoretical_prediction'):
        require(scope.get(name) is True, 'independent_math_scope_lost')
    for name in ('source_phase_uniform_proof_supplied_by_finite_controls', 'empirical_parameters_used',
                 'real_instrument_empirical_verdict_executed', 'controller_advance'):
        require(scope.get(name) is False, 'independent_scope_promoted')
    for name in ('public_statistical_tables_read', 'trial_event_files_read'):
        require(type(scope.get(name)) is int and scope[name] == 0, 'independent_access_count_changed')
    checks = independent['checks']
    require(type(checks.get('spectral_projection_count')) is int and checks['spectral_projection_count'] == 32,
            'full_spectral_carrier_changed')
    require(type(checks.get('normalized_distribution_count')) is int and checks['normalized_distribution_count'] == 8,
            'distribution_carrier_changed')
    for name in ('positive_gram_and_complement_checked', 'born_equals_projected_norm_sq_checked',
                 'local_half_marginals_checked', 'raw_aligned_reindexing_checked'):
        require(checks.get(name) is True, 'independent_source_check_lost')
    provenance = independent['provenance']
    for item in (provenance['criterion'], provenance['sources_manifest'],
                 *provenance['pure_theory_sources'], *provenance['scientific_programs']):
        require(item['sha256'] == binding(ROOT / item['path'])['sha256'], 'independent_source_binding_changed')
    raw = table(primary['prediction']['records'])
    aligned = table(primary['prediction']['aligned_records'])
    require(raw == table(independent['raw_records']), 'raw_Born_cross_disagrees')
    require(aligned == table(independent['aligned_records']), 'aligned_Born_cross_disagrees')
    for (herald, a, b, x, y), probability in raw.items():
        require(probability.sign() >= 0 and (constructor.lift(1) - probability).sign() >= 0,
                'nonphysical_probability')
        require(aligned[herald, a, b, x ^ (herald and a == 1), y] == probability,
                'herald_correction_not_source_generated')
        require(aligned[herald, a, b, x, y] == raw[False, a, b, x, y], 'aligned_source_tables_differ')
    for herald, a, b in itertools.product((False, True), (0, 1), (0, 1)):
        require(sum(raw[herald, a, b, x, y] for x, y in itertools.product((False, True), repeat=2)) == constructor.lift(1),
                'distribution_not_normalized')
        for x in (False, True):
            require(sum(raw[herald, a, b, x, y] for y in (False, True)) == constructor.lift(Fraction(1, 2)),
                    'Alice_marginal_not_half')
        for y in (False, True):
            require(sum(raw[herald, a, b, x, y] for x in (False, True)) == constructor.lift(Fraction(1, 2)),
                    'Bob_marginal_not_half')
    scores = []
    for herald in (False, True):
        correlations = [sum(constructor.sign(x)*constructor.sign(y)*raw[herald, a, b, x, y]
                            for x, y in itertools.product((False, True), repeat=2))
                        for a, b in itertools.product((0, 1), repeat=2)]
        score = -correlations[0]-correlations[1]-constructor.sign(herald)*correlations[2]+constructor.sign(herald)*correlations[3]
        require(score == constructor.Q2(Fraction(0), Fraction(2)) and (score-2).sign() > 0,
                'theoretical_CHSH_not_saturated')
        require(score == exact(primary['prediction']['chsh'][int(herald)]['value'])
                == exact(independent['herald_summaries'][int(herald)]['herald_corrected_chsh']),
                'CHSH_readout_does_not_commute')
        scores.append(score.encode())
    return {'raw_probability_records_checked': 32, 'aligned_probability_records_checked': 32,
            'full_source_dimension': 8, 'herald_CHSH': scores, 'constructor_capability_check': capability}


def generate():
    kernel = kernel_certify.consume()
    require(kernel.get('exact_Qsqrt2_export_bridge_certified') is True,
            'kernel_exact_export_bridge_missing')
    primary_path, independent_path = HERE / 'prediction-first.json', HERE / 'independent-first.json'
    checked = validate_firsts(json.loads(frozen(primary_path)), json.loads(frozen(independent_path)))
    return {'schema': SCHEMA, 'criterion_version': 'stage10-theory-blind-tb0001',
            'status': 'certified_blind_by_construction_theory_prediction',
            **{name: True for name in POSITIVE}, **{name: False for name in NEGATIVE},
            **{name: 0 for name in COUNTS},
            'source_identity': {'source': 'positiveSmoothUnifiedSource', 'visit': 10, 'current_tick': 16, 'next_tick': 17},
            'prediction_kind': 'source_native_mathematical_probability_law',
            'kernel_summary': {'owned_declaration_count': len(kernel['owned_declarations']),
                               'dependency_declaration_count': kernel['dependency_declaration_count'],
                               'axioms': kernel['axiom_union']},
            **checked,
            'source_bindings': [binding(HERE / name) for name in PROGRAMS],
            'first_bindings': [binding(path) for path in (primary_path, independent_path,
                                                        HERE / 'kernel-certification-first.json')]}


def validate_scope(report):
    require(report.get('schema') == SCHEMA and report.get('criterion_version') == 'stage10-theory-blind-tb0001'
            and report.get('status') == 'certified_blind_by_construction_theory_prediction', 'blind_certificate_schema_changed')
    require(all(report.get(name) is True for name in POSITIVE), 'blind_certificate_positive_scope_lost')
    require(all(report.get(name) is False for name in NEGATIVE), 'blind_certificate_scope_promoted')
    require(all(type(report.get(name)) is int and report[name] == 0 for name in COUNTS), 'blind_certificate_literal_counts_changed')


def consume(certificate_path=None, disabled=False):
    if disabled is True:
        return {'schema': SCHEMA, 'status': 'disabled_by_override',
                **{name: False for name in (*POSITIVE, *NEGATIVE)}}
    require(disabled is False, 'invalid_disable_selection')
    original = frozen(CERTIFICATE)
    supplied = original if certificate_path is None else Path(certificate_path).read_bytes()
    require(supplied == original, 'blind_certificate_override_changed_frozen_bytes')
    report = json.loads(supplied)
    validate_scope(report)
    require(canonical(report) == canonical(generate()), 'blind_certificate_current_source_or_scope_changed')
    return report


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check-only', action='store_true')
    parser.add_argument('--certificate', type=Path)
    parser.add_argument('--out', type=Path, default=CERTIFICATE)
    args = parser.parse_args()
    try:
        if args.check_only:
            report = consume(args.certificate)
        else:
            require(args.certificate is None, 'certificate_override_is_intake_only')
            report = generate()
            with args.out.open('x', encoding='utf-8') as output:
                json.dump(report, output, ensure_ascii=False, indent=2)
                output.write('\n')
        print(json.dumps(report, ensure_ascii=False))
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print(json.dumps({'schema': SCHEMA, 'status': 'invalid_theory_blind_evidence',
                          'evidence_valid': False, 'blind_theory_prediction_certified': False,
                          'reason': str(error)}))
        return 1


if __name__ == '__main__':
    sys.exit(main())
