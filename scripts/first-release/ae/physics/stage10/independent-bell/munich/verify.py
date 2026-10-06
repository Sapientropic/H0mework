"""Consume two frozen empirical firsts without opening or rescoring event archives."""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
SCHEMA = 'stage10-munich-adjudication-evidence/v1'
RUNS = ('2016-04-15', '2016-06-14')
COMPARISON_FIELDS = ('run', 'trials', 'contexts', 'four_outcomes', 'pooled_counts',
                     'components', 'terminal_e', 'max_e', 'max_prefix', 'first_crossing',
                     'first_crossing_e', 'prefix_e_sha256', 'alpha', 'threshold', 'status', 'token_dictionaries',
                     'local_audit', 'all_pair_records_scored')
PRIMARY_PATHS = ('criterion-mu0001.1.md', 'sources.json', 'source-methods.md', 'primary.py', 'schema.py', 'test_primary.py',
                 'invariant_independent.py', 'test_invariant_independent.py', 'verify.py', 'test_verify.py',
                 'format-repair-mu0001.1.json')
INDEPENDENT_PATHS = ('criterion-mu0001.1.md', 'sources.json', 'source-methods.md', 'schema.py', 'primary.py',
                     'invariant_independent.py', 'test_invariant_independent.py', 'verify.py', 'test_verify.py',
                 'format-repair-mu0001.1.json')
INDEPENDENT_FREEZE_PATHS = ('criterion-mu0001.1.md', 'sources.json', 'source-methods.md',
                            'invariant_independent.py', 'test_invariant_independent.py', 'format-repair-mu0001.1.json')


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def strict_json(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'duplicate_json_key')
            result[key] = value
        return result
    def invalid_constant(_):
        raise ValueError('nonfinite_json_constant')
    return json.loads(raw, object_pairs_hook=pairs, parse_constant=invalid_constant)


def canonical(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(',', ':'))


def binding(path):
    return {'path': str(path.relative_to(ROOT)), 'sha256': digest(path.read_bytes())}


def frozen(path):
    raw = path.read_bytes()
    saved = subprocess.run(['git', 'show', 'HEAD:' + str(path.relative_to(ROOT))],
                           cwd=ROOT, capture_output=True, check=False)
    require(saved.returncode == 0 and saved.stdout == raw, 'unfrozen_or_changed_artifact')
    return raw


def natural(value):
    return type(value) is int and value >= 0


def exact_summary(value):
    n, d = value.numerator, value.denominator
    require(value > 0, 'nonpositive_wealth')
    nb = n.to_bytes((n.bit_length() + 7) // 8, 'big')
    db = d.to_bytes((d.bit_length() + 7) // 8, 'big')
    exponent = n.bit_length() - d.bit_length()
    below = n < d * (1 << exponent) if exponent >= 0 else n * (1 << -exponent) < d
    exponent -= int(below)
    shift = 48 - exponent
    scaled_n, scaled_d = (n * (1 << shift), d) if shift >= 0 else (n, d * (1 << -shift))
    lower, remainder = divmod(scaled_n, scaled_d)
    return {'numerator_sha256': digest(nb), 'denominator_sha256': digest(db),
            'numerator_bits': n.bit_length(), 'denominator_bits': d.bit_length(),
            'dyadic': {'lower_mantissa': lower, 'upper_mantissa': lower + int(remainder != 0),
                       'exponent': exponent - 48}}


def bounds(summary):
    require(set(summary) == {'numerator_sha256', 'denominator_sha256', 'numerator_bits',
                             'denominator_bits', 'dyadic'}, 'exact_summary_shape')
    for name in ('numerator_bits', 'denominator_bits'):
        require(type(summary[name]) is int and summary[name] > 0, 'exact_integer_bits')
    for name in ('numerator_sha256', 'denominator_sha256'):
        require(isinstance(summary[name], str) and len(summary[name]) == 64
                and all(c in '0123456789abcdef' for c in summary[name]), 'exact_integer_digest')
    dyadic = summary['dyadic']
    require(set(dyadic) == {'lower_mantissa', 'upper_mantissa', 'exponent'}, 'dyadic_shape')
    lo, hi, exponent = (dyadic[x] for x in ('lower_mantissa', 'upper_mantissa', 'exponent'))
    require(all(type(x) is int for x in (lo, hi, exponent)) and
            (1 << 48) <= lo < (1 << 49) and hi in (lo, lo + 1), 'dyadic_range')
    unit = Fraction(1 << exponent) if exponent >= 0 else Fraction(1, 1 << -exponent)
    return lo * unit, hi * unit


def binary_wealth(counts):
    """The Jeffreys closed form, using factorials rather than prefix recurrence."""
    n0, n1 = counts
    require(natural(n0) and natural(n1), 'invalid_binary_counts')
    numerator = math.factorial(2 * n0) * math.factorial(2 * n1)
    denominator = ((1 << (n0 + n1)) * math.factorial(n0) * math.factorial(n1)
                   * math.factorial(n0 + n1))
    return Fraction(numerator, denominator)


def indexed(rows, axes, length):
    require(isinstance(rows, list) and len(rows) == 2 ** len(axes), 'incomplete_count_carrier')
    result = {}
    for row in rows:
        require(set(row) == set(axes) | {'counts'}, 'count_row_shape')
        key = tuple(row[a] for a in axes)
        require(all(type(x) is int and x in (0, 1) for x in key), 'invalid_context')
        require(key not in result, 'duplicate_context')
        counts = row['counts']
        require(isinstance(counts, list) and len(counts) == length
                and all(natural(n) for n in counts), 'invalid_counts')
        result[key] = counts
    require(set(result) == set(itertools.product(range(2), repeat=len(axes))), 'context_inventory')
    return result


def validate_run(run):
    total = run['trials']
    require(type(total) is int and total > 0, 'no_empirical_trial_verdict')
    require(run['alpha'] == '1/40' and run['threshold'] == '40', 'statistical_budget_changed')
    contexts = indexed(run['contexts'], ('h', 'a', 'b', 'c'), 2)
    joints = indexed(run['four_outcomes'], ('h', 'a', 'b'), 4)
    require(sum(sum(x) for x in contexts.values()) == total == sum(sum(x) for x in joints.values()),
            'event_accounting_changed')
    alice, bob = [0, 0], [0, 0]
    for key, counts in joints.items():
        require(contexts[key + (0,)] == [counts[0], counts[3]] and
                contexts[key + (1,)] == [counts[1], counts[2]], 'parity_projection_changed')
        alice[0] += counts[0] + counts[1]
        alice[1] += counts[2] + counts[3]
        bob[0] += counts[0] + counts[2]
        bob[1] += counts[1] + counts[3]
    require(canonical(run['pooled_counts']) == canonical({'alice': alice, 'bob': bob}), 'marginal_projection_changed')
    joint = math.prod((binary_wealth(counts) for counts in contexts.values()), start=Fraction(1))
    components = {'joint': joint, 'alice': binary_wealth(alice), 'bob': binary_wealth(bob)}
    require(canonical(run['components']) == canonical({k: exact_summary(v) for k, v in components.items()}),
            'terminal_component_closed_form_disagrees')
    terminal = sum(components.values()) / 3
    require(canonical(run['terminal_e']) == canonical(exact_summary(terminal)), 'terminal_mixture_closed_form_disagrees')
    lo, hi = bounds(run['max_e'])
    require(hi >= terminal and hi >= 1, 'prefix_maximum_impossible')
    peak, first = run['max_prefix'], run['first_crossing']
    require(natural(peak) and peak <= total, 'maximum_prefix_out_of_run')
    require(first is None or (type(first) is int and 1 <= first <= total), 'crossing_out_of_run')
    require(run['status'] == ('not_rejected' if first is None else 'rejected'), 'verdict_crossing_disagrees')
    require((first is None and lo < 40) or (first is not None and hi >= 40), 'threshold_disagrees')
    if first is None:
        require(run['first_crossing_e'] is None, 'unexecuted_crossing_wealth')
    else:
        crossing_lo, _ = bounds(run['first_crossing_e'])
        require(crossing_lo >= 40 and hi >= crossing_lo and peak >= first, 'crossing_wealth_disagrees')
    require(isinstance(run['prefix_e_sha256'], str) and len(run['prefix_e_sha256']) == 64,
            'missing_full_prefix_cross')
    dictionaries = run['token_dictionaries']
    require(set(dictionaries) == {'h', 'a', 'b', 'x', 'y'}, 'label_role_inventory')
    for values in dictionaries.values():
        require(isinstance(values, list) and 1 <= len(values) <= 2 and len(set(values)) == len(values)
                and all(isinstance(x, str) and x and x.isascii() and x == x.strip() for x in values)
                and values == sorted(values), 'noncanonical_binary_label_dictionary')
    audit = run['local_audit']
    require(type(audit['pair_records']) is int and audit['pair_records'] == total
            and run['all_pair_records_scored'] is True,
            'official_pairs_denominator_changed')
    require(audit['all_pairs_joined'] is True and audit['original_pair_order_preserved'] is True
            and audit['additional_outcome_selection'] is False, 'join_or_order_changed')
    offsets = audit['admissible_row_offset_pairs']
    require(isinstance(offsets, list) and 1 <= len(offsets) <= 4
            and all(isinstance(x, list) and len(x) == 2 and all(type(v) is int and v in (0, 1) for v in x)
                    for x in offsets) and len({tuple(x) for x in offsets}) == len(offsets), 'row_offset_inventory')
    candidates = audit['join_candidates']
    require(len(candidates) == len(offsets), 'incomplete_join_audit')
    for candidate, offset in zip(candidates, offsets):
        require(canonical([candidate['lab1_offset'], candidate['lab2_offset']]) == canonical(offset),
                'join_offset_identity')
        sizes = []
        for side in ('local1', 'local2'):
            local = candidate[side]
            require(all(natural(local[k]) for k in ('total_records', 'paired_records', 'unpaired_records'))
                    and local['paired_records'] == total
                    and local['total_records'] == total + local['unpaired_records'], 'local_row_accounting')
            sizes.append(local['total_records'])
        require(type(audit['record_lines_decoded']) is int
                and audit['record_lines_decoded'] == sum(sizes) + total, 'decode_accounting')
    return {'run': run['run'], 'trials': total, 'status': run['status'], 'first_crossing': first,
            'max_prefix': peak, 'max_e': run['max_e']['dyadic'], 'terminal_e': run['terminal_e']['dyadic'],
            'pooled_counts': run['pooled_counts'], 'prefix_e_sha256': run['prefix_e_sha256']}


def validate_firsts(primary, independent):
    require(primary.get('admission') == independent.get('admission') == 'admitted', 'archive_admission_failed')
    require(primary.get('version') == independent.get('version') == 'stage10-munich-mu0001.1', 'criterion_version_changed')
    require(primary.get('familywise_alpha') == independent.get('familywise_alpha') == '1/20', 'family_budget_changed')
    require(primary.get('scientific_adjudication_completed') is True and
            independent.get('scientific_adjudication_completed') is True, 'adjudication_not_executed')
    require(primary.get('real_instrument_empirical_verdict_executed') is True and
            independent.get('real_instrument_empirical_verdict_executed') is True,
            'empirical_execution_not_registered')
    p_scope, i_scope = primary['scope'], independent['scope']
    require(p_scope['contract'] == 'conditional_balanced_complement_all_unit_XZ_axes_both_heralds'
            and p_scope['nominal_instrument_transport_included'] is True, 'primary_null_contract_changed')
    for name in ('hardware_identity_validated', 'full_joint_validated', 'theory_validated', 'controller_advance'):
        require(p_scope[name] is False, 'primary_scope_promoted')
    for name in ('conditional_balanced_complement_instrument_contract', 'continuous_XZ_geometry_eliminated',
                 'actual_empirical_adjudication_executed'):
        require(i_scope[name] is True, 'independent_null_contract_changed')
    for name in ('empirical_parameters_used', 'encoding_selected_by_outcomes', 'full_joint_model_validated',
                 'underlying_theory_validated', 'hardware_identity_validated', 'source_theorem_changed',
                 'controller_advance'):
        require(i_scope[name] is False, 'independent_scope_promoted')
    checks = independent['checks']
    for name in ('independent_original_archive_parse', 'all_original_prefixes_scored',
                 'terminal_context_closed_form_checked'):
        require(checks[name] is True, 'independent_execution_check_lost')
    require(checks['primary_receipt_read'] is False, 'independent_read_primary_receipt')
    p_runs, i_runs = primary.get('runs'), independent.get('runs')
    require(isinstance(p_runs, list) and isinstance(i_runs, list) and len(p_runs) == len(i_runs) == 2,
            'complete_archive_family_required')
    require(tuple(x['run'] for x in p_runs) == tuple(x['run'] for x in i_runs) == RUNS, 'run_identity_changed')
    summaries = []
    for p_run, i_run in zip(p_runs, i_runs):
        require(canonical({k: p_run[k] for k in COMPARISON_FIELDS}) ==
                canonical({k: i_run[k] for k in COMPARISON_FIELDS}), 'independent_archive_or_prefix_cross_disagrees')
        summaries.append(validate_run(p_run))
    verdict = 'rejected' if any(r['status'] == 'rejected' for r in summaries) else 'not_rejected'
    require(primary.get('scientific_verdict') == independent.get('scientific_verdict') == verdict,
            'family_verdict_disagrees')
    require(type(i_scope['event_record_lines_decoded']) is int and
            i_scope['event_record_lines_decoded'] == sum(r['local_audit']['record_lines_decoded'] for r in p_runs),
            'independent_exposure_accounting_changed')
    return verdict, summaries


def validate_theory(sources):
    authority = sources['theory_authority']
    for name, value in {'source': 'positiveSmoothUnifiedSource', 'root_visit': 10,
                        'current_tick': 16, 'next_tick': 17, 'controller_advance': False,
                        'source_theorem_changed': False}.items():
        require(canonical(authority.get(name)) == canonical(value), 'original_source_identity_changed')
    require(len(authority['bindings']) == 13, 'theory_source_inventory_changed')
    for item in authority['bindings']:
        path = ROOT / item['path']
        require(path.is_relative_to(ROOT) and digest(frozen(path)) == item['sha256'], 'theory_source_changed')
    old = strict_json(frozen(HERE.parent / 'theory-blind/verification.json'))
    require(old['blind_theory_prediction_certified'] is True and
            old['complete_Born_probability_family_certified'] is True and
            old['same_original_source_current_next_certified'] is True, 'original_certification_missing')


def validate_provenance(report, names):
    provenance = report['provenance']
    paths = {str((HERE / name).relative_to(ROOT)) for name in names}
    blobs = provenance['scientific_path_git_blobs']
    require(set(blobs) == paths, 'incomplete_scientific_program_binding')
    head = provenance['execution_head']
    require(isinstance(head, str) and len(head) == 40 and all(c in '0123456789abcdef' for c in head),
            'invalid_execution_commit')
    for path, blob in blobs.items():
        saved = subprocess.run(['git', 'show', head + ':' + path], cwd=ROOT, capture_output=True, check=False)
        actual = subprocess.run(['git', 'hash-object', path], cwd=ROOT, text=True, capture_output=True, check=False)
        require(saved.returncode == actual.returncode == 0 and saved.stdout == frozen(ROOT / path)
                and actual.stdout.strip() == blob, 'scientific_program_changed_since_execution')
    epoch = subprocess.run(['git', 'log', '-1', '--format=%H', head, '--', *sorted(paths)],
                           cwd=ROOT, text=True, capture_output=True, check=False)
    require(epoch.returncode == 0 and epoch.stdout.strip() == provenance['last_scientific_path_commit'],
            'scientific_freeze_epoch_changed')


def validate_attempts(primary, independent):
    p_raw, i_raw = (frozen(HERE / name) for name in ('primary-attempt-mu0001.1.json', 'independent-attempt-mu0001.1.json'))
    p, i = strict_json(p_raw), strict_json(i_raw)
    require(primary['attempt_sha256'] == digest(p_raw) and independent['attempt_sha256'] == digest(i_raw),
            'first_attempt_identity_changed')
    require(p['schema'] == 'stage10-munich-primary-attempt/v1' and p['version'] == primary['version']
            and canonical(p['source_bindings']) == canonical(primary['source_bindings'])
            and canonical(p['provenance']) == canonical(primary['provenance'])
            and type(p['event_records_decoded_at_reservation']) is int
            and p['event_records_decoded_at_reservation'] == 0, 'primary_attempt_does_not_bind_first')
    require(i['schema'] == 'stage10-munich-independent-attempt/v1'
            and type(i['event_record_lines_decoded_before_attempt']) is int
            and i['event_record_lines_decoded_before_attempt'] == 0
            and canonical(i['program_bindings']) == canonical(independent['program_bindings']),
            'independent_attempt_does_not_bind_first')
    commit = i['freeze_commit']
    require(isinstance(commit, str) and 7 <= len(commit) <= 40
            and all(c in '0123456789abcdef' for c in commit), 'invalid_independent_freeze_commit')
    bindings = independent['program_bindings']
    expected_paths = {str((HERE / name).relative_to(ROOT)) for name in INDEPENDENT_FREEZE_PATHS}
    require(len(bindings) == len(expected_paths) and {row['path'] for row in bindings} == expected_paths,
            'incomplete_independent_freeze_binding')
    for row in bindings:
        require(row['freeze_commit'] == commit and binding(ROOT / row['path'])['sha256'] == row['sha256'],
                'independent_freeze_source_changed')
        saved = subprocess.run(['git', 'show', commit + ':' + row['path']], cwd=ROOT,
                               capture_output=True, check=False)
        require(saved.returncode == 0 and digest(saved.stdout) == row['sha256'], 'independent_freeze_not_committed')
    ancestor = subprocess.run(['git', 'merge-base', '--is-ancestor', commit,
                               independent['provenance']['execution_head']], cwd=ROOT,
                              capture_output=True, check=False)
    require(ancestor.returncode == 0, 'freeze_not_before_execution')


def generate():
    sources = strict_json(frozen(HERE / 'sources.json'))
    validate_theory(sources)
    primary = strict_json(frozen(HERE / 'primary-first-mu0001.1.json'))
    independent = strict_json(frozen(HERE / 'independent-first-mu0001.1.json'))
    verdict, runs = validate_firsts(primary, independent)
    validate_provenance(primary, PRIMARY_PATHS)
    validate_provenance(independent, INDEPENDENT_PATHS)
    validate_attempts(primary, independent)
    program_names = ('primary.py', 'schema.py', 'invariant_independent.py', 'verify.py')
    source_paths = [HERE / n for n in ('criterion-mu0001.1.md', 'sources.json', 'source-methods.md',
                                      'format-repair-mu0001.1.json', *program_names)]
    for report in (primary, independent):
        require(report['source_bindings']['sources_json_sha256'] == digest(frozen(HERE / 'sources.json')),
                'first_source_binding_changed')
        require(report['source_bindings']['criterion_sha256'] == digest(frozen(HERE / 'criterion-mu0001.1.md')),
                'first_criterion_binding_changed')
        expected_bindings = {'archive_bindings': sources['archives'], 'header_bindings': sources['headers'],
                             'metadata_access_commit': sources['metadata_access_commit'],
                             'header_access_commit': sources['header_access_commit'],
                             'theory_authority': sources['theory_authority']}
        require(canonical({k: report['source_bindings'][k] for k in expected_bindings}) ==
                canonical(expected_bindings), 'first_source_authority_changed')
    return {'schema': SCHEMA, 'criterion_version': 'stage10-munich-mu0001.1',
            'status': 'certified_public_instrument_adjudication', 'evidence_valid': True,
            'verdict': verdict, 'runs': runs, 'run_count': 2, 'familywise_alpha': '1/20',
            'pair_records_scored': sum(r['trials'] for r in runs),
            'public_instrument_adjudication_completed': True,
            'real_instrument_empirical_verdict_executed': True,
            'continuous_XZ_geometry_eliminated': True, 'independent_archive_cross_certified': True,
            'encoding_selected_by_outcomes': False, 'full_joint_model_certified': False,
            'source_theorem_changed': False, 'actual_hardware_identity_claimed': False,
            'apparatus_optimum_verified': False, 'controller_advance': False,
            'conditional_selected_instrument_contract_required': True,
            'new_science_executed_at_intake': 0, 'trial_event_files_read_at_intake': 0,
            'source_bindings': [binding(p) for p in source_paths],
            'first_receipts': [binding(HERE / n) for n in ('primary-first-mu0001.1.json', 'independent-first-mu0001.1.json')],
            'original_source_identity': sources['theory_authority'],
            'independent_implementations': ['prefix_joint_and_marginal_recurrence', 'context_odd_products_and_factorials']}


def consume(certificate=None):
    expected = generate()
    receipt = strict_json((HERE / 'verification.json' if certificate is None else Path(certificate)).read_bytes())
    require(canonical(receipt) == canonical(expected), 'certificate_does_not_match_fixed_consumer')
    return expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-only', action='store_true')
    parser.add_argument('--certificate', type=Path)
    args = parser.parse_args()
    try:
        result = consume(args.certificate) if args.check_only else generate()
        if not args.check_only:
            require(args.certificate is None, 'receipt_override_is_consume_only')
            with (HERE / 'verification.json').open('x', encoding='utf-8') as stream:
                json.dump(result, stream, indent=2, ensure_ascii=False)
                stream.write('\n')
        print(json.dumps(result, ensure_ascii=False))
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(json.dumps({'schema': SCHEMA, 'evidence_valid': False,
                          'public_instrument_adjudication_completed': False, 'reason': str(error)}))
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
