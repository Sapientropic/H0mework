#!/usr/bin/env python3
"""Independent rational statistics for complete setting exposures and source contrast."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
import importlib.util
import json
import lzma
import math
from pathlib import Path
import re
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / '.git').exists())
PUBLIC = HERE.parent
MW = PUBLIC / 'multi-window'
INPUTS = PUBLIC / 'public-summaries' / 'inputs.json'
VERSION = 'p23-public-source-compression-sc0001'
SCHEMA = 'p23-source-compression-statistics/v1'
CONTRACT_COMMIT = '3d3e32945a'
BOOKS = ('diag-02-54.xlsx', 'diag-03-43.xlsx', 'diag-19-45.xlsx',
         'diag-xor1.xlsx', 'diag-xor2.xlsx', 'diag-xor3.xlsx')
PULSES = {1: [6], 3: [5, 6, 7], 5: [4, 5, 6, 7, 8],
          7: [3, 4, 5, 6, 7, 8, 9], 9: [2, 3, 4, 5, 6, 7, 8, 9, 10]}
SHEETS = {1: '5', 3: '456', 5: '34567', 7: '2345678', 9: '123456789'}
FEATURES = ('both', 'onlyA', 'onlyB', 'neither', 'singleA', 'singleB')
_ARITH = None


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def frozen(path, commit=None):
    path = Path(path).resolve()
    require(path.is_relative_to(ROOT), 'foreign_source_compression_input')
    name = path.relative_to(ROOT).as_posix()
    if commit is None:
        commit = subprocess.check_output(['git', 'log', '-1', '--format=%H', '--', name],
                                        cwd=ROOT, text=True).strip()
    require(commit and subprocess.check_output(['git', 'show', commit + ':' + name], cwd=ROOT) == path.read_bytes(),
            'unfrozen_source_compression_source:' + name)
    subprocess.run(['git', 'merge-base', '--is-ancestor', commit, 'HEAD'], cwd=ROOT, check=True)
    return {'path': name, 'commit': commit, 'sha256': digest(path)}


def arithmetic():
    global _ARITH
    if _ARITH is None:
        spec = importlib.util.spec_from_file_location('_sc_independent_interval', MW / 'independent.py')
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        require(module.SCALE == 10 ** 60, 'independent_interval_precision_changed')
        _ARITH = module
    return _ARITH


def interval(lo=0, hi=None):
    return arithmetic().I(lo, hi)


def packet(value):
    return {'exact_lower': str(value.lo), 'exact_upper': str(value.hi)}


@lru_cache(maxsize=4096)
def log_one_plus(y):
    """Signed atanh series; each operation rounds outwards, including the tail."""
    y = F(y)
    require(F(-1, 2) <= y <= 1, 'log_one_plus_outside_reduced_domain')
    t = interval(y) / (2 + interval(y))
    square = t * t
    require(square.hi < 1, 'atanh_tail_not_geometric')
    total, power = interval(0), t
    for j in range(128):
        total += 2 * power / (2 * j + 1)
        power *= square
    magnitude = interval(max(abs(power.lo), abs(power.hi)))
    tail = 2 * magnitude / (257 * (1 - square))
    return interval(total.lo - (tail.hi if y < 0 else 0),
                    total.hi + (tail.hi if y > 0 else 0))


@lru_cache(maxsize=4096)
def logarithm(x):
    x = F(x)
    require(x > 0, 'nonpositive_logarithm')
    exponent = x.numerator.bit_length() - x.denominator.bit_length()
    reduced = x / F(2) ** exponent
    while reduced < 1:
        reduced *= 2
        exponent -= 1
    while reduced > 2:
        reduced /= 2
        exponent += 1
    return log_one_plus(reduced - 1) + exponent * log_one_plus(F(1))


@lru_cache(maxsize=4096)
def exp_small(x):
    x = F(x)
    require(abs(x) <= F(1, 2), 'exp_outside_small_Taylor_domain')
    value, term = interval(1), interval(1)
    for n in range(1, 49):
        term = term * x / n
        value += term
    radius = interval(abs(x))
    remainder = radius.power(49) / math.factorial(49) / (1 - radius / 50)
    return interval(value.lo - remainder.hi, value.hi + remainder.hi)


def exp_nonpositive(value):
    require(value.hi <= 0, 'positive_exponential_forbidden_in_log_mixture')
    steps, radius = 0, max(abs(value.lo), abs(value.hi))
    while radius > F(1, 2):
        radius /= 2
        steps += 1
    result = interval(max(0, exp_small(value.lo / 2 ** steps).lo),
                      exp_small(value.hi / 2 ** steps).hi)
    for _ in range(steps):
        result *= result
    return result


def log_interval(value):
    require(value.lo > 0, 'log_interval_touches_zero')
    return interval(logarithm(value.lo).lo, logarithm(value.hi).hi)


def configuration(inputs_path=None):
    bindings = [frozen(HERE / name, CONTRACT_COMMIT) for name in ('criterion.md', 'sources.json')]
    text = (HERE / 'criterion.md').read_text()
    blocks = re.findall(r'<!-- SOURCE-COMPRESSION-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- SOURCE-COMPRESSION-FROZEN-END -->', text, re.S)
    require(len(blocks) == 1, 'nonunique_source_compression_contract')
    cfg = json.loads(blocks[0])
    require(cfg['version'] == VERSION and cfg['alpha_total'] == '1/20' and cfg['old_CI_count'] == 72
            and cfg['old_inverse_delta'] == 2516505600 and cfg['old_bets_per_CI'] == 40
            and cfg['new_budget_split'] == '1/2' and cfg['epsilon'] == '3/1000'
            and cfg['public_family_size'] == 24 and cfg['spacelike_pulse_counts'] == [1, 3, 5, 7]
            and cfg['conditional_features'] == list(FEATURES) and cfg['setting_count'] == 4
            and cfg['bet_powers'] == [1, 20] and cfg['bisection_steps'] == 42
            and cfg['decimal_precision'] == 60 and cfg['rational_exp_terms'] == 48
            and cfg['rational_log_terms'] == 128 and cfg['source_workbook'] == 'diag-xor3.xlsx'
            and cfg['original_CI_modified'] is False and cfg['calibration_sigma_inserted_as_CI'] is False
            and cfg['actual_hardware_identity_claimed'] is False and cfg['bell_event_files_read'] == 0,
            'source_compression_contract_changed')
    manifest = json.loads((HERE / 'sources.json').read_text())
    require(manifest['version'] == VERSION, 'wrong_source_compression_manifest')
    for row in manifest['inputs']:
        path = ROOT / row['path']
        require(digest(path) == row['sha256'], 'source_compression_dependency_changed:' + row['path'])
        frozen(path, row['commit'])
    selected = INPUTS if inputs_path is None else Path(inputs_path)
    require(selected.read_bytes() == INPUTS.read_bytes(), 'lookalike_or_changed_public_input_override')
    bindings.extend(frozen(HERE / name) for name in ('independent.py', 'test_independent.py'))
    return cfg, json.loads(selected.read_text()), bindings


def budget(cfg):
    alpha = F(cfg['alpha_total'])
    old = F(cfg['old_CI_count'] * cfg['old_bets_per_CI'], cfg['old_inverse_delta'])
    remaining = alpha - old
    require(old == F(3, 80 * 32767) and remaining > 0, 'wrong_old_or_remaining_failure_budget')
    contrast = conditional = remaining / 2
    threshold = cfg['public_family_size'] / contrast
    inverse_delta = cfg['public_family_size'] * 4 * 6 * 40 / conditional
    return {'alpha_total': str(alpha), 'old_CI_failure_upper': str(old),
            'alpha_contrast': str(contrast), 'alpha_conditional': str(conditional),
            'contrast_threshold': str(threshold), 'conditional_inverse_delta': str(inverse_delta)}


def extract_records(inputs, prior):
    require(inputs['schema'] == 'p23-public-small-workbook-inputs/v1'
            and inputs['settings_order'] == ['ab', 'ab_prime', 'a_prime_b', 'a_prime_b_prime']
            and inputs['outcomes_order'] == ['++', '+0', '0+', '00'], 'wrong_public_count_order')
    books = inputs['diagnostic_workbooks']
    require(len(books) == 6 and {b['file'] for b in books} == set(BOOKS), 'changed_six_run_family')
    pmap = {run['workbook']: run for run in prior['runs']}
    require(len(pmap) == len(prior['runs']) == 6 and set(pmap) == set(BOOKS), 'changed_prior_count_family')
    by_book = {b['file']: b for b in books}
    records = []
    for name in BOOKS:
        book, old = by_book[name], pmap[name]
        require(digest(PUBLIC / 'public-summaries' / name) == book['sha256'], 'changed_original_workbook')
        groups = {g['pulse_count']: g for g in book['groups']}
        previous = {g['pulse_count']: g for g in old['groups']}
        require(len(groups) == len(book['groups']) == 5 and set(groups) == set(PULSES)
                and len(previous) == len(old['groups']) == 5 and set(previous) == set(PULSES),
                'missing_or_duplicate_public_window')
        for n in (1, 3, 5, 7):
            g, p = groups[n], previous[n]
            counts = g['counts']
            require(len(counts) == 4 and all(len(row) == 4 for row in counts)
                    and all(type(x) is int and x >= 0 for row in counts for x in row),
                    'incomplete_or_noninteger_public_outcomes')
            require(g['sheet'] == SHEETS[n] and g['paper_pulse_numbers'] == PULSES[n]
                    and g['cell_range'] == 'A1:P1', 'wrong_public_pulse_identity')
            exposures = [sum(row) for row in counts]
            total = sum(exposures)
            require(all(x > 0 for x in exposures), 'zero_setting_exposure')
            require(total == g['complete_trials_literal_count_sum'] == old['complete_trials']
                    and p['counts'] == counts and p['setting_trial_totals'] == exposures
                    and p['complete_trials'] == total and p['paper_pulse_numbers'] == PULSES[n],
                    'prior_full_count_or_exposure_mismatch')
            if name == 'diag-xor3.xlsx':
                require(total == 182137032 and exposures == [45544445, 45538661, 45527107, 45526819],
                        'old_prefix_or_lookalike_XOR3_exposure')
            records.append({'identity': {'workbook': name, 'pulse_count': n, 'pulse_indices': PULSES[n]},
                            'total_trials': total, 'setting_trials': exposures, 'counts': counts})
    require(len(records) == 24, 'missing_public_spacelike_record')
    return records


def retained_old_CI(prior, old_prefix):
    xor3 = next(run for run in prior['runs'] if run['workbook'] == 'diag-xor3.xlsx')
    result = []
    for group in xor3['groups']:
        for field in ('j', 'sA_cell', 'sB_cell'):
            for row, ci in enumerate(group['common_mean_confidence'][field]):
                lo, hi = F(ci['exact_lower']), F(ci['exact_upper'])
                require(0 <= lo <= hi <= 1, 'invalid_prior_CI')
                result.append({'identity': 'full_N' + str(group['pulse_count']), 'field': field,
                               'row': row, 'interval': {'exact_lower': ci['exact_lower'], 'exact_upper': ci['exact_upper']}})
    for field in ('j', 'sA_cell', 'sB_cell'):
        for row, ci in enumerate(old_prefix['common_mean_confidence'][field]):
            lo, hi = F(ci['exact_lower']), F(ci['exact_upper'])
            require(0 <= lo <= hi <= 1, 'invalid_old_prefix_CI')
            result.append({'identity': 'old_cut_N5', 'field': field, 'row': row,
                           'interval': {'exact_lower': ci['exact_lower'], 'exact_upper': ci['exact_upper']}})
    require(len(result) == 72, 'old_CI72_not_preserved')
    return result


def fixed_base_bets(wins, losses, epsilon=F(3, 1000)):
    require(type(wins) is int and type(losses) is int and wins >= 0 and losses >= 0,
            'invalid_contrast_counts')
    lo, hi = (1 - epsilon) ** 2 / 4, (1 + epsilon) ** 2 / 4
    rho, q0 = lo / hi, hi / (hi + lo)
    values = []
    for power in range(1, 21):
        f = F(1, 2 ** power)
        a, b = 1 + rho * f, 1 - f
        values.append({'power': power, 'a': str(a), 'b': str(b),
                       'base': wins * logarithm(a) + losses * logarithm(b)})
    return q0, values


def log_e_value(h, total, base):
    h = F(h)
    require(-1 <= h <= 1 and type(total) is int and total > 0, 'invalid_contrast_h_or_total')
    logs = [bet['base'] - total * log_one_plus(h / 2 ** bet['power']) for bet in base]
    shift = max(value.hi for value in logs)
    average = sum((exp_nonpositive(value - shift) for value in logs), interval(0)) / 20
    return shift + log_interval(average)


def contrast_bracket(total, base, threshold, steps=42):
    require(steps == 42 and F(threshold) > 1, 'changed_contrast_grid_or_threshold')
    log_threshold = logarithm(threshold)
    lower, upper = F(-1), F(1)
    lo_eval, hi_eval = log_e_value(lower, total, base), log_e_value(upper, total, base)
    require(lo_eval.lo > log_threshold.hi and hi_eval.hi <= log_threshold.lo,
            'contrast_root_initial_bracket_not_certified')
    ambiguous = False
    iterations = 0
    for _ in range(steps):
        midpoint = (lower + upper) / 2
        value = log_e_value(midpoint, total, base)
        if value.lo > log_threshold.hi:
            lower, lo_eval = midpoint, value
        elif value.hi <= log_threshold.lo:
            upper, hi_eval = midpoint, value
        else:
            ambiguous = True
            break
        iterations += 1
    return {'lower': str(lower), 'upper': str(upper), 'log_e_at_lower': packet(lo_eval),
            'log_e_at_upper': packet(hi_eval), 'log_threshold': packet(log_threshold),
            'lower_rejected': True, 'upper_not_rejected': True,
            'iterations': iterations, 'arithmetic_threshold_overlap': ambiguous}


def conditional_interval(count, trials, inverse_delta, bets=None, log_threshold=None):
    require(type(count) is int and type(trials) is int and trials > 0 and 0 <= count <= trials,
            'invalid_conditional_count_or_exposure')
    log_threshold = logarithm(inverse_delta) if log_threshold is None else log_threshold
    bets = [(F(sign, 2 ** power), exp_small(F(sign, 2 ** power)))
            for power in range(1, 21) for sign in (-1, 1)] if bets is None else bets
    lower, upper, grid = F(0), F(trials), []
    for lam, exponential in bets:
        value = (interval(lam * count) - log_threshold) / (exponential - 1)
        if lam > 0:
            lower = max(lower, value.lo)
        else:
            upper = min(upper, value.hi)
        grid.append({'lambda': str(lam), 'bound_expected_count': packet(value)})
    require(lower <= upper, 'conditional_CI_empty')
    return {'count': count, 'trials': trials, 'interval': packet(interval(lower / trials, upper / trials)),
            'grid40': grid}


def augment_record(record, bgt):
    rows, total = record['counts'], record['total_trials']
    wins, losses = rows[0][0], rows[1][1] + rows[2][2] + rows[3][0]
    q0, base = fixed_base_bets(wins, losses)
    contrast = {'win_count': wins, 'loss_count': losses, 'old_q0': str(q0),
                'fixed_bets20': [{k: value for k, value in bet.items() if k != 'base'}
                                 | {'base_log_e': packet(bet['base'])} for bet in base],
                'h_bracket': contrast_bracket(total, base, F(bgt['contrast_threshold']))}
    threshold = logarithm(F(bgt['conditional_inverse_delta']))
    bets = [(F(sign, 2 ** power), exp_small(F(sign, 2 ** power)))
            for power in range(1, 21) for sign in (-1, 1)]
    conditional = []
    for row, trials in zip(rows, record['setting_trials']):
        counts = row + [row[0] + row[1], row[0] + row[2]]
        conditional.append([{'feature': name, **conditional_interval(count, trials,
                            F(bgt['conditional_inverse_delta']), bets, threshold)}
                            for name, count in zip(FEATURES, counts)])
    return {**record, 'contrast': contrast, 'conditional': conditional}


def science(inputs_path=None):
    start = time.monotonic()
    cfg, inputs, bindings = configuration(inputs_path)
    prior = json.loads((MW / 'primary-first.json').read_text())
    old_prefix = json.loads((PUBLIC.parent / 'observable-prediction' / 'public-comparison-po0003.json').read_text())
    old_ci = retained_old_CI(prior, old_prefix)
    bgt = budget(cfg)
    records = []
    for record in extract_records(inputs, prior):
        records.append(augment_record(record, bgt))
        print(json.dumps({'independent_record': len(records), 'workbook': record['identity']['workbook'],
                          'N': record['identity']['pulse_count'],
                          'h_lower': records[-1]['contrast']['h_bracket']['lower']}, sort_keys=True), flush=True)
    return {'schema': SCHEMA, 'version': VERSION, 'implementation': 'independent', 'budget': bgt,
            'records': records, 'retained_old_CI72': old_ci, 'bindings': bindings,
            'arithmetic': {'interval_source': frozen(MW / 'independent.py'), 'decimal_precision': 60,
                           'signed_atanh_terms': 128, 'Taylor_exp_terms': 48,
                           'every_series_operation_outward_rounded': True,
                           'positive_large_exponentials_evaluated': False},
            'scope': {'source_conditional_snapshot_law_assumed': True, 'retrospective': True,
                      'settings_can_depend_on_past': True, 'source_stationarity_proved_from_counts': False,
                      'overlapping_windows_multiplied_as_independent': False, 'calibration_sigma_inserted_as_CI': False,
                      'original_CI_modified': False, 'source_tree_recomputed': False, 'Fock_recomputed': False,
                      'primary_new_program_or_outputs_read_before_first': False, 'bell_event_files_read': 0,
                      'actual_hardware_identity_claimed': False, 'controller_advance': False},
            'counts': {'records': 24, 'conditional_intervals': 576, 'conditional_bets': 23040,
                       'contrast_base_bets': 480, 'old_CI_retained': 72},
            'runtime_seconds': time.monotonic() - start}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--inputs', type=Path)
    args = parser.parse_args()
    storage = args.output.with_name(args.output.stem + '-storage.json')
    require(not args.output.exists() and not storage.exists(), 'immutable_independent_first_exists')
    require(args.output.suffix == '.xz', 'independent_first_must_use_lossless_xz')
    result = science(args.inputs)
    raw = (json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2, allow_nan=False) + '\n').encode()
    compressed = lzma.compress(raw, preset=6)
    args.output.write_bytes(compressed)
    metadata = {'schema': 'p23-source-compression-statistics-storage/v1', 'version': VERSION,
                'implementation': 'independent', 'logical_sha256': sha256(raw).hexdigest(),
                'logical_bytes': len(raw), 'compressed_sha256': sha256(compressed).hexdigest(),
                'compressed_bytes': len(compressed), 'program': frozen(__file__)}
    storage.write_text(json.dumps(metadata, ensure_ascii=False, sort_keys=True, indent=2) + '\n')
    print(json.dumps({'output': str(args.output), **metadata, 'counts': result['counts']},
                     ensure_ascii=False, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
