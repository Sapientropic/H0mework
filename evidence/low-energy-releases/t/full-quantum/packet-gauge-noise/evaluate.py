#!/usr/bin/env python3
"""Rigorous source-generated t=0 fixed-state gauge-noise intervals."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

import sympy as s

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('gauge_noise_intervals', HERE.parent/'packet-band-kernel/intervals.py')
intervals = importlib.util.module_from_spec(spec)
spec.loader.exec_module(intervals)
Box, F = intervals.Box, intervals.F


def main():
    source_path = HERE/'selected.json'
    mean_path = HERE.parent/'packet-current-hessian/integrals.json'
    source = json.loads(source_path.read_text())
    mean = json.loads(mean_path.read_text())
    mu = s.Symbol('mu', real=True)
    mu_box = Box(*mean['mean_zero']['rational'])

    def evaluate(expression):
        if expression == mu:
            return mu_box
        if expression.is_Rational:
            return Box(F(int(expression.p), int(expression.q)))
        if expression.is_Add:
            return sum((evaluate(term) for term in expression.args), Box(0))
        if expression.is_Mul:
            result = Box(1)
            for term in expression.args:
                result *= evaluate(term)
            return result
        if expression.is_Pow:
            base, power = expression.args
            if power == s.Rational(1, 2):
                return evaluate(base).sqrt()
            if power.is_Integer and power >= 0:
                return evaluate(base)**int(power)
        raise ValueError(expression)

    symbolic = {key: s.sympify(value, locals={'mu': mu})
        for key, value in source['normalized_reads_in_original_mu0'].items()}
    symbolic['noise_derivative'] = s.sympify(source['same_transfer_noise_derivative'], locals={'mu': mu})
    symbolic['variation_vector_norm_squared'] = s.sympify(source['centered_variation_norm_squared'], locals={'mu': mu})
    values = {key: evaluate(value) for key, value in symbolic.items()}
    assert values['mean'].hi < 0
    assert values['noise_derivative'].lo > 0
    assert values['variation_vector_norm_squared'].lo > 0
    assert s.simplify(symbolic['noise_derivative']-
        (symbolic['left_cross']+symbolic['right_cross']-2*mu*symbolic['mean'])) == 0
    assert s.simplify(symbolic['variation_vector_norm_squared']-
        (symbolic['variation_second']-symbolic['mean']**2)) == 0

    # All controls are against this exact original primitive and fixed state.
    dropped_centering = symbolic['left_cross']+symbolic['right_cross']
    center_error = evaluate(symbolic['noise_derivative']-dropped_centering)
    assert center_error.hi < 0
    lapse = Box(F(54, 125)).sqrt()
    wrong_density_error = (lapse-1)*values['noise_derivative']
    assert wrong_density_error.hi < 0
    mean_zero_error = values['mean']
    assert mean_zero_error.hi < 0

    receipt = {
        'scope': 'RIGOROUS_T0_FIXED_PREPARATION_SELECTED_PRIMITIVE_GAUGE_RESPONSE',
        'energy': 0, 'damping': 1, 'time': 0, 'both_transfers': [0, 0, 0],
        'primitive': 'A_epsilon=actualA+epsilon*a; a_mu=delta_mu1*S01',
        'fixed_state': source['fixed_state'],
        'source_inputs_sha256': {str(path.relative_to(HERE.parent)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [source_path, mean_path, HERE.parent/'packet-band-kernel/intervals.py']},
        'original_mean': mu_box.record(),
        'generated_intervals': {key: value.record() for key, value in values.items()},
        'controls': {
            'actual_minus_dropped_mean_variation': center_error.record(),
            'wrong_density_vertex_as_raw_minus_actual': wrong_density_error.record(),
            'actual_mean_variation_minus_assumed_zero': mean_zero_error.record(),
        },
        'no_new_halfline_integral': True,
        'normalization': 'The certified original ball mean is reused; no re-filtering, re-normalization or new state at epsilon.',
        'not_full_time_noise': 'This is the initial current/noise variation, not the complete noise at a complex external Laplace frequency.',
    }
    (HERE/'intervals.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print('PASS selected t=0 mu_prime', values['mean'].decimals(20),
        'noise_prime', values['noise_derivative'].decimals(20),
        'variation_norm_squared', values['variation_vector_norm_squared'].decimals(20), flush=True)


if __name__ == '__main__':
    main()
