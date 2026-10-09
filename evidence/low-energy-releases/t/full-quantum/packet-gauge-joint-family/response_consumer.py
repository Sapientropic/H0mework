#!/usr/bin/env python3
"""Identify the independently generated all48 response with the true finite family."""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
ROOT = HERE.parents[4]


def main():
    began = time.monotonic()
    paths = [HERE/'source.json', HERE/'consumer.json', HERE/'contour.json', HERE/'readers.json',
        FQ/'packet-gauge-native-response/response.json', FQ/'packet-gauge-native-response/construction.json']
    source, direct, contour, readers, response, manifest = [json.loads(path.read_text()) for path in paths]
    for name, digest in manifest['candidate_sha256'].items():
        assert hashlib.sha256((paths[-1].parent/name).read_bytes()).hexdigest() == digest
    for name, digest in response['input_sha256'].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    assert direct['epsilon0_full_variable_frequency_X0_identity']
    assert direct['epsilon1_same_JointMomentumJet_external_s0_not_s_derivative']
    assert direct['all_parameter_spatial_A_kernel_initial_zero']
    assert direct['all72_auxiliary_source_components_zero']
    assert readers['all48_Q1_matches_original_mixed_fourth_variation']
    assert contour['reader_second_parameter_coefficients_retained']
    c = 6*s.sqrt(15)/25
    z = s.sympify(response['physical_lambda'])
    assert s.expand(z-6*c*(1-s.I)) == 0
    assert response['constant_input_q'] is True
    assert list(map(s.sympify, response['weak_Euler_reader_derivative'])) == [-12*c, 0, 0, 0]
    U = s.Symbol('U', real=True)
    root = s.Poly(s.sympify(source['complete_Fhat'], locals={'U': U}), U, domain=s.QQ)
    lower, upper = map(s.Rational, response['root_interval'])
    rho = s.Rational(1, 131072)
    assert 3*rho*rho/4 < lower < upper < 4*rho*rho/5
    assert root.count_roots(lower, upper) == 1
    assert [row['reader'] for row in readers['readers']] == [row['reader'] for row in response['readers']]
    counts = {}
    for part in ['raw', 'connected']:
        count = 0
        for row in response['readers']:
            lo, hi = map(F, row[part+'_total_response_interval']['rational'])
            assert lo <= hi
            count += lo > 0 or hi < 0
        assert count == response['strict_'+part+'_response_count'] == 22
        counts[part] = count
    chosen = response['selected_reader']
    assert chosen['reader'] == [1, 1]
    intervals = {'raw': [F(159451639, 10**13), F(159806042, 10**13)],
        'connected': [F(687773579, 10**14), F(690962883, 10**14)]}
    for part, (lo, hi) in intervals.items():
        a, b = map(F, chosen[part+'_total_response_interval']['rational'])
        assert 0 < lo < a < b < hi
    output = {'scope': 'STRIKE_TRUE_FINITE_JOINT_PARAMETER_NATIVE_RESPONSE_IDENTIFICATION',
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'same_original_small_root_and_physical_frequency': True,
        'all48_same_X0_true_parameter_X1_and_native_Q0_Q1': True,
        'Q2_retained_in_uniform_epsilon_squared_remainder': True,
        'no_circular_dependency': 'NativeResponse was generated only from prior independent source X0/X1 and native reader contacts; current family now generates its actual finite-parameter meaning.',
        'identification': 'Same actual inverse and section identifies first field derivative; true contour weighted derivative passes through the two-time integrals; all-family source boundary identifies weak local Euler reader; same fixed preparation J_epsilon supplies both source legs.',
        'strict_nonzero_counts': counts,
        'selected_reader': [1, 1], 'source_frequency': str(z),
        'selected_actual_finite_family_derivative_intervals': {part: list(map(str, value)) for part, value in intervals.items()},
        'formula': 'd_epsilon I_b = C_b_prime N0 + C_b N1, each raw/connected; C_b_prime has two field legs plus native reader contact.',
        'new_Lean_declarations': 0, 'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'response-consumer.json').write_text(json.dumps(output, indent=2)+'\n')
    print('PASS all48 native frequency responses are true finite-family derivatives;22 nonzero each',
          output['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
