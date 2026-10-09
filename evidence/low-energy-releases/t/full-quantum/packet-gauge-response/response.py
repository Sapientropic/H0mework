#!/usr/bin/env python3
"""Consume the actual causal first variation and source double-time noise.

The two density jet slots retain their own Laplace variable.  This program
does not identify the double transform with the transform on the diagonal.
"""
from fractions import Fraction
from functools import lru_cache
import gzip
import hashlib
import json
from math import isqrt
from pathlib import Path
import sys
import time

import sympy as s

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
ROOT = HERE.parents[4]
sys.path.insert(0, str(FQ/'packet-gauge-bilocal'))
import hermitian as h

K, POLY, U = h.K, h.POLY, h.U
x = s.symbols('x', real=True)
c = 6*s.sqrt(15)/25
frequency = 5*(1-s.I)
normalized_frequency = h.scalar(25*s.sqrt(15)*(1-s.I)/18)
rho = s.Rational(1, 131072)
momentum = [21*s.sqrt(2)/13844480, 9*s.sqrt(2)/1730560,
            119*s.sqrt(2)/22151168]


@lru_cache(None)
def at_frequency(expr):
    if expr == x:
        return normalized_frequency
    if not expr.has(x):
        return h.scalar(expr)
    if expr.is_Add:
        return sum((at_frequency(term) for term in expr.args), K.zero)
    if expr.is_Mul:
        out = K.one
        for factor in expr.args:
            out *= at_frequency(factor)
        return out
    if expr.is_Pow and expr.exp.is_Integer:
        return at_frequency(expr.base)**int(expr.exp)
    raise AssertionError(('unexpected original frequency coefficient', expr))


def field(record):
    return h.matrix(*record['shape'], [(i, j, at_frequency(s.sympify(value, locals={'x': x})))
                                     for i, j, value in record['entries']])


def polynomial(expr):
    return POLY.from_dict({power: at_frequency(coefficient)
                          for power, coefficient in s.Poly(expr, U).terms()})


def add(left, right):
    return left[0]+right[0], left[1]+right[1]


def multiply(left, right):
    products = [a*b for a in left for b in right]
    return min(products), max(products)


def inverse(value):
    assert value[0]*value[1] > 0, ('interval crosses zero', value)
    return 1/value[1], 1/value[0]


def power(value, exponent):
    if exponent < 0:
        return power(inverse(value), -exponent)
    out = (Fraction(1), Fraction(1))
    while exponent:
        if exponent % 2:
            out = multiply(out, value)
        value = multiply(value, value)
        exponent //= 2
    return out


def root_interval(integer):
    scale = 10**90
    lower = isqrt(integer*scale*scale)
    assert lower*lower < integer*scale*scale < (lower+1)**2
    return Fraction(lower, scale), Fraction(lower+1, scale)


radical_intervals = {s.sqrt(2): root_interval(2), s.sqrt(15): root_interval(15),
                     s.sqrt(30): root_interval(30)}


@lru_cache(None)
def coefficient_interval(expr):
    if expr.is_Rational:
        value = Fraction(int(expr.p), int(expr.q))
        return value, value
    if expr in radical_intervals:
        return radical_intervals[expr]
    if expr.is_Add:
        out = (Fraction(0), Fraction(0))
        for term in expr.args:
            out = add(out, coefficient_interval(term))
        return out
    if expr.is_Mul:
        out = (Fraction(1), Fraction(1))
        for term in expr.args:
            out = multiply(out, coefficient_interval(term))
        return out
    if expr.is_Pow and expr.exp.is_Integer:
        return power(coefficient_interval(expr.base), int(expr.exp))
    raise AssertionError(('non-real source coefficient', expr))


def evaluate_interval(poly, interval):
    out = (Fraction(0), Fraction(0))
    for degree in range(poly.degree(), -1, -1):
        coefficient = poly.get((degree,), K.zero)
        assert h.conjugate(coefficient) == coefficient
        out = add(multiply(out, interval), coefficient_interval(K.to_sympy(coefficient)))
    return out


def decimal(value, lower, digits=32):
    scale = 10**digits
    integer = value.numerator*scale//value.denominator if lower else -(-value.numerator*scale//value.denominator)
    sign = '-' if integer < 0 else ''
    integer = abs(integer)
    return f'{sign}{integer//scale}.{integer%scale:0{digits}d}'


def interval_record(interval):
    return {'rational': list(map(str, interval)),
            'decimal_outward': [decimal(interval[0], True), decimal(interval[1], False)]}


def main():
    started = time.monotonic()
    paths = [FQ/'packet-gauge-causal/transfer.json.gz', FQ/'packet-gauge-causal/causal.json',
             FQ/'packet-gauge-causal/halfplane.json', FQ/'packet-gauge-bilocal/vertices.json',
             FQ/'packet-gauge-kernel/source.json', FQ.parent/'active-gauge/receipt.json',
             FQ/'packet-gauge-causal/source.json']
    transfer, causal, halfplane, vertices, source, original, causal_source = [json.loads(
        gzip.decompress(path.read_bytes()) if path.suffix == '.gz' else path.read_bytes()) for path in paths]
    assert transfer['all289_equations']
    assert causal['every_X0_and_X1_strictly_proper'] and causal['all289_variation_equations_paid']
    assert causal['H2_initial_X1_zero'] and causal['H1_initial_plus_H2_initial_derivative_equals_source_contact']
    assert hashlib.sha256(gzip.decompress(paths[0].read_bytes())).hexdigest() == causal['transfer_input_sha256']
    assert [s.sympify(value) for value in causal_source['physical_momentum']] == momentum
    assert halfplane['closed_safe_physical_halfplane'] == 'Re(lambda)>=5'
    assert s.simplify(sum(k*k for k in momentum)-2*rho*rho) == 0
    noise = halfplane['common_noise_consumer']
    assert s.sympify(noise['z']) == frequency and s.sympify(noise['w']) == frequency
    assert 2*rho*rho < s.Rational(noise['physical_transfer_radius'])**2
    noise0 = tuple(map(Fraction, noise['unvaried_interval']))
    noise1 = tuple(map(Fraction, noise['derivative_interval']))

    X, I1 = [field(transfer[key]) for key in ['X0', 'I1']]
    frequency_denominator = at_frequency(s.sympify(transfer['X1_frequency_denominator'], locals={'x': x}))
    assert frequency_denominator
    derivative = field(transfer['X1_numerator']).scalarmul(K.one/frequency_denominator)
    point = [frequency, *[s.I*k for k in momentum]]
    right = list(map(h.scalar, point))
    left = list(map(h.conjugate, right))
    H, H1 = h.operator(original['Fourier_Jacobi_entries'], point), h.operator(source['H1'], point)
    assert (H.matmul(derivative)+H1.matmul(X)-I1).is_zero_matrix
    Hbar = h.operator(original['Fourier_Jacobi_entries'], list(map(s.conjugate, point)))
    H1bar = h.operator(source['H1'], list(map(s.conjugate, point)))
    Xbar, derivative_bar = h.conjugate_matrix(X), h.conjugate_matrix(derivative)
    assert (Hbar.matmul(derivative_bar)+H1bar.matmul(Xbar)-h.conjugate_matrix(I1)).is_zero_matrix
    print('PASS actual new common-halfplane original289 response on both conjugate legs', flush=True)

    actual_factor = s.Poly(s.sympify(transfer['Fhat'], locals={'U': U}), U, domain=s.QQ)
    factor = polynomial(actual_factor.as_expr())
    lower, upper = 3*rho*rho/4, 4*rho*rho/5
    assert actual_factor.count_roots(lower, upper) == 1
    sign = s.sign(actual_factor.eval(lower))
    assert sign*actual_factor.eval(upper) < 0
    for _ in range(220):
        middle = (lower+upper)/2
        value = sign*actual_factor.eval(middle)
        assert value != 0
        if value > 0:
            lower = middle
        else:
            upper = middle
    interval = tuple(Fraction(int(value.p), int(value.q)) for value in [lower, upper])
    denominator = polynomial(s.sympify(transfer['theta_denominator'], locals={'x': x, 'U': U}))
    denominator_bar = POLY.from_dict({power: h.conjugate(value) for power, value in denominator.items()})
    modulus = (denominator_bar*denominator).rem(factor)
    assert modulus.gcd(factor).degree() == 0
    modulus_interval = evaluate_interval(modulus, interval)
    assert modulus_interval[0] > 0

    def pair(first, Q, second):
        coefficients = first.transpose().matmul(Q).matmul(second).to_dok()
        value = POLY.zero
        for (i, j), coefficient in coefficients.items():
            value += POLY.ground_new(coefficient/K.convert(2))*h.u**(i+j)
        return value.rem(factor)

    rows = []
    for reader in vertices['readers']:
        Q = h.bijet(reader['Q0_bijet'], left, right)
        Q1 = h.bijet(reader['Q1_bijet'], left, right)
        assert (Q-h.conjugate_matrix(Q).transpose()).is_zero_matrix
        current = pair(Xbar, Q, X)
        propagation = pair(derivative_bar, Q, X)+pair(Xbar, Q, derivative)
        contact = pair(Xbar, Q1, X)
        first = propagation+contact
        assert not contact
        for value in [current, first]:
            assert all(h.conjugate(coefficient) == coefficient for coefficient in value.values())
            if value:
                assert value.gcd(factor).degree() == 0
        current_interval = multiply(evaluate_interval(current, interval), inverse(modulus_interval)) if current else (Fraction(0), Fraction(0))
        first_interval = multiply(evaluate_interval(first, interval), inverse(modulus_interval)) if first else (Fraction(0), Fraction(0))
        propagation_contribution = multiply(first_interval, noise0)
        noise_contribution = multiply(current_interval, noise1)
        response = add(propagation_contribution, noise_contribution)
        baseline = multiply(current_interval, noise0)
        rows.append({'reader': reader['reader'], 'current_numerator': h.encode_poly(current),
            'propagator_first_variation_numerator': h.encode_poly(first),
            'direct_reader_contact_zero_on_actual_theta_input': True,
            'current_coefficient_interval': interval_record(current_interval),
            'propagator_variation_coefficient_interval': interval_record(first_interval),
            'unvaried_induced_current_interval': interval_record(baseline),
            'propagator_contribution_interval': interval_record(propagation_contribution),
            'noise_contribution_interval': interval_record(noise_contribution),
            'complete_first_response_interval': interval_record(response),
            'strict_sign': 1 if response[0] > 0 else -1 if response[1] < 0 else 0})
        print('reader', reader['reader'], 'complete response sign', rows[-1]['strict_sign'], flush=True)
    selected = next(row for row in rows if row['reader'] == [1, 1])
    selected_bounds = tuple(map(Fraction, selected['complete_first_response_interval']['rational']))
    assert Fraction(1134, 10**8) < selected_bounds[0] < selected_bounds[1] < Fraction(1146, 10**8)
    result = {'scope': 'STRIKE_ACTUAL_CAUSAL_LINEARIZED_INDUCED_DOUBLE_TIME_CURRENT_WITH_BOTH_SOURCE_AND_FIELD_VARIATIONS',
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'physical_lambda': str(frequency), 'normalized_x': str(25*s.sqrt(15)*(1-s.I)/18),
        'physical_symbol_momentum': list(map(str, momentum)),
        'quantum_current_transfer': list(map(str, [-k for k in momentum])),
        'root_U_interval': list(map(str, interval)), 'complete_Fhat': str(actual_factor.as_expr()),
        'positive_common_denominator_mod_F': h.encode_poly(modulus),
        'denominator_interval': interval_record(modulus_interval),
        'noise_interval': interval_record(noise0), 'noise_variation_interval': interval_record(noise1),
        'linearized_causal_fields': 'Y0=chi0*J0; Y1=chi1*J0+chi0*Z; all initial and Noether contact terms are those of the actual causal producer.',
        'paired_current': 'C_b*N0', 'complete_first_response': 'C_b[1]*N0+C_b*N[1]',
        'time_scope': 'Double-time polarization of the original co-rotating same-time quadratic density; diagonal restriction is performed in time, never by multiplying Laplace variables.',
        'parameter_scope': 'Actual causal first-variation system and its source-noise derivative. Uniform finite-epsilon retarded-family differentiability is a separate consumer obligation.',
        'all289_variation_equations_at_common_frequency': True,
        'readers': rows, 'strictly_nonzero_response_count': sum(row['strict_sign'] != 0 for row in rows),
        'selected_reader': selected, 'selected_simple_strict_interval': ['0.00001134', '0.00001146'],
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'response.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS complete48 source-and-field causal first response', result['strictly_nonzero_response_count'],
          result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
