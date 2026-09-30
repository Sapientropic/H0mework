#!/usr/bin/env python3
"""Actual conjugate-frequency field consumers of the native density bi-jet.

The left family is the conjugate of the same real-epsilon right family, at
conj(p), not the previously certified independent -p Fourier family.
"""
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import time

import sympy as s
from sympy.polys.matrices import DomainMatrix
from sympy.polys.rings import ring

import vertices

HERE = Path(__file__).resolve().parent
FQ = HERE.parent
BASE = FQ.parent
ROOT = HERE.parents[4]
K = s.QQ.algebraic_field(s.sqrt(2), s.sqrt(15), s.I)
ROOTS = {value: K.from_sympy(value) for value in [s.sqrt(2), s.sqrt(15), s.I]}
ROOTS[s.sqrt(30)] = ROOTS[s.sqrt(2)]*ROOTS[s.sqrt(15)]
POLY, u = ring('U', K)
U = s.symbols('U', real=True)


@lru_cache(None)
def scalar(expression):
    if expression.is_Rational:
        return K.convert(expression)
    if expression in ROOTS:
        return ROOTS[expression]
    if expression.is_Add:
        return sum((scalar(term) for term in expression.args), K.zero)
    if expression.is_Mul:
        value = K.one
        for factor in expression.args:
            value *= scalar(factor)
        return value
    if expression.is_Pow and expression.exp.is_Integer:
        return scalar(expression.base)**int(expression.exp)
    raise AssertionError(('coefficient outside original radical basis', expression))


@lru_cache(None)
def number(text):
    return scalar(s.sympify(text))


CONJUGATE_PRIMITIVE = scalar(s.conjugate(K.ext.as_expr()))


@lru_cache(None)
def conjugate(value):
    result = K.zero
    for coefficient in value.to_list():
        result = result*CONJUGATE_PRIMITIVE+K.convert(coefficient)
    return result


def matrix(rows, columns, entries):
    data = {}
    for i, j, value in entries:
        if value:
            data.setdefault(i, {})[j] = value
    return DomainMatrix(data, (rows, columns), K)


def stored_matrix(record):
    return matrix(*record['shape'], [(i, j, number(value)) for i, j, value in record['entries']])


def conjugate_matrix(value):
    return matrix(*value.shape, [(i, j, conjugate(coefficient)) for (i, j), coefficient in value.to_dok().items()])


def operator(entries, point):
    point = list(map(scalar, point))
    result = {}
    for i, j, powers, text in entries:
        value = number(text)
        for coordinate, power in zip(point, powers):
            value *= coordinate**power
        result[i, j] = result.get((i, j), K.zero)+value
    return matrix(289, 289, [(i, j, value) for (i, j), value in result.items()])


def bijet(entries, left, right):
    result = {}
    for i, j, a, b, text in entries:
        value = number(text)*(left[a] if a >= 0 else K.one)*(right[b] if b >= 0 else K.one)
        result[i, j] = result.get((i, j), K.zero)+value
    return matrix(289, 289, [(i, j, value) for (i, j), value in result.items()])


def polynomial(expression):
    return POLY.from_dict({power: scalar(coefficient) for power, coefficient in s.Poly(expression, U).terms()})


def encode_poly(value):
    return str(s.Add(*(K.to_sympy(coefficient)*U**power[0] for power, coefficient in value.items())))


def main():
    started = time.monotonic()
    data = json.loads((FQ/'packet-gauge-kernel/propagation.json').read_text())
    source = json.loads((FQ/'packet-gauge-kernel/source.json').read_text())
    original = json.loads((BASE/'active-gauge/receipt.json').read_text())
    density = json.loads((HERE/'vertices.json').read_text())
    for path, digest in data['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest
    point = [s.sympify(data['physical_lambda']), *[s.I*s.sympify(value) for value in data['physical_momentum']]]
    point_values = list(map(scalar, point))
    left_values = list(map(conjugate, point_values))
    plus = next(row for row in data['families'] if row['frequency_sign'] == 1)
    X, derivative = [stored_matrix(plus[key]) for key in ['X0_numerator_coefficients', 'X1_numerator_coefficients']]
    I0, I1 = [stored_matrix(plus[key]) for key in ['I0_numerator_coefficients', 'I1_numerator_coefficients']]
    left_X, left_derivative = conjugate_matrix(X), conjugate_matrix(derivative)
    H = operator(original['Fourier_Jacobi_entries'], list(map(s.conjugate, point)))
    H1 = operator(source['H1'], list(map(s.conjugate, point)))
    assert (H.matmul(left_X)-conjugate_matrix(I0)).is_zero_matrix
    assert (H.matmul(left_derivative)+H1.matmul(left_X)-conjugate_matrix(I1)).is_zero_matrix
    print('PASS actual conjugate-frequency original289 field and parameter derivative', flush=True)
    factor = polynomial(s.sympify(data['complete_Fhat'], locals={'U': U}))
    denominator = polynomial(s.sympify(data['common_theta_denominator'], locals={'U': U}))
    denominator_bar = POLY.from_dict({power: conjugate(value) for power, value in denominator.items()})
    modulus_squared = (denominator_bar*denominator).rem(factor)
    assert denominator.gcd(factor).degree() == 0 and modulus_squared.gcd(factor).degree() == 0

    def pair(left, Q, right):
        coefficients = left.transpose().matmul(Q).matmul(right).to_dok()
        value = POLY.zero
        for (i, j), coefficient in coefficients.items():
            value += POLY.ground_new(coefficient/K.convert(2))*u**(i+j)
        return value.rem(factor)

    rows = []
    for reader in density['readers']:
        Q = bijet(reader['Q0_bijet'], left_values, point_values)
        Q1 = bijet(reader['Q1_bijet'], left_values, point_values)
        assert (Q-conjugate_matrix(Q).transpose()).is_zero_matrix
        assert (Q1-conjugate_matrix(Q1).transpose()).is_zero_matrix
        zeroth = pair(left_X, Q, X)
        first_left = pair(left_derivative, Q, X)
        first_right = pair(left_X, Q, derivative)
        direct_contact = pair(left_X, Q1, X)
        derivative_value = first_left+first_right+direct_contact
        assert not direct_contact  # Actual old theta input has no scalar component.
        assert all(conjugate(value) == value for value in zeroth.values())
        assert all(conjugate(value) == value for value in derivative_value.values())
        if derivative_value:
            assert derivative_value.gcd(factor).degree() == 0
        if zeroth:
            assert zeroth.gcd(factor).degree() == 0
        wrong = bijet(reader['Q0_bijet'], [-value for value in point_values], point_values)
        wrong_current = pair(left_derivative, wrong, X)+pair(left_X, wrong, derivative)
        density_error = derivative_value-wrong_current
        rows.append({'reader': reader['reader'], 'value_numerator': encode_poly(zeroth),
            'derivative_numerator': encode_poly(derivative_value),
            'nonzero_value_on_actual_factor': bool(zeroth),
            'nonzero_derivative_on_actual_factor': bool(derivative_value),
            'direct_contact_zero_on_actual_theta_input': True,
            'wrong_opposite_density_derivative_difference': encode_poly(density_error),
            'wrong_opposite_density_changes_result': bool(density_error)})
        print('reader', reader['reader'], 'nonzero', bool(derivative_value), flush=True)
    selected = next(row for row in rows if row['reader'] == [1, 1])
    assert selected['nonzero_value_on_actual_factor'] and selected['nonzero_derivative_on_actual_factor']
    result = {
        'scope': 'STRIKE_TRUE_CONJUGATE_FREQUENCY_BILOCAL_DENSITY_RESPONSE_OF_THE_SAME_REAL_PARAMETER_FAMILY',
        'source_sha256': data['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in
            [HERE/'vertices.json', FQ/'packet-gauge-kernel/propagation.json', FQ/'packet-gauge-kernel/source.json']},
        'right_symbol': list(map(str, point)), 'left_symbol': list(map(str, map(s.conjugate, point))),
        'source_current_physical_transfer': ['-('+value+')' for value in data['physical_momentum']],
        'source_current_transfer_convention': 'The reconstructed field has exp(-i k_source x), so its original H symbol uses -k_source.',
        'parameter_family': 'The previously certified retained280/Noether9 source protocol; same real epsilon on both sides; the left field solves H(conj(p)) not H(-p).',
        'current': 'C_b(epsilon;p)=1/2 conjugate(X_epsilon(p))^T Q_b(epsilon;conj(p),p) X_epsilon(p)',
        'derivative': '1/2 [conj(Xprime)^T Q X+conj(X)^T Q Xprime+conj(X)^T Qprime X]',
        'common_real_denominator_mod_F': encode_poly(modulus_squared),
        'denominator_identity': '|D(U)(lambda^2-c^2 U)|^2; no conjugate leg is assigned D^2',
        'conjugate_full289_readback': True, 'all_currents_and_derivatives_real': True,
        'readers': rows, 'nonzero_values': sum(row['nonzero_value_on_actual_factor'] for row in rows),
        'nonzero_derivatives': sum(row['nonzero_derivative_on_actual_factor'] for row in rows),
        'density_opposition_errors': sum(row['wrong_opposite_density_changes_result'] for row in rows),
        'clock_and_frame': 'Original physical time; canonical polarization of the original FullPhase co-rotating local current density.',
        'consumer_contract': 'Multiply by the matched same-source double-Laplace covariance and apply the true product rule; independent opposite-frequency Fourier data are not relabeled.',
        'elapsed_seconds': round(time.monotonic()-started, 3),
    }
    (HERE/'hermitian.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS actual48 conjugate-frequency density consumers', result['nonzero_derivatives'], 'nonzero', result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
