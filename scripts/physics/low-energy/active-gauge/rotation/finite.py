#!/usr/bin/env python3
"""Exact finite rotation congruences of the actual 289-field polynomial symbol.

The half-angle coordinate z generates theta=4 atan z.  Each field matrix is
B(z)/(d*(1+z²)^4), with B an integer matrix polynomial of degree <= 8. Spatial
R(z) has denominator (1+z²)^2. Every coefficient of the cleared 289x289
congruence is checked; this is not a numerical sample or an isotropy premise.
"""
import argparse
from collections import defaultdict
import json
from pathlib import Path
import sys
import time

import sympy as s

PARENT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PARENT))
from compute import F, number


def clean(poly):
    values = list(poly)
    while values and values[-1] == 0:
        values.pop()
    return tuple(values)


def add(left, right):
    out = list(left)+[0]*max(0, len(right)-len(left))
    for i, value in enumerate(right):
        out[i] += value
    return clean(out)


def mul(left, right):
    if not left or not right:
        return ()
    out = [0]*(len(left)+len(right)-1)
    for i, a in enumerate(left):
        if a:
            for j, b in enumerate(right):
                if b:
                    out[i+j] += a*b
    return clean(out)


def scale(value, poly):
    return clean([value*x for x in poly])


def power(poly, exponent):
    out = (1,)
    for _ in range(exponent):
        out = mul(out, poly)
    return out


def accumulate(dictionary, key, value):
    updated = add(dictionary.get(key, ()), value)
    if updated:
        dictionary[key] = updated
    else:
        dictionary.pop(key, None)


def integer_polynomial(expression, variable):
    polynomial = s.Poly(s.expand(expression), variable, domain=s.ZZ)
    return clean([int(polynomial.nth(i)) for i in range(polynomial.degree()+1)]) if polynomial else ()


def field_rotation(generator):
    z, x = s.symbols('z x', real=True)
    size = generator.rows
    identity = s.SparseMatrix(s.eye(size))
    square = generator*generator
    weights = [s.Rational(1, 2), s.Rational(1), s.Rational(3, 2), s.Rational(2)]
    points = [0]+[-w*w for w in weights]
    powers = [identity]
    for _ in range(4):
        powers.append(powers[-1]*square)
    projectors = []
    for point in points:
        polynomial = s.Poly(s.prod((x-other)/(point-other) for other in points if other != point), x)
        projector = sum((polynomial.nth(i)*powers[i] for i in range(5)), s.zeros(size))
        projectors.append(s.SparseMatrix(projector))
    assert sum(projectors, s.zeros(size)) == identity
    assert generator*projectors[0] == s.zeros(size)
    for i, projector in enumerate(projectors):
        assert generator*projector == projector*generator
        assert square*projector == points[i]*projector
        for j, other in enumerate(projectors):
            assert projector*other == (projector if i == j else s.zeros(size))
    denominator = 1+z*z
    numerators = defaultdict(lambda: s.SparseMatrix(size, size, {}))

    def include(scalar_polynomial, matrix):
        poly = s.Poly(s.expand(scalar_polynomial), z)
        for (degree,), coefficient in poly.terms():
            numerators[degree] += coefficient*matrix

    include(denominator**4, projectors[0])
    for integer_weight, (weight, projector) in enumerate(zip(weights, projectors[1:]), 1):
        complex_power = s.expand((1+s.I*z)**(2*integer_weight))
        cosine = s.re(complex_power)
        sine = s.im(complex_power)
        assert s.expand(cosine*cosine+sine*sine-denominator**(2*integer_weight)) == 0
        include(denominator**(4-integer_weight)*cosine, projector)
        include(denominator**(4-integer_weight)*sine/weight, generator*projector)
    assert max(numerators) <= 8
    assert numerators[0] == identity and numerators[1] == 4*generator
    constant_denominator = 1
    for matrix in numerators.values():
        for value in matrix.todok().values():
            constant_denominator = s.ilcm(constant_denominator, s.denom(value))
    output = {}
    for degree, matrix in numerators.items():
        for (i, j), value in matrix.todok().items():
            polynomial = [0]*9
            polynomial[degree] = int(constant_denominator*value)
            accumulate(output, (i, j), polynomial)
    return int(constant_denominator), output


def field_inverse(field, denominator):
    rows = defaultdict(list)
    for (i, j), polynomial in field.items():
        rows[i].append((j, tuple((-1)**degree*value for degree, value in enumerate(polynomial))))
    product = {}
    for (i, j), polynomial in field.items():
        for column, other in rows[j]:
            accumulate(product, (i, column), mul(polynomial, other))
    identity = scale(-denominator**2, power((1, 0, 1), 8))
    for i in range(289):
        accumulate(product, (i, i), identity)
    assert not product


def spatial_rotation(spatial):
    z = s.symbols('z', real=True)
    d = 1+z*z
    cosine = 1-6*z*z+z**4
    sine = 4*z*(1-z*z)
    numerator = d*d*s.eye(4)+sine*spatial+(d*d-cosine)*spatial**2
    assert s.expand(cosine*cosine+sine*sine-d**4) == 0
    assert (numerator.T*numerator-d**4*s.eye(4)).applyfunc(s.expand) == s.zeros(4)
    assert s.expand(numerator.det()-d**8) == 0
    return {(i, j): integer_polynomial(value, z) for (i, j), value in s.SparseMatrix(numerator).todok().items()}


def source_integer_coefficients(receipt):
    values, denominator = [], 1
    for i, j, powers, raw in receipt['Fourier_Jacobi_entries']:
        coefficient = number(s.sympify(raw))
        assert not coefficient.imag
        coefficients = coefficient.real.to_list()
        coefficients = [s.S.Zero]*(4-len(coefficients))+[s.Rational(c.numerator, c.denominator) for c in coefficients]
        denominator = s.ilcm(denominator, *[s.denom(c) for c in coefficients])
        values.append((i, j, tuple(powers), coefficients))
    result = {}
    for i, j, powers, coefficients in values:
        for basis, value in enumerate(coefficients):
            if value:
                result[i, j, powers, basis] = int(value*denominator)
    return int(denominator), result


def rotate_monomial(powers, rotation):
    zero_power = (0, 0, 0, 0)
    terms = {zero_power: (1,)}
    for component, exponent in enumerate(powers):
        for _ in range(exponent):
            new = {}
            for existing, polynomial in terms.items():
                for target in range(4):
                    coefficient = rotation.get((target, component), ())
                    if coefficient:
                        changed = list(existing)
                        changed[target] += 1
                        accumulate(new, tuple(changed), mul(polynomial, coefficient))
            terms = new
    assert sum(powers) <= 2
    compensation = power((1, 0, 1), 4-2*sum(powers))
    return {key: mul(value, compensation) for key, value in terms.items()}


def finite_congruence(source, rotation, denominator, field):
    images = {p: rotate_monomial(p, rotation) for _, _, p, _ in source}
    transformed = {}
    for (i, j, powers, basis), coefficient in source.items():
        for new_power, polynomial in images[powers].items():
            accumulate(transformed, (i, j, new_power, basis), scale(coefficient, polynomial))
    rows = defaultdict(list)
    for (i, j), polynomial in field.items():
        rows[i].append((j, polynomial))
    left = {}
    for (i, j, powers, basis), polynomial in transformed.items():
        for row, coefficient in rows[i]:
            accumulate(left, (row, j, powers, basis), mul(coefficient, polynomial))
    output = {}
    for (i, j, powers, basis), polynomial in left.items():
        for column, coefficient in rows[j]:
            accumulate(output, (i, column, powers, basis), mul(polynomial, coefficient))
    slots = len(output)
    right = power((1, 0, 1), 12)
    for key, coefficient in source.items():
        accumulate(output, key, scale(-denominator**2*coefficient, right))
    assert not output, list(output.items())[:8]
    return slots


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path, required=True)
    parser.add_argument('--generators', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    receipt = json.loads(args.receipt.read_text())
    data = json.loads(args.generators.read_text())
    source_denominator, source = source_integer_coefficients(receipt)
    certificates = []
    for axis, entry in enumerate(data['generators']):
        started = time.monotonic()
        generator = s.SparseMatrix(289, 289, {(i, j): s.sympify(value) for i, j, value in entry['field_generator']})
        spatial = s.Matrix([[s.sympify(value) for value in row] for row in entry['spatial_matrix']])
        denominator, field = field_rotation(generator)
        field_inverse(field, denominator)
        rotation = spatial_rotation(spatial)
        slots = finite_congruence(source, rotation, denominator, field)
        certificates.append({'axis': axis, 'field_constant_denominator': denominator,
            'field_numerator': [[int(i), int(j), list(poly)] for (i, j), poly in sorted(field.items())],
            'spatial_numerator': [[int(i), int(j), list(poly)] for (i, j), poly in sorted(rotation.items())],
            'exact_zero_congruence_coefficient_slots': slots,
            'semisimple_weight_projectors_checked': True, 'field_inverse_is_parameter_negation': True,
            'inverse_matrix_polynomial_coefficients_verified': True,
            'elapsed_seconds': round(time.monotonic()-started, 3)})
        print('PASS: finite source rotation axis', axis, '; all polynomial congruence coefficients zero;',
              certificates[-1]['elapsed_seconds'], 'seconds', flush=True)
    result = {'scope': 'EXACT_FINITE_ALL_ANGLE_CONGRUENCES_OF_THE_SOURCE_289_HESSIAN',
        'identity': 'S(z)^T H(R(z)^T p) S(z)=H(p)',
        'angle_parameter': 'theta=4 atan(z); every rotation-circle angle in [-pi,pi] has finite z',
        'spatial_matrix_readback': 'R(z)=spatial_numerator/(1+z^2)^2',
        'field_matrix_readback': 'S(z)=field_numerator/(field_constant_denominator*(1+z^2)^4)',
        'cleared_identity_degree_bound': 24,
        'verification': 'all exact integer coefficients in z and all four momentum variables; no sampling',
        'source_coefficient_field_generator': str(F.ext.as_expr()),
        'source_coefficient_field_minimal_polynomial': str(F.ext.minpoly.as_expr()),
        'source_coefficient_common_denominator': source_denominator,
        'certificates': certificates,
        'local_diffeomorphism_invariance_used': False}
    args.out.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n')


if __name__ == '__main__':
    main()
