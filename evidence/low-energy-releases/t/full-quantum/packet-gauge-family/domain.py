#!/usr/bin/env python3
"""Generate a common pole disk for the actual finite parameter family."""
from fractions import Fraction as Q
import hashlib
import json
from math import factorial
from pathlib import Path

import sympy as s

HERE = Path(__file__).resolve().parent
FQ = HERE.parent
x, epsilon, a = s.symbols('x epsilon a', real=True)


def rational(value):
    assert value.is_Rational
    return Q(int(value.p), int(value.q))


def coefficient_bound(value):
    return abs(rational(s.re(value)))+abs(rational(s.im(value)))


def main():
    source = json.loads((HERE/'source.json').read_text())
    infinity = json.loads((HERE/'infinity.json').read_text())
    old = json.loads((FQ/'packet-gauge-causal/source.json').read_text())
    assert infinity['complete_frequency_degree'] == 126
    radius = Q(1, 100)
    pivots = []
    for component in infinity['components']:
        for step in component['steps']:
            if not step['rank']:
                continue
            numerator, denominator = s.fraction(s.cancel(s.sympify(step['pivot_determinant'], locals={'a': a})))
            bounds = []
            for value in [numerator, denominator]:
                poly = s.Poly(value, a, domain=s.QQ_I)
                constant = poly.nth(0)
                lower = max(abs(rational(s.re(constant))), abs(rational(s.im(constant))))
                lower -= sum(coefficient_bound(coefficient)*radius**power
                             for (power,), coefficient in poly.terms() if power)
                assert lower > 0
                bounds.append(str(lower))
            pivots.append({'dimension': step['rank'], 'determinant': step['pivot_determinant'],
                           'numerator_and_denominator_lower_bounds': bounds})
    determinant_lower = Q(1)
    factor_bounds = []
    for block in old['all103_source_factor_blocks']:
        determinant_lower *= abs(Q(block['constant']))
        for factor in block['factors']:
            poly = s.Poly(s.sympify(factor['polynomial'], locals={'x': x}), x, domain=s.QQ)
            degree = poly.degree()
            lower = abs(rational(poly.LC()))*5**degree
            lower -= sum(abs(rational(coefficient))*5**power for (power,), coefficient in poly.terms() if power < degree)
            assert lower > 0
            determinant_lower *= lower**factor['multiplicity']
            factor_bounds.append({'polynomial': factor['polynomial'], 'multiplicity': factor['multiplicity'],
                                  'circle_lower_bound': str(lower)})
    lapse = 3*s.sqrt(30)/25
    G = s.SparseMatrix(*old['scalar_block']['shape'], {(i, j): s.sympify(v)/lapse
                                                      for i, j, v in old['scalar_block']['entries']})
    scalar_determinant = rational(s.simplify(G.det()))
    determinant_lower *= abs(scalar_determinant)
    assert determinant_lower > 0
    scales = {i: s.sympify(value) for i, j, value in old['scales103']['entries'] if i == j}
    diagonal = [s.Integer(1)]*9+[scales[i] for i in range(103)]
    row_bounds = [[Q(0) for _ in range(112)] for _ in range(3)]
    entry_bound = Q(0)
    for i, j, text in source['complete112']['entries']:
        expression = s.expand(s.sympify(text, locals={'x': x, 'epsilon': epsilon}).subs(epsilon, 3*s.sqrt(2)*a/10)
                              *diagonal[i]*diagonal[j]/lapse)
        by_parameter = [Q(0), Q(0), Q(0)]
        for (dx, da), coefficient in s.Poly(expression, x, a, domain=s.QQ_I).terms():
            by_parameter[da] += coefficient_bound(coefficient)*5**dx
        entry_bound = max(entry_bound, by_parameter[0])
        for degree in range(3):
            row_bounds[degree][i] += by_parameter[degree]
    first, second = max(row_bounds[1]), max(row_bounds[2])
    inverse_bound = factorial(112)*entry_bound**111/determinant_lower
    delta = min(radius, 1/(4*inverse_bound*(first+second+1)))
    perturbation = inverse_bound*(delta*first+delta**2*second)
    assert delta > 0 and perturbation < Q(1, 4)
    result = {'scope': 'STRIKE_GENERATED_COMMON_FINITE_PARAMETER_POLE_DISK_AND_PHYSICAL_HALFPLANE',
        'input_sha256': {name: hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                         for name in ['source.json', 'infinity.json']},
        'parameter_identity': 'epsilon=3*sqrt(2)*a/10',
        'exact_infinity_pivot_radius_in_a': str(radius), 'pivot_bounds': pivots,
        'original_factor_circle_bounds': factor_bounds, 'scalar_block_determinant': str(scalar_determinant),
        'complete_normalized_determinant_circle_lower': str(determinant_lower),
        'unvaried_max_entry_circle_bound': str(entry_bound),
        'unvaried_inverse_infinity_norm_circle_bound': str(inverse_bound),
        'first_and_second_parameter_matrix_norm_circle_bounds': [str(first), str(second)],
        'generated_positive_delta_in_a': str(delta),
        'uniform_neumann_ratio_upper': str(perturbation),
        'common_original_frequency_disk': '|x_pole(a)|<5 for every real |a|<=delta',
        'physical_clock': 'lambda=(6*sqrt(15)/25)*x; original t',
        'common_physical_halfplane': 'Re(lambda)>=5',
        'proof': 'Exact infinity degree126 on |a|<=1/100; generated Neumann bound keeps the entire circle |x|=5 invertible along the real parameter homotopy. Its126 original zeros therefore remain inside. No determinant zero can enter through infinity.',
        'scope_note': 'Fixed original nonaxial momentum and complete112/aux168; this proves the pole domain before any source-specific properness or contact identity.'}
    (HERE/'domain.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS generated nonempty original finite-parameter common halfplane; exact pivots', len(pivots), flush=True)


if __name__ == '__main__':
    main()
