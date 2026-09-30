#!/usr/bin/env python3
"""Independent whole-field Taylor division at a non-axial actual source root."""
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import sys
import time

import sympy as s
from sympy.polys.rings import ring

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
CANDIDATE = HERE.parent
ROOT = CANDIDATE.parents[4]
FQ = CANDIDATE.parent
u, q, U, T, r = s.symbols('u q U T r', real=True)
kx, ky, kz = s.symbols('kx ky kz', real=True)


def main():
    started = time.monotonic()
    target = json.loads((CANDIDATE/'receipt.json').read_text())
    seed = json.loads((FQ/'packet-seed-regularity/receipt.json').read_text())
    original = json.loads((FQ/'light-modes/field-receipt.json').read_text())
    current = json.loads((FQ/'packet-field/current-data.json').read_text())
    for path, digest in target['source_inputs_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest
    F = s.Poly(s.sympify(original['axial_source_factor'], locals={'u': u, 'q': q}), u, q, domain=s.QQ)
    cf = F.coeff_monomial(u**2)
    f = s.Poly(sum(c/cf*U**(a//2)*T**(b//2) for (a, b), c in F.terms()), U, T, domain=s.QQ)
    point = [s.Rational(1, 262144), s.Rational(2, 262144), s.Rational(3, 262144)]
    T0 = sum(value**2 for value in point)/2
    epsilon = s.Rational(target['root']['epsilon'])
    assert 0 < T0 < epsilon**2
    Fs = s.Poly(f.as_expr().subs(T, T0), U, domain=s.QQ)
    radial = s.Poly(Fs.as_expr().subs(U, T0*r), r, domain=s.QQ)
    assert radial.count_roots(s.Rational(3, 4), s.Rational(4, 5)) == 1
    assert s.gcd(Fs, Fs.diff()).degree() == 0
    K = s.QQ.algebraic_field(s.sqrt(2), s.sqrt(15), s.I)
    R, variable = ring((U,), K)
    basis_expr = list(map(s.sympify, target['coefficient_basis']))
    basis = list(map(K.from_sympy, basis_expr))
    @lru_cache(None)
    def number(value):
        value = s.expand(value)
        if value.is_Add:
            return sum((number(item) for item in value.args), K.zero)
        scalar, radical = value.as_coeff_Mul()
        return K.convert(scalar)*basis[basis_expr.index(radical)]
    def poly(expression):
        return R.from_dict({powers: number(value) for powers, value in s.Poly(s.expand(expression), U).terms()})
    modulus = poly(Fs.as_expr())
    zero, one = R.zero, R.one
    def red(value):
        return value % modulus
    def const(value):
        return R.ground_new(number(value))
    def at(polynomial):
        return poly(polynomial.as_expr().subs(T, T0))
    Du, Dt = f.diff(U), f.diff(T)
    D0 = at(Du)
    invD = poly(s.invert(s.Poly(Du.as_expr().subs(T, T0), U), Fs).as_expr())
    slope = red(-at(Dt)*invD)
    curvature = red(-(at(f.diff(T).diff(T))+2*at(f.diff(U).diff(T))*slope+
        at(f.diff(U).diff(U))*slope**2)*invD)
    assignments = [const(value) for value in point]+[variable, const(T0),
        slope-const(s.Rational(target['root']['s0'])), curvature]
    tensors = target['tensor_polynomials']
    tables = [tensors['alpha']]+tensors['beta']+tensors['delta']
    maxima = [max(exponents[axis] for table in tables for exponents, _ in table['numerator'])
        for axis in range(7)]
    powers = []
    for value, maximum in zip(assignments, maxima):
        row = [one]
        for _ in range(maximum):
            row.append(red(row[-1]*value))
        powers.append(row)
    @lru_cache(None)
    def monomial(exponents):
        value = one
        for axis, exponent in enumerate(exponents):
            value = red(value*powers[axis][exponent])
        return value
    def tensor(table):
        result = zero
        for exponents, pieces in table['numerator']:
            coefficient = sum((K.convert(s.Rational(value))*basis[i] for i, value in pieces), K.zero)
            result += monomial(tuple(exponents)).mul_ground(coefficient)
        return red(result*invD**table['denominator_power'])
    alpha = tensor(tensors['alpha'])
    beta = [tensor(table) for table in tensors['beta']]
    delta = {tuple(table['axes']): tensor(table) for table in tensors['delta']}
    print('PASS actual non-axial root and full tensor evaluation', flush=True)

    Jzero, Jone = (zero, zero, zero), (one, zero, zero)
    def add(a, b):
        return tuple(red(x+y) for x, y in zip(a, b))
    def mul(a, b):
        return tuple(red(sum((a[j]*b[n-j] for j in range(n+1)), zero)) for n in range(3))
    def scale(jet, coefficient):
        return tuple(value.mul_ground(coefficient) for value in jet)
    def reciprocal(jet):
        assert jet[0] == D0
        c1 = red(-invD*jet[1]*invD)
        c2 = red(-invD*(jet[1]*c1+jet[2]*invD))
        result = (invD, c1, c2)
        assert mul(jet, result) == Jone
        return result
    conjugate_generator = K.from_sympy(s.conjugate(K.ext.as_expr()))
    conjugate_powers = [K.one]
    for _ in range(7):
        conjugate_powers.append(conjugate_powers[-1]*conjugate_generator)
    @lru_cache(None)
    def star_coefficient(value):
        coefficients = value.to_list()
        return sum((K.convert(coefficient)*conjugate_powers[len(coefficients)-i-1]
            for i, coefficient in enumerate(coefficients)), K.zero)
    def star(polynomial):
        return R.from_dict({power: star_coefficient(value) for power, value in polynomial.items()})
    names = {'kx': kx, 'ky': ky, 'kz': kz, 'U': U, 'T': T}
    variables = [kx, ky, kz, U, T]
    source = {row['index']: s.Poly(s.sympify(row['numerator'], locals=names), *variables)
        for row in seed['fields']}
    Q = {(i, j): number(s.sympify(value)) for i, j, value in current['selected']['entries']
        if i in source and j in source}
    checks = []
    for direction in [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, 0, 1), (0, 1, 1)]:
        T1 = sum(value*v for value, v in zip(point, direction))
        T2 = s.Rational(sum(v*v for v in direction), 2)
        U1 = red(slope*const(T1))
        # Solve the full source equation's second coefficient directly.  No
        # target tensor, scalar quotient derivative, or U'' formula is used here.
        U2 = red(-invD*(at(Dt)*const(T2)+
            (at(f.diff(U).diff(U))*U1**2+2*at(f.diff(U).diff(T))*U1*const(T1)+
             at(f.diff(T).diff(T))*const(T1**2))/2))
        jets = ([(const(value), const(v), zero) for value, v in zip(point, direction)]+
            [(variable, U1, U2), (const(T0), const(T1), const(T2))])
        jet_powers = []
        for jet in jets:
            row = [Jone]
            for _ in range(12):
                row.append(mul(row[-1], jet))
            jet_powers.append(row)
        @lru_cache(None)
        def jet_monomial(exponents):
            value = Jone
            for axis, exponent in enumerate(exponents):
                value = mul(value, jet_powers[axis][exponent])
            return value
        def evaluate(polynomial):
            answer = Jzero
            for exponents, coefficient in polynomial.terms():
                answer = add(answer, scale(jet_monomial(tuple(exponents)), number(coefficient)))
            return answer
        assert evaluate(s.Poly(f.as_expr(), *variables)) == Jzero
        denominator = evaluate(s.Poly(Du.as_expr(), *variables))
        reciprocal_D = reciprocal(denominator)
        fields = {i: mul(evaluate(polynomial), reciprocal_D) for i, polynomial in source.items()}
        print('BUILT original field jet', direction, flush=True)
        output = Jzero
        for (i, j), coefficient in Q.items():
            output = add(output, tuple(red(star(fields[i][0])*value).mul_ground(coefficient) for value in fields[j]))
        expected_beta = red(sum((beta[a]*v for a, v in enumerate(direction)), zero))
        expected_delta = red(sum(((1 if a == b else 2)*direction[a]*direction[b]*value
            for (a, b), value in delta.items()), zero))
        assert output[0] == alpha
        assert output[1] == expected_beta
        assert red(2*output[2]) == expected_delta
        checks.append({'direction': list(direction), 'full_source_equation_jet_zero': True,
            'whole289_W_division_then_Q_matches_alpha_beta_delta': True})
        print('PASS independent original W quotient jet', direction, flush=True)
    (HERE/'jets.json').write_text(json.dumps({'verdict': 'PASS', 'physical_k': list(map(str, point)),
        'T': str(T0), 'actual_radial_root_window': ['3/4', '4/5'],
        'sturm_count': 1, 'whole_even_factor_simple': True,
        'method': 'Complete original field composed in K[U]/Fhat[h]/h^3; original equation solves U1/U2; entire D series is inverted before Q contraction.',
        'checks': checks, 'seconds': round(time.monotonic()-started, 3)}, indent=2)+'\n')


if __name__ == '__main__':
    main()
