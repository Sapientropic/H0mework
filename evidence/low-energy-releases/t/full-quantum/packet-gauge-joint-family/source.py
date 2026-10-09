#!/usr/bin/env python3
"""Actual constitutive A/B finite family and its full112 source section."""
import hashlib
import json
from pathlib import Path
import sys
import time

import sympy as s

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
x, epsilon, U = s.symbols('x epsilon U', real=True)


def matrix(record):
    return s.SparseMatrix(*record['shape'], {(i, j): s.sympify(v, locals={'x': x})
                                          for i, j, v in record['entries']})


def clean(M):
    return s.SparseMatrix(M.rows, M.cols, {ij: v for ij, raw in s.SparseMatrix(M).todok().items()
                                         if (v := s.expand(raw)) != 0})


def encode(M):
    return {'shape': list(M.shape), 'entries': [[i, j, str(v)] for (i, j), v in sorted(M.todok().items())]}


def main():
    started = time.monotonic()
    path = FQ/'packet-gauge-causal/source.json'
    source = json.loads(path.read_text())
    native_path = HERE/'native.json'
    native = json.loads(native_path.read_text())
    p = s.symbols('p0:4', real=True)
    world = [6*s.sqrt(15)*x/25, *[s.I*s.sympify(value) for value in source['physical_momentum']]]
    def raw_matrix(record):
        return s.SparseMatrix(*record['shape'], {(i, j): s.sympify(v, locals={str(t): t for t in p})
            for i, j, v in record['entries']})
    L, Li = matrix(source['L']), matrix(source['L_inverse'])
    H0 = matrix(source['H0'])
    H1, H2 = [clean(L.T*raw_matrix(native[name]).subs(dict(zip(p, world)))*L) for name in ['H1', 'H2']]
    K0 = matrix(source['K0'])
    Kworld = clean(raw_matrix(native['K0']).subs(dict(zip(p, world))))
    basis = clean(matrix(source['symmetry_minor_inverse'])*(Li*Kworld).extract(source['removed'], range(9)))
    basis_inverse = clean(basis.inv(method='DM'))
    assert clean(basis*basis_inverse) == clean(basis_inverse*basis) == s.eye(9)
    assert clean(Li*Kworld-K0*basis) == s.zeros(289, 9)
    K1 = clean(Li*raw_matrix(native['K1'])*basis_inverse)
    C1, C2 = [clean(L.T*raw_matrix(native[name])*basis_inverse) for name in ['C1', 'C2']]
    assert clean(H1*K0+H0*K1+C1) == s.zeros(289, 9)
    assert clean(H2*K0+H1*K1+C2) == s.zeros(289, 9)
    assert clean(H2*K1) == s.zeros(289, 9)
    H = clean(H0+epsilon*H1+epsilon**2*H2)
    pole = json.loads((FQ/'packet-field/pole-source.json').read_text())
    fields = json.loads((FQ/'light-modes/field-receipt.json').read_text())
    u, q = s.symbols('u q', real=True)
    rho = s.Rational(source['rho'])
    factor = s.Poly(s.sympify(fields['axial_source_factor'], locals={'u': u, 'q': q}), u, q)
    assert all(du % 2 == dq % 2 == 0 for (du, dq), _ in factor.terms())
    Fhat = s.Poly(sum(coefficient*U**(du//2)*rho**dq for (du, dq), coefficient in factor.terms()), U)
    def even(text):
        expression = s.Poly(s.sympify(text, locals={'u': u, 'q': q}).subs(q, rho), u)
        assert all(degree % 2 == 0 for (degree,), _ in expression.terms())
        return sum(coefficient*U**(degree//2) for (degree,), coefficient in expression.terms())
    Z = s.MutableSparseMatrix(289, Fhat.degree(), {})
    for row, _, text in pole['source_projection_numerator']['entries']:
        reduced = s.Poly(even(text), U).rem(Fhat)
        for (degree,), coefficient in reduced.terms():
            Z[row, degree] = coefficient
    Z = clean(Z)
    original_source = Z
    current = H
    indices = list(range(289))
    steps = []
    for number, step in enumerate(source['auxiliary_steps']):
        eliminated, kept = step['eliminated'], step['kept']
        erows = [indices.index(i) for i in eliminated]
        krows = [indices.index(i) for i in kept]
        inverse = matrix(step['inverse'])
        pivot = current.extract(erows, erows)
        assert clean(pivot*inverse) == s.eye(len(eliminated))
        assert clean(inverse*pivot) == s.eye(len(eliminated))
        right, left = current.extract(erows, krows), current.extract(krows, erows)
        back = clean(-inverse*right)
        particular = clean(inverse*Z.extract(erows, range(Fhat.degree())))
        steps.append({'eliminated': eliminated, 'kept': kept, 'inverse': step['inverse'],
                      'left': encode(left), 'back': encode(back), 'particular_source': encode(particular)})
        Z = clean(Z.extract(krows, range(Fhat.degree()))-left*particular)
        current = clean(current.extract(krows, krows)+left*back)
        indices = kept
        print('PASS original auxiliary block for all epsilon', number, len(eliminated), flush=True)
    assert indices == list(range(121))
    keep = source['keep121']
    section = clean(current.extract(keep, keep))
    assert clean(section.subs(epsilon, 0)-matrix(source['complete112'])) == s.zeros(112)
    C = matrix(source['polynomial_separation'])
    minus = C.subs(x, -x).conjugate()
    transformed = clean(minus.T*section*C)
    assert clean(transformed.subs(epsilon, 0)-s.diag(matrix(source['scalar_block']), matrix(source['Q103']))) == s.zeros(112)
    assert max(s.degree(v, epsilon) for v in transformed) <= 2
    coefficients = [clean(transformed.applyfunc(lambda v: v.coeff(epsilon, degree))) for degree in range(3)]
    rows = []
    for degree, M in enumerate(coefficients):
        rows.append({'epsilon_degree': degree, 'nonzero_entries': len(M.todok()),
                     'max_x_degree': int(max(s.degree(v, x) for v in M if v != 0)),
                     'scalar_scalar_x_degree': int(max((s.degree(v, x) for v in M[:9, :9] if v != 0), default=-1)),
                     'scalar_rest_x_degree': int(max((s.degree(v, x) for v in M[:9, 9:] if v != 0), default=-1))})
    result = {'scope': 'STRIKE_CONSTITUTIVE_JOINT_FINITE_PARAMETER_COMPLETE112_SECTION',
        'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
        'native_sha256': hashlib.sha256(native_path.read_bytes()).hexdigest(),
        'native_source_sha256': native['source_sha256'],
        'H0': encode(H0), 'H1': encode(H1), 'H2': encode(H2),
        'K0': encode(K0), 'K1': encode(K1), 'C1': encode(C1), 'C2': encode(C2),
        'source_basis_change': encode(basis),
        'epsilon_family': 'H(epsilon)=H0+epsilon*H1+epsilon^2*H2; the original removed9 section is fixed.',
        'auxiliary_steps': steps, 'all168_pivots_parameter_independent': True,
        'complete121': encode(current), 'complete112': encode(section),
        'original_source_numerator': encode(original_source),
        'section_source_numerator': encode(clean(Z.extract(keep, range(Fhat.degree())))),
        'source_denominator': str(even(pole['factor_D'])), 'complete_Fhat': str(Fhat.as_expr()),
        'source_convention': 'Columns j are U^j, all sources divided by D(U); U is the actual complete Fhat small positive root. Retained280 source components are fixed for all epsilon.',
        'fixed_polynomial_change': source['polynomial_separation'],
        'transformed_coefficients': [encode(M) for M in coefficients],
        'profiles': rows, 'removed': source['removed'], 'keep121': keep,
        'source_Noether': 'Kepsilon=K0+epsilon K1, Eepsilon=epsilon E1+epsilon² E2, Hepsilon Kepsilon=-epsilon C1-epsilon² C2; removed9 source is generated from this exact Ward, retained280 fixed.',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS actual finite-epsilon complete source', rows, result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
