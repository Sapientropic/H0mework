#!/usr/bin/env python3
"""Independently enclose the full implicit derivatives and complex tensors."""
from fractions import Fraction as F
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

import sympy as s

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
CANDIDATE = HERE.parent
ROOT = CANDIDATE.parents[4]
FQ = CANDIDATE.parent
kx, ky, kz, U, T = s.symbols('kx ky kz U T', real=True)
u, q = s.symbols('u q', real=True)


def main():
    start = time.monotonic()
    target = json.loads((CANDIDATE/'receipt.json').read_text())
    seed = json.loads((FQ/'packet-seed-regularity/receipt.json').read_text())
    current = json.loads((FQ/'packet-field/current-data.json').read_text())
    original = json.loads((FQ/'light-modes/field-receipt.json').read_text())
    for path, digest in target['source_inputs_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest
    spec = importlib.util.spec_from_file_location('curvature_audit_boxes', FQ/'packet-band-kernel/intervals.py')
    interval = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(interval)
    Box = interval.Box
    Fsource = s.Poly(s.sympify(original['axial_source_factor'], locals={'u': u, 'q': q}), u, q, domain=s.QQ)
    cf = Fsource.coeff_monomial(u**2)
    f = s.Poly(sum(c/cf*U**(a//2)*T**(b//2) for (a, b), c in Fsource.terms()), U, T, domain=s.QQ)
    D = f.diff(U).as_expr()
    epsilon = F(seed['source_root_control']['epsilon'])
    rupper = F(seed['source_root_control']['r_window'][1])
    Ucap, Tcap = rupper*epsilon**2, epsilon**2
    Ub, Tb = Box(0, Ucap), Box(0, Tcap)
    def enclosure(expression):
        return sum((Box(F(str(c)))*(Ub**a)*(Tb**b)
            for (a, b), c in s.Poly(s.expand(expression), U, T, domain=s.QQ).terms()), Box(0))
    Dbox = enclosure(D).rounded(45)
    assert Dbox.lo > 0
    origin = {U: 0, T: 0}
    s0 = -f.diff(T).as_expr().subs(origin)/D.subs(origin)
    ds = (enclosure(-f.diff(T).as_expr()-s0*D)/Dbox).rounded(45)
    slope = Box(F(str(s0)))+ds
    curvature = (-(enclosure(f.diff(T).diff(T).as_expr())+
        2*enclosure(f.diff(U).diff(T).as_expr())*slope+
        enclosure(f.diff(U).diff(U).as_expr())*slope.square())/Dbox).rounded(45)
    ds_cap = max(abs(ds.lo), abs(ds.hi))
    c_cap = max(abs(curvature.lo), abs(curvature.hi))
    assert ds_cap <= F(target['root']['s_minus_s0_bound'])
    assert c_cap < F(target['root']['t_absolute_bound'])

    # Center values are reconstructed from the actual full field before
    # checking the candidate's scalar centers.
    names = {str(v): v for v in [kx, ky, kz, U, T]}
    N = {row['index']: s.sympify(row['numerator'], locals=names) for row in seed['fields']}
    Q = {(i, j): s.sympify(c) for i, j, c in current['selected']['entries'] if i in N and j in N}
    k = [kx, ky, kz]
    at0 = {kx: 0, ky: 0, kz: 0, U: 0, T: 0}
    W0 = {i: value.subs(at0) for i, value in N.items()}
    W1 = [{i: s.diff(value, coordinate).subs(at0) for i, value in N.items()} for coordinate in k]
    radialD0 = (s0*s.diff(D, U)+s.diff(D, T)).subs(at0)
    W2 = {}
    for a in range(3):
        for b in range(a, 3):
            W2[a, b] = {i: s.expand(s.diff(value, k[a], k[b]).subs(at0)+
                (s0*s.diff(value, U)+s.diff(value, T)).subs(at0)*int(a == b)-
                W0[i]*radialD0*int(a == b)) for i, value in N.items()}
    def contract(vector):
        return s.expand(sum(s.conjugate(W0[i])*value*vector[j] for (i, j), value in Q.items()))
    a0 = contract(W0)
    b0 = [contract(vector) for vector in W1]
    d0 = {key: contract(vector) for key, vector in W2.items()}
    tensors = target['tensor_polynomials']
    centers = [a0]+b0+[d0[tuple(row['axes'])] for row in tensors['delta']]
    tables = [tensors['alpha']]+tensors['beta']+tensors['delta']
    assert all(s.simplify(center-s.sympify(row['center'])) == 0 for center, row in zip(centers, tables))
    print('PASS independently reconstructed center and complete-root signed derivative boxes', flush=True)

    basis = list(map(s.sympify, target['coefficient_basis']))
    rad = [F(1)]+[Box(n).sqrt().rounded(20).hi for n in [2, 15, 30]]
    absolute_basis = rad+rad
    caps = [2*epsilon]*3+[Ucap, Tcap, ds_cap, c_cap]
    max_powers = [max(powers[a] for table in tables for powers, _ in table['numerator']) for a in range(7)]
    for axis, variable in [(3, U), (4, T)]:
        max_powers[axis] = max(max_powers[axis], 4*int(s.degree(D, variable)))
    power_cache = [[cap**j for j in range(maximum+1)] for cap, maximum in zip(caps, max_powers)]
    computed = []
    for table, center in zip(tables, centers):
        coefficients = {tuple(powers): {i: F(value) for i, value in pieces}
            for powers, pieces in table['numerator']}
        if center != 0:
            center_parts = {}
            for term in s.Add.make_args(s.expand(center)):
                scalar, radical = term.as_coeff_Mul()
                center_parts[basis.index(radical)] = F(str(scalar))
            for (a, b), value in s.Poly(s.expand(D**table['denominator_power']), U, T, domain=s.QQ).terms():
                monomial = (0, 0, 0, a, b, 0, 0)
                row = coefficients.setdefault(monomial, {})
                for i, c in center_parts.items():
                    row[i] = row.get(i, F(0))-F(str(value))*c
        total = F(0)
        for powers, pieces in coefficients.items():
            coefficient_bound = sum(abs(c)*absolute_basis[i] for i, c in pieces.items())
            monomial_bound = F(1)
            for axis, power in enumerate(powers):
                monomial_bound *= power_cache[axis][power]
            total += coefficient_bound*monomial_bound
        total /= Dbox.lo**table['denominator_power']
        computed.append(total)
    expected = target['uniform_errors']
    assert computed[0] <= F(expected['alpha'])
    assert all(value <= F(bound) for value, bound in zip(computed[1:4], expected['beta_components']))
    delta = {tuple(table['axes']): value for table, value in zip(tensors['delta'], computed[4:])}
    for (a, b), value in delta.items():
        assert value <= F(expected['delta_components'][f'{a}{b}'])
    beta_square = sum(value**2 for value in computed[1:4])
    beta_bound = Box(beta_square).sqrt().rounded(22).hi
    delta_rows = max(sum(delta[min(a, b), max(a, b)] for b in range(3)) for a in range(3))
    delta_frob = Box(sum((1 if a == b else 2)*value**2 for (a, b), value in delta.items())).sqrt().rounded(22).hi
    delta_bound = min(delta_rows, delta_frob)
    assert beta_bound <= F(expected['all_unit_v_beta'])
    assert delta_bound <= F(expected['all_unit_v_delta'])
    result = {'verdict': 'PASS',
        'method': 'Signed rational interval evaluation of full Fhat derivatives, then tighter rational radical upper bounds on the exact centered complex tensors.',
        'D_box': Dbox.record(), 'true_U_prime_minus_center': ds.record(), 'true_U_second_box': curvature.record(),
        'original_full_field_center_reconstructed': True,
        'all_ten_component_errors_below_candidate_bounds': True,
        'independent_all_unit_beta_upper': str(beta_bound),
        'independent_all_unit_delta_upper': str(delta_bound),
        'complex_parts_retained': True, 'candidate_bounds': expected,
        'seconds': round(time.monotonic()-start, 3)}
    (HERE/'bounds.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS every full-ball coefficient error and all real unit directions', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
