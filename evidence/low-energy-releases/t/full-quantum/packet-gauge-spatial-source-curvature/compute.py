#!/usr/bin/env python3
"""Integrate the actual quantum-source q-Hessian over the whole original band."""
from fractions import Fraction as F
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
FQ = HERE.parent
ROOT = HERE.parents[4]
sys.path.insert(0, str(FQ/'packet-gauge-bilocal'))
import hermitian as h
sys.path.insert(0, str(FQ/'packet-band-kernel'))
from intervals import Box, pi_box

symbols = s.symbols('kx ky kz U T', real=True)
kx, ky, kz, U, T = symbols
R, *generators = ring('kx,ky,kz,U,T', h.K)
K = h.K


def read(path):
    return json.loads(path.read_bytes())


@lru_cache(None)
def polynomial(text):
    expression = s.sympify(text, locals=dict(zip(map(str, symbols), symbols)))
    return R.from_dict({power: h.scalar(value) for power, value in s.Poly(expression, *symbols).terms()})


def conjugate(poly):
    return R.from_dict({power: h.conjugate(value) for power, value in poly.items()})


@lru_cache(None)
def real_box(value):
    assert h.conjugate(value) == value
    expr = s.expand(K.to_sympy(value))
    total = Box(0)
    for radical, square in [(s.sqrt(30), 30), (s.sqrt(15), 15), (s.sqrt(2), 2)]:
        coefficient = expr.coeff(radical)
        assert coefficient.is_Rational
        total += Box(F(int(coefficient.p), int(coefficient.q)))*Box(square).sqrt()
        expr = s.expand(expr-coefficient*radical)
    assert expr.is_Rational
    return total+F(int(expr.p), int(expr.q))


def main():
    began = time.monotonic()
    paths = [FQ/'packet-gauge-global-transfer/source.json',
        FQ/'packet-gauge-global-transfer/equations.json',
        FQ/'packet-gauge-bilocal/vertices.json',
        FQ/'packet-gauge-constitutive-vertex/vertices.json',
        FQ/'packet-gauge-kinetic/receipt.json',
        FQ/'packet-gauge-reduced-current/current.json',
        FQ/'packet-gauge-cosine-curvature/consumer.json',
        FQ/'packet-gauge-cosine-curvature/probe-bounds.json',
        FQ/'packet-band-kernel/intervals.py']
    source, causal, vertices, auxiliary, kinetic, old_current, curvature, probe = [read(p) for p in paths[:-1]]
    original_path = FQ.parent/'active-gauge/receipt.json'
    pole_path = FQ/'packet-field/pole-source.json'
    original, pole = read(original_path), read(pole_path)
    for path, expected in source['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == expected
    c = 6*s.sqrt(15)/25
    lam = 6*c*(1-s.I)
    klam = h.scalar(lam)
    A, B = [{i: polynomial(value) for i, _, value in source['columns'][name]['global_numerator']['entries']}
            for name in ['A', 'B']]
    gauge = [i for i, field in enumerate(original['fields']) if field['group'] == 'gauge_A']
    spatial_gauge = [i for i in gauge if original['fields'][i]['coordinate'][0] != 0]
    bg = {i for i, field in enumerate(original['fields']) if field['group'] == 'gauge_B'}
    assert all(not A.get(i, R.zero) for i in spatial_gauge)
    assert all(i not in bg for i, j, value in source['columns']['Z']['global_numerator']['entries'])
    X = {i: klam*A.get(i, R.zero)+B.get(i, R.zero) for i in set(A)|set(B)}
    Xbar = {i: conjugate(value) for i, value in X.items()}
    imaginary = h.scalar(s.I)
    left = [R.ground_new(h.conjugate(klam)), *[imaginary*generators[j] for j in range(3)]]
    right = [R.ground_new(klam), *[-imaginary*generators[j] for j in range(3)]]
    selected = next(row for row in vertices['readers'] if row['reader'] == [1, 1])
    Q = {}
    for i, j, a, b, value in selected['Q0_bijet']:
        coef = R.ground_new(h.scalar(s.sympify(value)))
        Q[i, j] = Q.get((i, j), R.zero)+coef*(left[a] if a >= 0 else R.one)*(right[b] if b >= 0 else R.one)
    p = s.symbols('p0:4', real=True)
    curvature_time_coefficient = s.SparseMatrix(*kinetic['curvature_derivative']['shape'],
        {(i, j): s.diff(s.sympify(v, locals={str(t): t for t in p}), p[0])
         for i, j, v in kinetic['curvature_derivative']['entries']})
    first_curvature_double_frequency = [R.zero for _ in range(72)]
    for (i, j), value in curvature_time_coefficient.todok().items():
        first_curvature_double_frequency[i] += h.scalar(value)*A.get(gauge[j], R.zero)
    assert not any(first_curvature_double_frequency)
    weak = [-12*c, 0, 0, 0]
    curvature_matrix = s.SparseMatrix(*kinetic['curvature_derivative']['shape'],
        {(i, j): s.sympify(v, locals={str(t): t for t in p}).subs(dict(zip(p, weak)))
         for i, j, v in kinetic['curvature_derivative']['entries']})
    star = h.stored_matrix(kinetic['source_hodge']).to_Matrix()
    star72 = s.kronecker_product(star, s.eye(12))
    unit = s.zeros(48, 1)
    unit[13] = 1
    bb = -2*star72*curvature_matrix*unit
    for row in auxiliary['original_unit_auxiliary_readers']:
        pair, color = row['auxiliary']
        multiplier = h.scalar(s.expand(bb[12*pair+color]))
        if not multiplier:
            continue
        for i, j, value in row['Q']['entries']:
            Q[i, j] = Q.get((i, j), R.zero)+R.ground_new(multiplier*h.scalar(s.sympify(value)))
    assert all(conjugate(value) == Q.get((j, i), R.zero) for (i, j), value in Q.items())
    numerator = R.zero
    for (i, j), value in Q.items():
        if i in Xbar and j in X:
            numerator += Xbar[i]*value*X[j]/K.convert(2)
    assert numerator and all(h.conjugate(v) == v for v in numerator.values())
    D = polynomial(source['denominator_D'])
    denominator = D*D*R.ground_new(h.scalar(c**4))*(generators[3]**2+5184)
    const = (0, 0, 0, 0, 0)
    n0, den0 = numerator.get(const, K.zero), denominator.get(const, K.zero)
    origin = s.simplify(K.to_sympy(n0/den0))
    assert real_box(n0).lo > 0
    print('PASS actual global native current polynomial, original weak reader and exact Hermitian pairing', flush=True)

    # Recover the signed old nonaxial current, using the actual negative
    # Fourier label and the full incoming root rather than a root expansion.
    rho = s.Rational(1, 131072)
    point = [-h.scalar(s.sympify(v)) for v in old_current['physical_momentum']]
    point_t = h.scalar(rho*rho)
    def restrict(poly):
        out = h.POLY.zero
        for powers, value in poly.items():
            for j in range(3):
                value *= point[j]**powers[j]
            value *= point_t**powers[4]
            out += h.POLY.ground_new(value)*h.u**powers[3]
        return out
    old_selected = old_current['selected_reader']
    old_num = h.polynomial(s.sympify(old_selected['reduced_current_numerator'], locals={'U': h.U}))
    field_factor = read(FQ/'light-modes/field-receipt.json')['axial_source_factor']
    u, q = s.symbols('u q', real=True)
    original_factor = s.Poly(s.sympify(field_factor, locals={'u': u, 'q': q}), u, q)
    assert all(a % 2 == b % 2 == 0 for (a, b), value in original_factor.terms())
    factor = h.polynomial(sum(value*h.U**(a//2)*rho**b for (a, b), value in original_factor.terms()))
    assert (restrict(numerator)-old_num).rem(factor) == 0
    old_D = s.Poly(s.sympify(pole['factor_D'], locals={'u': u, 'q': q}), u, q)
    assert all(a % 2 == 0 for (a, b), value in old_D.terms())
    old_D_poly = h.polynomial(sum(value*h.U**(a//2)*rho**b for (a, b), value in old_D.terms()))
    old_den = old_D_poly**2*h.polynomial(c**4*(h.U**2+5184))
    assert restrict(denominator) == old_den
    print('PASS original full-F nonaxial native current and all normalization factors', flush=True)

    # The true root has 0<=U<=T<=epsilon² on the original ball; no finite
    # momentum samples or low-order dispersion stand in for this bound.
    eps = F(source['source_root_control']['epsilon'])
    tup, kup = eps*eps, 3*eps/2
    error = F(0)
    for powers, value in numerator.items():
        if powers == const:
            continue
        box = real_box(value)
        absolute = max(abs(box.lo), abs(box.hi))
        error += absolute*kup**sum(powers[:3])*tup**sum(powers[3:])
    d_error = F(0)
    assert D.get(const) == K.one
    for powers, value in D.items():
        if powers == const:
            continue
        box = real_box(value)
        d_error += max(abs(box.lo), abs(box.hi))*tup**sum(powers[3:])
    assert d_error < F(1, 40)
    norm_den = Box(1-d_error, 1+d_error)**2*Box(F(11664, 15625))*Box(5184, 5184+tup*tup)
    coefficient = real_box(n0).grow(error)/norm_den
    assert coefficient.lo > 0
    raw = next(row for row in curvature['source_full_probe_ball_consumers'] if row['domain'] == 'whole_original_light_ball')
    source_hessian = Box(*map(F, raw['all_unit_external_directions_raw_real_interval']['rational']))
    assert source_hessian.hi < 0
    # Original physical volume /(2pi)^3, not normalized by band volume.
    physical_radius = Box(2).sqrt()*eps
    physical_volume = physical_radius**3/(6*pi_box()**2)
    integral = coefficient*source_hessian*physical_volume
    assert integral.hi < 0
    source_paths = [*paths, FQ/'light-modes/field-receipt.json', original_path, pole_path]
    result = {'scope': 'WHOLE_ORIGINAL_BALL_RAW_QUANTUM_SOURCE_CONTRIBUTION_TO_NATIVE_CURRENT_EXTERNAL_Q_HESSIAN',
        'source_sha256': source['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in source_paths},
        'reader': [1, 1], 'outgoing_momentum': [0, 0, 0], 'physical_frequency': str(lam),
        'physical_weak_reader': list(map(str, weak)),
        'native_current_coefficient_numerator': str(numerator.as_expr()),
        'native_current_coefficient_denominator': str(denominator.as_expr()),
        'native_current_coefficient_at_origin': str(origin),
        'numerator_term_count': len(numerator),
        'full_ball_numerator_variation_bound': str(error),
        'full_ball_D_variation_bound': str(d_error),
        'native_current_coefficient_full_ball': coefficient.record(),
        'all_unit_external_directions_raw_source_Hessian': source_hessian.record(),
        'original_physical_ball_measure': physical_volume.record(),
        'whole_ball_current_source_Hessian': integral.record(),
        'all_unit_external_directions_strictly_negative': True,
        'actual_no_extra_cosine_half_or_Taylor_half': True,
        'old_full_root_native_current_readback': True,
        'original_theta_denominator_readback': True,
        'all_momentum_spatial_A_kernel_initial_zero': True,
        'all_momentum_first_curvature_transfer_strictly_proper': True,
        'original_Bg_source_rows_zero': True,
        'decomposition': 'This is the two quantum-source legs of the five-term spatial response at p=0. Field propagation and native reader variations remain separate summands.',
        'proof_identity': 'Actual global rational coefficient, source root whole-ball bounds, certified full-time source Hessian and exact physical measure; analytic dominated-integral proof in README.',
        'new_Lean_declarations': 0, 'new_axioms': 0,
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'receipt.json').write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n')
    print('PASS whole-band native source curvature', integral.decimals(), result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
