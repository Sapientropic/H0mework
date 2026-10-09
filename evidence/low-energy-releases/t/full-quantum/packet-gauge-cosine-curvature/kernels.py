#!/usr/bin/env python3
"""Native six-component cosine-potential curvature on the fixed source packet."""
from functools import lru_cache
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

import sympy as s
from sympy.polys.rings import ring

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
FQ = HERE.parent
BASE = FQ.parent
x = s.Symbol('x', real=True)
p = s.symbols('p1:4', real=True)


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    started = time.monotonic()
    path = FQ/'packet-noise/source_kernel.py'
    source = load(path, 'cosine_curvature_source')
    provenance, (N, omega, H0, Hj, CI, K, w) = source.exact_source()
    inputs = [path, BASE/'occupied-response/receipt.json', BASE/'matter-vertices/receipt.json',
        FQ/'receipt.json', FQ/'packet-gauge-cosine/source.json',
        FQ/'packet-gauge-cosine-momentum/momentum.json']
    occupied, vertices, full, cosine, momentum = [json.loads(item.read_text()) for item in inputs[1:]]
    for record in [occupied, vertices, full, cosine, momentum]:
        assert record['source_sha256'] == provenance['source_sha256']
    frame = source.decode(occupied['occupied_frame'])
    CIfull = source.decode(full['time_principal_inverse'])
    density = source.decode(next(row['operator'] for row in vertices['primitive_vertices']
        if row['group'] == 'gauge_A' and row['coordinate'] == [1, 1]))
    Vfull = source.clean(-s.I*CIfull*density/N)
    V = source.clean(frame.H*Vfull*frame)
    source.zero(Vfull*frame-frame*V)
    source.zero(frame.H*Vfull-V*frame.H)
    source.zero(V-source.decode(cosine['V']))
    source.zero(V.H-V)
    source.zero(K*V-V*K)
    W = source.clean(2*K*V/N**2)
    source.zero(W.H-W)
    Q, G0 = K/s.sqrt(2), CI/(s.I*N)

    domain = s.QQ.algebraic_field(s.sqrt(2), s.sqrt(15), s.I).frac_field(x)
    polynomial, *variables = ring(p, domain)
    zero = polynomial.zero

    @lru_cache(None)
    def scalar(value):
        return domain.from_sympy(value)

    @lru_cache(None)
    def star(value):
        return scalar(s.conjugate(domain.to_sympy(value)))

    @lru_cache(None)
    def derivative(value):
        return scalar(s.diff(domain.to_sympy(value), x))

    def conjugate(poly):
        return polynomial.from_dict({powers: star(value) for powers, value in poly.items()})

    def partial(poly, axis):
        radial = polynomial.from_dict({powers: derivative(value) for powers, value in poly.items()})
        return poly.diff(variables[axis])+2*variables[axis]*radial

    def add(*vectors):
        return [sum((v[i] for v in vectors), zero) for i in range(12)]

    def scale(value, vector):
        factor = value if isinstance(value, type(zero)) else polynomial.from_dict({(0, 0, 0): scalar(value)})
        return [factor*v for v in vector]

    def multiply(matrix, vector):
        result = [zero for _ in range(12)]
        for (i, j), value in s.SparseMatrix(matrix).todok().items():
            result[i] += vector[j].mul_ground(scalar(value))
        return result

    def hamiltonian(vector):
        return add(multiply(H0, vector),
            *(scale(variables[a], multiply(Hj[a], vector)) for a in range(3)))

    def angular(poly):
        result = domain.zero
        for powers, value in poly.items():
            if any(power % 2 for power in powers):
                continue
            degree = sum(powers)
            moment = s.prod(s.factorial2(power-1) for power in powers)/s.factorial2(degree+1)
            result += value*scalar(moment*x**(degree//2))
        return result

    def inner(left, right):
        return angular(sum((conjugate(a)*b for a, b in zip(left, right)), zero))

    def expr(value):
        return s.factor(domain.to_sympy(value), extension=[s.sqrt(2), s.sqrt(15), s.I])

    f = [zero for _ in range(12)]
    cyclic = []
    for sign in [-1, 1]:
        seed = (s.eye(12)+sign*Q)*G0*w/2
        denominator = s.expand((s.I-sign*omega)*(s.I-3*sign*omega)-N**2*x)
        partner = [sign*Hj[a]*seed/N for a in range(3)]
        for i in range(12):
            terms = {(0, 0, 0): scalar(-N*(s.I-3*sign*omega)/denominator*seed[i])}
            for a in range(3):
                powers = tuple(int(a == b) for b in range(3))
                terms[powers] = scalar(-sign*N**2/denominator*partner[a][i])
            f[i] += polynomial.from_dict(terms)
        cyclic.append({'chirality': sign, 'denominator': str(denominator)})
    a0 = scale(2/N**2, multiply(K, hamiltonian(f)))
    df = [[partial(value, axis) for value in f] for axis in range(3)]

    def integration_by_parts(coefficients):
        alpha, beta, delta = coefficients
        # psi=f*b. t=b'/r, u=(b''-b'/r)/r². The real normalized
        # position-ball transform obeys b''+4b'/r+b=0.
        aa = alpha-delta/scalar(x)
        bb = beta-5*delta/scalar(x)
        weight = aa-bb/scalar(2*x)-derivative(bb)
        mixed = expr(bb)
        if mixed == 0:
            origin, infinity = None, None
        else:
            numerator, denominator = s.fraction(mixed)
            np, dp = s.Poly(numerator, x), s.Poly(denominator, x)
            origin = min(power[0] for power, _ in np.terms())-min(power[0] for power, _ in dp.terms())
            infinity = np.degree()-dp.degree()
            assert origin >= 0 and infinity <= 1
        return {'b_squared': str(expr(alpha)), 'b_times_bprime_over_r': str(expr(beta)),
            'b_times_bsecond_minus_bprime_over_r_over_r2': str(expr(delta)),
            'ODE_reduced_mixed_coefficient': str(mixed),
            'ball_squared_rational_weight': str(expr(weight)),
            'boundary_at_zero_order': origin, 'boundary_at_infinity_degree_in_r2': infinity,
            'both_integration_by_parts_endpoints_zero': True}, weight

    weights, records, second_vectors = {}, [], {}
    for a in range(3):
        for b in range(a, 3):
            ddf = [partial(value, b) for value in df[a]]
            bb = multiply(W, ddf)
            bt = multiply(W, add(scale(variables[a], df[b]), scale(variables[b], df[a]),
                                f if a == b else [zero]*12))
            bu = multiply(W, scale(variables[a]*variables[b], f))
            mean, mean_weight = integration_by_parts((inner(f, bb), inner(f, bt), inner(f, bu)))
            cross, cross_weight = integration_by_parts((inner(a0, bb), inner(a0, bt), inner(a0, bu)))
            assert star(mean_weight) == mean_weight
            weights[a, b] = mean_weight, cross_weight
            second_vectors[a, b] = (bb, bt, bu)
            records.append({'axes': [a, b], 'mean_second': mean, 'raw_current_second_pairing': cross,
                'raw_pairing_weight_real': star(cross_weight) == cross_weight})
            print('PASS cosine external curvature', a, b,
                'mean', expr(mean_weight), 'raw degrees',
                [s.degree(value, x) for value in s.fraction(expr(cross_weight))], flush=True)

    # The same derivative must match a direct original Green inverse at a
    # fresh nonaxial momentum. Keep the actual ball derivatives independent.
    point = [s.Rational(2, 9), -s.Rational(1, 7), s.Rational(3, 11)]
    radius2 = sum(value**2 for value in point)
    number_field = domain.domain
    radius_value = number_field.from_sympy(radius2)
    @lru_cache(None)
    def evaluate_scalar(value):
        return value.numer.evaluate(0, radius_value)/value.denom.evaluate(0, radius_value)
    def evaluate(vector):
        return s.Matrix([number_field.to_sympy(sum((evaluate_scalar(value)*
            number_field.from_sympy(s.prod(point[j]**powers[j] for j in range(3)))
            for powers, value in poly.items()), number_field.zero))
            for poly in vector])
    fpoint = evaluate(f)
    hp = H0+sum((point[j]*Hj[j] for j in range(3)), s.zeros(12))
    M = s.I*s.eye(12)-hp
    def exact_zero(vector):
        assert all(s.expand(value) == 0 for value in vector)
    exact_zero(M*fpoint-s.I*CI*w)
    dpoint = [evaluate(vector) for vector in df]
    for a in range(3):
        exact_zero(M*dpoint[a]-Hj[a]*fpoint)
    for a in range(3):
        for b in range(a, 3):
            ddf = evaluate([partial(value, b) for value in df[a]])
            exact_zero(M*ddf-Hj[a]*dpoint[b]-Hj[b]*dpoint[a])
            expected = [W*ddf,
                W*(point[a]*dpoint[b]+point[b]*dpoint[a]+(fpoint if a == b else s.zeros(12, 1))),
                W*(point[a]*point[b]*fpoint)]
            for generated, target in zip(second_vectors[a, b], expected):
                exact_zero(evaluate(generated)-target)
    isotropic = all(weights[a, a] == weights[0, 0] for a in range(3)) and all(
        value == domain.zero for a in range(3) for b in range(a+1, 3) for value in weights[a, b])
    r = s.Symbol('r', positive=True)
    ball = (s.sin(r)-r*s.cos(r))/r**3
    assert s.simplify(s.diff(ball, r, 2)+4/r*s.diff(ball, r)+ball) == 0
    output = {'scope': 'STRIKE_FIXED_PACKET_SELECTED_COSINE_EXTERNAL_MOMENTUM_CURVATURE',
        'source_sha256': provenance['source_sha256'],
        'input_sha256': {str(item.relative_to(ROOT)): hashlib.sha256(item.read_bytes()).hexdigest() for item in inputs},
        'lapse': str(N), 'frequency': str(omega), 'V': source.encode(V), 'W': source.encode(W),
        'density_to_H': 'Vfull=-i*C0inv*density/N; full252 both sides restrict to same original12',
        'original_Dirac_inverse': provenance['original_Dirac_inverse_side'],
        'cyclic_denominators': cyclic,
        'physical_momentum': 'p=2*pi*xi; external q in cos(q.y) is physical, no extra2pi',
        'fixed_packet': 'psi(p)=f(p)*b(|p|)/n, same normalized position unit ball and original E0 eta1 Green',
        'curvature': 'Csecond_ij psi(p)=(2KV/N²)*partial_pi partial_pj( f(p)b(|p|) )/n',
        'all_time_zero_probe': 'B_epsilon,0(t)=2K[H+epsilon cos(q.y)V]/N²; current variation and all q derivatives are time independent',
        'fixed_centering': '2Re<j0,Csecond_ij psi>-2Re(conj(mu0)*<psi,Csecond_ij psi>); P and n fixed',
        'zero_mean_weight': str(expr(inner(f, a0))),
        'zero_second_weight': str(expr(inner(a0, a0))),
        'second_derivatives': records, 'isotropic_computed_not_assumed': isotropic,
        'direct_Green_point': list(map(str, point)), 'direct_Green_jet_all_six_components': True,
        'original_ball_ODE_checked': True,
        'endpoint_argument': 'b finite at0 and O(r^-2) at infinity; r*beta(r²)*b(r)²/2 vanishes by recorded rational orders',
        'measure': 'd³p/(2pi)³ with the original normalized ball Fourier transform, entire r in[0,infinity)',
        'new_Lean_declarations': 0, 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'kernels.json').write_text(json.dumps(output, indent=2)+'\n')
    print('PASS true six-component cosine curvature kernels, isotropic:', isotropic,
          'seconds', output['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
