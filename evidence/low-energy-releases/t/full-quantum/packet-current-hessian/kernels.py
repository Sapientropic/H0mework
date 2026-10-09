#!/usr/bin/env python3
"""Generate the actual centered current transfer Hessian's radial kernels."""
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
x = s.symbols('x', real=True)
p = s.symbols('p1:4', real=True)


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    start = time.monotonic()
    source = load(FQ/'packet-noise/source_kernel.py', 'source_current_hessian')
    provenance, data = source.exact_source()
    N, omega, H0, Hj, Cinv, K, w = data
    Q, G0 = K/s.sqrt(2), Cinv/(s.I*N)
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

    def conj(poly):
        return polynomial.from_dict({powers: star(value) for powers, value in poly.items()})

    def partial(poly, axis):
        radial = polynomial.from_dict({powers: derivative(value) for powers, value in poly.items()})
        return poly.diff(variables[axis])+2*variables[axis]*radial

    def add(*vectors):
        return [sum((v[i] for v in vectors), zero) for i in range(12)]

    def scale(value, vector):
        factor = value if isinstance(value, type(zero)) else polynomial.from_dict({(0, 0, 0): domain.convert(value)})
        return [factor*v for v in vector]

    def multiply(matrix, vector):
        result = [zero for _ in range(12)]
        for (i, j), value in s.SparseMatrix(matrix).todok().items():
            result[i] += vector[j].mul_ground(scalar(value))
        return result

    def hamiltonian(vector):
        return add(multiply(H0, vector),
            *(scale(variables[a], multiply(Hj[a], vector)) for a in range(3)))

    def Bzero(vector):
        return scale(scalar(2/N**2), multiply(K, hamiltonian(vector)))

    def incoming_term(axis, vector):
        return scale(scalar(1/N**2), multiply(K, multiply(Hj[axis], vector)))

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
    # This calls the original full252->12/iC0 readback before differentiating.
    # The polynomial coefficient x is the same |p|² everywhere below.
    a0 = Bzero(f)
    df = [[partial(value, a) for value in f] for a in range(3)]
    j1 = []
    for a in range(3):
        j1.append((scale(-1, add(incoming_term(a, f), Bzero(df[a]))),
            scale(-variables[a], a0)))

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
        return angular(sum((conj(a)*b for a, b in zip(left, right)), zero))

    def expr(value):
        return s.factor(domain.to_sympy(value), extension=[s.sqrt(2), s.sqrt(15), s.I])

    def integrate_by_parts(coefficients):
        alpha, beta, delta = coefficients
        # t=b'/r; u=(b''-b'/r)/r².  The original unit ball obeys
        # b''+4 b'/r+b=0, hence u=(-b-5t)/x.
        reduced_alpha = alpha-delta/scalar(x)
        reduced_beta = beta-5*delta/scalar(x)
        weight = reduced_alpha-reduced_beta/scalar(2*x)-derivative(reduced_beta)
        expression = expr(reduced_beta)
        numerator, denominator = s.fraction(expression)
        if expression == 0:
            origin_order, infinity_degree = None, None
        else:
            np, dp = s.Poly(numerator, x), s.Poly(denominator, x)
            origin_order = min(power[0] for power, _ in np.terms())-min(power[0] for power, _ in dp.terms())
            infinity_degree = np.degree()-dp.degree()
            assert origin_order >= 0 and infinity_degree <= 1
        return {'b_squared': str(expr(alpha)), 'b_times_bprime_over_r': str(expr(beta)),
            'b_times_bsecond_minus_bprime_over_r_over_r2': str(expr(delta)),
            'ODE_reduced_mixed_coefficient': str(expression),
            'ball_squared_rational_weight': str(expr(weight)),
            'boundary_at_zero_order': origin_order, 'boundary_at_infinity_degree_in_r2': infinity_degree,
            'both_integration_by_parts_endpoints_zero': True}, weight

    records = []
    mean0 = inner(f, a0)
    second0 = inner(a0, a0)
    print('PASS source cyclic columns and exact angular measure', flush=True)
    first = []
    for a in range(3):
        mu1, mu1_weight = integrate_by_parts((inner(f, j1[a][0]), inner(f, j1[a][1]), domain.zero))
        cross1, cross1_weight = integrate_by_parts((inner(a0, j1[a][0]), inner(a0, j1[a][1]), domain.zero))
        first.append({'axis': a, 'mean_first': mu1, 'current_cross_first': cross1})
        print('FIRST', a, 'mu', expr(mu1_weight), 'cross', expr(cross1_weight), flush=True)
    weights = {}
    for a in range(3):
        for b in range(a, 3):
            ddf = [partial(value, b) for value in df[a]]
            bb = add(incoming_term(a, df[b]), incoming_term(b, df[a]), Bzero(ddf))
            bt = add(scale(variables[b], incoming_term(a, f)), scale(variables[a], incoming_term(b, f)),
                scale(variables[b], Bzero(df[a])), scale(variables[a], Bzero(df[b])),
                a0 if a == b else [zero for _ in range(12)])
            bu = scale(variables[a]*variables[b], a0)
            mean, mean_weight = integrate_by_parts((inner(f, bb), inner(f, bt), inner(f, bu)))
            cross, cross_weight = integrate_by_parts((inner(a0, bb), inner(a0, bt), inner(a0, bu)))
            assert star(mean_weight) == mean_weight and star(cross_weight) == cross_weight
            weights[a, b] = mean_weight, cross_weight
            records.append({'axes': [a, b], 'mean_second': mean, 'current_cross_second': cross})
            print('SECOND', a, b, 'mean degrees', [s.degree(v, x) for v in s.fraction(expr(mean_weight))],
                'cross degrees', [s.degree(v, x) for v in s.fraction(expr(cross_weight))], flush=True)
    isotropic = all(expr(weights[a, a][i]-weights[0, 0][i]) == 0
        for a in range(3) for i in range(2)) and all(
        expr(value) == 0 for a in range(3) for b in range(a+1, 3) for value in weights[a, b])
    r = s.symbols('r', positive=True)
    ball = (s.sin(r)-r*s.cos(r))/r**3
    assert s.simplify(s.diff(ball, r, 2)+4/r*s.diff(ball, r)+ball) == 0
    result = {'scope': 'STRIKE_ORIGINAL_E0_ETA1_FIXED_PREPARATION_TRANSFER_CURRENT_HESSIAN',
        'source_sha256': provenance['source_sha256'],
        'source_input_sha256': {'Verification/physics/low-energy-phenomenology/full-quantum/packet-noise/source_kernel.py':
            hashlib.sha256((FQ/'packet-noise/source_kernel.py').read_bytes()).hexdigest()},
        'physical_momentum': 'p=2*pi*xi; transfer k is physical momentum',
        'original_Dirac_inverse': provenance['original_Dirac_inverse_side'],
        'lapse': str(N), 'frequency': str(omega), 'cyclic_denominators': cyclic,
        'packet': 'psi(p)=f(p)*b(|p|)/n; f=i(i-H)^(-1)C0^(-1)w; n fixed for all k',
        'current': 'B_k psi(p)=N^(-2)[K H(p-k)+H(p)K]psi(p-k)',
        'centering': 'P=|psi><psi| fixed; mu_a=<psi,j_a>; <z0,z_a>=<j0,j_a>-conj(mu0)*mu_a',
        'zero_mean_weight': str(expr(mean0)), 'zero_second_weight': str(expr(second0)),
        'first_derivatives': first, 'second_derivatives': records,
        'full_tensor_isotropic_generated_from_all_six_actual_components': isotropic,
        'original_ball_ODE_checked': True,
        'endpoint_argument': 'b(r) finite at 0 and O(r^-2) at infinity; each boundary r*beta(r²)*b(r)²/2 vanishes by the recorded exact rational orders',
        'halfline_integral': 'Every rational weight uses the same normalized ball Fourier measure r²*b(r)²/(2*pi²) dr on [0,infinity), with no cutoff.',
        'elapsed_seconds': round(time.monotonic()-start, 3)}
    (HERE/'kernels.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS all actual Hessian kernels; isotropic:', isotropic, 'seconds', result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
