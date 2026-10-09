#!/usr/bin/env python3
"""Exact partial fractions and rational enclosures of the whole half-line."""
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import importlib.util
import json
from math import factorial
from pathlib import Path
import sys
import time

import sympy as s

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
x = s.symbols('x', real=True)


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    started = time.monotonic()
    record = json.loads((HERE/'kernels.json').read_text())
    exact = json.loads((FQ/'packet-noise/source-kernel-receipt.json').read_text())['exact_source']
    assert record['source_sha256'] == exact['source_sha256']
    interval = load(FQ/'packet-band-kernel/intervals.py', 'current_hessian_intervals')
    Box, cmul = interval.Box, interval.complex_product
    czero = (Box(0), Box(0))
    cone = (Box(1), Box(0))
    def cadd(a, b):
        return a[0]+b[0], a[1]+b[1]
    def cscale(a, b):
        return a[0]*b, a[1]*b
    def cconj(a):
        return a[0], -a[1]
    def cdiv(a, b):
        square = b[0].square()+b[1].square()
        assert square.lo > 0
        numerator = cmul(a, cconj(b))
        return numerator[0]/square, numerator[1]/square
    def cpow(a, degree):
        if degree < 0:
            return cdiv(cone, cpow(a, -degree))
        result = cone
        for _ in range(degree):
            result = cmul(result, a)
        return result

    N = s.sympify(record['lapse'])
    omega = s.sympify(record['frequency'])
    N2, omega2 = s.simplify(N*N), s.simplify(omega*omega)
    masses = [s.Integer(0), s.simplify((1-3*omega2+4*s.I*omega)/N2),
        s.simplify((1-3*omega2-4*s.I*omega)/N2)]
    field = s.QQ.algebraic_field(s.sqrt(2), s.sqrt(15), s.I)
    partials = {}

    def decompose(expression):
        numerator, denominator = s.fraction(s.cancel(expression))
        P, Q = s.Poly(numerator, x, domain=field), s.Poly(denominator, x, domain=field)
        quotient, P = P.div(Q)
        assert quotient.is_zero or quotient.degree() == 0
        result = {'constant': str(quotient.as_expr()), 'poles': []}
        rebuilt = quotient.as_expr()
        accounted = s.Poly(1, x, domain=field)
        for mass in masses:
            linear = s.Poly(x+mass, x, domain=field)
            remainder_denominator, multiplicity = Q, 0
            while True:
                reduced, remainder = remainder_denominator.div(linear)
                if not remainder.is_zero:
                    break
                multiplicity += 1
                remainder_denominator = reduced
            if multiplicity == 0:
                continue
            assert mass != 0 or multiplicity == 1
            accounted *= linear**multiplicity
            root = -mass
            ppoly, qpoly = P, remainder_denominator
            pjet, qjet = [], []
            for n in range(multiplicity):
                pjet.append(field.from_sympy(ppoly.eval(root)/s.factorial(n)))
                qjet.append(field.from_sympy(qpoly.eval(root)/s.factorial(n)))
                ppoly, qpoly = ppoly.diff(), qpoly.diff()
            assert qjet[0] != field.zero
            jet = []
            for n in range(multiplicity):
                value = (pjet[n]-sum((qjet[j]*jet[n-j] for j in range(1, n+1)), field.zero))/qjet[0]
                jet.append(value)
                coefficient = field.to_sympy(value)
                order = multiplicity-n
                result['poles'].append({'mass_squared': str(mass), 'order': order, 'coefficient': str(coefficient)})
                rebuilt += coefficient/(x+mass)**order
        assert Q.degree() == accounted.degree()
        assert s.cancel(expression-rebuilt, extension=[s.sqrt(2), s.sqrt(15), s.I]) == 0
        result['exact_original_weight_identity'] = True
        return result

    n2q, o2q = F(str(N2)), F(str(omega2))
    nI, oI, spin = Box(n2q).sqrt(), Box(o2q).sqrt(), Box(2).sqrt()
    real, imag = Box((1-3*o2q)/n2q), 4*oI/n2q
    modulus = (real.square()+imag.square()).sqrt()
    kr, ki = ((modulus+real)/2).sqrt(), ((modulus-real)/2).sqrt()
    assert kr.lo > 0 and ki.lo > 0 and modulus.hi < 9
    kappa = (kr, ki)
    degree = 130
    derivatives = [czero for _ in range(4)]
    power = cone
    for n in range(degree+1):
        for j in range(len(derivatives)):
            moment = F(3*2**(n+j+2), (n+j+2)*(n+j+3)*(n+j+5))
            derivatives[j] = cadd(derivatives[j], cscale(power, (-1)**j*moment/F(factorial(n))))
        power = cmul(power, (-kr, -ki))
    tail = F(2, 5)*729*F(6**(degree+1), factorial(degree+1))
    for j in range(len(derivatives)):
        derivatives[j] = tuple(value.grow(2**j*tail) for value in derivatives[j])

    kappas = s.symbols('kappa')
    jets = s.symbols('J0:4')
    transforms = {1: jets[0]}
    for n in range(1, 3):
        value = transforms[n]
        differentiated = s.diff(value, kappas)+sum(s.diff(value, jets[j])*jets[j+1] for j in range(3))
        transforms[n+1] = s.expand(-differentiated/(2*n*kappas))

    def evaluate(expression, bindings=None):
        if bindings and expression in bindings:
            return bindings[expression]
        if expression.is_Rational:
            return Box(F(int(expression.p), int(expression.q))), Box(0)
        if expression == s.I:
            return Box(0), Box(1)
        if expression.is_Add:
            result = czero
            for term in expression.args:
                result = cadd(result, evaluate(term, bindings))
            return result
        if expression.is_Mul:
            result = cone
            for term in expression.args:
                result = cmul(result, evaluate(term, bindings))
            return result
        if expression.is_Pow:
            base, exponent = expression.args
            if exponent.is_Integer:
                return cpow(evaluate(base, bindings), int(exponent))
            assert exponent == s.Rational(1, 2) and base.is_Rational and base > 0
            return Box(F(int(base.p), int(base.q))).sqrt(), Box(0)
        raise AssertionError(expression)

    def transform(mass, order):
        if mass == 0:
            assert order == 1
            return Box(F(2, 5)), Box(0)
        sign = 1 if s.simplify(mass-masses[1]) == 0 else -1
        assert sign == 1 or s.simplify(mass-masses[2]) == 0
        branch = kappa if sign == 1 else cconj(kappa)
        values = derivatives if sign == 1 else [cconj(value) for value in derivatives]
        return evaluate(transforms[order], {kappas: branch, **dict(zip(jets, values))})

    @lru_cache(None)
    def integrate(text):
        expression = s.sympify(text, locals={'x': x})
        decomposition = decompose(expression)
        partials[text] = decomposition
        answer = evaluate(s.sympify(decomposition['constant']))
        for pole in decomposition['poles']:
            coefficient = evaluate(s.sympify(pole['coefficient']))
            basis = transform(s.sympify(pole['mass_squared']), pole['order'])
            answer = cadd(answer, cmul(coefficient, basis))
        assert answer[1].lo <= 0 <= answer[1].hi
        return answer[0]

    radius = s.symbols('r', nonnegative=True)
    norm_expr = s.sympify(exact['zero_transfer_raw_norm_integrand'], locals={'r': radius})
    norm_expr = s.expand(norm_expr).subs(radius**2, x)
    assert radius not in norm_expr.free_symbols
    old_mean = s.sympify(exact['zero_transfer_raw_mean_integrand'], locals={'r': radius}).subs(radius**2, x)
    assert s.cancel(s.sympify(record['zero_mean_weight'], locals={'x': x})-old_mean) == 0
    assert s.cancel(s.sympify(record['zero_second_weight'], locals={'x': x})-(8/N2-8/N2**2*norm_expr)) == 0
    n2 = integrate(str(norm_expr))
    assert n2.lo > 0
    mu0 = integrate(record['zero_mean_weight'])/n2
    nu0 = integrate(record['zero_second_weight'])/n2-mu0.square()
    # Consume the original overlap normalization independently of the new kernels.
    Z = cmul((-3*oI, Box(1)), derivatives[0])
    assert not (n2.hi < Z[1].lo or Z[1].hi < n2.lo)
    n2 = n2.intersect(Z[1])
    moments = []
    for row in record['first_derivatives']:
        mean = integrate(row['mean_first']['ball_squared_rational_weight'])/n2
        raw = integrate(row['current_cross_first']['ball_squared_rational_weight'])/n2
        centered = raw-mu0*mean
        assert mean.lo == mean.hi == centered.lo == centered.hi == 0
    for row in record['second_derivatives']:
        mean = integrate(row['mean_second']['ball_squared_rational_weight'])/n2
        raw = integrate(row['current_cross_second']['ball_squared_rational_weight'])/n2
        centered = raw-mu0*mean
        entry = {'axes': row['axes'], 'mean_second': mean.record(),
            'raw_current_second_pairing': raw.record(),
            'centered_current_second_pairing': centered.record(),
            'centering_correction_mu0_mu2': (mu0*mean).record()}
        if row['axes'][0] == row['axes'][1]:
            assert mean.lo > 0 or mean.hi < 0
            assert centered.lo > 0 or centered.hi < 0
            entry['omitting_actual_mu2_changes_answer'] = not (mu0*mean).lo <= 0 <= (mu0*mean).hi
            slope_square = 2/n2q-mu0*mean-centered
            noise_quadratic = 2/n2q-mu0*mean
            assert slope_square.lo > 0 and noise_quadratic.lo > 0
            entry['actual_centered_first_derivative_norm_squared'] = slope_square.record()
            entry['noise_quadratic_coefficient'] = noise_quadratic.record()
            print('G2', row['axes'], centered.decimals(25), 'mu2', mean.decimals(25), flush=True)
        else:
            assert mean.lo == mean.hi == raw.lo == raw.hi == 0
        moments.append(entry)
    result = {'scope': 'STRIKE_STRICT_ORIGINAL_PACKET_CURRENT_TRANSFER_HESSIAN',
        'source_sha256': record['source_sha256'],
        'original_zero_transfer_norm_mean_second_kernel_identities': True,
        'kernel_sha256': hashlib.sha256((HERE/'kernels.json').read_bytes()).hexdigest(),
        'full_halfline_without_UV_cutoff': True,
        'measure': 'd^3p/(2*pi)^3, same unit position ball b and same fixed n',
        'partial_fraction_identities': partials,
        'pole_transform': {str(order): str(value) for order, value in transforms.items()},
        'ball_overlap_moment': 'M_j=3*2^(j+2)/((j+2)(j+3)(j+5))',
        'exponential_series_degree': degree, 'J_derivative_remainder_bound': '2^j*(2/5)*729*6^131/131!',
        'J_remainder_exact': str(tail),
        'kappa_real': kr.record(), 'kappa_imaginary': ki.record(),
        'raw_filtered_norm_squared': n2.record(), 'mean_zero': mu0.record(),
        'noise_zero': nu0.record(),
        'all_first_derivative_means_and_centered_pairings_exact_zero': True,
        'second_derivatives': moments,
        'constant_centering_projection_retained': True,
        'source_Gram_control': 'K^2=2, Hv^2=N^2|v|^2, and B_k=N^-2 M_k K(2H+Hk) give raw ||B_k psi||^2 second derivative 4|v|^2/N^2. Thus ||z1||^2=2/N^2-Re(conj(mu0)mu2)-|mu1|^2-Re<z0,z2> for unit v.',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'integrals.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS exact half-line transforms and strict current Hessian enclosures', result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
