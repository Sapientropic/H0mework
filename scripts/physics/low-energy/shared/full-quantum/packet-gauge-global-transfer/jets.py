#!/usr/bin/env python3
"""Actual physical first/second jets including the complete implicit source root."""
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
spec = importlib.util.spec_from_file_location('global_source_equation_algebra', HERE/'equations.py')
eq = importlib.util.module_from_spec(spec)
spec.loader.exec_module(eq)
R, FIELD = eq.R, eq.FIELD
rz, rx, ry, rU, rT, rl = eq.rz, eq.rx, eq.ry, eq.rU, eq.rT, eq.rl
P, pu = ring('U', FIELD)
AXES = [rx, ry, rz]
read = eq.read


def evaluate_jet(source, point, frequency):
    """Full289 jet circuit; numerators with explicit denominators at the same U(T).

    At nonzero exact momenta it uses the complete Fhat quotient, without replacing
    the distinguished source root by a dispersion truncation. At the origin the
    source's own U(0)=0 evaluation is used directly.
    """
    point = list(map(s.sympify, point))
    physical_T = s.expand(sum(v*v for v in point)/2)
    ground = [eq.scalar(point[2]), eq.scalar(point[0]), eq.scalar(point[1]),
              None, eq.scalar(physical_T), eq.scalar(frequency)]
    raw_mod = eq.poly(source['complete_Fhat'])
    def raw_evaluate(expression):
        coefficients = {}
        for monomial, value in expression.items():
            out = value
            for j, exponent in enumerate(monomial):
                if j != 3 and exponent: out *= ground[j]**exponent
            coefficients[monomial[3]] = coefficients.get(monomial[3], FIELD.zero)+out
        return P.from_dict({(i,): v for i, v in coefficients.items() if v})
    origin = all(v == 0 for v in point)
    modulus = pu if origin else raw_evaluate(raw_mod)
    def reduce(value): return value.rem(modulus)
    def ev(expression): return reduce(raw_evaluate(expression))
    def mul(a, b): return reduce(a*b)
    cf = eq.scalar(s.sympify(source['source_coefficient']))
    root = raw_mod.quo_ground(cf)
    g, a = ev(root.diff(rU)), -ev(root.diff(rT))
    g2, g3 = mul(g, g), mul(mul(g, g), g)
    b = reduce(-mul(ev(root.diff(rT).diff(rT)), g2)
               -2*mul(ev(root.diff(rU).diff(rT)), mul(a, g))
               -mul(ev(root.diff(rU).diff(rU)), mul(a, a)))
    assert g.gcd(modulus) == P.one
    assert g == ev(eq.poly(source['denominator_D']))
    kg = [P.ground_new(eq.scalar(v)) for v in point]

    def total(expression):
        value, nU, nT = ev(expression), ev(expression.diff(rU)), ev(expression.diff(rT))
        radial = mul(g, nT)+mul(a, nU)
        spatial = [ev(expression.diff(a)) for a in AXES]
        mixed = [mul(g, ev(expression.diff(axis).diff(rT)))+mul(a, ev(expression.diff(axis).diff(rU))) for axis in AXES]
        radial2 = mul(g3, ev(expression.diff(rT).diff(rT)))+2*mul(mul(a, g2), ev(expression.diff(rU).diff(rT)))
        radial2 += mul(mul(mul(a, a), g), ev(expression.diff(rU).diff(rU)))+mul(b, nU)
        first = [reduce(mul(g, spatial[i])+mul(kg[i], radial)) for i in range(3)]
        second = {}
        for i in range(3):
            for j in range(i, 3):
                second[i, j] = reduce(mul(g3, ev(expression.diff(AXES[i]).diff(AXES[j])))
                    +(mul(g2, radial) if i == j else P.zero)+mul(mul(g2, kg[i]), mixed[j])+mul(mul(g2, kg[j]), mixed[i])
                    +mul(mul(kg[i], kg[j]), radial2))
        return value, first, second

    def quotient(expressions, denominator):
        d, di, dij = total(denominator)
        assert d.gcd(modulus) == P.one
        d2 = mul(d, d)
        values, first = [], [[] for _ in range(3)]
        second = {(i, j): [] for i in range(3) for j in range(i, 3)}
        for expression in expressions:
            n, ni, nij = total(expression)
            gradient = [reduce(mul(ni[i], d)-mul(n, di[i])) for i in range(3)]
            values.append(n)
            for i in range(3):
                first[i].append(gradient[i])
                for j in range(i, 3):
                    second[i, j].append(reduce(mul(nij[i, j], d2)
                        -mul(mul(g, d), mul(ni[i], di[j])+mul(ni[j], di[i]))
                        -mul(mul(n, d), dij[i, j])+2*mul(mul(g, n), mul(di[i], di[j]))))
        return {'value': values, 'first': first, 'second': second,
                'denominators': [d, mul(g, d2), mul(g3, mul(d2, d))]}

    A, B, Z = [eq.column(source['columns'][name]['global_numerator']) for name in ['A', 'B', 'Z']]
    D = eq.poly(source['denominator_D'])
    c2 = R.ground_new(eq.scalar(s.sympify(source['physical_clock'])**2))
    numerator = [rl*a+b for a, b in zip(A, B)]
    denominator = D*(rl*rl-c2*rU)
    X = quotient(numerator, denominator)
    I = quotient(Z, D)
    dU = reduce(mul(ev(numerator[57].diff(rU)), ev(denominator))-mul(X['value'][57], ev(denominator.diff(rU))))
    return {'X': X, 'I': I, 'modulus': modulus, 'up_numerator': a, 'upp_numerator': b, 'root_denominator': g,
            'evaluate': ev, 'reduce': reduce, 'mul': mul, 'g00_partial_U': dU,
            'physical_T': physical_T, 'origin': origin}


def main():
    start = time.monotonic()
    source, actual = read(HERE/'source.json'), read(eq.BASE/'active-gauge/receipt.json')
    c = s.sympify(source['physical_clock'])
    frequency = s.expand(c*(7-2*s.I))
    rho = s.Rational(1, 131072)
    n = [s.Rational(2, 7), -s.Rational(3, 7), s.Rational(6, 7)]
    points = [('origin', [0, 0, 0]), ('nonaxis', [s.sqrt(2)*rho*v for v in n])]
    Fhat = s.sympify(source['complete_Fhat'], locals=eq.locals_)
    r = s.Symbol('r', real=True)
    remainder = s.sympify(source['source_root_remainder'], locals={'r': r, 'w': eq.T})
    center = s.Rational(125, 162)
    cf = s.sympify(source['source_coefficient'])
    E = r-center+eq.T*remainder
    assert s.expand(Fhat.subs(eq.U, eq.T*r)-cf*eq.T*E) == 0
    denominator = s.sympify(source['denominator_D'], locals=eq.locals_)
    assert s.expand(denominator.subs(eq.U, eq.T*r)-s.diff(E, r)) == 0
    origin_up = s.cancel(-s.diff(Fhat, eq.T)/s.diff(Fhat, eq.U)).subs({eq.U: 0, eq.T: 0})
    assert origin_up == center
    origin_upp = s.cancel(-(s.diff(Fhat, eq.T, 2)+2*origin_up*s.diff(Fhat, eq.U, eq.T)
                          +origin_up**2*s.diff(Fhat, eq.U, 2))/s.diff(Fhat, eq.U)).subs({eq.U: 0, eq.T: 0})
    print('PASS same normalized root, full implicit U derivatives and actual Uprime(0)', origin_up, flush=True)
    physical = [rl, -R.ground_new(eq.scalar(s.I))*rx,
                 -R.ground_new(eq.scalar(s.I))*ry, -R.ground_new(eq.scalar(s.I))*rz]
    operator = {}
    for i, j, powers, value in actual['Fourier_Jacobi_entries']:
        term = R.ground_new(eq.scalar(s.sympify(value)))
        for a, degree in zip(physical, powers): term *= a**degree
        operator[i, j] = operator.get((i, j), R.zero)+term
    records = []
    def sparse_vector(values):
        return [[i, str(v.as_expr(eq.U))] for i, v in enumerate(values) if v]
    for label, point in points:
        data = evaluate_jet(source, point, frequency)
        red, mul, ev = data['reduce'], data['mul'], data['evaluate']
        X, I = data['X'], data['I']
        g = data['root_denominator']
        qfield = X['denominators'][0]
        L = ev(rl*rl-R.ground_new(eq.scalar(c*c))*rU)
        gq = mul(g, qfield)
        g2q = mul(mul(g, g), qfield)
        g3q2 = mul(mul(mul(g, g), g), mul(qfield, qfield))
        def scale(q, vector): return [mul(q, v) for v in vector]
        def apply(axes, vector):
            out = [P.zero for _ in range(289)]
            for (i, j), value in operator.items():
                for axis in axes: value = value.diff(AXES[axis])
                if value and vector[j]: out[i] += mul(ev(value), vector[j])
            return list(map(red, out))
        def check(*parts):
            failures = [i for i in range(289) if red(sum((v[i] for v in parts), P.zero))]
            assert not failures, failures[:8]
        check(apply([], X['value']), scale(-L, I['value']))
        for i in range(3):
            check(apply([], X['first'][i]), scale(gq, apply([i], X['value'])), scale(-mul(L, L), I['first'][i]))
            for j in range(i, 3):
                check(apply([], X['second'][i, j]), scale(g2q, apply([i], X['first'][j])),
                      scale(g2q, apply([j], X['first'][i])), scale(g3q2, apply([i, j], X['value'])),
                      scale(-mul(mul(L, L), L), I['second'][i, j]))
        entry = {'point': label, 'physical_k': list(map(str, point)), 'all289_value_first_second_equations': True,
                 'root_implicit_first_second_retained': True,
                 'nonzero_X_numerator_rows': len(sparse_vector(X['value'])), 'nonzero_I_numerator_rows': len(sparse_vector(I['value']))}
        if label == 'origin':
            assert data['up_numerator'] == g.mul_ground(eq.scalar(origin_up))
            assert data['upp_numerator'] == mul(mul(g, g), g).mul_ground(eq.scalar(origin_upp))
            A0, Z0 = [eq.column(source['columns'][name]['origin']) for name in ['A', 'Z']]
            assert X['value'] == [ev(v).mul_ground(eq.scalar(frequency)) for v in A0]
            assert I['value'] == list(map(ev, Z0))
            entry['common_X_denominators'] = [str(v.as_expr(eq.U)) for v in X['denominators']]
            entry['common_I_denominators'] = [str(v.as_expr(eq.U)) for v in I['denominators']]
            entry['origin_X_numerator'] = sparse_vector(X['value'])
            entry['origin_I_numerator'] = sparse_vector(I['value'])
            entry['origin_first'] = [{'axis': i, 'X_numerator': sparse_vector(X['first'][i]), 'I_numerator': sparse_vector(I['first'][i])} for i in range(3)]
            entry['origin_second'] = [{'axes': [i, j], 'X_numerator': sparse_vector(X['second'][i, j]), 'I_numerator': sparse_vector(I['second'][i, j])}
                                      for i in range(3) for j in range(i, 3)]
        else:
            error1 = mul(data['up_numerator']-g.mul_ground(eq.scalar(center)), data['g00_partial_U'])
            error2 = mul(data['upp_numerator'], data['g00_partial_U'])
            assert error1 and error2 and error1.gcd(data['modulus']).degree() == error2.gcd(data['modulus']).degree() == 0
            entry['wrong_constant_dispersion_first_nonzero_gcd'] = 0
            entry['omitted_U_second_nonzero_gcd'] = 0
            entry['g00_value_numerator'] = str(X['value'][57].as_expr(eq.U))
            entry['g00_common_denominators'] = [str(v.as_expr(eq.U)) for v in X['denominators']]
            entry['g00_direction_first_numerator'] = str(red(sum((X['first'][i][57].mul_ground(eq.scalar(n[i])) for i in range(3)), P.zero)).as_expr(eq.U))
            entry['g00_direction_second_numerator'] = str(red(sum((X['second'][i, j][57].mul_ground(eq.scalar((1 if i == j else 2)*n[i]*n[j]))
                for i in range(3) for j in range(i, 3)), P.zero)).as_expr(eq.U))
        records.append(entry)
        print('PASS physical full289 source/value/gradient/Hessian', label, flush=True)
    output = {'scope': 'STRIKE_SAME_ROOT_GLOBAL_ANALYTIC_TRANSFER_AND_ACTUAL_PHYSICAL_FIRST_SECOND_JETS',
              'input_sha256': {str(p.relative_to(eq.ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in [HERE/'source.json', eq.BASE/'active-gauge/receipt.json']},
              'normalized_full_root_identity': 'Fhat(T*r,T)=cF*T*(r-125/162+T*P(r,T))',
              'root_first': '-F_T/F_U', 'root_second': '-(F_TT+2*F_UT*Uprime+F_UU*Uprime^2)/F_U',
              'root_first_at0': str(origin_up), 'root_second_at0': str(origin_upp),
              'physical_composition': 'd_i g=partial_i g+k_i*(partial_T g+Uprime*partial_U g); d_ij includes delta_ij, both explicit-radial crosses and k_i*k_j*Udoubleprime*partial_U g',
              'quotient_jet': 'q X=P; q Xi=Pi-qi X; q Xij=Pij-qi Xj-qj Xi-qij X',
              'stored_jet_convention': 'Value/first/second vectors are exact numerators; divide by the matching common denominator. Uprime=a/D and Udoubleprime=b/D^3 are never expanded as inverses in the complete-F quotient.',
              'analytic_domain': 'Same source U(T) analytic near the closed original light ball, D in [39/40,41/40]; lambda^2-c^2 U nonzero. This includes every Re(lambda)>=5 and the origin.',
              'physical_frequency_for_consumers': str(frequency), 'consumers': records,
              'no_low_order_dispersion_replacement': True,
              'seconds': round(time.monotonic()-start, 3)}
    (HERE/'jets.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS source global analytic jets', output['seconds'], flush=True)


if __name__ == '__main__': main()
