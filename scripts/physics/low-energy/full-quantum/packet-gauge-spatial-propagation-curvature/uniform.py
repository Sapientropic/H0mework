#!/usr/bin/env python3
"""Whole-radius effective-row/force bounds for the genuine propagation kernel."""
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial
import importlib.util
import json
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('uniform_source', HERE/'source.py')
source = importlib.util.module_from_spec(spec); spec.loader.exec_module(source)
FQ, BASE = source.FQ, source.BASE
sys.path.insert(0, str(FQ/'packet-band-kernel'))
from intervals import Box


@lru_cache(None)
def coefficient_bound(value):
    amount = F(0)
    for part in [s.expand(s.re(value)), s.expand(s.im(value))]:
        for radical, upper in [(s.sqrt(30), F(5478, 1000)), (s.sqrt(15), F(3873, 1000)), (s.sqrt(2), F(1415, 1000))]:
            c = part.coeff(radical); assert c.is_Rational
            amount += abs(F(str(c)))*upper
            part = s.expand(part-c*radical)
        assert part.is_Rational
        amount += abs(F(str(part)))
    return amount


def product_jet(a, b):
    return [sum(F(comb(n, j))*a[j]*b[n-j] for j in range(n+1)) for n in range(5)]


def power_jet(a, n):
    result = [F(1), F(0), F(0), F(0), F(0)]
    for _ in range(n): result = product_jet(result, a)
    return result


def main():
    started = time.monotonic()
    glob = source.read(FQ/'packet-gauge-global-transfer/source.json')
    actual = source.read(BASE/'active-gauge/receipt.json')
    kernel = source.read(HERE/'kernel.json')
    axis = source.read(HERE/'axis-source.json')
    inverse = source.read(HERE/'inverse-series.json')
    U, T = s.symbols('U T', real=True)
    q = s.symbols('q1:4', real=True)
    kx, ky, kz = s.symbols('kx ky kz', real=True)
    z = s.sympify(kernel['physical_frequency']); c = s.sympify(glob['physical_clock'])
    eps = F(5234375, 294988800512); tiny = eps*eps
    Fbar = s.Poly(s.sympify(glob['complete_Fhat'], locals={'U': U, 'T': T})/s.sympify(glob['source_coefficient']), U, T)
    Den = Fbar.diff(U)
    def radial(P): return sum(coefficient_bound(v)*tiny**sum(a) for a, v in P.terms())
    error = radial(Den-s.Poly(1, U, T)); lower = 1-error
    assert lower > F(39, 40)
    derivatives = s.symbols('u1:5', real=True)
    expression = Fbar.as_expr(); root_bounds = []
    for order in range(1, 5):
        expression = s.diff(expression, T)+derivatives[0]*s.diff(expression, U)+sum(
            derivatives[j+1]*s.diff(expression, derivatives[j]) for j in range(3))
        rest = s.expand(expression-Den.as_expr()*derivatives[order-1])
        P = s.Poly(rest, U, T, *derivatives[:order-1])
        bound = F(0)
        for a, value in P.terms():
            term = coefficient_bound(value)*tiny**(a[0]+a[1])
            for power, b in zip(a[2:], root_bounds): term *= b**power
            bound += term
        root_bounds.append(bound/lower)
    u1, u2, u3, u4 = root_bounds
    Tjet = [tiny, 2*eps, F(2), F(0), F(0)]
    Ujet = [tiny, 2*u1*eps, 4*u2*eps**2+2*u1,
            8*u3*eps**3+12*u2*eps,
            16*u4*eps**4+48*u3*eps**2+12*u2]
    axes = [*q, U, T]
    bounds = [[eps, F(1), F(0), F(0), F(0)]]*3+[Ujet, Tjet]
    def polyjet(expression):
        P = s.Poly(s.expand(expression), *axes)
        total = [F(0)]*5
        for powers, value in P.terms():
            term = [coefficient_bound(value), F(0), F(0), F(0), F(0)]
            for power, b in zip(powers, bounds): term = product_jet(term, power_jet(b, power))
            total = [a+b for a, b in zip(total, term)]
        return total
    denominator = Den.as_expr()*(z*z-c*c*U)
    dj = polyjet(denominator)
    invj = [1/(lower*F(str(s.expand(z*s.conjugate(z)))))]
    for n in range(1, 5): invj.append(invj[0]*sum(F(comb(n, j))*dj[j]*invj[n-j] for j in range(1, n+1)))
    names = {str(v): v for v in [kx, ky, kz, U, T]}
    def column(label):
        return s.SparseMatrix(289, 1, {(i, j): s.expand(s.sympify(v, locals=names).subs(
            {kx: s.sqrt(2)*q[0], ky: s.sqrt(2)*q[1], kz: s.sqrt(2)*q[2]}))
            for i, j, v in glob['columns'][label]['global_numerator']['entries']})
    Fnum = source.clean(z*column('A')+column('B'))
    keep = kernel['keep112']; D = source.matrix(kernel['actual_normalization_D'])
    lift = s.MutableSparseMatrix(289, 112, {(i, j): D[j, j] for j, i in enumerate(keep)})
    momentum = [z, *[-s.I*s.sqrt(2)*v for v in q]]
    for step in reversed(actual['algebraic_Schur_steps']):
        W = source.native.ward.operator(step['write_back_auxiliary_from_retained'], values=momentum)
        lift = source.clean(lift+W*lift)
    bg = actual['algebraic_Schur_steps'][0]['eliminated_fields']
    assert len(bg) == 72
    r = s.Symbol('r', real=True)
    def profile_matrix(record):
        M = source.native.matrix(record, {str(v): v for v in [r, *source.d]})
        return source.clean(M.subs({r: 0, **{a: -s.sqrt(2)*v for a, v in zip(source.d, q)}}, simultaneous=True))
    left, left_bg = [F(0)]*5, [F(0)]*5
    left_records = []
    for profile in axis['profiles']:
        Q = profile_matrix(profile['Q'])
        row, row_bg = source.clean(s.conjugate(Fnum).T*Q*lift), source.clean(s.conjugate(Fnum).T*Q[:, bg])
        one = [F(0)]*5; two = [F(0)]*5
        for value in row.todok().values(): one = [a+b for a, b in zip(one, polyjet(value))]
        for value in row_bg.todok().values(): two = [a+b for a, b in zip(two, polyjet(value))]
        one, two = product_jet(one, invj), product_jet(two, invj)
        left = [max(a, b) for a, b in zip(left, one)]
        left_bg = [max(a, b) for a, b in zip(left_bg, two)]
        left_records.append({'direction': profile['direction'], 'left': list(map(str, one)), 'left_Bg': list(map(str, two))})
    print('PASS actual effective reader rows after whole auxiliary lift', list(map(float, left)), flush=True)
    qr = s.Symbol('q', real=True)
    def rhs_bounds(data):
        result = {}
        for beta, record in data:
            table = source.native.matrix(record, {'q': qr, 'U': U})
            largest = [F(0)]*5
            for value in table.todok().values():
                bound = product_jet(polyjet(value.subs(qr, q[2])), invj)
                largest = [max(a, b) for a, b in zip(largest, bound)]
            result[tuple(beta)] = largest
        out = {}
        for a in range(5):
            out[a, 0] = result[0, 0, 0][a]
            if a <= 3:
                out[a, 1] = Box(sum(result[tuple(1 if j == i else 0 for j in range(3))][a]**2 for i in range(3))).sqrt().hi
            if a <= 2:
                out[a, 2] = max(sum(result[tuple((1 if l == i else 0)+(1 if l == j else 0) for l in range(3))][a]
                                      for j in range(3)) for i in range(3))
        return out
    force = rhs_bounds(kernel['normalized_force_jets'])
    particular = rhs_bounds(kernel['auxiliary_backwrites'][0]['particular'])
    assert all(not record['entries'] for step in kernel['auxiliary_backwrites'][1:] for beta, record in step['particular'])
    table = {(tuple(v['transverse']), v['radial_order']): F(v['normalized_q_coordinate_derivative_bound'])
             for v in inverse['uniform_derivatives']}
    p = {}
    for a in range(5):
        p[a, 0] = table[(0, 0), a]
        if a <= 3:
            p[a, 1] = Box(table[(1, 0), a]**2+table[(0, 1), a]**2+table[(0, 0), a+1]**2).sqrt().hi
        if a <= 2:
            values = [[table[(2, 0), a], table[(1, 1), a], table[(1, 0), a+1]],
                      [table[(1, 1), a], table[(0, 2), a], table[(0, 1), a+1]],
                      [table[(1, 0), a+1], table[(0, 1), a+1], table[(0, 0), a+2]]]
            p[a, 2] = max(map(sum, values))
    scalar = {}
    for a in range(5):
        for b in range(min(2, 4-a)+1):
            total = F(0)
            for ar in range(a+1):
                for br in range(b+1):
                    for ap in range(a-ar+1):
                        for bp in range(b-br+1):
                            af, bf = a-ar-ap, b-br-bp
                            factor = F(comb(a, ar)*comb(a-ar, ap)*comb(b, br)*comb(b-br, bp))
                            total += factor*left[ar+br]*p[ap, bp]*force[af, bf]
                    total += F(comb(a, ar)*comb(b, br))*left_bg[ar+br]*particular[a-ar, b-br]
            # Each real native dyad has l1 coefficient norm <=3. The same
            # source and reader are retained; this is only a uniform bound.
            scalar[a, b] = 9*total/(Box(2).sqrt()**(a+b)).lo
    report = {'scope': 'SOURCE_GENERATED_WHOLE_LIGHT_BALL_PROPAGATION_SCALAR_MIXED_BOUNDS',
              'normalization': 'Original normalized112, physical k=sqrt2*q; actual dyad reader and source each l1<=3',
              'root_U_T_derivatives': list(map(str, root_bounds)), 'root_D_lower': str(lower),
              'root_U_q_mixed_jets': list(map(str, Ujet)),
              'effective_reader_rows': left_records,
              'effective_reader_uniform_q_jets': list(map(str, left)),
              'effective_Bg_reader_uniform_q_jets': list(map(str, left_bg)),
              'actual_source_force_mixed_q_bounds': [[a, b, str(v)] for (a, b), v in force.items()],
              'actual_particular_Bg_mixed_q_bounds': [[a, b, str(v)] for (a, b), v in particular.items()],
              'original_inverse_mixed_q_bounds': [[a, b, str(v)] for (a, b), v in p.items()],
              'scalar_physical_mixed_bounds': [[a, b, str(v)] for (a, b), v in scalar.items()],
              'non_Bg_particular_exact_zero': True,
              'seconds': round(time.monotonic()-started, 3)}
    (HERE/'uniform.json').write_text(json.dumps(report, separators=(',', ':'))+'\n')
    print('PASS actual full propagation scalar physical mixed bounds',
          [(key, float(value)) for key, value in scalar.items()], report['seconds'], flush=True)


if __name__ == '__main__': main()
