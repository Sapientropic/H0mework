#!/usr/bin/env python3
"""Independent directed arithmetic and cap remainder/matrix-sign consumer."""
from fractions import Fraction as F
from math import comb, isqrt
from pathlib import Path
import json
import sys
import time
import sympy as s

sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
CANDIDATE = HERE.parent
FQ = CANDIDATE.parent
UNIT = 2**512


class Interval:
    def __init__(self, lo, hi=None):
        self.lo, self.hi = F(lo), F(lo if hi is None else hi)
        assert self.lo <= self.hi
    def __add__(a, b):
        b = promote(b); return Interval(a.lo+b.lo, a.hi+b.hi)
    __radd__ = __add__
    def __neg__(a): return Interval(-a.hi, -a.lo)
    def __sub__(a, b): return a+-promote(b)
    def __mul__(a, b):
        b = promote(b); values = [x*y for x in [a.lo, a.hi] for y in [b.lo, b.hi]]
        return Interval(min(values), max(values))
    __rmul__ = __mul__
    def inverse(a):
        assert a.lo > 0 or a.hi < 0
        return Interval(1/a.hi, 1/a.lo)
    def __truediv__(a, b): return a*promote(b).inverse()
    def __rtruediv__(a, b): return promote(b)*a.inverse()
    def __pow__(a, n):
        assert n >= 0
        value = Interval(1)
        for _ in range(n): value = value*a
        return value
    def sqrt(a):
        assert a.lo >= 0
        def end(v, upper):
            p, q = isqrt(v.numerator), isqrt(v.denominator)
            if p*p == v.numerator and q*q == v.denominator:
                return F(p, q)
            integer = isqrt(v.numerator*UNIT*UNIT//v.denominator)
            return F(integer+int(upper), UNIT)
        return Interval(end(a.lo, False), end(a.hi, True))
    def record(a): return [str(a.lo), str(a.hi)]


def promote(value): return value if isinstance(value, Interval) else Interval(value)
def read(path): return json.loads(path.read_bytes())
def decode(row): return Interval(*map(F, row['rational']))
def up(value): return F(-((-value.numerator*10**14)//value.denominator), 10**14)
def absolute_box(value): return max(abs(value.lo), abs(value.hi))
def norm_complex(row):
    return (Interval(absolute_box(decode(row['real'])))**2+
            Interval(absolute_box(decode(row['imaginary'])))**2).sqrt().hi


def arctangent(inverse):
    value, count = F(0), 150
    for n in range(count): value += F((-1)**n, (2*n+1)*inverse**(2*n+1))
    next_term = F(1, (2*count+1)*inverse**(2*count+1))
    return Interval(value, value+next_term)


def main():
    began = time.monotonic()
    left = read(CANDIDATE/'uniform.json')
    solution = read(CANDIDATE/'solution-series.json')
    angular = read(CANDIDATE/'angular.json')
    published = read(CANDIDATE/'remainder.json')
    complete = read(CANDIDATE/'complete.json')
    quantum = read(FQ/'packet-gauge-probe-fourth/receipt.json')
    moments = read(FQ/'packet-gauge-probe-moments/integrals.json')
    others = read(FQ/'packet-gauge-projected-source-reader/receipt.json')
    pi = 16*arctangent(5)-4*arctangent(239)
    eps = F(5234375, 294988800512)
    B = Interval(2).sqrt()*eps
    l, lb = [list(map(lambda v: up(F(v)), left[key])) for key in
             ['effective_reader_uniform_q_jets', 'effective_Bg_reader_uniform_q_jets']]
    part = {(a, b): up(F(v)) for a, b, v in left['actual_particular_Bg_mixed_q_bounds']}
    ys = {(tuple(row['external_multiindex']), row['radial_order']): up(F(row['normalized_q_source_solution_derivative']))
          for row in solution['uniform_derivatives']}
    y = {}
    for a in range(5):
        y[a, 0] = ys[(0, 0, 0), a]
        if a <= 3:
            y[a, 1] = up(Interval(sum(ys[tuple(int(k == j) for k in range(3)), a]**2 for j in range(3))).sqrt().hi)
        if a <= 2:
            y[a, 2] = max(sum(ys[tuple(int(k == i)+int(k == j) for k in range(3)), a] for j in range(3)) for i in range(3))
    D = {}
    for a in range(5):
        for b in range(min(2, 4-a)+1):
            value = sum(F(comb(a, i)*comb(b, j))*(l[i+j]*y[a-i, b-j]+lb[i+j]*part[a-i, b-j])
                        for i in range(a+1) for j in range(b+1))
            D[a, b] = up(9*value/(Interval(2).sqrt()**(a+b)).lo)
    oldD = {(a, b): F(v) for a, b, v in published['physical_scalar_mixed_bounds']}
    assert all(value <= oldD[a] for a, value in D.items())
    gram = {row['name']: row for row in moments['all_two_probe_Gram_jets']}
    raw = [up(F(row['actual_frequency_light_ball_B'])) for row in quantum['vector_derivatives']]
    norm, left_re = s.symbols('norm left_re', real=True)
    leading_polynomials = [s.Poly(s.expand(s.sympify(v, locals={'norm': norm, 'left_re': left_re})/s.sqrt(30)), norm, left_re)
                           for v in angular['leading_diagonal_coefficients_divided_by_pi']]
    sectors = {}
    for layer in ['raw', 'mean', 'connected']:
        B0 = decode(gram['N0_left_base'][layer]['real']).sqrt().hi
        B1 = Interval(max(sum(norm_complex(gram[f'N0_mixed_{i}{j}'][layer]) for j in range(3)) for i in range(3))).sqrt().hi
        vector = list(raw)
        if layer == 'mean':
            means = moments['actual_complex_mean_jets']
            mean2 = max(sum(norm_complex(means[f'mean_B_{min(i,j)}{max(i,j)}']) for j in range(3)) for i in range(3))
            vector[2] = up(mean2+B.hi*vector[3])
        vector[1] = up(B1+B.hi*vector[2])
        vector[0] = up(B0+B.hi*B1+B.hi**2*vector[2]/2)
        Nj = {(a, b): sum(F(comb(a, j))*vector[b+j]*vector[a-j] for j in range(a+1))
              for a in range(5) for b in range(min(2, 4-a)+1)}
        M = {}
        for a, b in [(2, 2), (3, 1), (4, 0)]:
            M[a, b] = sum(F(comb(a, i)*comb(b, j))*D[i, j]*Nj[a-i, b-j]
                          for i in range(a+1) for j in range(b+1))
        original_M = {(a, b): F(v) for a, b, v in published['layers'][layer]['full_complex_pair_mixed_fourth_bounds']}
        assert all(value <= original_M[key] for key, value in M.items())
        error = B**5/pi**2*(M[2, 2]/40+M[3, 1]/48+(1+1/Interval(3).sqrt())*M[4, 0]/144)
        assert error.hi <= F(published['layers'][layer]['quadratic_uniform_error_radius'])
        inputs = [decode(gram['N0_left_base'][layer]['real']), decode(gram['N0_left_00'][layer]['real'])]
        leading = []
        for polynomial in leading_polynomials:
            value = Interval(0)
            for powers, coefficient in polynomial.terms():
                assert coefficient.is_Rational
                term = Interval(F(str(coefficient)))
                for index, exponent in enumerate(powers): term = term*inputs[index]**exponent
                value = value+term
            leading.append(value*Interval(30).sqrt()*B**3/(8*pi**2))
        intervals = []
        for i in range(3):
            rest = decode(others['sectors'][layer]['diagonal'][i]['source_two_legs_plus_reader_quadratic_coefficient'])
            current = leading[i]+Interval(-error.hi, error.hi)+rest
            target = decode(complete['sectors'][layer]['complete_five_diagonal_enclosures'][i])
            assert target.lo <= current.lo <= current.hi <= target.hi
            intervals.append(current)
        mixed = F(complete['sectors'][layer]['complete_five_mixed_entry_abs_bound'])
        inertia = None
        if layer != 'mean':
            assert intervals[0].hi+2*mixed < 0
            assert intervals[1].lo-2*mixed > 0
            assert intervals[2].hi+2*mixed < 0
            inertia = {'negative': 2, 'positive': 1, 'zero': 0}
        sectors[layer] = {'sharper_directed_error': error.record(),
            'all_diagonal_intervals_contained_in_published': True,
            'Gershgorin_inertia_independent_of_published_Weyl_argument': inertia,
            'complete_intervals': [value.record() for value in intervals]}

    # Derive each radial cap error constant, with the actual angular measure.
    u, radius = s.symbols('u radius', positive=True)
    angular_abs = s.simplify(4*s.pi*(s.integrate(1-3*u*u, (u, 0, 1/s.sqrt(3)))+
                                        s.integrate(3*u*u-1, (u, 1/s.sqrt(3), 1))))
    assert angular_abs == 16*s.pi/(3*s.sqrt(3))
    body = s.simplify(s.Rational(1, 4)*4*s.pi*radius**5/5/(2*s.pi)**3)
    first = s.simplify(s.Rational(1, 12)*2*s.pi*radius**5/(2*s.pi)**3)
    radial = s.simplify(s.Rational(1, 24)*4*s.pi*radius**5/3/(2*s.pi)**3)
    curvature = s.simplify(s.Rational(1, 96)*angular_abs*radius**5/(2*s.pi)**3)
    assert body == radius**5/(40*s.pi**2)
    assert first == radius**5/(48*s.pi**2)
    assert s.simplify(radial+curvature-radius**5*(1+1/s.sqrt(3))/(144*s.pi**2)) == 0
    result = {'passed': True, 'independent_arithmetic': 'Fraction intervals,512bit integer-square-root enclosures,150-term Machin alternating bounds,14-decimal upward grids',
        'all_source_scalar_and_projected_Gram_bounds_no_larger_than_candidate': True,
        'three_geometric_B5_constants_independently_derived': True,
        'sectors': sectors, 'seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent-bounds.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS independent whole-ball directed bounds, all five sectors and matrix inertia', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
