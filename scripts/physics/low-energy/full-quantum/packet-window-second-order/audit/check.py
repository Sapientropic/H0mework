#!/usr/bin/env python3
"""Independent horizontal-disk integration, source controls and isolated replay."""
import contextlib
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import time
from unittest.mock import patch
import sympy as s

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
FQ = HERE.parents[1]
ROOT = HERE.parents[5]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def main():
    start = time.monotonic()
    names = ['compute.py', 'receipt.json', 'README.md', 'check.log', 'construction.json']
    paths = [HERE.parent/name for name in names]
    before = {p.name: digest(p) for p in paths}
    construction = read(HERE.parent/'construction.json')
    assert all(before[name] == sha for name, sha in construction['candidate_sha256'].items())
    frozen = read(HERE.parent/'receipt.json')
    assert all(digest(ROOT/path) == sha for path, sha in frozen['source_inputs_sha256'].items())
    raw = read(FQ/'packet-field/current-data.json')['selected']
    assert raw['shape'] == [289, 289] and raw['source_coordinate'] == [1, 1]
    Q = {(i, j): s.sympify(value) for i, j, value in raw['entries']}
    assert all(s.conjugate(value) == value and Q[j, i] == value for (i, j), value in Q.items())
    Bbb = sum(Q.get((i, j), 0) for i in [9, 259] for j in [9, 259])
    assert Bbb == 4
    x, y, t = s.symbols('x y t', real=True)
    R, delta = s.symbols('R delta', positive=True)
    variables = [x, y, t]
    v = s.Matrix([s.Rational(2, 3), -s.Rational(1, 3), s.Rational(2, 3)])
    normal = s.Matrix([0, 0, 1])-v
    O = s.eye(3)-2*normal*normal.T/(normal.T*normal)[0]
    assert O.T*O == s.eye(3) and O[:, 2] == v
    kx, ky, kz = O*s.Matrix(variables)
    g = s.expand(1+(2+s.I)*kx+(1-2*s.I)*ky+s.I*kz+
                 (1+s.I)*kx*ky+(2-s.I)*kz**2)
    def real(expr):
        return s.expand(s.expand_complex(expr).as_real_imag()[0])
    def disk(expr, radius2, circle=False):
        result = 0
        for (a, b, c), value in s.Poly(s.expand(expr), x, y, t).terms():
            if a % 2 or b % 2:
                continue
            m, n = a//2, b//2
            if circle:
                coefficient = 2*s.gamma(m+s.Rational(1, 2))*s.gamma(n+s.Rational(1, 2))/s.gamma(m+n+1)
                result += value*coefficient*radius2**(m+n)*t**c
            else:
                coefficient = s.pi*s.factorial(2*m)*s.factorial(2*n)/(
                    4**(m+n)*s.factorial(m)*s.factorial(n)*s.factorial(m+n+1))
                result += value*coefficient*radius2**(m+n+1)*t**c
        return s.expand(result)
    density = (2*s.pi)**-3
    paired = Bbb*real(s.conjugate(g)*g.subs(t, t+delta))
    # The intersection splits at t=-delta/2. These are actual disk radii
    # and moving vertical endpoints, rather than the candidate chord variable.
    lower = s.integrate(disk(paired, R**2-t**2), (t, -R, -delta/2))
    upper = s.integrate(disk(paired, R**2-(t+delta)**2), (t, -delta/2, R-delta))
    L = s.factor(density*(lower+upper)/2)
    diagonal = Bbb*real(s.conjugate(g)*g)
    sphere_diagonal = disk(diagonal, R**2-t**2, circle=True)
    cv = s.simplify(density/4*(s.integrate(-t*sphere_diagonal, (t, -R, 0))+
                              s.integrate(t*sphere_diagonal, (t, 0, R))))
    acceleration = Bbb*real(s.conjugate(g)*s.diff(g, t, 2))
    bulk = s.simplify(s.integrate(disk(acceleration, R**2-t**2), (t, -R, R)))
    K = s.simplify(density*bulk/4)
    assert s.simplify(s.diff(L, delta).subs(delta, 0)+cv) == 0
    assert s.simplify(s.diff(L, delta, 2).subs(delta, 0)/2-K) == 0
    residual = s.Poly(s.expand(L-L.subs(delta, 0)+cv*delta-K*delta**2), delta)
    assert all(residual.nth(j) == 0 for j in range(3))
    cross = Bbb*real(s.conjugate(g)*s.diff(g, t))
    energy = s.simplify(s.integrate(disk(Bbb*real(s.conjugate(s.diff(g, t))*s.diff(g, t)),
                                            R**2-t**2), (t, -R, R)))
    flux = s.simplify(s.integrate(t*disk(cross, R**2-t**2, circle=True), (t, -R, R)))
    assert s.simplify(flux-energy-bulk) == 0
    assert flux != 0 and s.simplify(-density*energy/4-K) != 0
    # Full W/J product, with different non-cancelling phases and original Q.
    alpha, theta = 3*s.I*Bbb, -5*s.I
    zeta, eta, gamma = -9*Bbb, -25, 9*Bbb
    actual_second = zeta+2*s.re(alpha*theta)+Bbb*eta
    wrong_second = zeta+2*s.re(alpha)*s.re(theta)+Bbb*eta
    actual_gradient = gamma+25*Bbb+2*s.re(s.conjugate(alpha)*theta)
    wrong_gradient = gamma+25*Bbb+2*s.re(alpha*theta)
    assert (actual_second, wrong_second, actual_gradient, wrong_gradient) == (-16, -136, 16, 256)
    # Integral-kernel remainder constants, including the entire short-chord set.
    h, r = s.symbols('h r', nonnegative=True)
    short_area = s.integrate(2*s.pi*h, (h, 0, delta/2))
    short_volume = s.integrate(4*s.pi*h**2, (h, 0, delta/2))
    assert short_area == s.pi*delta**2/4 and short_volume == s.pi*delta**3/6
    assert s.integrate(delta-r, (r, 0, delta)) == delta**2/2
    assert s.integrate((delta-r)*r, (r, 0, delta)) == delta**3/6
    assert s.Rational(1, 3)+s.Rational(1, 2) == s.Rational(5, 6)
    assert s.Rational(1, 3)+s.Rational(1, 2)+s.Rational(1, 2) == s.Rational(4, 3)
    assert short_volume+delta*short_area == 5*s.pi*delta**3/12
    assert delta**2*short_volume/2 == s.pi*delta**5/12
    spec = importlib.util.spec_from_file_location('frozen_second_order', HERE.parent/'compute.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    write_text = Path.write_text
    stdout = io.StringIO()
    def redirect(path, data, *args, **kwargs):
        assert path.resolve() == (HERE.parent/'receipt.json').resolve(), path
        return write_text(HERE/'replay-receipt.json', data, *args, **kwargs)
    with patch.object(Path, 'write_text', redirect), contextlib.redirect_stdout(stdout):
        module.main()
    (HERE/'replay.log').write_text(stdout.getvalue())
    replay = read(HERE/'replay-receipt.json')
    assert {k: value for k, value in replay.items() if k != 'elapsed_seconds'} == {
        k: value for k, value in frozen.items() if k != 'elapsed_seconds'}
    assert before == {p.name: digest(p) for p in paths}
    result = {
        'passed': True, 'scope': 'actual-source analytic second-coefficient identity; no value for actual K integral',
        'source_Q_test_vector': 'e9+e259', 'source_pairing': str(Bbb),
        'independent_direction': list(map(str, v)),
        'independent_method': 'piecewise horizontal disks across the exact intersection midplane',
        'test_scalar_polynomial_in_rotated_coordinates': str(g),
        'test_not_replacement_of_actual_WJ': True,
        'exact_three_dimensional_test_L': str(L),
        'test_cusp_coefficient': str(cv), 'test_second_coefficient': str(K),
        'test_IBP_flux': str(flux), 'test_gradient_energy': str(energy),
        'test_remainder_after_second_order': str(residual.as_expr()),
        'uniform_remainder_constants_independently_rederived': True,
        'controls': {'drop_sphere_flux_rejected': True,
                     'response_second_coefficient_vs_loss_sign': True,
                     'source_phase_full_second_contraction': int(actual_second),
                     'wrong_drop_imaginary_cross': int(wrong_second),
                     'source_phase_full_gradient_contraction': int(actual_gradient),
                     'wrong_gradient_left_conjugate': int(wrong_gradient)},
        'frozen_replay_match_except_elapsed_time': True,
        'candidate_sha256': before,
        'elapsed_seconds': round(time.monotonic()-start, 3),
    }
    (HERE/'receipt.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS independent three-dimensional integration, remainders, complex source controls and replay')
    print('K for the explicit nonaxial test:', K)
    print(result['elapsed_seconds'], 'seconds')


if __name__ == '__main__':
    main()
