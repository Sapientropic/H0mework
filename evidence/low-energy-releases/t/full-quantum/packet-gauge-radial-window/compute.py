#!/usr/bin/env python3
"""Direct radial cap calculus for the original fixed-incoming two-ball window."""
import hashlib
import json
from pathlib import Path
import time
import sympy as s

HERE = Path(__file__).resolve().parent
FQ = HERE.parent
ROOT = HERE.parents[4]


def main():
    start = time.monotonic()
    source_path = FQ/'packet-gauge-spatial-current/assembly.json'
    source = json.loads(source_path.read_text())
    R = s.Symbol('R', positive=True)
    h, u = s.symbols('h u', real=True)
    f0, fr, f1 = s.symbols('f0 fr f1')
    branches = []
    for sigma in [-1, 1]:
        old = next(item for item in source['window_tables'] if item['branch'] == sigma
                   and item['term'] == 'right_propagation' and item['outgoing_slope'] == '0'
                   and item['observer'] == 'R_equals_source_radius')
        centers = sorted({s.Rational(a)+sigma for a in old['all_centers']})
        assert centers == sorted([s.Integer(0), s.Integer(sigma)])
        edge = sigma*h*u+s.sqrt(R*R-h*h*(1-u*u))
        assert s.simplify((edge*edge-2*sigma*h*u*edge+h*h-R*R)) == 0
        delta = s.series(edge-R, h, 0, 3).removeO()
        assert s.expand(delta-sigma*h*u+h*h*(1-u*u)/(2*R)) == 0
        # This branch loses the fixed-angle radial strip when sigma*u<0.
        strip = s.expand(delta*R*R*(f0+sigma*h*f1)
                         +delta**2*(2*R*f0+R*R*fr)/2)
        first, second = [s.expand(strip).coeff(h, j) for j in [1, 2]]
        expected = R*R*u*f1 + R*(3*u*u-1)*f0/2 + R*R*u*u*fr/2
        assert s.expand(second-expected) == 0
        branches.append({'sigma': sigma, 'fixed_incoming_window_centers': list(map(str, centers)),
                         'true_radial_edge': str(edge), 'first_strip_coefficient': str(first),
                         'second_strip_coefficient': str(second)})
    # Exact 3-D lens integration of a complex kernel. The second branch is
    # reflected into the first domain before averaging; no angular derivative.
    z = s.Symbol('z', real=True)
    a0, a1, a2, a3 = 2+s.I, 3-2*s.I, 5+s.I, -7+3*s.I
    b0, b1, c0 = 11-s.I, -13+2*s.I, 17+4*s.I
    density = a0+a2*z*z+h*b1*z+h*h*c0/2
    def disk(radius_squared):
        return s.pi*radius_squared*density+a3*s.pi*radius_squared**2/4
    exact = s.expand(s.integrate(disk(R*R-(z-h)**2), (z, h-R, h/2))
                     +s.integrate(disk(R*R-z*z), (z, h/2, R)))
    direct = [s.expand(exact).coeff(h, j) for j in range(3)]
    prediction = [4*s.pi*R**3*a0/3+4*s.pi*R**5*(a2+a3)/15,
                  -s.pi*R*R*a0-s.pi*R**4*a2/2-s.pi*R**4*a3/4,
                  2*s.pi*R**3*(a2+b1+c0)/3]
    assert all(s.expand(a-b) == 0 for a, b in zip(direct, prediction))
    assert direct[2] == 2*s.pi*R**3*(9+7*s.I)/3 or s.expand(direct[2]-2*s.pi*R**3*(9+7*s.I)/3) == 0
    print('PASS exact original two-ball reindex, radial edge and full complex 3-D lens coefficients', flush=True)

    # Angular discontinuity is allowed. For f0(nu)=nu1 1_(nu3>0), a naive
    # ordinary angular derivative misses the actual jump contribution.
    v = s.symbols('v1:4', real=True)
    n = [s.Rational(3, 5), 0, s.Rational(4, 5)]
    uu = sum(a*b for a, b in zip(n, v))
    def hemisphere(expr):
        total = 0
        for powers, coefficient in s.Poly(s.expand(expr), *v).terms():
            a, b, c = powers
            if a % 2 == 0 and b % 2 == 0:
                total += coefficient*s.prod(s.gamma(s.Rational(e+1, 2)) for e in powers) / s.gamma(s.Rational(a+b+c+3, 2))
        return s.simplify(total)
    actual = s.simplify(R*hemisphere((3*uu*uu-1)*v[0])/4)
    naive = s.simplify(R*hemisphere(uu*(n[0]-v[0]*uu))/4)
    assert actual == 9*s.pi*R/50 and naive == 3*s.pi*R/50
    difference = s.simplify(actual-naive)
    assert difference == 3*s.pi*R/25
    output = {'scope': 'DIRECT_RADIAL_CAP_OPERATOR_WITH_BOREL_ANGULAR_DEPENDENCE',
        'input_sha256': {str(source_path.relative_to(ROOT)): hashlib.sha256(source_path.read_bytes()).hexdigest()},
        'original_cosine_half': source['cosine_weights']['boson_and_contact_each_signed_branch'],
        'physical_measure': 'd3k/(2pi)^3, sphere measure dS/(2pi)^3',
        'definition': 'I(h)=1/2 sum_sigma integral_(B intersect (B+sigma*h*n)) Phi(k,sigma*h)',
        'branches': branches,
        'coefficient0': 'integral_B Phi0',
        'coefficient1': '-1/2 integral_S |n.nu| Phi0',
        'coefficient2': '1/2 integral_B Phi2 +1/2 integral_S (n.nu) Phi1 +1/4 integral_S [(n.nu)^2 radial_Phi0+((3*(n.nu)^2-1)/R)*Phi0]',
        'true_switching_belt': '0<sigma*(n.nu)<h/(2R)',
        'belt_area_bound': 'pi*h*R', 'belt_radial_depth_bound': 'h^2/R',
        'belt_volume_bound_each_branch': 'pi*h^3',
        'angular_regularities': 'bounded Borel; no angular derivative or seam continuity',
        'radial_regularities': 'uniform one-sided radial C2 of Phi0 and C1 of Phi1 near R; bounded Phi2; uniform external third-order Taylor control',
        'full_lens_complex_kernel': {'a': list(map(str, [a0, a1, a2, a3])), 'b': list(map(str, [b0, b1])),
                                     'c': str(c0), 'exact_integral': str(exact), 'coefficients': list(map(str, direct))},
        'angular_jump_consumer': {'function': 'nu1 * indicator(nu3>0)', 'direction': list(map(str, n)),
                                  'true_radial_quadratic_coefficient': str(actual),
                                  'incorrect_classical_angular_coefficient': str(naive),
                                  'nonzero_missed_jump': str(difference)},
        'seconds': round(time.monotonic()-start, 3)}
    (HERE/'receipt.json').write_text(json.dumps(output, indent=2)+'\n')
    print('PASS angular-jump consumer and retained physical cap, belt and curvature terms', output['seconds'], flush=True)


if __name__ == '__main__':
    main()
