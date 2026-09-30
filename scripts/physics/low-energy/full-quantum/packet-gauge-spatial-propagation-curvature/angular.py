#!/usr/bin/env python3
"""Actual paired-frame angular integration of the generated quadratic source kernel."""
from fractions import Fraction as F
import json
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
sys.path.insert(0, str(FQ/'packet-band-kernel'))
from intervals import Box, pi_box


def read(path): return json.loads(path.read_bytes())
def decode(record): return Box(*map(F, record['rational']))


def main():
    began = time.monotonic()
    axis = read(HERE/'axis.json')
    moments = read(FQ/'packet-gauge-probe-moments/integrals.json')
    assert s.expand(s.sympify(axis['physical_frequency'])-s.sympify(moments['physical_frequency'])) == 0
    assert axis['zero_first_jets_on_all_rank_one_probes']
    v = s.symbols('v1:4', real=True)
    n = s.symbols('n1:4', real=True)
    t, st, cp, sp = s.symbols('t st cp sp', real=True)
    expressions = {tuple(a): s.sympify(text, locals=dict(zip(map(str, v), v)))
                   for a, text in axis['rank_one_original_probe_contraction']}
    base = expressions[(0, 0, 0, 0)]
    base_value = s.expand(base.subs({v[0]: 1, v[1]: 0, v[2]: 0}))
    assert s.expand(base-base_value*sum(a*a for a in v)**2) == 0
    # The actual paired frame uses a northern representative and the signed
    # radial coordinate. The two radial signs give twice the northern measure.
    R = s.Matrix([[t*cp, t*sp, -st], [-sp, cp, 0], [st*cp, st*sp, t]])
    finite = read(FQ.parent/'active-gauge/rotation/finite.json')
    ty, tz = s.symbols('ty tz', real=True)
    def original_rotation(axis, parameter):
        entry = finite['certificates'][axis]
        M = s.SparseMatrix(4, 4, {(i, j): sum(v*parameter**n for n, v in enumerate(poly))/(1+parameter**2)**2
                                for i, j, poly in entry['spatial_numerator']})
        return M[1:4, 1:4]
    cosine = lambda a: (1-6*a*a+a**4)/(1+a*a)**2
    sine = lambda a: 4*a*(1-a*a)/(1+a*a)**2
    generated_R = original_rotation(1, ty)*original_rotation(2, tz)
    spherical_R = R.subs({t: cosine(ty), st: sine(ty), cp: cosine(tz), sp: sine(tz)})
    assert all(s.cancel(v) == 0 for v in generated_R-spherical_R)
    body_probe, body_direction = R[:, 0], R*s.Matrix(n)
    substitution = dict(zip(v, body_probe))
    Drr = expressions.get((2, 0, 0, 0), 0)
    Drd, Ddd = 0, 0
    for i in range(3):
        a = [1, 0, 0, 0]; a[i+1] += 1
        Drd += body_direction[i]*expressions.get(tuple(a), 0)
        for j in range(i, 3):
            b = [0]*4; b[i+1] += 1; b[j+1] += 1
            Ddd += (1 if i == j else 2)*body_direction[i]*body_direction[j]*expressions.get(tuple(b), 0)
    Drr, Drd, Ddd = [s.expand(s.sympify(value).subs(substitution)) for value in [Drr, Drd, Ddd]]
    u = body_direction[2]
    n2 = sum(a*a for a in n)
    norm, left_re, left_im, mixed = s.symbols('norm left_re left_im mixed', real=True)
    left = left_re+s.I*left_im
    # Complete complex product rule. The left-probe derivative is negative
    # because the outgoing current is evaluated at r*axis-d.
    fdd = Ddd*norm+base_value*left*n2
    frd = Drd*norm-base_value*(left+mixed)*u
    frr = Drr*norm+base_value*(2*left_re+2*mixed)
    body = s.expand(s.re(fdd)/6)
    first_flux = s.expand(u*s.re(frd)/2)
    zeroth_flux = s.expand((5*u*u-n2)*s.re(frr)/8)

    def angular_average(expression):
        P = s.Poly(expression, t, st, cp, sp)
        result = 0
        for (a, b, c, d), coefficient in P.terms():
            if c % 2 or d % 2:
                continue
            # Two hemispheres; dt=sin(theta)dtheta, t>=0.
            phi = 2*s.gamma(s.Rational(c+1, 2))*s.gamma(s.Rational(d+1, 2))/s.gamma(s.Rational(c+d+2, 2))
            theta = s.gamma(s.Rational(a+1, 2))*s.gamma(s.Rational(b+2, 2))/(2*s.gamma(s.Rational(a+b+3, 2)))
            result += 2*coefficient*phi*theta
        return s.simplify(s.expand(result))

    pieces = [angular_average(value) for value in [body, first_flux, zeroth_flux]]
    total = s.expand(sum(pieces))
    assert angular_average(s.Integer(1)) == 4*s.pi
    assert s.expand(angular_average(u*u)-4*s.pi*n2/3) == 0
    assert total.coeff(left_im) == total.coeff(mixed) == 0
    assert s.expand(total.coeff(left_re)-2*s.pi*s.re(base_value)*n2/3) == 0
    assert s.Poly(total, *n).total_degree() == 2
    coefficient = s.simplify(total/s.pi)
    Hessian = s.hessian(coefficient, n)/2
    assert all(Hessian[i, j] == 0 for i in range(3) for j in range(3) if i != j)
    raw_records = {row['name']: row for row in moments['all_two_probe_Gram_jets']}
    eps = F(5234375, 294988800512)
    B = Box(2).sqrt()*eps
    measure_factor = B**3/(8*pi_box()**2)
    def real_box(expression, values):
        result = Box(0)
        P = s.Poly(s.expand(expression), norm, left_re)
        for powers, value in P.terms():
            radical = s.simplify(value/s.sqrt(30))
            assert radical.is_Rational
            term = Box(F(str(radical)))*Box(30).sqrt()
            for name, exponent in zip([norm, left_re], powers):
                term *= values[name]**exponent
            result += term
        return result
    layers = {}
    for layer in ['raw', 'mean', 'connected']:
        values = {norm: decode(raw_records['N0_left_base'][layer]['real']),
                  left_re: decode(raw_records['N0_left_00'][layer]['real'])}
        leading = [real_box(Hessian[j, j], values)*measure_factor for j in range(3)]
        layers[layer] = {'diagonal_source_quadratic_polynomial_integral': [v.record() for v in leading],
                         'off_diagonal': '0', 'source_Gram0': values[norm].record(),
                         'source_left_second_real': values[left_re].record()}
    assert any(s.expand(value) != 0 for value in pieces[1:])
    assert s.expand(pieces[0]-total) != 0
    result = {'scope': 'ACTUAL_ALL_ANGLE_PAIRED_FRAME_SOURCE_QUADRATIC_PART_WITH_REAL_CAP_FLUX',
              'physical_frequency': axis['physical_frequency'], 'physical_measure': 'd^3k/(2*pi)^3',
              'frame_matrix': [[str(v) for v in row] for row in R.tolist()],
              'actual_all_parameter_spatial_circle_matrix_verified': True,
              'paired_measure': '2 * integral(theta in [0,pi/2], phi in [0,2pi])',
              'all_rank_one_first_jets_zero': True, 'constant_source_value': str(base_value),
              'radial_jet': str(Drr), 'radial_external_jet': str(Drd), 'external_second_jet': str(Ddd),
              'integrated_body_and_flux': list(map(str, pieces)),
              'complete_angular_quadratic': str(total),
              'leading_diagonal_coefficients_divided_by_pi': [str(Hessian[j, j]) for j in range(3)],
              'complete_complex_cross_before_integration': True,
              'imaginary_left_and_mixed_moments_cancel_after_actual_angular_integral': True,
              'layers': layers, 'drop_flux_changes_leading_coefficient': True,
              'remaining_scope': 'The actual whole-band remainder is generated separately; these are exact integrals of the source quadratic part.',
              'seconds': round(time.monotonic()-began, 3)}
    (HERE/'angular.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    for layer, data in layers.items():
        print(layer, [v['decimal'] for v in data['diagonal_source_quadratic_polynomial_integral']], flush=True)
    print('PASS full paired angular measure, actual body and both cap fluxes', result['seconds'], flush=True)


if __name__ == '__main__': main()
