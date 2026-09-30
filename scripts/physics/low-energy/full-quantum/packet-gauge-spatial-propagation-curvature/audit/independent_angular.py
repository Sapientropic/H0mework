#!/usr/bin/env python3
"""Native9x9 tensors integrated by finite Laurent Fourier words, not Beta moments."""
from pathlib import Path
import json
import time
import sympy as s

HERE = Path(__file__).resolve().parent
CANDIDATE = HERE.parent


def main():
    started = time.monotonic()
    axis = json.loads((CANDIDATE/'axis.json').read_bytes())
    published = json.loads((CANDIDATE/'angular.json').read_bytes())
    v = s.symbols('v1:4', real=True)
    n = s.symbols('n1:4', real=True)
    ct, st, cp, sp = s.symbols('ct st cp sp', real=True)
    norm, lr, li, mixed = s.symbols('norm left_re left_im mixed', real=True)
    weights = [v[i]*v[j] for i in range(3) for j in range(3)]
    tensors = {}
    for index, record in axis['scalar_tensor']:
        tensors[tuple(index)] = s.expand(sum(weights[i]*s.sympify(value)*weights[j]
                                             for i, j, value in record['entries']))
    zero = (0, 0, 0, 0)
    constant = tensors[zero].subs(dict(zip(v, [1, 0, 0])))
    assert s.expand(tensors[zero]-constant*sum(a*a for a in v)**2) == 0
    assert all(value == 0 for index, value in tensors.items() if sum(index) == 1)
    rotation = s.Matrix([[ct*cp, ct*sp, -st], [-sp, cp, 0], [st*cp, st*sp, ct]])
    probe, direction = rotation[:, 0], rotation*s.Matrix(n)
    substitution = dict(zip(v, probe))
    rr = tensors[(2, 0, 0, 0)].subs(substitution)
    rd, dd = 0, 0
    for i in range(3):
        beta = [1, 0, 0, 0]; beta[1+i] = 1
        rd += direction[i]*tensors[tuple(beta)].subs(substitution)
        for j in range(3):
            beta = [0]*4; beta[1+i] += 1; beta[1+j] += 1
            dd += direction[i]*direction[j]*tensors[tuple(beta)].subs(substitution)
    u, nn = direction[2], sum(a*a for a in n)
    left = lr+s.I*li
    phi_dd = dd*norm+constant*left*nn
    phi_rd = rd*norm-constant*(left+mixed)*u
    phi_rr = rr*norm+constant*(2*lr+2*mixed)
    pieces = [s.expand(s.re(phi_dd)/6), s.expand(u*s.re(phi_rd)/2),
              s.expand((5*u*u-nn)*s.re(phi_rr)/8)]
    # Integrate actual2*sin(theta) dtheta dphi on the northern representative.
    # Each trigonometric monomial is a finite Laurent word. Phi integration
    # selects the zero Fourier coefficient; theta has exact endpoints1 andi.
    z, w = s.symbols('z w')
    substitutions = {ct: (z+1/z)/2, st: (z-1/z)/(2*s.I),
                     cp: (w+1/w)/2, sp: (w-1/w)/(2*s.I)}
    def integrate(expression):
        laurent = s.expand(expression.subs(substitutions, simultaneous=True)*(z-1/z)/s.I)
        polynomial = s.Poly(s.expand(laurent*z**16*w**16), z, w)
        total = 0
        for (a, b), coefficient in polynomial.terms():
            if b != 16:
                continue
            frequency = a-16
            primitive = s.pi/2 if frequency == 0 else (s.I**frequency-1)/(s.I*frequency)
            total += coefficient*2*s.pi*primitive
        return s.simplify(s.expand(total))
    assert integrate(s.Integer(1)) == 4*s.pi
    assert s.expand(integrate(u*u)-4*s.pi*nn/3) == 0
    result = [integrate(value) for value in pieces]
    named = {**dict(zip(map(str, n), n)), 'norm': norm, 'left_re': lr, 'left_im': li, 'mixed': mixed}
    expected = [s.sympify(value, locals=named) for value in published['integrated_body_and_flux']]
    assert all(s.expand(a-b) == 0 for a, b in zip(result, expected))
    total = s.expand(sum(result))
    assert total.coeff(li) == total.coeff(mixed) == 0
    assert s.expand(total-s.sympify(published['complete_angular_quadratic'], locals=named)) == 0
    assert s.expand(result[0]-total) != 0
    report = {'passed': True, 'source': 'all original9x9 scalar tensors, not the published rank-one contracted polynomials',
        'exact_integration': 'finite two-variable Laurent words with actual northern-pair measure2*sin(theta)',
        'constant_origin_direction_term_exactly_isotropic': True,
        'potential_radius_order_surface_term_exactly_zero': True,
        'body_and_both_fluxes_identical_separately': True,
        'complex_left_and_mixed_cancel_only_after_whole_angular_sum': True,
        'dropping_flux_nonzero': True, 'seconds': round(time.monotonic()-started, 3)}
    (HERE/'independent-angular.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS source9x9 tensors, all-angle Laurent integration, raw complex cross and both cap fluxes', report['seconds'], flush=True)


if __name__ == '__main__':
    main()
