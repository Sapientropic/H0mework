#!/usr/bin/env python3
"""Transport the actual external-q Hessian across the whole light probe band."""
from math import comb, factorial
import hashlib
import json
from pathlib import Path
import time

import sympy as s

HERE = Path(__file__).resolve().parent
FQ = HERE.parent
ROOT = HERE.parents[4]


def main():
    began = time.monotonic()
    paths = [FQ/'packet-gauge-cosine-momentum/momentum.json', FQ/'packet-current-hessian/integrals.json',
             FQ/'packet-gauge-momentum-domain/source.json']
    data, baseline, propagation_domain = [json.loads(p.read_text()) for p in paths]
    source = data['generated_moment_upper_bounds']
    M, T = [list(map(s.Rational, source[k])) for k in ['psi', 'Hpsi']]
    N, alpha = s.Rational(source['N']), s.Rational(source['alpha'])
    t, u, eta = s.symbols('t u eta', positive=True)

    def propagated(m, values, at):
        return s.expand(sum(comb(m, j)*(N*at)**(m-j)*values[j] for j in range(m+1)))

    def laplace(poly):
        return s.expand(sum(coef*factorial(j)/eta**(j+1)
                            for (j,), coef in s.Poly(s.expand(poly), t).terms()))

    records = {}
    for m in [0, 2]:
        # Mixed position moments X_v X_n^j use the same all-unit-direction
        # order-(j+1) bound by Holder. The two actual Duhamel legs differ.
        left_integrand = sum(comb(m, j)*(N*(t-u))**(m-j)*propagated(j+1, T, t)
                             for j in range(m+1))
        right_integrand = propagated(m+1, T, u)+N*(t-u)*propagated(m, T, u)
        left = s.integrate(left_integrand, (u, 0, t))
        right = s.integrate(right_integrand, (u, 0, t))
        direct = 2*N*(M[m+1]+N*t*M[m])
        gamma = N**2*s.integrate(propagated(m, M, u), (u, 0, 2*t))
        complete = s.expand(alpha*(direct+2*N*(left+right)+gamma))
        assert all(coef >= 0 for _, coef in s.Poly(complete, t).terms())
        if m == 0:
            expected = alpha*(2*N*M[1]+4*N*(T[1]+N)*t+4*N*N*T[0]*t*t)
            assert s.expand(complete-expected) == 0
        records[str(m)] = {'left_H_leg_moment': str(s.expand(left)),
            'right_H_leg_moment': str(s.expand(right)), 'direct_current_term': str(s.expand(direct)),
            'Hk_current_term': str(s.expand(gamma)), 'probe_Lipschitz_polynomial': str(complete),
            'probe_Lipschitz_Laplace_bound': str(laplace(complete))}

    B_difference = s.expand(alpha*(2*T[1]+N+2*N*T[0]*t))
    Jlip = s.factor(laplace(B_difference).subs(eta, 5))
    Clip = s.factor(s.sympify(records['2']['probe_Lipschitz_Laplace_bound'],
                              locals={'eta': eta}).subs(eta, 5))
    A2zero = s.expand(alpha*N*(2*M[2]+2*s.integrate(propagated(2, T, u), (u, 0, 2*t))))
    Z2zero = s.factor(laplace(A2zero).subs(eta, 5))
    assert Jlip > 0 and Clip > 0 and Z2zero > 0
    variance = tuple(map(s.Rational, baseline['noise_zero']['rational']))
    mean = tuple(map(s.Rational, baseline['mean_zero']['rational']))
    assert mean[0] < mean[1] < 0
    assert variance[1]+mean[0]**2 < 49
    frequency_modulus_squared = s.Rational(7776, 125)
    assert frequency_modulus_squared > 49
    # Thus the actual raw and centered zero-probe Laplace vectors have norm<1.
    k, ell = s.symbols('k ell', nonnegative=True)
    error = s.expand((k+ell)*(Clip+Jlip*Z2zero)+2*k*ell*Jlip*Clip)
    radius = s.Rational(1, 20000)
    assert s.Rational(2, 32768**2) < radius**2
    common_error = s.factor(error.subs({k: radius, ell: radius}))
    root_radius = s.Rational(propagation_domain['actual_light_q_radius'])
    light_upper = s.Rational(251, 10**7)
    assert 2*root_radius**2 < light_upper**2
    light_error = s.factor(error.subs({k: light_upper, ell: light_upper}))
    actual_kin_upper = s.Rational(1, 90000)
    actual_error = s.factor(error.subs({k: actual_kin_upper, ell: actual_kin_upper}))
    result = {'scope': 'STRIKE_ACTUAL_EXTERNAL_Q_HESSIAN_TRANSPORT_BETWEEN_CONTINUUM_CURRENT_PROBES',
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_moment_bounds': source, 'all_unit_external_and_probe_directions': True,
        'weighted_probe_difference': records,
        'unvaried_raw_current_probe_polynomial': str(B_difference),
        'eta_ge5_constants': {'J_probe_Lipschitz': str(Jlip), 'source_q_Hessian_probe_Lipschitz': str(Clip),
                             'zero_probe_source_q_Hessian_norm': str(Z2zero)},
        'source_frequency': 'z=w=6c(1-i), c=6sqrt15/25',
        'zero_probe_raw_and_centered_Laplace_norm_lt_one': True,
        'two_leg_full_complex_Hessian_error': str(error),
        'whole_domain': {'physical_radius': 'sqrt2/32768', 'rational_radius_upper': str(radius),
                         'uniform_complex_error': str(common_error)},
        'whole_original_light_ball': {'radial_source_radius': str(root_radius),
            'physical_radius_upper': str(light_upper), 'uniform_complex_error': str(light_error)},
        'actual_minus_kin_pair': {'physical_radius_upper': str(actual_kin_upper), 'complex_error': str(actual_error)},
        'native_tensor_scope': 'all real unit external direction n; diagonal ray Hessian and mixed coordinate components by unit-vector polarization',
        'raw_connected_mean': 'same bounds before P and after fixed P; raw and connected each transported, mean retains the exact fixed-preparation product rule',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'probe-bounds.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS exact two-leg all-probe external-q Hessian transport bounds', result['elapsed_seconds'], flush=True)
    print('whole light-ball complex error <', float(light_error), flush=True)
    print('whole propagation-ball complex error <', float(common_error), flush=True)


if __name__ == '__main__':
    main()
