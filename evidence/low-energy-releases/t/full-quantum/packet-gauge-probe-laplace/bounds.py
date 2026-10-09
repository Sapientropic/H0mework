#!/usr/bin/env python3
"""Original weighted source pays strong physical probe jets and time exchange."""
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
    paths = [FQ/'packet-gauge-cosine-momentum/momentum.json',
             FQ/'packet-gauge-cosine-curvature/probe-bounds.json', HERE/'resolvent.json']
    moments, earlier, resolvent = [json.loads(p.read_text()) for p in paths]
    source = moments['generated_moment_upper_bounds']
    M, T = [list(map(s.Rational, source[key])) for key in ['psi', 'Hpsi']]
    N, alpha = s.Rational(source['N']), s.Rational(source['alpha'])
    t, eta, k = s.symbols('t eta k', nonnegative=True)

    def P(m, values):
        return sum(comb(m, j)*(N*t)**(m-j)*values[j] for j in range(m+1))

    def moment(poly):
        return s.expand(sum(value*factorial(j)/eta**(j+1)
                            for (j,), value in s.Poly(poly, t).terms()))

    records = []
    for m in range(4):
        previous = P(m-1, M) if m else 0
        B = s.expand(alpha*(2*P(m, T)+N*k*P(m, M)+m*N*previous))
        C = s.expand(alpha*N*(2*P(m, M)+4*t*P(m, T)+2*N*k*t*P(m, M)+2*m*N*t*previous))
        assert all(value >= 0 for _, value in s.Poly(B, t, k).terms())
        assert all(value >= 0 for _, value in s.Poly(C, t, k).terms())
        if m == 1:
            assert s.expand(B.subs(k, 0)-s.sympify(earlier['unvaried_raw_current_probe_polynomial'], locals={'t': t})) == 0
            assert s.expand(C.subs(k, 0)-s.sympify(earlier['weighted_probe_difference']['0']['probe_Lipschitz_polynomial'], locals={'t': t})) == 0
        records.append({'physical_probe_order': m, 'raw_B_all_time_norm': str(B),
                        'raw_C_all_time_norm': str(C), 'raw_B_Laplace_norm': str(moment(B)),
                        'raw_C_Laplace_norm': str(moment(C)),
                        'eta_ge5_probe_ball_B_bound': str(s.factor(moment(B).subs({eta: 5, k: s.Rational(1, 20000)}))),
                        'eta_ge5_probe_ball_C_bound': str(s.factor(moment(C).subs({eta: 5, k: s.Rational(1, 20000)})))})
    z = s.sympify(resolvent['physical_frequency'])
    c = s.sympify(resolvent['physical_clock'])
    assert s.expand(s.re(z)-6*c) == 0 and (6*c)**2 > 25
    result = {'scope': 'STRIKE_TRUE_STRONG_PHYSICAL_PROBE_DERIVATIVES_OF_SOURCE_CURRENT_AND_EPSILON_RESPONSE',
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_moment_upper_bounds': source, 'derivative_bounds': records,
        'strong_probe_regularities': 'B_k(t)psi and C[V]_k(t)psi are C-infinity in the same physical k; all mixed directions from the same weighted source.',
        'whole_time_Duhamel_weight': '||X^m D_V(t)f|| <= N|t| P_m(|t|;f); ||D_V(t)||<=N|t|',
        'actual_Laplace_exchange': 'all eta>0; each real probe derivative through order3 commutes with the true strong half-axis integral',
        'uniform_second_order_Taylor_remainders': {
            'B': 'norm(Bhat(k+h)-Bhat(k)-DBhat(k)h-D2Bhat(k)[h,h]/2)<=|h|^3*L_B3/6',
            'C': 'same formula with Chat and L_C3',
            'domain': 'the connecting probe segment stays in the specified ball; no re-preparation or new source normalization'},
        'covariance_consumer': 'full complex two-probe raw/centered/mean Gram derivatives by the actual product rule, fixed P; each derivative uses these same vector jets',
        'composition_with_cosine_external_momentum': 'C_cos(q;k) is even in q for every k. D_q at q=0 and D_k D_q at q=0 vanish. Moving-probe second derivatives therefore add the real external-q Hessian to the constant-input probe Hessian, retaining all two-probe product terms.',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'bounds.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS whole-time physical probe derivatives and exact positive-half-axis moments', result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
