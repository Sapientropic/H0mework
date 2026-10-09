#!/usr/bin/env python3
"""Fourth physical probe derivatives of the same full-time prepared current."""
from math import comb, factorial, isqrt
import hashlib
import json
from pathlib import Path
import time
import sympy as s

HERE = Path(__file__).resolve().parent
FQ = HERE.parent
ROOT = HERE.parents[4]


def upper_decimal(value, digits=20):
    scale = 10**digits
    rounded = int(s.ceiling(value*scale))
    return f'{rounded//scale}.{rounded % scale:0{digits}d}'


def main():
    start = time.monotonic()
    paths = [FQ/'packet-gauge-cosine-momentum/momentum.json',
             FQ/'packet-gauge-probe-laplace/bounds.json',
             FQ/'packet-gauge-probe-laplace/resolvent.json',
             FQ/'packet-gauge-global-transfer/source.json']
    moments, old, resolvent, theta = [json.loads(path.read_bytes()) for path in paths]
    source = moments['generated_moment_upper_bounds']
    assert source == old['source_moment_upper_bounds']
    M, T = [list(map(s.Rational, source[name])) for name in ['psi', 'Hpsi']]
    assert len(M) == len(T) == 5
    N, alpha = s.Rational(source['N']), s.Rational(source['alpha'])
    t, eta, k = s.symbols('t eta k', nonnegative=True)
    def evolved(m, data):
        return sum(comb(m, j)*(N*t)**(m-j)*data[j] for j in range(m+1))
    def laplace(poly):
        return s.expand(sum(value*factorial(j)/eta**(j+1) for (j,), value in s.Poly(poly, t).terms()))
    scale = 10**80
    root2 = s.Rational(isqrt(2*scale*scale)+1, scale)
    root15 = s.Rational(isqrt(15*scale*scale), scale)
    assert (root2-s.Rational(1, scale))**2 <= 2 < root2**2
    assert root15**2 <= 15 < (root15+s.Rational(1, scale))**2
    epsilon = s.Rational(theta['source_root_control']['epsilon'])
    actual_k = root2*epsilon
    actual_eta = 36*root15/25
    assert actual_k < s.Rational(1, 20000) and actual_eta > 5
    z = s.sympify(resolvent['physical_frequency'])
    assert s.simplify(s.re(z)-36*s.sqrt(15)/25) == 0
    records, B, C = [], [], []
    for m in range(5):
        previous = evolved(m-1, M) if m else 0
        bt = s.expand(alpha*(2*evolved(m, T)+N*k*evolved(m, M)+m*N*previous))
        ct = s.expand(alpha*N*(2*evolved(m, M)+4*t*evolved(m, T)
                               +2*N*k*t*evolved(m, M)+2*m*N*t*previous))
        assert all(value >= 0 for _, value in s.Poly(bt, t, k).terms())
        assert all(value >= 0 for _, value in s.Poly(ct, t, k).terms())
        bl, cl = laplace(bt), laplace(ct)
        if m < 4:
            oldrow = old['derivative_bounds'][m]
            assert s.expand(bt-s.sympify(oldrow['raw_B_all_time_norm'], locals={'t': t, 'k': k})) == 0
            assert s.expand(ct-s.sympify(oldrow['raw_C_all_time_norm'], locals={'t': t, 'k': k})) == 0
        b, cc = [s.factor(value.subs({eta: actual_eta, k: actual_k})) for value in [bl, cl]]
        B.append(b)
        C.append(cc)
        b0, c0 = [s.factor(value.subs({eta: 5, k: s.Rational(1, 20000)})) for value in [bl, cl]]
        if m:
            assert b > s.factor(bt.subs({t: 0, k: actual_k})/actual_eta)
        else:
            assert b == s.factor(bt.subs({t: 0, k: actual_k})/actual_eta)
        assert cc > s.factor(ct.subs({t: 0, k: actual_k})/actual_eta)
        records.append({'order': m, 'all_time_B': str(bt), 'all_time_C': str(ct),
            'Laplace_B': str(bl), 'Laplace_C': str(cl),
            'eta_ge5_small_probe_B': str(b0), 'eta_ge5_small_probe_C': str(c0),
            'actual_frequency_light_ball_B': str(b), 'actual_frequency_light_ball_C': str(cc),
            'actual_B_decimal_upper': upper_decimal(b), 'actual_C_decimal_upper': upper_decimal(cc)})
    gram = []
    for total in range(5):
        for a in range(total+1):
            b = total-a
            bound = sum(comb(a, j)*B[b+j]*B[a-j] for j in range(a+1))
            response = sum(comb(a, j)*(C[b+j]*B[a-j]+B[b+j]*C[a-j]) for j in range(a+1))
            gram.append({'radial_order': a, 'external_order': b, 'raw_mean_connected_N0': str(bound),
                         'raw_mean_connected_N1': str(response),
                         'N0_decimal_upper': upper_decimal(bound), 'N1_decimal_upper': upper_decimal(response)})
    mixed = {str(a): next(v for v in gram if v['radial_order'] == a and v['external_order'] == 4-a) for a in [2, 3, 4]}
    assert s.Rational(mixed['2']['raw_mean_connected_N0']) == B[4]*B[0]+2*B[3]*B[1]+B[2]**2
    assert s.Rational(mixed['3']['raw_mean_connected_N0']) == B[4]*B[0]+4*B[3]*B[1]+3*B[2]**2
    assert s.Rational(mixed['4']['raw_mean_connected_N0']) == 2*B[4]*B[0]+8*B[3]*B[1]+6*B[2]**2
    result = {'scope': 'ACTUAL_FULL_TIME_STRONG_MIXED_FOURTH_PHYSICAL_PROBE_BOUNDS',
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'same_source_position_moments': source, 'physical_k_not_Fourier_h': True,
        'actual_eta_lower': str(actual_eta), 'actual_light_probe_radius_upper': str(actual_k),
        'vector_derivatives': records, 'two_probe_derivatives': gram,
        'two_probe_path': 'left=kin+r*v-d*w, right=kin+r*v; v,w arbitrary unit physical directions',
        'centering': 'same fixed P, no new preparation or normalization; raw/P/(I-P) each is a contraction',
        'vector_Taylor_after_order3': 'norm remainder <= L4*|h|^4/24 on any segment in the ball',
        'even_pair_body_remainder': '|average(Phi_dd(r),Phi_dd(-r))-Phi_dd(0)| <= r^2*M_rrdd/2',
        'odd_pair_first_flux_remainder': '|(Phi_d(r)-Phi_d(-r))/2-r*Phi_rd(0)| <= |r|^3*M_rrrd/6',
        'even_pair_scalar_remainder': '|average(Phi(r),Phi(-r))-Phi(0)-r^2*Phi_rr(0)/2| <= r^4*M_rrrr/24',
        'wrong_t0_over_damping_strictly_smaller_B_orders1_to4_and_all_C': True,
        'no_H2_preparation_no_time_or_UV_cutoff': True,
        'seconds': round(time.monotonic()-start, 3)}
    (HERE/'receipt.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS same-source full-time B/C mixed fourth jets and all15 two-probe product bounds', result['seconds'], flush=True)
    print('Actual B0..4 upper bounds:', [upper_decimal(value, 12) for value in B], flush=True)
    print('N0 rrdd/rrrd/rrrr bounds:', [mixed[str(a)]['N0_decimal_upper'] for a in [2, 3, 4]], flush=True)


if __name__ == '__main__':
    main()
