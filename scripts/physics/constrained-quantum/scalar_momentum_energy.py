#!/usr/bin/env python3
"""Global scalar momentum bounds from the original projected wave energy.

The positive comparison energy is an analytic norm, not the signed physical
Hamiltonian. Its exact derivative uses that physical Hamiltonian unchanged.
It removes exponential growth in a momentum-window radius from the free flow.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from full_matter_ports import clean, equal, encode
from scalar_canonical_phase import ScalarCanonicalPhase, K
from scalar_dyson_time import ScalarDysonTime, KAPPA
from scalar_dyson_bounds import norms


def main():
    started = time.monotonic()
    phase = ScalarCanonicalPhase()
    P, N = phase.P, phase.N
    L = clean(P * phase.L * P)
    constant = clean(L.subs(dict.fromkeys(K, 0)))
    linear = [clean(L.diff(k).subs(dict.fromkeys(K, 0))) for k in K]
    radius_squared = sum(k*k for k in K)
    equal(L, radius_squared*P + constant + sum((k*M for k, M in zip(K, linear)), s.zeros(70)))
    for M in [P, L, constant, *linear]:
        equal(M, M.H)
        equal(P*M*P, M)
    b0 = norms(constant)['operator_two_norm_upper_bound']
    b = [norms(M)['operator_two_norm_upper_bound'] for M in linear]
    shift = s.simplify(1+b0+sum(x*x for x in b)/2)
    energy_K = clean(L+shift*P)
    # Completing each scalar square proves positivity on the whole projected
    # carrier for every real k, not merely a matrix at selected momenta.
    r = s.symbols('absolute_k1:4', nonnegative=True)
    lower = sum(x*x for x in r)-sum(x*y for x, y in zip(r, b))-b0+shift
    completed = 1+sum(x*x for x in r)/2+sum((x-y)**2 for x, y in zip(r, b))/2
    assert s.expand(lower-completed) == 0
    upper_coefficient = s.simplify(1+shift+b0+sum(b))
    assert upper_coefficient.is_positive is True
    # |k_j| <= (1+|k|^2)/2 is stronger than the bound used here.
    for x in r:
        assert s.expand((1+x*x)/2-x-(x-1)**2/2) == 0
    energy = s.diag(energy_K, P)
    off_diagonal = s.SparseMatrix.vstack(s.SparseMatrix.hstack(s.zeros(70), P),
                                        s.SparseMatrix.hstack(P, s.zeros(70)))
    equal(phase.A.H*energy+energy*phase.A, -N*shift*off_diagonal)
    canonical_energy = clean(phase.T.H*energy*phase.T)
    equal(phase.canonical_A.H*canonical_energy+canonical_energy*phase.canonical_A,
          -N*shift*phase.T.H*off_diagonal*phase.T)
    Sbound = norms(phase.S)['operator_two_norm_upper_bound']
    Tbound = norms(phase.T)['operator_two_norm_upper_bound']
    condition = s.simplify(Sbound*Tbound)
    constant_bound = s.simplify(condition*s.sqrt(upper_coefficient))
    growth = s.simplify(N*shift/2)
    derivative1 = s.simplify(condition*N*(2+s.Max(*b)))
    derivative2 = s.simplify(2*condition*N)
    print('PASS original scalar L(k)=|k|^2 P+linear+constant, global shifted-energy identity', flush=True)

    native = ScalarDysonTime()
    # Unit-normalized plus/minus Fourier coordinates of the real244 pair.
    U = s.SparseMatrix.zeros(244)
    for j in range(61):
        for offset, sign in ((0, 1), (122, -1)):
            U[offset+j, j] = 1/s.sqrt(2)
            U[offset+j, j+61] = sign*s.I/s.sqrt(2)
            U[offset+j+61, j+122] = 1/s.sqrt(2)
            U[offset+j+61, j+183] = sign*s.I/s.sqrt(2)
    equal(U*U.H, s.eye(244))
    plus = clean(phase.canonical_A.subs(dict(zip(K, KAPPA)), simultaneous=True))
    minus = clean(phase.canonical_A.subs(dict(zip(K, [-x for x in KAPPA])), simultaneous=True))
    equal(U*native.scalar_A*U.H, s.diag(plus, minus))
    equal(native.scalar_zero_A, phase.canonical_A.subs(dict.fromkeys(K, 0)))
    print('PASS actual244 pair unitarily realizes both original122 fibers; no transfer cutoff', flush=True)

    files = ['scalar_canonical_phase.py', 'scalar_canonical_phase.json',
             'independent_scalar_canonical_phase.json', 'scalar_joint_hamiltonian.json',
             'scalar_dyson_time.py', 'scalar_dyson_time.json', 'scalar_dyson_bounds.py',
             'scalar_momentum_energy.py']
    result = {
        'root': ROOT_ID,
        'source_sha256': native.source['source_sha256'],
        'input_sha256': {str((HERE/name).relative_to(ROOT)): hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                         for name in files},
        'scope': 'SOURCE_SCALAR_GLOBAL_MOMENTUM_ENERGY_AND_POLYNOMIAL_FLOW_BOUNDS',
        'source_lapse': str(N), 'principal_symbol': '|k|^2 P61',
        'projected_constant': encode(constant), 'projected_linear': [encode(M) for M in linear],
        'constant_norm_bound': str(b0), 'linear_norm_bounds': list(map(str, b)),
        'energy_shift_a': str(shift), 'energy_upper_C': str(upper_coefficient),
        'comparison_energy': 'E=||Pi||^2+<phi,(L(k)+a P61)phi>, on P61 phi=phi and P61 Pi=Pi',
        'positivity': 'L(k)+a P61 >= (1+|k|^2/2) P61, by three exact completed squares and source coefficient norm bounds',
        'energy_derivative': 'Eprime=-2 N a Re<Pi,phi>; |Eprime|<=N a E',
        'canonical_frame_condition_bound': str(condition),
        'canonical_flow_constant_C': str(constant_bound),
        'coordinate_time_growth_beta': str(growth),
        'canonical_global_flow_bound': '||exp(t A61(k))||_2 <= C sqrt(1+|k|^2) exp(beta |t|), for every real k and t; A61 has phase dimension122',
        'real244_pair_same_bound': True,
        'real244_unitary_conjugate_identity': encode(U),
        'zero122_is_exact_specialization': True,
        'first_generator_derivative_constant': str(derivative1),
        'second_generator_derivative_constant': str(derivative2),
        'generator_derivative_bounds': '||partial_j A||<=D1(1+|k|); ||partial_i partial_j A||<=D2; derivatives of order>2 vanish',
        'all_order_flow_argument': {
            'recurrence': 'F_alpha prime=A F_alpha+sum_(0<nu<=alpha) binom(alpha,nu)(partial^nu A)F_(alpha-nu), F_alpha(0)=0',
            'constants': 'C0=C; Cr(T)=C T [r D1 C_(r-1)(T)+r(r-1)/2 D2 C_(r-2)(T)], with C_(-1)=0',
            'bound': '||partial_k^alpha exp(tA(k))||<=Cr(T)(1+|k|)^(2r+1) exp(beta T), |t|<=T, r=|alpha|',
            'proof': 'variation of constants; first derivative terms have polynomial degree (2r-1)+1+1=2r+1; second derivative terms have degree (2r-3)+0+1<=2r+1; multiindex binomial sums are r and r(r-1)/2',
            'Schwartz_consumer': 'each finite-time free phase multiplier and every momentum derivative grows polynomially; it maps Schwartz phase data to Schwartz phase data',
        },
        'primitive_consumer': 'the scalar factor of each actual N1 coefficient signal is this same phase flow; its matter tensor factors are unitary on Lambda6/Lambda2, so the k-window exponential bound can be replaced by this global polynomial bound',
        'physical_Hamiltonian_changed': False,
        'positive_comparison_energy_is_physical_Hilbert_state': False,
        'continuous_interacting_boson_kappa_integral_or_UV_completion_constructed': False,
        'formal_Lean_energy_inequality_installed': False,
        'proper_clock': 'tau=N t; exp(beta |t|)=exp(a |tau|/2)',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3),
    }
    (HERE/'scalar_momentum_energy.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source global momentum polynomial-flow bound', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
