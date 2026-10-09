#!/usr/bin/env python3
"""Physical external-momentum derivatives of the actual cosine source current."""
from fractions import Fraction
from math import comb, factorial
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

import sympy as s
from sympy.polys.matrices import DomainMatrix

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
ROOT = HERE.parents[4]
FIELD = s.QQ.algebraic_field(s.sqrt(2), s.sqrt(15), s.I)


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def clean(matrix):
    return s.SparseMatrix(matrix.rows, matrix.cols, {key: value for key, raw in
        s.SparseMatrix(matrix).todok().items() if (value := s.expand(raw)) != 0})


def zero(matrix):
    assert not clean(matrix).todok(), list(clean(matrix).todok().items())[:2]


def decode(record):
    return s.SparseMatrix(*record['shape'], {(i, j): s.sympify(value)
                                           for i, j, value in record['entries']})


def encode(matrix):
    return {'shape': [matrix.rows, matrix.cols], 'entries':
            [[i, j, str(v)] for (i, j), v in sorted(clean(matrix).todok().items())]}


def inverse(matrix):
    return DomainMatrix.from_Matrix(clean(matrix)).convert_to(FIELD).inv().to_Matrix()


def main():
    started = time.monotonic()
    paths = [FQ/'packet-gauge-cosine/source.json', FQ/'packet-current-moments/receipt.json',
             FQ/'packet-noise/kernel-audit/receipt.json']
    cosine, moments, noise = [json.loads(p.read_text()) for p in paths]
    original = load(FQ/'packet-noise/source_kernel.py', 'cosine_momentum_original')
    provenance, (N, omega, H0, Hj, CI, K, seed) = original.exact_source()
    for path, digest in provenance['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest
    V = decode(cosine['V'])
    zero(K-decode(cosine['K']))
    zero(H0-decode(cosine['H0']))
    for index, H in enumerate(Hj):
        zero(H-decode(cosine['Hj'][index]))
        zero(K*H-H*K)
    zero(V.H-V)
    zero(K*V-V*K)
    kin = s.Matrix(list(map(s.sympify, cosine['kin'])))
    rho = s.sympify(cosine['rho_in'])
    direction = clean(kin/(s.sqrt(2)*rho))
    assert all(x.is_Rational for x in direction)
    zero(direction.T*direction-s.ones(1))
    Hn = clean(sum((direction[j]*Hj[j] for j in range(3)), s.zeros(12)))
    zero(Hn*Hn-N**2*s.eye(12))
    S = inverse(s.I*s.eye(12)-H0)
    zero((s.I*s.eye(12)-H0)*S-s.eye(12))
    zero(S*(s.I*s.eye(12)-H0)-s.eye(12))
    R = [clean(s.I*factorial(j)*(S*Hn)**j*S*CI) for j in range(3)]
    u = [clean(R[0]*seed), clean(R[1]*seed), clean((R[2]-R[0]/5)*seed)]
    # The source is the normalized physical unit ball: its exact directional
    # Fourier second derivative is -bhat(0)/5, before applying the Green.
    for j in range(3):
        expected = -s.I*CI*seed if j == 0 else -j*Hn*(R[j-1]*seed)
        zero((H0-s.I*s.eye(12))*(R[j]*seed)-expected)
    zero((H0-s.I*s.eye(12))*u[2]+2*Hn*u[1]-s.I*CI*seed/5)
    current_second = clean(2*K*V*u[2]/N**2)
    minor = None
    for i in range(12):
        for j in range(i+1, 12):
            value = s.expand(u[0][i]*current_second[j]-u[0][j]*current_second[i])
            if value != 0:
                minor = [i, j, str(value)]
                break
        if minor:
            break
    assert minor
    mixed = []
    contracted = s.zeros(12, 1)
    for i in range(3):
        for j in range(i, 3):
            Rij = clean(s.I*(S*Hj[i]*S*Hj[j]*S+S*Hj[j]*S*Hj[i]*S)*CI)
            uij = clean((Rij-(R[0]/5 if i == j else s.zeros(12)))*seed)
            gij = clean(2*K*V*uij/N**2)
            contracted += (1 if i == j else 2)*direction[i]*direction[j]*gij
            mixed.append({'coordinates': [i, j], 'actual_packet_mixed_derivative': encode(uij),
                          'zero_probe_current_mixed_curvature': encode(gij)})
    zero(contracted-current_second)
    print('PASS source physical ray, actual Green second jet and centered curvature nonzero minor', flush=True)

    def add(a, b):
        return [clean(a[j]+b[j]) for j in range(3)]

    def mul(a, b):
        return [clean(sum((a[j]*b[n-j] for j in range(n+1)), s.zeros(a[0].rows, b[0].cols)))
                for n in range(3)]

    def scale(c, a):
        return [clean(c*v) for v in a]

    Z = s.zeros(12)

    def constant(M):
        return [M, Z, Z]

    order = 4
    tests = []
    for label, probe in [('zero_probe', s.zeros(3, 1)), ('actual_minus_kin', -kin)]:
        Hk = clean(sum((probe[j]*Hj[j] for j in range(3)), Z))
        total = [s.zeros(12, 1) for _ in range(order+1)]
        odd = [s.zeros(12, 1) for _ in range(order+1)]
        # Actual two shifted Fourier current kernels, applied to the actual
        # incoming packet at -sigma*s*n, at output momentum equal to probe.
        for sign in [-1, 1]:
            hr = [H0, -sign*Hn, Z]
            hl = [H0+Hk, -sign*Hn, Z]
            hout, hpr = constant(H0+Hk), constant(H0)
            A = scale(1/N**2, mul(constant(K), add(hl, hr)))
            shifted_A = constant(clean(K*(2*H0+Hk)/N**2))
            b, bs = [A], [shifted_A]
            C = [constant(clean(K*V/N**2))]
            for n in range(order):
                b.append(scale(s.I/(n+1), add(mul(hl, b[n]), scale(-1, mul(b[n], hr)))))
                bs.append(scale(s.I/(n+1), add(mul(hout, bs[n]), scale(-1, mul(bs[n], hpr)))))
                rhs = add(mul(hout, C[n]), scale(-1, mul(C[n], hr)))
                forcing = scale(s.Rational(1, 2), add(mul(constant(V), b[n]), scale(-1, mul(bs[n], constant(V)))))
                C.append(scale(s.I/(n+1), add(rhs, forcing)))
            packet = [u[0], -sign*u[1], u[2]/2]
            for n in range(order+1):
                applied = mul(C[n], packet)
                total[n] += 2*applied[2]
                odd[n] += applied[1]
        total = list(map(clean, total))
        for value in odd:
            zero(value)

        # Independently differentiate the full current Heisenberg equation.
        # W''_0=-X_n^2 V becomes +V*d_p^2. The Leibniz terms below retain
        # both derivatives of the packet and of the unvaried current kernel.
        hp = [H0, Hn, Z]
        hpk = [H0+Hk, Hn, Z]
        bj = [scale(1/N**2, mul(constant(K), add(hpk, hp)))]
        T = [[Z, Z, clean(2*K*V/N**2)]]
        for n in range(order):
            bj.append(scale(s.I/(n+1), add(mul(hpk, bj[n]), scale(-1, mul(bj[n], hp)))))
            forcing = [2*s.I*V*bj[n][2], 2*s.I*V*bj[n][1], s.I*(V*bj[n][0]-bj[n][0]*V)]
            next_T = []
            for j in range(3):
                rhs = s.I*((H0+Hk)*T[n][j]-T[n][j]*H0)+forcing[j]
                if j < 2:
                    rhs -= s.I*(j+1)*T[n][j+1]*Hn
                next_T.append(clean(rhs/(n+1)))
            T.append(next_T)
        for n in range(order+1):
            direct = clean(sum((T[n][j]*u[j] for j in range(3)), s.zeros(12, 1)))
            zero(total[n]-direct)
        zero(total[0]-current_second)
        if label == 'zero_probe':
            for value in total[1:]:
                zero(value)
        else:
            assert any(value.todok() for value in total[1:])
        tests.append({'probe': label, 'physical_momentum': list(map(str, probe)),
                      'source_curvature_time_coefficients': list(map(encode, total)),
                      'two_shift_and_differential_operator_recurrences_agree': True})
    print('PASS true two-shift source versus X_n squared current through time order4, both probes', flush=True)

    # Generate uniform full-time and half-axis bounds from the same packet.
    Nup, alphaup, hup = s.Rational(2, 3), s.Rational(10, 3), s.Rational(21, 20)
    nlower = s.Rational(noise['h0']['n_squared'][0])
    assert N**2 < Nup**2 and 2 < (alphaup*N**2)**2
    assert N**2/nlower-1 < hup**2
    M = [s.Integer(1)]+[s.Rational(moments['response_moment_bounds'][str(j)]['rational'][1]) for j in range(1, 5)]
    TM = [hup]+[s.Rational(moments['H_response_moment_bounds'][str(j)]['rational'][1]) for j in range(1, 5)]
    t, uvar, eta, rnorm = s.symbols('t u eta r', positive=True)

    def propagated(m, values, at):
        return sum(comb(m, j)*(Nup*at)**(m-j)*values[j] for j in range(m+1))

    def moment(poly):
        return s.expand(sum(v*factorial(j)/eta**(j+1) for (j,), v in s.Poly(s.expand(poly), t).terms()))

    bounds = {}
    for m in [0, 2, 4]:
        incoming = propagated(m, TM, uvar)
        packet = propagated(m, M, uvar)
        cm = s.expand(alphaup*Nup*(2*M[m]+s.integrate(2*incoming+rnorm*packet, (uvar, 0, 2*t))))
        left_plus_right = s.integrate(2*propagated(m, TM, uvar)+rnorm*propagated(m, M, uvar), (uvar, 0, t))
        left_plus_right += s.integrate(2*propagated(m, TM, 2*t-uvar)+rnorm*propagated(m, M, 2*t-uvar), (uvar, 0, t))
        assert s.expand(cm-alphaup*Nup*(2*M[m]+left_plus_right)) == 0
        lm = moment(cm)
        common = s.factor(lm.subs({eta: 5, rnorm: s.Rational(1, 30000)}))
        assert common > 0
        bounds[str(m)] = {'current_all_time_polynomial': str(cm), 'Laplace_moment': str(lm),
                         'whole_propagation_ball_eta_ge5_bound': str(common)}
    assert s.expand(s.sympify(bounds['0']['current_all_time_polynomial'], locals={'t': t, 'r': rnorm})-
                    (2*alphaup*Nup+2*Nup*alphaup*(2*hup+rnorm)*t)) == 0
    radius = s.sqrt(2)/32768
    assert radius**2 < s.Rational(1, 20000)**2 and (Nup/s.Integer(20000)) == s.Rational(1, 30000)
    a = alphaup*(2*hup+s.Rational(1, 30000))
    L2 = s.Rational(bounds['2']['whole_propagation_ball_eta_ge5_bound'])
    L4 = s.Rational(bounds['4']['whole_propagation_ball_eta_ge5_bound'])
    print('PASS source all-position moments generate whole-time q squared jet and q fourth remainder', flush=True)
    result = {
        'scope': 'STRIKE_TRUE_PHYSICAL_EXTERNAL_COSINE_MOMENTUM_SECOND_DERIVATIVE_AND_UNIFORM_FOURTH_REMAINDER',
        'source_sha256': provenance['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_direction': list(map(str, direction)), 'physical_external_momentum': 'q=s*n with |n|=1; M_q=exp(i*q.x)',
        'Green0': encode(R[0]), 'actual_packet_directional_jets_at_zero': list(map(encode, u)),
        'normalization_of_point_representatives': 'all omit the same positive bhat(0)/norm(raw_packet)',
        'zero_probe_current_curvature': encode(current_second), 'centered_curvature_nonzero_minor': minor,
        'full_symmetric_three_dimensional_curvature': mixed,
        'actual_ray_is_same_tensor_contraction': True,
        'point_to_L2': 'source Fourier representatives are continuous; the nonzero wedge survives on an open set and cancels any expectation multiple of psi',
        'time_consumers': tests,
        'generated_moment_upper_bounds': {'psi': list(map(str, M)), 'Hpsi': list(map(str, TM)),
                                        'N': str(Nup), 'alpha': str(alphaup)},
        'all_time_and_Laplace_bounds': bounds,
        'true_expansion': 'C_cos(s),k psi = C_const,k psi - s^2/2 * C[X_n^2 V]_k psi + R; norm R <= s^4/24 * bound_4(t,k)',
        'second_derivative': 'partial_s^2 C_cos(s),k psi at0 = -C[X_n^2 V]_k psi; first derivative zero',
        'full_external_momentum_Hessian': 'D_q^2 C_cos(0),k [u,v] psi = -C[(u.x)(v.x)V]_k psi; true Frechet Hessian by the uniform all-direction fourth remainder',
        'full_time_growth': 'norm X_n^m U(t)f <= sum_j binom(m,j)(N|t|)^(m-j) norm X_n^j f',
        'same_centering_and_mean': 'fixed P commutes with strong derivatives and integrals; raw, mean and connected all consume this same source curvature',
        'Laplace_curvature_uniform_norm_bound': str(L2), 'Laplace_fourth_remainder_coefficient': str(L4/24),
        'two_probe_noise_response_curvature_norm_bound': str(2*a*L2/5),
        'two_probe_noise_response_fourth_remainder_coefficient': str(a*L4/60),
        'probe_range': 'all |k|,|l| <= sqrt(2)/32768; eta_left,eta_right>=5, independent imaginary parts',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'momentum.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS actual cosine momentum producer', result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
