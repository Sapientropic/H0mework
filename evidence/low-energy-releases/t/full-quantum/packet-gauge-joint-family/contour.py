#!/usr/bin/env python3
"""Source-bounded contour kernels, strong parameter jets and native currents."""
from fractions import Fraction as F
import hashlib
import importlib.util
import json
from math import factorial
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
ROOT = HERE.parents[4]
spec = importlib.util.spec_from_file_location('joint_contour_source_bounds', FQ/'packet-gauge-family/remainder.py')
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
x, epsilon, a, U = helper.x, helper.epsilon, helper.a, helper.U
matrix, number_bound, circle_bound = helper.matrix, helper.number_bound, helper.circle_bound


def read(path):
    return json.loads(path.read_text())


def main():
    began = time.monotonic()
    files = ['source.json', 'infinity.json', 'domain.json', 'proper.json', 'lift.json', 'readers.json']
    source, infinity, domain, proper, lift, readers = [read(HERE/name) for name in files]
    old = read(FQ/'packet-gauge-causal/source.json')
    assert proper['nonpositive_section_powers'] == []
    assert lift['all289_strictly_proper_for_the_same_parameter_family'] is True
    assert infinity['complete_frequency_degree'] == 126
    delta = F(domain['generated_positive_delta_in_a'])
    assert 0 < delta <= F(1, 100)
    assert F(domain['uniform_neumann_ratio_upper']) < F(1, 4)
    eps_star, complex_eps = delta/5, 2*delta/5
    assert F(4, 25) < F(9, 50)
    rho, N = F(1, 131072), 3*s.sqrt(30)/25
    fhat = s.Poly(s.sympify(source['complete_Fhat'], locals={'U': U}), U, domain=s.QQ)
    assert fhat.count_roots(s.Rational(3, 4)*s.Rational(rho)**2,
                            s.Rational(4, 5)*s.Rational(rho)**2) == 1
    D = s.Poly(s.sympify(source['source_denominator'], locals={'U': U}), U, domain=s.QQ)
    Ubound = rho*rho
    Dlower = abs(F(str(D.nth(0))))-sum(abs(F(str(value)))*Ubound**degree
        for (degree,), value in D.terms() if degree)
    assert Dlower > F(1, 2)
    scales = matrix(old['scales103'])
    diagonal = [s.Integer(1)]*9+[scales[i, i] for i in range(103)]
    source_rows = [F(0)]*112
    for i, j, text in source['section_source_numerator']['entries']:
        value = s.sympify(text, locals={'x': x, 'epsilon': epsilon})*diagonal[i]/N
        source_rows[i] += circle_bound(str(value))*Ubound**j/Dlower
    inverse_bound = F(4, 3)*F(domain['unvaried_inverse_infinity_norm_circle_bound'])
    section_bound = max(map(number_bound, diagonal))*inverse_bound*max(source_rows)
    coordinates = [F(0)]*289
    for row in source['keep121']:
        coordinates[row] = section_bound
    for step in reversed(source['auxiliary_steps']):
        out = [F(0)]*len(step['eliminated'])
        for i, j, text in step['particular_source']['entries']:
            out[i] += circle_bound(text)*Ubound**j/Dlower
        for i, j, text in step['back']['entries']:
            out[i] += circle_bound(text)*coordinates[step['kept'][j]]
        for i, row in enumerate(step['eliminated']):
            coordinates[row] = out[i]
    world = [F(0)]*289
    for i, j, text in old['L']['entries']:
        world[i] += number_bound(s.sympify(text))*coordinates[j]
    G = max(world)
    assert G > 0
    K0, K1, C1, C2 = map(matrix, [source[name] for name in ['K0', 'K1', 'C1', 'C2']])
    Z = matrix(source['original_source_numerator'])
    removed = source['removed']
    Km = K0.extract(removed, range(9))
    Kmi = matrix(old['symmetry_minor_inverse'])
    assert (Km*Kmi-s.eye(9)).applyfunc(s.expand) == s.zeros(9)
    assert all(not value.has(x) for M in [Km, K1, C1, C2] for value in M)
    Ktime = K0.applyfunc(lambda v: s.expand(v).coeff(x, 1))
    assert (Ktime.T*Z).applyfunc(s.expand) == s.zeros(9, 6)
    ratio = complex_eps*helper.constant_matrix_norm(Kmi*K1.extract(removed, range(9)))
    assert ratio < F(1, 4)
    # Keep full source scalar root separate from x; the contour is in original
    # lambda, radius5c. All bounds below enlarge it only to beta=19/4<5.
    c2, beta = F(108, 125), F(19, 4)
    assert 25*c2 < beta*beta and beta < 5
    dscale = 5/delta
    kernel_bounds = []
    for j in range(3):
        output_bound = 17*factorial(j)*dscale**j*G
        value = 4*beta*output_bound
        initial = beta*output_bound
        time_derivative = 4*beta**2*output_bound
        complete = value+initial+time_derivative
        assert complete == 1938*factorial(j)*dscale**j*G
        kernel_bounds.append({'parameter_order': j,
            'weighted_kernel_L1': str(value), 'kernel_initial': str(initial),
            'weighted_time_derivative_L1': str(time_derivative),
            'weighted_value_timejet_operator': str(complete)})
    T0, T1, T2 = [F(row['weighted_value_timejet_operator']) for row in kernel_bounds]
    # Same original matter family: B does not enter the Dirac Hamiltonian.
    # These actual all-time packet estimates were paid before the boson family.
    A0, A1, A2 = F(17, 5), F(74, 25), F(148, 125)
    assert 2*rho*rho < F(1, 90000)**2
    NF, DF = T0*A0, T1*A0+T0*A1
    CF = T2*A0/2+T1*A1+T0*A2
    remainder = [2*CF*NF+DF*DF, 2*DF*NF+eps_star*DF*DF, NF*NF]
    source_current = []
    for row in readers['readers']:
        bounds = list(map(F, row['source_value_timejet_bilinear_bounds']))
        assert len(bounds) == 3 and all(value >= 0 for value in bounds)
        total = sum(v*c for v, c in zip(bounds, remainder))
        source_current.append({'reader': row['reader'], 'V0_V1_V2': list(map(str, bounds)),
            'true_epsilon_squared_current_remainder': str(total)})
    assert len(source_current) == 48
    output = {'scope': 'STRIKE_ACTUAL_JOINT_RETARDED_CONTOUR_FAMILY_AND_STRONG_NATIVE_CURRENT_RESPONSE',
        'input_sha256': {str((HERE/name).relative_to(ROOT)): hashlib.sha256((HERE/name).read_bytes()).hexdigest()
            for name in files},
        'upstream_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [FQ/'packet-gauge-family/remainder.py', FQ/'packet-gauge-dynamics/bounds.json',
                FQ/'packet-gauge-causal/source.json']},
        'native_source_sha256': source['native_source_sha256'],
        'actual_parameter': 'Aepsilon=Abar+epsilon a, Bepsilon=Bbar+epsilon b0; epsilon=3sqrt2*a/10',
        'real_epsilon_radius': str(eps_star), 'complex_epsilon_disk_radius': str(complex_eps),
        'source_positive_delta_in_a': str(delta), 'actual_D_lower': str(Dlower),
        'world289_infinity_bound_on_actual_circle': str(G),
        'Noether_minor_neumann_ratio': str(ratio),
        'Noether_source': 'Kepsilon=K0+epsilon K1; Hepsilon Kepsilon=-epsilon C1-epsilon² C2. Frequency-independent minor and Ktime^T Z=0 leave instant plus proper source, no delta-prime.',
        'contour': 'Gamma:lambda=5c exp(i theta), c=6sqrt15/25; all actual poles enclosed; original time unchanged',
        'kernel_definition': 'chi_epsilon(t)=(2pi i)^-1 integral_Gamma exp(lambda*t) X_epsilon(lambda) d lambda, t>=0; zero for negative time',
        'Laplace_identity': 'integral_0^infinity exp(-z*t)chi_epsilon(t)dt=X_epsilon(z), Re z>=5, by genuine proper rational source and contour Cauchy',
        'parameter_derivative_scale': str(dscale), 'exponential_bound_rate': str(beta),
        'damping_minimum': 5, 'kernel_bounds': kernel_bounds,
        'true_strong_Taylor_remainder': '||T_epsilon-T0-epsilon T1||<=epsilon²*T2/2, including chi(0) input contact',
        'field_bounds': {'uniform_value_timejet': str(NF), 'first_difference_over_abs_epsilon': str(DF),
            'epsilon_squared_remainder': str(CF)},
        'all48_native_current_bounds': source_current,
        'quadratic_reader_current_remainder': 'epsilon²[V0(2 CF NF+DF²)+V1(2 DF NF+epsilon_star DF²)+V2 NF²]',
        'reader_second_parameter_coefficients_retained': True,
        'time_zero': 'Yepsilon(0)=0, right time derivative retains chi_epsilon(0)J_epsilon(0); no Jprime input',
        'phase': 'original FullPhase co-rotating289, same physical time; original unrotated field by existing FullPhase readback',
        'new_Lean_declarations': 0, 'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'contour.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS actual contour kernel, weighted strong jets and48 quadratic native reader remainders',
          output['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
