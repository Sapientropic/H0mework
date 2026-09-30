#!/usr/bin/env python3
"""Original epsilon-family audit of the time-independent positive Fock metric."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_coframe_live_ordering import (
    RawLiveCoefficients, HERE, ROOT, ROOT_ID, rational, eq, full,
    polynomial_action, terms, current, state_encode)
from independent_source_quantum_ordered_temporal import raw_coframe_family
from independent_source_gauge_legendre import bindings, decode, encode
from independent_source_gauss_quantum_current import decoded_state


def zero(value): assert s.cancel(s.expand(value)) == 0
def state_equal(left, right): assert not terms([(1, left), (-1, right)])


def at(value, substitutions):
    if isinstance(value, list): return [at(v, substitutions) for v in value]
    if isinstance(value, s.MatrixBase): return rational(value.subs(substitutions))
    return s.cancel(value.subs(substitutions))


def main():
    started = time.monotonic(); path = HERE/'source_temporal_coframe_pairing.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    names = ('independent_source_reducing_coframe_metric', 'independent_source_quantum_ordered_temporal',
             'independent_source_full_quantum_adjoint')
    for name in names:
        record = json.loads((HERE/(name+'.json')).read_text()); count += bindings(record)
        assert record['root'] == ROOT_ID
    raw = RawLiveCoefficients()
    ys = (s.Symbol('quantum_n', positive=True), *s.symbols('quantum_b1:4', real=True))
    e, cf = raw_coframe_family(raw, ys); q = raw.q
    volume = q[0]*q[2]*q[5]
    gradient_log = s.Matrix([s.diff(volume, x)/volume for x in q])
    Hessian_log = gradient_log.jacobian(q)
    K = cf['K']; eq(K.H, K); eq(K.conjugate(), K)
    Ki, free = K.gauss_jordan_solve(s.eye(6)); assert free.rows == 0
    eq(K*Ki, s.eye(6)); eq(Ki*K, s.eye(6))
    divergence = rational(s.Matrix([sum(s.diff(K[i, j], q[i]) for i in range(6)) for j in range(6)]))
    D = rational(s.I*cf['drift'].T)
    t = rational(s.Matrix([s.trace(M.H-M)/(16*s.I) for M in cf['M']]))
    eq(t, K*gradient_log); eq(D-divergence, 2*t)
    Mh = []
    for j, M in enumerate(cf['M']):
        eq(M.H-M, 2*s.I*t[j]*s.eye(8))
        Mh.append(rational((M+M.H)/2)); eq(Mh[-1].H, Mh[-1])
        eq(Mh[-1], decode(candidate['generic_identities']['all6_Hermitian_mixed_matrices'][j],
                          {str(v): v for v in (*q, *ys)}))
    divM = rational(sum((M.diff(q[j]) for j, M in enumerate(Mh)), s.zeros(8)))
    logM = rational(sum((gradient_log[j]*M for j, M in enumerate(Mh)), s.zeros(8)))
    eq(divM, s.zeros(8)); eq(logM, s.zeros(8))
    constant = rational(cf['one_body']+cf['correction']); eq(constant.H, constant)
    tensor = rational(sum((weight*s.kronecker_product(cf['J'][a], cf['J'][b])
                           for (a, b), weight in cf['W'].todok().items()), s.zeros(64)))
    eq(tensor.H, tensor)
    zero(s.im(cf['constant']))
    number = s.Symbol('particle_number', integer=True, nonnegative=True)
    effective = rational(D+number*t)
    generated_log_weight = rational(Ki*(effective-divergence))
    eq(generated_log_weight, (number+2)*gradient_log)
    weight = volume**(number+2)
    for j in range(6): zero(s.diff(weight, q[j])/weight-generated_log_weight[j])
    for y in ys: zero(s.diff(weight, y))
    # Every integration-by-parts coefficient is checked before testing an
    # actual state. This includes the complete zeroth-order divergence.
    eq(-2*(divergence+K*generated_log_weight)+effective, -effective)
    div2 = sum(s.diff(K[i, j], q[i], q[j])+
        generated_log_weight[j]*s.diff(K[i, j], q[i])+
        generated_log_weight[i]*s.diff(K[i, j], q[j])+
        (s.diff(generated_log_weight[i], q[j])+generated_log_weight[i]*generated_log_weight[j])*K[i, j]
        for i in range(6) for j in range(6))
    div1 = sum(s.diff(effective[j], q[j])+generated_log_weight[j]*effective[j] for j in range(6))
    zero(div1-div2)
    eq(divM+sum((generated_log_weight[j]*M for j, M in enumerate(Mh)), s.zeros(8)), s.zeros(8))
    alpha = (number+2)/2
    deltaV = s.cancel(alpha*(effective.T*gradient_log)[0]-alpha**2*(gradient_log.T*K*gradient_log)[0]+
        alpha*sum(K[i, j]*Hessian_log[i, j] for i in range(6) for j in range(6)))
    zero(deltaV-3*ys[0]*(number+2)*(number+4)/(16*volume))
    zero(deltaV-s.sympify(candidate['uniform_half_density_potential'], locals={str(v): v for v in (*q, *ys, number)}))
    # The three shifts really cancel in the final original coframe action.
    # This is read from every matrix coefficient rather than inferred from a
    # nonzero-shift fixture whose output could be accidentally insensitive.
    support = []
    for b in ys[1:]:
        report = {'K': len(rational(K.diff(b)).todok()),
            'mixed': sum(len(rational(M.diff(b)).todok()) for M in cf['M']),
            'normal_tensor': len(rational(tensor.diff(b)).todok()),
            'onebody_with_live_correction': len(rational(constant.diff(b)).todok())}
        assert all(value == 0 for value in report.values())
        support.append(report)
    assert support == candidate['shift_coefficient_support']
    for key, old in [('K', raw.K), ('drift', raw.drift), ('constant', 3*raw.e.det())]:
        value = cf[key]
        if isinstance(value, s.MatrixBase): eq(value, ys[0]/raw.N*old)
        else: zero(value-ys[0]/raw.N*old)
    for value, old in zip(cf['M'], raw.M): eq(value, ys[0]/raw.N*old)
    eq(constant, ys[0]/raw.N*(raw.one_body+raw.correction))
    source_tensor = rational(sum((v*s.kronecker_product(raw.J[a], raw.J[b])
                                 for (a, b), v in raw.W.todok().items()), s.zeros(64)))
    eq(tensor, ys[0]/raw.N*source_tensor)
    print('PASS raw all-sixq/four-time full adjoint coefficients and source-normalized number metric', flush=True)

    saved = candidate['actual_consumer']; qpoint = tuple(map(s.sympify, saved['q']))
    timepoint = tuple(map(s.sympify, saved['time'])); word = tuple(saved['input_CAR'])
    assert word == (133, 385) and all(timepoint[1:])
    assert timepoint[0] > 0 and timepoint[0]**2 > sum(b*b for b in timepoint[1:])
    sub = {**dict(zip(q, qpoint)), **dict(zip(ys, timepoint))}
    data = {key: at(value, sub) for key, value in cf.items()}
    gradient, Hessian = decode(saved['gradient6']), decode(saved['Hessian6'])
    z = s.Matrix(s.symbols('half_density_increment0:6', real=True)); origin = dict.fromkeys(z, 0)
    polynomial = 1+(gradient.T*z)[0]+(z.T*Hessian*z)[0]/2
    volume0 = s.prod(qpoint[j] for j in (0, 2, 5))
    live_volume = s.prod(qpoint[j]+z[j] for j in (0, 2, 5))
    transformed_polynomial = (volume0/live_volume)**s.Rational(len(word)+2, 2)*polynomial
    g = rational(s.Matrix([s.diff(transformed_polynomial, y).subs(origin) for y in z]))
    H = rational(s.hessian(transformed_polynomial, list(z)).subs(origin))
    actual, _ = polynomial_action(data, word, 1, g, H)
    constant_image, _ = polynomial_action(data, word, 1, s.zeros(6, 1), s.zeros(6))
    shift = s.cancel(deltaV.subs(number, len(word)).subs(sub))
    scalar = -sum(v*Hessian[i, j] for (i, j), v in data['K'].todok().items())
    scalar -= (at(divergence, sub).T*gradient)[0]; scalar += shift
    expected = terms([(1, constant_image), (scalar, {word: 1})]+
        [(-s.I*gradient[j], current(full(at(M, sub)), {word: 1})) for j, M in enumerate(Mh)])
    state_equal(actual, expected)
    state_equal(actual, decoded_state(saved['U_H_U_inverse']))
    state_equal(expected, decoded_state(saved['independent_divergence_representation']))
    zero(shift-s.sympify(saved['real_potential_shift'])); assert shift != 0 and s.im(shift) == 0
    assert terms([(1, expected), (-1, terms([(1, expected), (-shift, {word: 1})]))])
    print('PASS actual three-shift fullCAR action by literal half-density differentiation and raw divergence form', flush=True)
    paths = [Path(__file__), path, HERE/'source_temporal_coframe_pairing.py',
        HERE/'independent_source_coframe_live_ordering.py', HERE/'independent_source_quantum_ordered_temporal.py',
        HERE/'independent_source_reducing_coframe_metric.py']+[HERE/(name+'.json') for name in names]
    result = {'verdict': 'CERTIFIED_ORIGINAL_FOUR_TIME_COFRAME_FAMILY_ON_ONE_SOURCE_POSITIVE_PAIRING',
        'root': ROOT_ID, 'source_sha256': candidate['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks': count, 'candidate_constructor_imported': False,
        'independent_method': 'Original epsilon Hessian and primary graph; full Kronecker64 normal-product tensor; all integration-by-parts coefficients; literal six-variable inverse half-density polynomial differentiation and exterior-slot CAR action.',
        'all_generic_sixq_fourtime_adjoint_coefficients_match': True,
        'number_weight_generated_by_inverting_original_K': str(weight),
        'number_weight_independent_of_four_time_parameters': True,
        'both_complete_Hermitian_mixed_divergences_zero': True,
        'full_normal_product_tensor_nonzero_entries': len(tensor.todok()),
        'complete_coframe_family_identity': 'Hcoframe(n,b)=n/N_source * Hcoframe(N_source,0), as an identity of every collected differential and normal-product coefficient. The three shifts cancel in this component.',
        'actual_shift_coefficient_support': support,
        'same_positive_pairing': 'rho3*v^(2+Number); the original residual3 density is q-independent. The coframe-only metric and source normalization are unchanged throughout the original family.',
        'generic_half_density_real_potential': str(deltaV),
        'actual_consumer': {'q': list(map(str, qpoint)), 'time': list(map(str, timepoint)), 'input_CAR': list(word),
            'literal_transformed_gradient6': encode(g), 'literal_transformed_Hessian6': encode(H),
            'complete_U_H_U_inverse': state_encode(actual), 'independent_divergence_image': state_encode(expected),
            'nonzero_real_potential_shift': str(shift)},
        'scope': 'All original coframe time parameters and live sixq coefficients on the positive source chart. This closes the coframe pairing family; it does not solve temporal secondary constraints, sum their formal series, or supply the quantum spectrum and lifetime.',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'independent_source_temporal_coframe_pairing.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent temporal coframe pairing', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
