#!/usr/bin/env python3
"""The same source coframe Fock pairing over the original four-time family."""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_joint_form_hamiltonian import SourceJointFormHamiltonian, read_bound
from source_quantum_ordered_temporal import SourceTemporalQuantumFamily
from source_coframe_live_ordering import full, verify_jet_action
from source_coframe_legendre import rational
from source_lorentz_contact import equal, encode
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state


def generic_pairing(model, family):
    cf = family.cf; q = model.coframe.q; g = model.metric['g']; v = model.metric['volume']
    K = cf['K']; t = rational(K*g); D = rational(s.I*cf['drift'].T)
    divergence = rational(s.Matrix([sum(s.diff(K[i, j], q[i]) for i in range(6)) for j in range(6)]))
    equal(rational(D-divergence-2*t), s.zeros(6, 1))
    Mh = []
    for j, M in enumerate(cf['M']):
        equal(rational(M.H-M-2*s.I*t[j]*s.eye(8)), s.zeros(8))
        Mh.append(rational(M+s.I*t[j]*s.eye(8)))
        equal(Mh[-1].H, Mh[-1])
    equal(rational(sum((Mh[j].diff(q[j]) for j in range(6)), s.zeros(8))), s.zeros(8))
    equal(rational(sum((g[j]*Mh[j] for j in range(6)), s.zeros(8))), s.zeros(8))
    constant = cf['one_body']+cf['correction']; equal(rational(constant.H-constant), s.zeros(8))
    flat = s.Matrix.hstack(*(J.reshape(64, 1) for J in cf['J']))
    tensor = rational(flat*cf['W']*flat.T)
    indices = [8*j+i for i in range(8) for j in range(8)]
    equal(rational(tensor.conjugate().extract(indices, indices)-tensor), s.zeros(64))
    m = s.Symbol('particle_number', integer=True, nonnegative=True); alpha = (m+2)/2
    effective = rational(D+m*t)
    equal(rational(effective-divergence-(m+2)*K*g), s.zeros(6, 1))
    potential = s.cancel(alpha*(effective.T*g)[0]-alpha**2*(g.T*K*g)[0]+
                        alpha*sum(K[i, j]*model.metric['Hessian'][i, j] for i in range(6) for j in range(6)))
    assert s.cancel(potential-3*family.y[0]*(m+2)*(m+4)/(16*v)) == 0
    return dict(K=K, t=t, D=D, divergence=divergence, Mh=Mh, tensor=tensor,
                m=m, potential=potential, volume=v)


def main():
    started = time.monotonic(); read_bound('source_reducing_coframe_metric')
    model = SourceJointFormHamiltonian(); family = SourceTemporalQuantumFamily(model.native)
    d = generic_pairing(model, family)
    print('PASS all6q/all4time coframe formal adjoints and the same positive Fock pairing', flush=True)
    q = (s.Rational(7, 6), s.Rational(1, 11), s.Rational(9, 8),
         s.Rational(-1, 13), s.Rational(1, 17), s.Rational(11, 10))
    timepoint = (model.coframe.N, s.Rational(1, 13), -s.Rational(1, 17), s.Rational(1, 19))
    assert timepoint[0]**2 > sum(b*b for b in timepoint[1:])
    sub = {**dict(zip(model.coframe.q, q)), **dict(zip(family.y, timepoint))}
    def at(value):
        if isinstance(value, list): return [at(item) for item in value]
        if isinstance(value, s.MatrixBase): return rational(value.subs(sub))
        return s.cancel(value.subs(sub))
    cf = {key: at(value) for key, value in family.cf.items()}
    word = (133, 385); m = len(word); alpha = s.Rational(m+2, 2)
    g = at(model.metric['g']); h = at(model.metric['Hessian'])
    gradient = s.Matrix([s.I*s.Rational(j+1, 17) for j in range(6)])
    u = s.Matrix([s.Rational(j % 3-1, 19) for j in range(6)]); H = u*u.T-s.eye(6)
    transformed_g = gradient-alpha*g
    transformed_H = H-alpha*(g*gradient.T+gradient*g.T)+alpha**2*g*g.T-alpha*h
    direct = verify_jet_action(cf, word, 1, transformed_g, transformed_H)
    actual = {tuple(w): s.sympify(value) for w, value in direct['raw_nested_square']}
    constant = verify_jet_action(cf, word, 1, s.zeros(6, 1), s.zeros(6))
    shift = s.cancel(d['potential'].subs(d['m'], m).subs(sub))
    scalar = -sum(v*H[i, j] for (i, j), v in cf['K'].todok().items())-(at(d['divergence']).T*gradient)[0]+shift
    terms = [(1, {tuple(w): s.sympify(value) for w, value in constant['raw_nested_square']}), (scalar, {word: 1})]
    for j, M in enumerate(d['Mh']):
        terms.append((-s.I*gradient[j], apply_superposition(full(at(M)), {word: 1})))
    expected = weighted_sum(terms)
    assert weighted_sum([(1, actual), (-1, expected)]) == {}
    assert actual
    # Record genuine parameter support; a vanishing shift coefficient is kept
    # as a source identity, not replaced by an assumed independent atom.
    shift_support = []
    for b in family.y[1:]:
        shift_support.append({'K': len(rational(d['K'].diff(b)).todok()),
            'mixed': sum(len(rational(M.diff(b)).todok()) for M in family.cf['M']),
            'normal_tensor': len(rational(d['tensor'].diff(b)).todok()),
            'onebody_with_live_correction': len(rational((family.cf['one_body']+family.cf['correction']).diff(b)).todok())})
    print('PASS actual nonzero three-shift fullCAR action and independent half-density divergence representation', flush=True)
    paths = [HERE/name for name in ('source_temporal_coframe_pairing.py', 'source_quantum_ordered_temporal.py',
        'source_quantum_ordered_temporal.json', 'source_reducing_coframe_metric.py',
        'source_reducing_coframe_metric.json', 'source_joint_form_hamiltonian.py')]
    result = {'root': ROOT_ID, 'scope': 'ORIGINAL_FOUR_TIME_COFRAME_FAMILY_ON_THE_SAME_SOURCE_FOCK_PAIRING',
        'source_sha256': model.native.graph.common.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'parameters': list(map(str, family.y)), 'pairing': 'rho3*v^(2+Number), independent of all four original time parameters',
        'generic_identities': {'D_minus_divK': '2*K*grad(log v)', 'M_adjoint_minus_M': '2*i*(K*grad(log v)) I8',
            'all6_Hermitian_mixed_matrices': [encode(M) for M in d['Mh']],
            'ordinary_and_log_volume_mixed_divergence_zero': True,
            'complete64_normal_current_tensor_adjoint': True, 'onebody_plus_live_correction_Hermitian': True,
            'all_Fock_number_weighted_divergence_identity': True},
        'uniform_half_density_potential': str(d['potential']),
        'shift_coefficient_support': shift_support,
        'actual_consumer': {'q': list(map(str, q)), 'time': list(map(str, timepoint)), 'input_CAR': list(word),
            'gradient6': encode(gradient), 'Hessian6': encode(H), 'U_H_U_inverse': encode_state(actual),
            'independent_divergence_representation': encode_state(expected), 'real_potential_shift': str(shift)},
        'direct_consumer': 'The original coframe family and each real time derivative share the same positive test pairing. This connects the fixed-time form to the original four-time constraints without a time-dependent Hilbert metric.',
        'temporal_secondary_solution_or_series_sum_supplied': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_temporal_coframe_pairing.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source temporal coframe pairing', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
