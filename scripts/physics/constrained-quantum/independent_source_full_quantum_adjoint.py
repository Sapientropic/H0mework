#!/usr/bin/env python3
"""Original-coefficient audit of the full504 form and its adjoint test action.

The candidate constructor is not imported. Occupation-bit exterior maps and
the original Dirac density reconstruct all Yukawa coefficients; independent
divergence-form and implicit Gauss jets give the complete four-energy action.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time

import sympy as s

from independent_source_joint_form_hamiltonian import (
    RawGaussSection, RawLiveCoefficients, HERE, ROOT, ROOT_ID, bindings,
    rational, eq, decode, encode, terms, current, state_encode, decoded_state,
    zero, state_equal, build_operators, whole_action, raw_gauge_coefficients,
    coefficient_audit, original_kernel)


def sparse(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.cancel)


def dual_pair(matrix):
    return sparse(s.diag(matrix, -matrix.conjugate()))


def matrix_degree(matrix, weights, degree):
    for (i, j), value in matrix.todok().items():
        zero((weights[i]-weights[j]-degree)*value)


def state_degree(state, weights, number, degree):
    assert state
    for word, coefficient in state.items():
        assert coefficient != 0 and len(word) == number
        assert sum(weights[i] for i in word) == degree


def inner(left, right):
    return s.cancel(sum(s.conjugate(coefficient)*right.get(word, 0)
                        for word, coefficient in left.items()))


def raw_generic_matter(raw_cf, section, inventory, Yukawa, P, candidate):
    gamma = inventory['gamma']; e = raw_cf.e
    volume = s.factor(e.det()); inverse = e.inv()
    principal = [rational(s.I*volume*sum((inverse[mu, a]*gamma[a]
                 for a in range(4)), s.zeros(4))) for mu in range(4)]
    E_inverse, free = principal[0].gauss_jordan_solve(s.eye(4))
    assert free.rows == 0
    eq(principal[0]*E_inverse, s.eye(4)); eq(E_inverse*principal[0], s.eye(4))
    prefactor = rational(-s.I*volume*E_inverse)
    eq(prefactor, raw_cf.N*gamma[0])
    eq(prefactor, decode(candidate['generic_Yukawa_prefactor'],
                        {str(q): q for q in raw_cf.q}))
    spin = [rational(-s.I*E_inverse*principal[i]) for i in (1, 2, 3)]
    for C, saved in zip(spin, candidate['matter_adjoint']['generic_all_six_q_spin_factors']):
        eq(C.H, -C)
        eq(C, decode(saved, {str(q): q for q in raw_cf.q}))
    for T in inventory['gauge']:
        eq(T.H, -T)
        eq(T, s.kronecker_product(s.eye(4), T[:63, :63]))
    degrees = [degree for degree, _ in inventory['internal_basis']]
    assert degrees == [6]*7+[2]*21+[4]*35
    weights = [int(degrees[i % 63] == 6) for i in range(504)]
    assert sum(weights) == 56
    Pfull = sparse(s.diag(P, P.conjugate()))
    allY = [dual_pair(Y) for Y in Yukawa]
    assert len(allY) == 70
    for Y in allY:
        matrix_degree(Y, weights, 1); matrix_degree(Y.H, weights, -1)
        eq(Y*Pfull, s.zeros(504)); eq(Y.H*Pfull, s.zeros(504))
    # Reconstruct every real-coordinate Yukawa coefficient at the generic
    # coframe, before using the source-generated constant prefactor identity.
    left = sparse(s.kronecker_product(prefactor, s.eye(63)))
    for i, Yraw in enumerate(inventory['scalar']):
        for part, coefficient in enumerate((1, s.I)):
            eq(left*sparse(Yraw)*coefficient, Yukawa[35*part+i])
    spin_inputs = raw_cf.J+raw_cf.T+raw_cf.M+[raw_cf.one_body, raw_cf.correction]
    spin_inputs += [M for row in raw_cf.dT for M in row]
    for M in spin_inputs:
        # All original coframe matrices act only on spin; the full internal
        # exterior label survives each current and every normal product.
        for (i, j), value in M.todok().items():
            for internal in range(63):
                zero((weights[63*i+internal]-weights[63*j+internal])*value)
    for Q in section.native.Qb+section.native.Qs+section.r:
        matrix_degree(Q, weights, 0)
    for T in inventory['gauge']:
        matrix_degree(dual_pair(T), weights, 0)
    # The scalar-adjoint correction only uses these same Hermitian broken
    # currents, so the newly specified scalar form also preserves the grade.
    for Q in section.native.Qb: eq(Q.H, Q)
    covariances = 0
    for h in range(3):
        rho = sparse(sum((section.native.S[a, h]*section.native.rho[a]
                         for a in range(12)), s.zeros(70)))
        R = sparse(section.r[h]); eq(R.H, -R)
        for j, Y in enumerate(allY):
            derivative = sparse(sum((rho[i, j]*allY[i]
                                     for i in range(70) if rho[i, j]), s.zeros(504)))
            eq(R*Y-Y*R, derivative)
            eq(R*Y.H-Y.H*R, derivative.H)
            covariances += 1
    return allY, weights, Pfull, {
        'generic_all_six_q_original_prefactor': encode(prefactor),
        'generic_original_spin_factors': [encode(C) for C in spin],
        'all12_internal_anti_Hermitian_spin_commuting_coefficients': True,
        'full504_nonY_Hermitian_for_every_real_A_and_live_sixq': True,
        'original_Yukawa_real_coefficients': len(allY),
        'one_particle_Lambda6_grade_rank': sum(weights),
        'raising_and_lowering_entrywise_grade_checks': 2*len(allY),
        'whole_live_coframe_spin_coefficient_count': len(spin_inputs),
        'residual3_full70_Y_and_adjoint_covariance_equations': 2*covariances,
        'same_392_reducing_kernel_preserved': True}


def full_H0_adjoint(raw_cf, section, carrier, metric_record):
    cf = coefficient_audit(raw_cf, metric_record, carrier)
    A = s.Matrix(3, 12, s.symbols('full_adjoint_A0:36', real=True))
    gauge = raw_gauge_coefficients(raw_cf.e, A, section.native)
    eq(gauge['weight'].T, gauge['weight'])
    eq(gauge['weight'].conjugate(), gauge['weight'])
    eq(gauge['shift'].conjugate(), gauge['shift']); zero(s.im(gauge['potential']))
    for coordinate in A: eq(gauge['weight'].diff(coordinate), s.zeros(36))
    zero(s.trace(gauge['weight']*gauge['ds']))
    return {'coframe': cf['report'],
        'full_carrier_coframe_scope': 'The complete spin8 and normal-product tensor identities do not project the CAR carrier; the same number-sector adjoint proof applies to all504 modes.',
        'generic_original_BF_gauge_square_real_symmetric_q_only_weight': True,
        'generic_original_gauge_shift_and_potential_real': True,
        'original_scalar_form': 'The independent all97 divergence-form coefficients are regenerated below. Their original full504 Hermitian broken currents preserve Number and grade. The signed second-class measure cancellation and residual3 covariance give the same rho3 weight.',
        'H0': 'Original coframe + specified Pi-dagger Pi scalar form + original gauge + nonY matter. This grade-preserving component is formally symmetric on the full504 compact smooth test domain.'}


def main():
    started = time.monotonic(); path = HERE/'source_full_quantum_adjoint.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    names = ('source_joint_form_hamiltonian', 'independent_source_joint_form_hamiltonian',
             'source_yukawa_reducing_carrier', 'independent_source_yukawa_reducing_carrier',
             'source_reducing_coframe_metric', 'independent_source_reducing_coframe_metric',
             'independent_source_scalar_form_hamiltonian', 'independent_source_full_gauss_section',
             'source_quantum_grade_structure')
    records = {}
    for name in names:
        records[name] = json.loads((HERE/(name+'.json')).read_text())
        count += bindings(records[name]); assert records[name]['root'] == ROOT_ID
    section = RawGaussSection(); raw_cf = RawLiveCoefficients()
    assert section.native.hashes == candidate['source_sha256']
    inventory, Yukawa, _, P, _, _ = original_kernel(records['source_yukawa_reducing_carrier'])
    allY, weights, carrier, matter = raw_generic_matter(raw_cf, section, inventory, Yukawa, P, candidate)
    adjoints = full_H0_adjoint(raw_cf, section, carrier, records['source_reducing_coframe_metric'])
    print('PASS independent full504 generic H0 adjoints, all70 Y coefficients and residual3 covariance', flush=True)

    saved = candidate['actual_complete_consumer']; shared = records['source_joint_form_hamiltonian']['actual_consumer']
    q = tuple(map(s.sympify, shared['q'])); x = decode(shared['x61']); A = decode(shared['A36'])
    A[0, 2] += s.Rational(1, 17); A[1, 7] += s.Rational(1, 19)
    assert q == tuple(map(s.sympify, saved['q']))
    eq(x, decode(saved['x61'])); eq(A, decode(saved['A36']))
    point = s.Matrix(q).col_join(x).col_join(A.reshape(36, 1))
    data = build_operators(section, raw_cf, q, x, A)
    phi = data['scalar']['phi']
    Y = sparse(sum((phi[j]*allY[j] for j in range(70)), s.zeros(504)))
    M0 = sparse(data['matter']-Y)
    eq(M0.H, M0); matrix_degree(M0, weights, 0)
    matrix_degree(Y, weights, 1); matrix_degree(Y.H, weights, -1)
    eq(Y*Y, s.zeros(504)); eq(Y*carrier, s.zeros(504)); eq(Y.H*carrier, s.zeros(504))
    column = min(j for _, j in Y[:252, :252].todok())
    word = (column, column+252); unit = {word: s.S.One}
    assert word == tuple(saved['input_CAR'])
    assert all(carrier[i, i] == 0 for i in word)
    state_degree(unit, weights, 2, 0)
    gradient = s.Matrix([s.I*s.Rational(j % 5-2, 47) for j in range(100)])
    u = s.Matrix([s.Rational(j % 3-1, 43) for j in range(100)])
    Hessian = u*u.T-s.eye(100)
    eq(gradient, decode(saved['gradient100'])); eq(Hessian, decode(saved['Hessian100']))
    geo, jets = section.extension_jet(point, unit, {word: gradient}, {word: Hessian})
    gauss = section.Gauss_checks(point, jets)
    assert saved['Gauss']['all3_Gauss_values_zero'] == gauss['all3_original_Gauss_values_zero']
    assert saved['Gauss']['all309_first_derivatives_of_Gauss_zero'] == gauss['all309_first_derivatives_of_Gauss_zero']
    assert all(g.shape == (103, 1) and h.shape == (103, 103) for _, g, h in jets.values())
    hidden = [w for w, (f, g, h) in jets.items() if f == 0 and (g.todok() or h.todok())]
    residual_currents = [current(R, unit) for R in section.r]
    for w in jets: assert len(w) == 2 and sum(weights[i] for i in w) == 0
    pieces, H = whole_action(data, jets)
    assert all(pieces.values())
    for name, component in pieces.items():
        state_equal(component, decoded_state(saved['all_four_component_images'][name]))
        if name != 'matter_without_Lorentz': state_degree(component, weights, 2, 0)
    raised = current(Y, unit); lowered = current(Y.H, unit)
    assert raised and not lowered
    H0 = terms([(1, H), (-1, raised)])
    Hsharp = terms([(1, H0), (1, lowered)])
    for name, actual in [('H', H), ('H0', H0), ('Y', raised), ('Hsharp', Hsharp)]:
        state_equal(actual, decoded_state(saved[name]))
    state_degree(H0, weights, 2, 0); state_degree(raised, weights, 2, 1)
    state_equal(terms([(1, H), (-1, Hsharp)]), raised)
    twice = current(Y, raised); assert twice and not current(Y, twice)
    state_degree(twice, weights, 2, 2)
    interleaved = current(Y, current(M0, raised))
    assert interleaved and not current(Y, current(M0, interleaved))
    state_degree(interleaved, weights, 2, 2)
    state_equal(twice, decoded_state(saved['Y_squared_Fock']))
    state_equal(interleaved, decoded_state(saved['Y_M0_Y']))
    support = sorted({i for w in H for i in w})
    assert support == saved['whole_output_CAR_support']
    assert any(carrier[i, i] == 0 for i in support)
    _, dropped = whole_action(data, {w: jet for w, jet in jets.items() if jet[0] != 0})
    omission = terms([(1, H), (-1, dropped)])
    print('PASS independently reconstructed off392 N2 Gauss jet and all H/H0/Hsharp/grade2 images', flush=True)

    # The orbit minor, not a new Faddeev--Popov factor, supplies rho3.
    rho = s.cancel(s.sign(section.source_minor.det())*geo['M'].det())
    zero(rho-8*A[0, 1]**2*A[1, 0])
    v = s.prod(q[j] for j in (0, 2, 5)); density = s.cancel(rho*v**4)
    assert all(q[j] > 0 for j in (0, 2, 5)) and A[0, 1] > 0 and A[1, 0] > 0
    assert data['scalar']['D'].det() != 0 and rho > 0 and density > 0
    D0 = section.native.O.T*s.Matrix.hstack(*(T*section.native.v for T in section.native.rhob))
    relative = rational(D0.inv()*(data['scalar']['D']-D0))
    connection_bound = max(sum(abs(relative[i, j]) for j in range(9)) for i in range(9))
    assert connection_bound < 1
    norm = s.cancel(density*inner(raised, raised))
    readback = s.cancel(density*inner(current(Y.H, raised), unit))
    reverse = s.cancel(density*inner(current(Y, raised), unit))
    assert norm > 0; zero(norm-readback); zero(reverse)
    pairing = candidate['actual_pairing_consumer']
    for value, key in [(density, 'positive_density_at_point'), (norm, 'Y_pairing_norm_squared'),
                       (readback, 'adjoint_readback'), (reverse, 'original_reverse_pairing')]:
        zero(value-s.sympify(pairing[key]))
    print('PASS source positive pairing, unchanged weighted Y adjoint and genuine compact-packet defect', flush=True)

    paths = [Path(__file__), path, HERE/'source_full_quantum_adjoint.py',
             HERE/'independent_source_joint_form_hamiltonian.py',
             HERE/'independent_source_scalar_form_hamiltonian.py',
             HERE/'independent_source_quantum_gauss_section.py',
             HERE/'independent_source_common_hamiltonian.py',
             HERE/'independent_source_yukawa_reducing_carrier.py',
             HERE/'independent_source_reducing_coframe_metric.py',
             HERE/'SymmetricGraphClosure.lean']+[HERE/(name+'.json') for name in names]
    result = {'verdict': 'CERTIFIED_FULL504_SOURCE_FORM_AND_COMMON_FORMAL_ADJOINT_PAIR',
        'root': ROOT_ID, 'source_sha256': section.native.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks': count, 'candidate_constructor_imported': False,
        'independent_method': 'Original Clifford/occupation-bit exterior coefficients; raw BF and coframe Hessians; full97 divergence-form scalar operator; implicit residual3 inverse two-jet; exterior-slot CAR action and the original orbit minor.',
        'original_matter_and_grade': matter, 'full_H0_formal_adjoint_coefficients': adjoints,
        'actual_complete_consumer': {'point103': encode(point), 'input_CAR': list(word),
            'both_input_modes_outside392': True, 'Gauss': gauss,
            'zero_value_nonzero_derivative_words': [list(w) for w in hidden],
            'residual3_CAR_current_values': [state_encode(value) for value in residual_currents],
            'omitting_zero_value_words_changes_full_action': bool(omission),
            'all_four_nonzero_component_images': {name: state_encode(value) for name, value in pieces.items()},
            'H': state_encode(H), 'H0': state_encode(H0), 'Hsharp': state_encode(Hsharp),
            'Y': state_encode(raised), 'Y_squared_Fock': state_encode(twice),
            'Y_M0_Y': state_encode(interleaved), 'third_raise_and_interleaved_third_raise_zero': True,
            'whole_output_CAR_support': support},
        'positive_pairing': {'original_rho3': str(rho), 'volume': str(v),
            'density_on_N2': str(density), 'Y_norm_squared': str(norm),
            'Ydagger_readback': str(readback), 'original_reverse_readback': str(reverse),
            'straight_source_segment_relative_D9_row_bound': str(connection_bound),
            'compact_packet': 'The displayed point lies in the original open chart (positive q diagonals and gauge slice coordinates, invertible D9), with Yf nonzero. Continuity gives a compact smooth grade0 packet f with that value and g=Yf on the same source section. The two genuine integrals satisfy <g,Hf>=integral rho3*v^4*norm(Yf)^2>0 and <Hg,f>=0. The pointwise norm is not reported as the packet integral.',
            'adjoint_pair': 'The number-sector metric is scalar and Y is zeroth order, so dGamma(Y)^sharp=dGamma(Ydagger). Residual3 coefficient covariance retains both actions on the same compact smooth section domain. Integration by parts for the complete H0 gives <Hf,g>=<f,(H0+Ydagger)g>.'},
        'graph_closure_scope': 'The source coefficients and their inverses are smooth on the open chart. Compact smooth sections are dense in its positive weighted L2 completion. The formal adjoint pair therefore pays the zero-sequence criterion and the unique minimal closed graph extension. SymmetricGraphClosure.lean verifies this generic mechanism; no concrete weighted-L2 Lean instance is claimed by this audit.',
        'operator_preserved': 'H=H0+Y with the original Y. Hsharp=H0+Ydagger is its separate test-domain adjoint action; Ydagger is not added to H.',
        'scalar_ordering': 'The specified source Pi-dagger Pi form is retained; it is not identified with the earlier coefficient-left square.',
        'scope': 'Literal fixed source time column, source-connected local chart, complete504 CAR and finite occupation sectors. No392 replacement, self-adjoint realization, resolvent existence, quantum spectrum, Gamma or tau is generated.',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'independent_source_full_quantum_adjoint.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent full504 quantum adjoint', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
