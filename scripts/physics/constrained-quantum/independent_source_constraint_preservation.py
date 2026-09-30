#!/usr/bin/env python3
"""Independent source Noether and time-connection constraint audit.

The next A0 rate is solved directly from the original scalar Euler equation
for phi_ddot, not by reproducing the candidate's differentiated-rhs routine.
"""
from __future__ import annotations

import hashlib
import itertools
from pathlib import Path
import time

import sympy as s

from independent_source_gauge_legendre import (
    HERE, BASE, ROOT, ROOT_ID, ETA, PAIRS, SIGMA, W, source,
    bindings, clean, decode, dot, encode, equal, exterior, hodge,
    matrix_coordinates, read, read_gamma, realify, zero)


def wedge_yukawa(word):
    two = list(itertools.combinations(range(7), 2))
    six = list(itertools.combinations(range(7), 6))
    rows = {value: i for i, value in enumerate(six)}
    result = s.MutableSparseMatrix.zeros(7, 21)
    for column, pair in enumerate(two):
        if set(word) & set(pair): continue
        sign = (-1)**sum(i > j for i in word for j in pair)
        result[rows[tuple(sorted((*word, *pair)))], column] = sign
    return s.SparseMatrix(result)


def main():
    began = time.monotonic()
    path = HERE/'source_constraint_preservation.json'
    candidate = read(path)
    assert candidate['root'] == ROOT_ID
    count = bindings(candidate)
    _, vacuum, degrees, hashes = source.parse_source(ROOT)
    assert hashes == candidate['source_sha256']
    raw = source.generators([(0, 1, 2), (3, 4)])
    fundamental = [s.Matrix(M)*(s.I if imaginary else 1) for _, imaginary, M in raw]
    rho = [realify(exterior(T, 4)) for T in fundamental]
    internal = [clean(s.diag(*(exterior(T, degree) for degree in degrees))) for T in fundamental]
    matter_rho = [clean(s.kronecker_product(s.SparseMatrix.eye(4), T)) for T in internal]
    words = list(itertools.combinations(range(7), 4))
    v = s.Matrix([vacuum.get(word, 0) for word in words]+[0]*35)
    O = clean(s.Matrix.hstack(*(R*v for R in rho)))
    torque = candidate['source_potential_torque']
    equal(v, decode(torque['vacuum']))
    equal(O, decode(torque['orbit']))
    assert O.rank() == 9
    broken = list(O.rref()[1])
    S = s.eye(12)[:, broken]
    U = O*S
    stabilizer = clean(s.Matrix.hstack(*O.nullspace()))
    P = clean(s.eye(70)-U*(U.T*U).inv()*U.T)
    equal(stabilizer, decode(torque['fixed_source_stabilizer']))
    equal(P, decode(torque['scalar_constraint_projector']))
    equal(O.T*P, s.zeros(12, 70)); equal(P*P, P)
    assert P.rank() == 61 and broken == torque['broken_parameter_columns']
    scalar_receipt_path = BASE/'scalar-exchange/receipt.json'
    equal(P, decode(read(scalar_receipt_path)['peripheral_projector']))

    def D(phi): return clean(O.T*s.Matrix.hstack(*(R*phi for R in rho)))
    def action(A): return clean(sum((a*R for a, R in zip(A, rho)), s.zeros(70)))

    constants = {}
    for a, b in itertools.product(range(12), repeat=2):
        coeff = matrix_coordinates(fundamental[a]*fundamental[b]-fundamental[b]*fundamental[a])
        for c, value in enumerate(coeff):
            if value: constants[a, b, c] = value
        equal(rho[a]*rho[b]-rho[b]*rho[a], sum((coeff[c]*rho[c] for c in range(12)), s.zeros(70)))
    phi_symbol = s.Matrix(s.symbols('phi0:70', real=True))
    C = O.T*phi_symbol
    generic_D = D(phi_symbol)
    for a, R in enumerate(rho):
        equal(R.T, -R)
        zero(-2*dot(phi_symbol-v, R*phi_symbol)+2*C[a])
        for b in range(12):
            zero(generic_D[a, b]-generic_D[b, a]-sum(constants.get((a, b, c), 0)*C[c] for c in range(12)))
    equal(stabilizer.T*generic_D, s.zeros(3, 12))

    active_path = BASE/'active-gauge/receipt.json'; active = read(active_path)
    N = s.sympify(active['source_lapse'])
    original_Ward = s.SparseMatrix(9, 12, {(i, j): s.sympify(value) for i, j, powers, value in active['H_p_times_T_p']})
    equal(-2*N*U.T*O, original_Ward)
    inverse_Ward = s.Matrix(active['Ward_constraint_elimination']['scalar_constraint_inverse']).applyfunc(s.sympify)
    equal((-2*N*U.T*U)*inverse_Ward, s.eye(9))
    print('PASS raw source potential torque, complete rank9 constraints, original P61 and actual Ward9 identity', flush=True)

    # Rebuild the whole repaired operator, without extracting a supposedly
    # representative block from an already supplied full252 matrix.
    projector = (s.eye(4)+s.diag(-1, -1, 1, 1))/2
    Y = []
    for word in words:
        small = s.MutableSparseMatrix.zeros(63, 63)
        small[:7, 7:28] = wedge_yukawa(word)
        Y.append(clean(s.kronecker_product(projector, small)))
    Y += [s.I*matrix for matrix in Y.copy()]
    assert len(Y) == 70
    checked = 0
    for a in range(12):
        for b in range(70):
            variation = sum((value*Y[c] for (c, column), value in rho[a].todok().items() if column == b), s.zeros(252))
            equal(variation, matter_rho[a]*Y[b]-Y[b]*matter_rho[a])
            checked += 1
    assert checked == 840
    gamma = read_gamma()
    for R in matter_rho:
        for G in gamma:
            spin = s.kronecker_product(G, s.SparseMatrix.eye(63))
            equal(R*spin, spin*R)
    source_gauge = read(HERE/'source_gauge_legendre.json')
    Gnative = decode(source_gauge['native_Lie_algebra']['native_Lie_Gram'])
    ad = [s.Matrix(12, 12, lambda c, b: constants.get((a, b, c), 0)) for a in range(12)]
    for matrix in ad: equal(matrix.T*Gnative+Gnative*matrix, s.zeros(12))
    print('PASS all840 full252 repaired Yukawa covariance matrices, scalar representation and original kinetic/Lie Noether cancellations', flush=True)

    consumer = candidate['actual_time_connection_consumer']
    phi = decode(consumer['live_phi']); Pi = decode(consumer['live_scalar_momentum'])
    spatial_phi = [decode(value) for value in consumer['live_spatial_scalar_jet']]
    equal(phi, v+P*s.Matrix([s.Rational((i*2)%9-4, 101) for i in range(70)]))
    equal(Pi, s.Matrix([s.Rational((i*3)%11-5, 37) for i in range(70)]))
    equal(O.T*phi, s.zeros(12, 1))
    live_D = D(phi)
    equal(live_D, live_D.T)
    equal(live_D, decode(consumer['live_consistency_matrix']))
    equal(D(v), O.T*O)
    assert live_D.rank() == 9
    assert s.factor((S.T*live_D*S).det()) == s.sympify(consumer['live_broken_matrix_determinant'])
    equal(live_D*stabilizer, s.zeros(12, 3))
    assert S.row_join(stabilizer).det() != 0
    e = s.Matrix(active['actual_background']['coframe']).applyfunc(s.sympify)
    h = s.Abs(e.det())*(e.T*ETA*e).inv()
    equal(h, s.diag(-1/N, N, N, N))
    connection = s.Matrix(active['actual_background']['gauge_connection']).applyfunc(s.sympify)

    def solve_full(rhs):
        solution, free = (live_D*S).gauss_jordan_solve(rhs)
        assert free.rows == 0
        value = clean(S*solution)
        equal(live_D*value, rhs)
        return value

    a0 = solve_full(O.T*Pi/h[0, 0])
    residual = s.Matrix(s.symbols('residual0:3', real=True))
    saved_a0 = decode(consumer['generated_time_connection'], {str(x): x for x in residual})
    equal(saved_a0, a0+stabilizer*residual)
    equal(O.T*(Pi/h[0, 0]-action(saved_a0)*phi), s.zeros(12, 1))
    connection[0, :] = a0.T
    spatial_pi = [s.Matrix([s.Rational((i+3*j)%13-6, 47) for i in range(70)]) for j in range(3)]
    second_phi = [[P*s.Matrix([s.Rational((i+j+k)%5-2, 53) for i in range(70)]) for k in range(3)] for j in range(3)]
    spatial_A = s.Matrix(3, 48, lambda i, j: s.Rational((2*i+j)%7-3, 59))
    for i in range(3):
        spatial_A[i, :12] = solve_full(O.T*spatial_pi[i]/h[0, 0]-D(spatial_phi[i])*a0).T
    velocity = clean(Pi/h[0, 0]-action(a0)*phi)
    velocity_spatial = [clean(spatial_pi[i]/h[0, 0]-action(spatial_A[i, :12])*phi-
        action(a0)*spatial_phi[i]) for i in range(3)]
    equal(O.T*velocity, s.zeros(12, 1))
    for vector in velocity_spatial: equal(O.T*vector, s.zeros(12, 1))
    dropped_rhs = O.T*Pi/h[0, 0]
    equal(D(s.zeros(70, 1)), s.zeros(12))
    equal(dropped_rhs, decode(consumer['rank_drop_retained_rhs']))
    assert dropped_rhs != s.zeros(12, 1)
    print('PASS full12-row A0 solve with all3 residual parameters, differentiated spatial constraints and nonempty rank-drop compatibility', flush=True)

    next_state = candidate['actual_next_consistency_update']
    occupied_path = BASE/'occupied-response/receipt.json'; occupied = read(occupied_path)
    old_psi = decode(occupied['occupied_frame'])*s.Matrix(active['actual_background']['primal_H']).applyfunc(s.sympify)
    old_chi = s.sympify(active['actual_background']['dual_multiple'])*old_psi.T
    psi, chi = old_psi.copy(), old_chi.copy()
    psi[135] += 1; chi[126] += 1
    equal(psi, decode(next_state['live_full252_primal']))
    equal(chi, decode(next_state['live_independent_full252_dual']))
    jY = s.Matrix([s.expand(N*s.re((chi*matrix*psi)[0])) for matrix in Y])
    old_jY = s.Matrix([s.expand(N*s.re((old_chi*matrix*old_psi)[0])) for matrix in Y])
    equal(old_jY, s.zeros(70, 1)); equal(old_jY, decode(next_state['original_prepared_Yukawa_source']))
    equal(jY, decode(next_state['actual_full_Yukawa_scalar_source']))
    equal(O.T*jY, decode(next_state['actual_broken_orbit_Yukawa_source']))
    assert dict(clean(jY).todok()) == {(10, 0): -N, (23, 0): N}
    assert dict(clean(O.T*jY).todok()) == {(2, 0): N}

    def bracket(A, B):
        return s.Matrix([sum(constants.get((a, b, c), 0)*A[a]*B[b] for a in range(12) for b in range(12)) for c in range(12)])

    gauge_Pi = s.Matrix(3, 12, lambda i, j: s.Rational((i+j*3)%11-5, 61))
    gauge_Q = clean(-W*hodge(e)/SIGMA)
    gauge_rate = clean(gauge_Q[:3, :3].inv()*gauge_Pi*Gnative.inv()+s.Matrix.vstack(*(
        spatial_A[i, :12]+bracket(connection[i+1, :], a0).T for i in range(3))))
    equal(gauge_rate, decode(next_state['source_generated_gauge_velocity']))
    connection_actions = [action(connection[mu, :]) for mu in range(4)]
    first = [velocity, *spatial_phi]
    covariant = [first[mu]+connection_actions[mu]*phi for mu in range(4)]
    scalar_momenta = [sum((h[mu, nu]*covariant[nu] for nu in range(4)), s.zeros(70, 1)) for mu in range(4)]
    equal(scalar_momenta[0], Pi)

    def raw_acceleration(time_connection_rate, source_force):
        dconnection = [s.Matrix.vstack(time_connection_rate.T, gauge_rate).reshape(1, 48),
                       *[spatial_A[i, :] for i in range(3)]]
        second = [[s.zeros(70, 1), *velocity_spatial]]
        second += [[velocity_spatial[i], *second_phi[i]] for i in range(3)]
        raw_divergence = s.zeros(70, 1)
        for mu, nu in itertools.product(range(4), repeat=2):
            derivative_covariant = (second[mu][nu]+action(dconnection[mu][0, 12*nu:12*(nu+1)])*phi+
                                    connection_actions[nu]*first[mu])
            raw_divergence += h[mu, nu]*derivative_covariant
        raw_divergence += sum((connection_actions[mu]*scalar_momenta[mu] for mu in range(4)), s.zeros(70, 1))
        # The only omitted second jet is phi_00; its Euler coefficient is -h00.
        return clean((-raw_divergence-2*N*(phi-v)+source_force)/h[0, 0])

    unsolved_acceleration = raw_acceleration(s.zeros(12, 1), jY)
    a0_rate = solve_full(O.T*unsolved_acceleration)
    equal(a0_rate, decode(next_state['generated_time_connection_rate']))
    acceleration = raw_acceleration(a0_rate, jY)
    equal(O.T*acceleration, s.zeros(12, 1))
    Pi_rate = clean(h[0, 0]*(acceleration+action(a0_rate)*phi+action(a0)*velocity))
    equal(velocity, decode(next_state['source_generated_scalar_velocity']))
    equal(Pi_rate, decode(next_state['source_generated_scalar_momentum_rate']))
    rhs_rate = clean(O.T*Pi_rate/h[0, 0])
    equal(rhs_rate, decode(next_state['generated_consistency_rhs_rate']))
    equal(live_D*a0_rate+D(velocity)*a0, rhs_rate)
    baseline_a0_rate = solve_full(O.T*raw_acceleration(s.zeros(12, 1), old_jY))
    delta_rate = clean(a0_rate-baseline_a0_rate)
    equal(delta_rate, decode(next_state['nonzero_Yukawa_induced_A0_rate_change']))
    force_rhs = clean(O.T*(jY-old_jY)/h[0, 0])
    equal(force_rhs, decode(next_state['nonzero_Yukawa_induced_rhs_rate_change']))
    equal(live_D*delta_rate, force_rhs)
    assert dict(force_rhs.todok()) == {(2, 0): -s.Rational(54, 125)}
    assert len(delta_rate.todok()) == 9

    scalar_charge = s.Matrix([dot(Pi, R*phi) for R in rho])
    E4 = s.Abs(e.det())*sum((e.inv()[0, a]*s.I*gamma[a] for a in range(4)), s.zeros(4))
    matter_charge = s.Matrix([s.re((chi*s.kronecker_product(E4, R)*psi)[0]).expand() for R in internal])
    spatial_gauge_Pi = [decode(value) for value in next_state['compatible_spatial_gauge_momentum_jet']]
    gauss = sum((spatial_gauge_Pi[i][i, :].T-sum((connection[i+1, a]*ad[a].T*gauge_Pi[i, :].T for a in range(12)), s.zeros(12, 1))
                 for i in range(3)), s.zeros(12, 1))+scalar_charge+matter_charge
    equal(gauss, s.zeros(12, 1))
    gauss_rate = sum((a0[a]*ad[a].T*gauss for a in range(12)), s.zeros(12, 1))-2*N*O.T*phi
    equal(gauss_rate, s.zeros(12, 1))
    print('PASS raw original scalar Euler generates phi_ddot with zero torque projection, the exact nonzero Yukawa-driven A0 rate and actual total Gauss0', flush=True)

    count += bindings(active)+bindings(occupied)+bindings(source_gauge)
    paths = [path, HERE/'source_constraint_preservation.py', Path(__file__),
        HERE/'independent_source_gauge_legendre.py', HERE/'independent_source_gauge_legendre.json',
        BASE/'exact_readout.py', active_path, occupied_path, scalar_receipt_path]
    paths += [ROOT/'Lean/SaturationMonoid/PhysicsCore'/name for name in
        ['DiracCliffordRepresentation.lean', 'StageNineDiracDualYukawaSpinJurisdiction.lean',
         'StageNineHolonomicField.lean', 'StageNineDynamicBreakingVacuum.lean']]
    result = {'verdict': 'CERTIFIED_SOURCE_NOETHER_GAUSS_TORQUE_AND_GENERATED_TIME_CONNECTION_RATE',
        'root': ROOT_ID, 'source_sha256': hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'candidate_constructor_or_rate_algorithm_imported': False,
        'independent_algorithm': 'indexed wedge full252 Yukawa reconstruction; full840 matrix identities; raw potential gradient; all12-row Gauss-Jordan consistency solve; original scalar Euler solution for phi_ddot rather than differentiated canonical rhs; raw full252/full70 Gauss currents',
        'source_binding_checks': count, 'constraint_rank': 9, 'peripheral_rank': 61,
        'potential_torque': '-2 abs(det e) O^T phi for the fixed actual source vacuum',
        'all840_full252_Yukawa_covariance_matrices': True,
        'all144_scalar_representation_brackets': True,
        'source_Noether_derivation': 'original gauge pairing invariance, scalar skew representation and symmetric spacetime coefficients, full Dirac principal/internal commutation, all840 repaired Yukawa covariance and independent-dual cancellation leave exactly the fixed-source potential torque after integration by parts',
        'Gauss_rate_domain': 'after the original spatial connection, scalar and both independent matter Euler equations are consumed',
        'Gauss_rate': 'dotG-ad(A0)^T G=-2 abs(det e) C',
        'D_symmetry_domain': 'D-D^T=f*C, so D is symmetric on C=0',
        'original_Ward9_and_P61_consumed': True,
        'all3_residual_A0_parameters_retained': True,
        'rank_drop_control': 'phi=0 gives D=0 with a nonzero retained rhs; no inverse or consistent time connection is assigned',
        'actual_nonzero_Yukawa_fixture': {'primal': 'original psi+unit135', 'independent_dual': 'original chi+unit126',
            'scalar_force': {'10': '-N', '23': 'N'}, 'active_force': {'2': 'N'},
            'rhs_rate_change': {'2': '-54/125'}, 'A0_rate_change_nonzero_entries': 9,
            'original_prepared_force_zero_preserved': True},
        'actual_source_dynamics_consumer': {'raw_phi_ddot_torque_projection_zero': True,
            'scalar_momentum_rate_recovered_from_raw_Euler': True,
            'original_gauge_velocity_rebuilt': True, 'all12_differentiated_A0_equations': True,
            'compatible_spatial_A0_jets_checked': True, 'original_total_Gauss_and_Noether_rate_zero': True,
            'scope': 'the frozen local canonical jet at the original source coframe, with full70 scalar and independent full252 matter; no global Cauchy trajectory is inferred'},
        'all12_gauge_directions_or_remaining3_declared_first_class': False,
        'coframe_secondary_constraint_chain_or_full_joint_Cauchy_claimed': False,
        'new_source_occurrence': False, 'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    import json
    (HERE/'independent_source_constraint_preservation.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS independent source constraint preservation audit', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
