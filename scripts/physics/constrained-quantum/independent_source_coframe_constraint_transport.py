#!/usr/bin/env python3
"""Independent full12 linear Euler reconstruction and Noether transport audit.

Neither the candidate projector formula nor its derivative is imported.
Metric lifts, spatial Euler rows and all four coordinate derivatives are
solved by their defining linear systems, including their dual-number curves.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_lorentz_contact import HERE, BASE, ROOT, ROOT_ID, GENERATORS
from independent_source_gauge_legendre import bindings, clean, decode, ETA
from independent_source_joint_temporal_rates import encode, eq, zero


TIME = [0, 4, 8, 12]
SPATIAL = [j for j in range(16) if j not in TIME]
PAIRS = ((0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (1, 2))


def symmetric(column):
    result = s.zeros(3)
    for value, (i, j) in zip(column, PAIRS): result[i, j] = result[j, i] = value
    return result


def solve_unique(matrix, rhs):
    solution, free = matrix.gauss_jordan_solve(rhs)
    assert free.rows == 0
    return clean(solution)


def original_system(e):
    # e^T eta delta(e_sp) has temporal row0 and spatial symmetric block/2.
    # Solve this full12 equation instead of writing down the inverse lift.
    lift_matrix = s.kronecker_product(e.T*ETA, s.eye(3))
    lift_rhs = s.zeros(12, 6)
    for a in range(6):
        value = s.zeros(4, 3); value[1:, :] = symmetric(s.eye(6)[:, a])/2
        lift_rhs[:, a] = value.reshape(12, 1)
    R = solve_unique(lift_matrix, lift_rhs)
    Z = s.Matrix.hstack(*((T*e).reshape(16, 1) for T in GENERATORS))
    Zs, Zt = Z[SPATIAL, :], Z[TIME, :]
    matrix = R.T.col_join(Zs.T)
    rhs = s.zeros(6, 4).col_join(-Zt.T)
    spatial = solve_unique(matrix, rhs)
    whole = s.zeros(16, 4)
    for a in range(4): whole[4*a, a] = 1
    for row, index in enumerate(SPATIAL): whole[index, :] = spatial[row, :]
    return {'lift_matrix': lift_matrix, 'lift_rhs': lift_rhs, 'R': R, 'Z': Z,
        'matrix': matrix, 'rhs': rhs, 'spatial': spatial, 'whole': whole}


def original_dual_number(e, direction, data):
    d_lift = s.kronecker_product(direction.T*ETA, s.eye(3))
    dR = solve_unique(data['lift_matrix'], -d_lift*data['R'])
    dZ = s.Matrix.hstack(*((T*direction).reshape(16, 1) for T in GENERATORS))
    dmatrix = dR.T.col_join(dZ[SPATIAL, :].T)
    drhs = s.zeros(6, 4).col_join(-dZ[TIME, :].T)
    dK = solve_unique(data['matrix'], drhs-dmatrix*data['spatial'])
    # Exact epsilon0 and epsilon1 coefficients of both original systems.
    eq(data['lift_matrix']*data['R'], data['lift_rhs'])
    eq(d_lift*data['R']+data['lift_matrix']*dR, s.zeros(12, 6))
    eq(data['matrix']*data['spatial'], data['rhs'])
    eq(dmatrix*data['spatial']+data['matrix']*dK, drhs)
    whole = s.zeros(16, 4)
    for row, index in enumerate(SPATIAL): whole[index, :] = dK[row, :]
    return whole


def raw_Noether_coefficients(e, de):
    data = original_system(e)
    variations = [original_dual_number(e, direction, data) for direction in de]
    F = s.Matrix(s.symbols('constraint0:4', real=True))
    dF = [s.Matrix(s.symbols('derivative'+str(mu)+'_0:4', real=True)) for mu in range(4)]
    E = (data['whole']*F).reshape(4, 4)
    dE = [(variations[mu]*F+data['whole']*dF[mu]).reshape(4, 4) for mu in range(4)]
    # Direct coordinate Noether expression before collecting any PDE terms.
    residual = s.Matrix([sum(E[a, mu]*de[nu][a, mu]-dE[mu][a, mu]*e[a, nu]-E[a, mu]*de[mu][a, nu]
        for a in range(4) for mu in range(4)) for nu in range(4)])
    time = clean(-residual.jacobian(list(dF[0])))
    spatial = [clean(-residual.jacobian(list(dF[i]))) for i in range(1, 4)]
    lower = clean(-residual.jacobian(list(F)))
    eq(time, e.T)
    eq(residual+time*dF[0]+sum((spatial[i]*dF[i+1] for i in range(3)), s.zeros(4, 1))+lower*F, s.zeros(4, 1))
    eq(data['R'].T*data['spatial'], s.zeros(6, 4))
    eq(data['Z'][SPATIAL, :].T*data['spatial'], -data['Z'][TIME, :].T)
    return data, time, spatial, lower


def generic_rank_proof():
    e = s.Matrix(4, 4, s.symbols('generic_coframe0:16', real=True))
    spatial = e[:, 1:]; h = spatial.T*ETA*spatial
    n = ETA*e.adjugate().T[:, 0]
    # This is an actual source normal, not a hypothesized extra vector.
    eq(spatial.T*ETA*n, s.zeros(3, 1))
    zero((n.T*ETA*n)[0]+h.det())
    for T in GENERATORS: eq(T.T*ETA+ETA*T, s.zeros(4))
    assert s.Matrix.hstack(*(T.reshape(16, 1) for T in GENERATORS)).rank() == 6
    # The polynomial metric identities use a cofactor lift to avoid any
    # specialization or generic inverse accepted without a nonzero guard.
    packed_h = s.Matrix([h[i, j] for i, j in PAIRS])
    D = packed_h.jacobian(list(e))
    columns = []
    for a in range(6):
        variation = s.zeros(4)
        variation[:, 1:] = ETA*e.adjugate().T[:, 1:]*symmetric(s.eye(6)[:, a])/2
        columns.append(variation.reshape(16, 1))
    Rnum = s.Matrix.hstack(*columns)
    Z = s.Matrix.hstack(*((T*e).reshape(16, 1) for T in GENERATORS))
    eq(D*Rnum, e.det()*s.eye(6)); eq(D*Z, s.zeros(6))
    return {'generic_coframe_variables': 16, 'metric_lift_polynomial_identity': True,
        'Lorentz_metric_kernel_polynomial_identity': True,
        'source_normal': 'n=eta adj(e)^T e0; E_sp^T eta n=0 and n^T eta n=-det(h_sp)',
        'uniform_injectivity': 'For det(e)det(h_sp)!=0, a Lorentz-skew map killing the spatial3-plane preserves its orthogonal normal line. Skewness and the computed nonzero normal norm force its action on that line to vanish, hence the map is zero; independence of the original six generators gives rank(Z_sp)=6.',
        'uniform_linear_system': 'D_sp R_sp=I and D_sp Z_sp=0, together with rank(Z_sp)=6, make [R_sp Z_sp] and its12x12 transpose invertible. The metric6 and Spin6 equations uniquely generate K.'}


def main():
    began = time.monotonic(); path = HERE/'source_coframe_constraint_transport.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    generic = generic_rank_proof()
    print('PASS generic cofactor metric lift and uniform six-Lorentz injection on the nondegenerate spatial plane', flush=True)
    active = json.loads((BASE/'active-gauge/receipt.json').read_text()); count += bindings(active)
    source_e = s.Matrix(active['actual_background']['coframe']).applyfunc(s.sympify)
    source, source_time, source_spatial, source_lower = raw_Noether_coefficients(source_e, [s.zeros(4)]*4)
    for i, A in enumerate(source_spatial):
        solved = solve_unique(source_time, -A)
        expected = s.zeros(4); expected[0, i+1] = source_e[0, 0]
        eq(solved, expected)
    eq(source_lower, s.zeros(4))
    assert source['spatial'].todok()
    zero(source_time.det()-s.sympify(candidate['source_time_determinant']))
    e = decode(candidate['actual_coframe'])
    de = [s.Matrix(4, 4, lambda a, mu: s.Rational((3*a+2*mu+nu)%7-3, 41+2*nu)) for nu in range(4)]
    actual, time_matrix, spatial_matrices, lower = raw_Noether_coefficients(e, de)
    eq(time_matrix, decode(candidate['actual_time_matrix']))
    for actual_matrix, saved in zip(spatial_matrices, candidate['actual_spatial_matrices']): eq(actual_matrix, decode(saved))
    eq(lower, decode(candidate['actual_lower_matrix']))
    assert lower.todok() and actual['spatial'].todok()
    print('PASS independent12x12 Euler solves and four exact dual-number derivatives; every F/dF coefficient in original Noether transport matches', flush=True)
    paths = [Path(__file__), path, HERE/'source_coframe_constraint_transport.py',
        HERE/'independent_source_lorentz_contact.py', HERE/'source_spatial_time_coframe.json',
        HERE/'independent_source_spatial_time_coframe.json', BASE/'active-gauge/receipt.json']
    result = {'verdict': 'CERTIFIED_ORIGINAL_SPATIAL_EULER_RECONSTRUCTION_AND_TEMPORAL_CONSTRAINT_PDE',
        'root': ROOT_ID, 'source_sha256': candidate['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks': count, 'candidate_projection_formula_imported': False,
        'independent_algorithm': 'full12 metric-lift equations, full12 metric6/Spin6 Euler solve, differentiated defining linear systems modulo epsilon squared, raw coordinate Noether coefficient extraction',
        'uniform_reconstruction': generic,
        'all4_actual_directional_derivatives_verified': True,
        'all_symbolic_constraint_and_first_derivative_coefficients': True,
        'spatial_Euler_off_constraint_nonzero_retained': True,
        'source_equation': 'partial_t F0=N(partial_1 F1+partial_2 F2+partial_3 F3); partial_t Fi=0 for i=1,2,3',
        'actual_time_matrix': encode(time_matrix), 'actual_lower_matrix': encode(lower),
        'analytic_zero_initial_consumer': {
            'status': 'CERTIFIED_CONDITIONAL_LINEAR_ANALYTIC_CONSTRAINT_PROPAGATION',
            'proof': 'On an already generated analytic first-order field solution in the noncharacteristic source chart, all coefficients K(e), derivatives and B(e,de) are analytic. Inverting e^T yields a first-order linear PDE solved for partial_t F. The zero function solves its zero-data Cauchy problem and analytic Cauchy uniqueness gives F=0 locally.',
            'consumer_order': 'First preserve torsion, scalar gradient, gauge curvature, C9 and Gauss and pay the other original Euler equations. Metric6 plus full Spin6 then reconstruct E_sp=K F without assuming F=0. The separately generated coordinate defect equation divQ=0 yields this homogeneous transport, after which zero initial F is propagated.',
            'time_constraint_zero_assumed_to_derive_spatial_Euler_zero': False,
            'all_prior_first_order_producers_assumed_assembled_by_this_receipt': False},
        'complete_spatial_Cauchy_solution_or_quantum_measure_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_coframe_constraint_transport.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS independent coframe constraint transport', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
