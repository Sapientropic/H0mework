#!/usr/bin/env python3
"""Independent original-density and canonical-graph audit of the tail splice."""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from independent_source_stabilizer_phase_reduction import RawStabilizerPhase
from independent_source_full_linear_split import build_raw, real_fourier, affine, read_matrix, K, P
from independent_source_joint_temporal_rates import HERE, ROOT, ROOT_ID, bindings, clean, eq, encode
from independent_source_gauss_quantum_current import polynomial_real_action
from independent_source_lorentz_contact import real_bilinear


def rectangular(rows, cols, blocks):
    values = {}
    for row, col, matrix in blocks:
        for (i, j), value in s.SparseMatrix(matrix).todok().items():
            values[row+i, col+j] = values.get((row+i, col+j), 0)+value
    return clean(s.SparseMatrix(rows, cols, values))


def canonical(n):
    return s.SparseMatrix(2*n, 2*n, {**{(i, n+i): 1 for i in range(n)},
                                        **{(n+i, i): -1 for i in range(n)}})


def pairing(M):
    return clean(M.applyfunc(s.re).row_join(-M.applyfunc(s.im)).col_join(
        (-M.applyfunc(s.im)).row_join(-M.applyfunc(s.re))))


def main():
    began = time.monotonic(); file = HERE/'source_physical_phase_splice.json'
    candidate = json.loads(file.read_text()); checks = bindings(candidate)
    graph = RawStabilizerPhase(); raw = graph.raw; source = build_raw(raw)
    assert candidate['root'] == ROOT_ID and candidate['source_sha256'] == raw.hashes
    q, mom = graph.source_pair(); V = clean(s.Matrix.hstack(*(T*q for T in graph.generators)))
    Fq = clean(s.Matrix.vstack(*((T.T*mom).T for T in graph.generators)))
    gauge_positions = graph.coordinates
    free = [j for j in range(607) if j not in gauge_positions]
    If, Ip = s.SparseMatrix.eye(607)[:, free], s.SparseMatrix.eye(607)[:, gauge_positions]
    minor = clean(Ip.T*V)
    # Solve the actual linearized Gauss equations, preserving every original
    # remaining momentum and position; do not read the proposed graph map.
    dependent, parameters = minor.T.gauss_jordan_solve(-Fq*If)
    assert not parameters.rows
    response, parameters = minor.T.gauss_jordan_solve(-V.T*If)
    assert not parameters.rows
    T = rectangular(1214, 1208, [(0, 0, If), (607, 0, Ip*dependent),
                                    (607, 604, If+Ip*response)])
    reader = rectangular(1208, 1214, [(0, 0, If.T), (604, 607, If.T)])
    eq(reader*T, s.eye(1208)); eq(Fq*T[:607, :]+V.T*T[607:, :], s.zeros(3, 1208))
    J = canonical(607); eq(T.T*J*T, canonical(604))
    eq(T, read_matrix(candidate['original_nonlinear_chart_tangent']))
    E, C, O, N = source['principal'][0], source['C'], source['O'], source['N']
    EC = clean(C.T*E*C)
    # p=-i chi E; pi_real=(-Im p,-Re p). Differentiate this literal map
    # entrywise, keeping the two independent chi components independent.
    Pcomplex = clean(-s.I*EC.T)
    S = rectangular(480, 480, [(0, 0, -Pcomplex.applyfunc(s.im)),
        (0, 240, -Pcomplex.applyfunc(s.re)), (240, 0, -Pcomplex.applyfunc(s.re)),
        (240, 240, Pcomplex.applyfunc(s.im))])
    Si = S.inv(); eq(S*Si, s.eye(480)); eq(Si*S, s.eye(480))
    Cr = rectangular(504, 480, [(0, 0, C), (252, 240, C)])
    X = rectangular(1214, 1082, [(6, 480, s.eye(61)), (613, 541, s.eye(61)),
        (103, 602, Cr), (710, 0, Cr*S)])
    L = rectangular(1082, 1214, [(480, 6, s.eye(61)), (541, 613, s.eye(61)),
        (602, 103, Cr.T), (0, 710, Si*Cr.T)])
    x, r = clean(reader*X), clean(L*T)
    eq(r*x, s.eye(1082)); eq(T*x, X)
    eq(x, read_matrix(candidate['tail_embedding_into_actual1208']))
    eq(r, read_matrix(candidate['tail_reader_from_actual1208']))
    Omega = clean(-X.T*J*X)
    eq(Omega, read_matrix(candidate['tail_original_symplectic_form']))
    eq(mom.T*X[:607, :], s.zeros(1, 1082))
    eq(Fq*X[:607, :]+V.T*X[607:, :], s.zeros(3, 1082))
    print('PASS raw607-pair constraint differential, independent dual canonical momentum and actual1082 symplectic embedding', flush=True)

    # Hamiltonian scalar density before reading any time generator: original
    # Pi_phi=-dot(phi)/N, H=-N Pi_phi^2/2-N sum(D_i phi)^2/2+N phi^2.
    R, Rd = graph.R, graph.Rd
    gram = clean(R.T*R)
    connection70 = [raw.action(raw.A[i+1, :], raw.rho70) for i in range(3)]
    Qqq = 2*N*gram
    for k, A in zip(K, connection70):
        Lk = (s.I*k*s.eye(70)+A)*R
        Qqq -= N*Lk.subs(dict(zip(K, [-v for v in K])), simultaneous=True).T*Lk
    Qqq = clean(Qqq)
    Hs = rectangular(122, 122, [(0, 0, Qqq), (61, 61, -N*gram.inv())])
    As = rectangular(122, 122, [(0, 61, -N*gram.inv()), (61, 0, -Qqq)])
    KC = clean(C.T*source['D'].subs(dict.fromkeys(P, 0))*C)
    Ei = [clean(C.T*matrix*C) for matrix in source['principal'][1:]]
    B70 = clean(s.Matrix.hstack(*(N*C.T*Y*raw.psi0 for Y in raw.Y)))
    B61 = clean(B70*R)
    Jchi = clean(B61.T.applyfunc(s.re).row_join(-B61.T.applyfunc(s.im)))
    matter_pair = clean(pairing(KC)+sum((s.I*k*pairing(M) for k, M in zip(K, Ei)), s.zeros(480)))
    star = lambda M: clean(M.subs(dict(zip(K, [-k for k in K])), simultaneous=True).T)
    H = rectangular(1082, 1082, [(480, 480, Hs), (0, 602, -matter_pair),
        (602, 0, -star(matter_pair)), (0, 480, -Jchi.T), (480, 0, -Jchi)])
    inverseE = EC.inv()
    Ap = real_fourier([clean(-inverseE*KC), *[clean(-inverseE*M) for M in Ei]])
    Ad = real_fourier([clean((KC*inverseE).T), *[clean(-(M*inverseE).T) for M in Ei]])
    complex_force = clean(-inverseE*B61)
    eq(EC*complex_force+B61, s.zeros(240, 61))
    # These are61 real scalar directions, not a complex61 field to double.
    Cforce = clean(complex_force.applyfunc(s.re).col_join(complex_force.applyfunc(s.im)))
    A = rectangular(1082, 1082, [(0, 0, Ad), (480, 480, As), (602, 602, Ap),
                                  (541, 0, Jchi), (602, 480, Cforce)])
    eq(Omega*A, H); eq(star(H), H); eq(star(A)*Omega+Omega*A, s.zeros(1082))
    eq(H, read_matrix(candidate['original_tail_Hamiltonian']['original_density_Hamiltonian_hessian']))
    assert Jchi.todok()
    print('PASS original scalar momentum density, full independent Dirac equations and nonzero Yukawa cross give Omega A=H at all three momenta', flush=True)

    checked = 0
    for kind, _, M in source['vertices']:
        if kind == 'scalar':
            eq(raw.chi0*M*raw.psi0, s.zeros(1))
        else:
            for coefficient in affine(M):
                eq(C.T*coefficient*raw.psi0, s.zeros(240, 1))
                eq(raw.chi0*coefficient*C, s.zeros(1, 240)); checked += 1
    for rho in raw.rho70:
        # Normal scalar sources cannot enter the peripheral tangent Gauss
        # momentum, including its full incoming/transfer spatial symbols.
        eq(R.T*rho*raw.v, s.zeros(61, 1))
    for A70 in [raw.action(raw.A[mu, :], raw.rho70) for mu in range(4)]:
        eq(A70*raw.v, s.zeros(70, 1))
        eq(A70*raw.P61, raw.P61*A70)
    eq(X[67:103, :], s.zeros(36, 1082)); eq(X[674:710, :], s.zeros(36, 1082))
    for k in K:
        eq(k*X[674:710, :], s.zeros(36, 1082))
    frequency, Q = source['frequency'], source['phase']
    Rp = clean(-C.T*Q*C)
    Rdphase = clean(C.T*E*Q*E.inv()*C)
    phi = rectangular(1082, 1082, [(0, 0, polynomial_real_action(s.I*frequency*Rdphase.T)),
                                    (602, 602, polynomial_real_action(s.I*frequency*Rp))])
    eq(phi, read_matrix(candidate['original_tail_Hamiltonian']['phase_generator']))
    eq(phi.T*Omega+Omega*phi, s.zeros(1082))
    Koriginal = clean(KC+s.I*frequency*EC*(C.T*Q*C))
    delta_pair = pairing(Koriginal-KC)
    delta_H = rectangular(1082, 1082, [(0, 602, -delta_pair), (602, 0, -delta_pair.T)])
    eq(delta_H, Omega*phi)
    original = candidate['actual_response_consumer']
    column = original['input_dual_coordinate']
    seed = s.SparseMatrix(1082, 1, {(column, 0): 1})
    A0 = clean(A.subs(dict.fromkeys(K, 0)))
    second = clean(A0*(A0*seed)); third = clean(A0*second)
    eq(second[602:, :], s.zeros(480, 1)); assert third[602:, :].todok()
    eq(third[602:, :], read_matrix(original['third_time_primal']))
    eq(x*third, read_matrix(original['third_time_actual1208_chart']))
    eq(r*(x*third), third)
    print('PASS original full constraints, canonical phase shift and true nonzero retarded cascade in the actual physical chart', flush=True)
    paths = [file, HERE/'source_physical_phase_splice.py', HERE/'independent_source_physical_phase_splice.py',
        HERE/'independent_source_stabilizer_phase_reduction.py', HERE/'independent_source_full_linear_split.py',
        HERE/'independent_source_joint_temporal_rates.py', HERE/'independent_source_full_linear_retarded.json',
        HERE/'independent_source_temporal_dirac_reduction.json']
    out = {'root': ROOT_ID, 'source_sha256': raw.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'verdict': 'CERTIFIED_ACTUAL1082_TAIL_SYMPLECTIC_SPLICE_IN_SOURCE1208_PHASE',
        'candidate_constructor_imported': False, 'source_binding_checks': checks,
        'independent_method': 'raw exterior/native moment maps; direct linearized Gauss solve; literal p=-i chi E real component derivatives; original scalar Legendre and repaired Dirac-dual density before generator comparison',
        'actual_chart': {'phase_dimension': 1208, 'tail_dimension': 1082,
            'original_linearized_constraints_and_canonical_graph': True,
            'tail_embedding_reader_both_source_maps_checked': True,
            'original_one_form_and_nondegenerate_symplectic_pullback': True,
            'independent_dual_replaced_by_Hilbert_adjoint': False},
        'original_Hamiltonian': {'all_three_momentum_symbols_retained': True,
            'scalar_kinetic_sign_from_original_Pi': True, 'scalar_dual_coupling_nonzero': True,
            'Omega_A_equals_original_density_Hessian': True, 'formal_Fourier_adjoint_H_minus_k_transpose': True,
            'source_Noether_phase_shift_retained': True},
        'original_constraint_tangent': {'non_scalar_original_coefficients_checked': checked,
            'full_Gauss_spatial_divergence_zero': True,
            'time_and_Spin_restrictions_zero_from_original_vertex_and_background_coefficients': True},
        'actual_nonzero_time_consumer': {'third_time_primal': encode(third[602:, :]), 'original1208_chart_round_trip': True},
        'active126_complete_splice_claimed': False,
        'interacting_quantum_spectral_measure_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_physical_phase_splice.json').write_text(json.dumps(out, separators=(',', ':'))+'\n')
    print('PASS independent source physical tail splice', out['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
