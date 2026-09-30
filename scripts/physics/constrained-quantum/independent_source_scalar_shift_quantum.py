#!/usr/bin/env python3
"""Independent complete scalar shifted square on the live Gauss graph.

All97 partial derivatives are assembled from raw scalar/gauge representations.
The original70 momentum squares are composed as differential operators, then
acted on the actual compact-support wavepacket jet and two-branch exterior CAR.
"""
from __future__ import annotations

import hashlib
import itertools
import json
from pathlib import Path
import time
import sympy as s

from independent_source_gauge_legendre import (
    HERE, BASE, ROOT, ROOT_ID, ETA, source, bindings, clean, decode,
    matrix_coordinates, read)
from independent_source_joint_temporal_rates import encode, eq, zero, dot
from independent_source_gauss_quantum_current import (
    exterior_bits, polynomial_real_action, apply_state, add_terms, decoded_state)


def encode_vector(vector): return [[list(state), str(value)] for state, value in sorted(vector.items())]


def compare_state(actual, record):
    assert add_terms([(1, actual), (-1, decoded_state(record))]) == {}


def main():
    began = time.monotonic(); path = HERE/'source_scalar_shift_quantum.json'
    candidate = read(path); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    _, vacuum, degrees, hashes = source.parse_source(ROOT)
    assert candidate['source_sha256'] == hashes
    fundamental = [s.SparseMatrix(M)*(s.I if imaginary else 1) for _, imaginary, M in source.generators([(0, 1, 2), (3, 4)])]
    rho70 = [polynomial_real_action(exterior_bits(T, 4)) for T in fundamental]
    rho252 = [clean(s.kronecker_product(s.eye(4), s.diag(*(exterior_bits(T, degree) for degree in degrees)))) for T in fundamental]
    adjoint = [s.Matrix.hstack(*(matrix_coordinates(T*S-S*T) for S in fundamental)) for T in fundamental]
    v = s.Matrix([vacuum.get(word, 0) for word in itertools.combinations(range(7), 4)]+[0]*35)
    orbit = clean(s.Matrix.hstack(*(rho*v for rho in rho70)))
    broken = list(orbit.rref()[1]); select = s.eye(12)[:, broken]; O = orbit*select
    Gram = clean(O.T*O); P = clean(s.eye(70)-O*Gram.inv()*O.T)
    R = P[:, list(P.rref()[1])]; Rdual = clean(R*(R.T*R).inv())
    eq(Rdual.T*O, s.zeros(61, 9)); eq(Rdual.T*R, s.eye(61))
    Q = [clean(s.diag(s.I*rho252[a], s.I*rho252[a].conjugate())) for a in broken]
    T = [clean(s.diag(Rdual.T*rho70[a]*R, *[adjoint[a]]*3)) for a in broken]
    for rho in rho70:
        zero(s.trace(Rdual.T*rho*R))
    e, x, A = decode(candidate['actual_coframe']), decode(candidate['actual_scalar_coordinates']), decode(candidate['actual_spatial_gauge'])
    active = read(BASE/'active-gauge/receipt.json'); count += bindings(active)
    N = s.sympify(active['source_lapse'])
    expected_e = s.diag(N, 1, 1, 1); expected_e[1, 0] = N/5
    eq(e, expected_e)
    expected_A = s.Matrix(active['actual_background']['gauge_connection']).applyfunc(s.sympify)[1:, :]
    expected_A[0, broken[0]] += s.Rational(1, 17)
    eq(A, expected_A)
    h = clean(s.Abs(e.det())*(e.T*ETA*e).inv()); volume = s.Abs(e.det()); h00 = h[0, 0]
    eq(h, decode(candidate['metric_density'])); assert h[0, 1] == s.Rational(1, 5)
    y0 = x.col_join(A.reshape(36, 1))
    y = s.Matrix(s.symbols('scalar_gauge_coordinate0:97', real=True))
    point = dict(zip(y, y0))
    phi_symbol = v+R*y[:61, :]
    D_symbol = clean(O.T*s.Matrix.hstack(*(rho70[a]*phi_symbol for a in broken)))
    D = clean(D_symbol.subs(point))
    F, free = D.T.gauss_jordan_solve(s.eye(9)); assert free.rows == 0
    eq(D.T*F, s.eye(9))
    phi = clean(phi_symbol.subs(point))
    V_symbol = s.Matrix.vstack(*((Ta*y).T for Ta in T))
    V = clean(V_symbol.subs(point))
    b_symbol = s.zeros(70, 1)
    U = []
    for i in range(3):
        RA_symbol = sum((y[61+12*i+a]*rho70[a] for a in range(12)), s.zeros(70))
        b_symbol += h[0, i+1]*RA_symbol*phi_symbol
        U.append(clean((RA_symbol*phi_symbol).subs(point)))
    b = clean(b_symbol.subs(point))
    b_jacobian = clean(b_symbol.jacobian(list(y)).subs(point))
    eq(b, decode(candidate['original_shift']))
    # Each derivative solves the differentiated original D^T F=I; there is
    # no imported inverse-derivative or candidate momentum-direction helper.
    derivatives_F, derivatives_V = [], []
    for alpha in range(97):
        dD = D_symbol.diff(y[alpha])
        if dD.todok():
            dF, parameters = D.T.gauss_jordan_solve(-dD.T*F)
            assert parameters.rows == 0
        else: dF = s.zeros(9)
        derivatives_F.append(clean(dF))
        derivatives_V.append(V_symbol.diff(y[alpha]))
    embedding = Rdual.row_join(s.zeros(70, 36))
    OF = clean(O*F)
    a = clean(embedding-OF*V)
    m = -OF
    drift = s.zeros(1, 97); current_derivative = s.zeros(1, 9)
    derivatives_a, derivatives_m = [], []
    for alpha in range(97):
        dm = clean(-O*derivatives_F[alpha])
        da = clean(dm*V-OF*derivatives_V[alpha])
        derivatives_m.append(dm); derivatives_a.append(da)
        drift += a[:, alpha].T*da
        current_derivative += a[:, alpha].T*dm
    drift, current_derivative = clean(drift), clean(current_derivative)
    assert any(matrix.todok() for matrix in derivatives_F)
    print('PASS source full70 momentum coefficients and all97 scalar/gauge partial derivatives, including live inverse Gauss map', flush=True)

    original = {(5, 258): s.S.One}
    ell = s.Matrix([s.Rational((j % 11)+1, 67) for j in range(97)])
    radial = s.Matrix([s.Rational((j % 7)-3, 53) for j in range(97)])
    gradient = s.I*ell; Hessian = radial*radial.T-s.eye(97)
    J = [apply_state(Qa, original) for Qa in Q]
    JJ = {(i, j): apply_state(Q[i], J[j]) for i in range(9) for j in range(9)}
    # Compose every original (-i a_j.partial + m_j.J-b_j)^2. Collecting
    # the complete differential coefficients is independent of applying
    # each candidate's nested momentum to an intermediate wavepacket.
    principal = clean(a.T*a)
    coefficient_scalar = -s.trace(principal*Hessian)-(drift*gradient)[0]+2*s.I*(b.T*a*gradient)[0]
    coefficient_scalar += s.I*dot(a, b_jacobian)+dot(b, b)
    coefficient_current = clean(-2*s.I*(gradient.T*a.T*m)-s.I*current_derivative-2*b.T*m)
    coefficient_JJ = clean(m.T*m)
    kinetic = add_terms([(coefficient_scalar/(2*h00), original)]+
        [(coefficient_current[j]/(2*h00), J[j]) for j in range(9)]+
        [(value/(2*h00), JJ[i, j]) for (i, j), value in coefficient_JJ.todok().items()])

    # Rebuild each requested expansion component from the original graph.
    free_energy = add_terms([(-s.trace((R.T*R).inv()*Hessian[:61, :61])/(2*h00), original)])
    quadratic = clean(F.T*Gram*F/(2*h00))
    linear = s.zeros(1, 9)
    for c in range(9):
        directional_F = sum((V[c, alpha]*derivatives_F[alpha] for alpha in range(97)), s.zeros(9))
        linear += -s.I*F[:, c].T*Gram*directional_F/(2*h00)
    linear = clean(linear)
    G = [add_terms([(-s.I*(V[j, :]*gradient)[0], original), (1, J[j])]) for j in range(9)]
    normal_terms = []
    for (i, j), value in quadratic.todok().items():
        derivative_vector_j = sum((V[i, alpha]*derivatives_V[alpha][j, :] for alpha in range(97)), s.zeros(1, 97))
        scalar_GG = -(derivative_vector_j*gradient)[0]-(V[i, :]*Hessian*V[j, :].T)[0]
        normal_terms += [(value*scalar_GG, original), (-s.I*value*(V[i, :]*gradient)[0], J[j]),
            (-s.I*value*(V[j, :]*gradient)[0], J[i]), (value, JJ[i, j])]
    normal_terms += [(linear[j], G[j]) for j in range(9)]
    normal_energy = add_terms(normal_terms)
    t, n = clean(Rdual.T*b), clean(O.T*b)
    n_jacobian = clean(O.T*b_jacobian)
    w = clean(F.T*n)
    eq(w, decode(candidate['normal_current_shift'])); assert w.todok()
    commutator = s.cancel(-s.I*sum(F[i, j]*(n_jacobian[i, :]*V[j, :].T)[0] for i in range(9) for j in range(9))/(2*h00))
    zero(commutator-s.sympify(candidate['normal_shift_commutator']))
    assert commutator != 0 and w[0] == s.Rational(1, 85)
    zero(s.trace(Rdual.T*b_jacobian[:, :61]))
    shift_scalar = s.I*(t.T*gradient[:61, :])[0]/h00+commutator+dot(b, b)/(2*h00)
    normal_shift_action = add_terms([(w[j]/h00, G[j]) for j in range(9)])
    assert normal_shift_action
    peripheral_shift_action = add_terms([(s.I*(t.T*gradient[:61, :])[0]/h00, original)])
    full_normal_shift_action = add_terms([(commutator, original), (1, normal_shift_action)])
    assert full_normal_shift_action
    shift_energy = add_terms([(shift_scalar, original), (1, normal_shift_action)])
    assert add_terms([(1, kinetic), (-1, free_energy), (-1, normal_energy), (-1, shift_energy)]) == {}
    assert shift_energy
    potential_value = s.expand(-sum(h[i+1, j+1]*dot(U[i], U[j])/2 for i in range(3) for j in range(3))+volume*dot(phi-v, phi-v))
    potential = add_terms([(potential_value, original)])
    values = {'original_squared_momentum': kinetic, 'peripheral_kinetic': free_energy,
        'normal_kinetic': normal_energy, 'shift': shift_energy, 'spatial_potential': potential,
        'peripheral_shift': peripheral_shift_action, 'normal_shift': full_normal_shift_action,
        'full_scalar_bulk': add_terms([(1, kinetic), (1, potential)])}
    assert set(values) == set(candidate['wavepacket']['components'])
    for name, value in values.items(): compare_state(value, candidate['wavepacket']['components'][name])
    print('PASS all70 original squared differential operators on the actual97-variable two-branch CAR wavepacket and every expansion component', flush=True)

    # The classical source density fixes the multiplication term and shift.
    # A0 remains nonzero here; its scalar term is removed only by the common
    # gauge-plus-matter-plus-scalar Gauss combination, not inside this block.
    pi = s.Matrix([s.Rational((j % 5)-2, 31) for j in range(61)])
    zeta = s.Matrix([s.Rational(j-4, 29) for j in range(9)])
    momentum = Rdual*pi+O*zeta
    time_connection = s.Matrix([s.Rational(j-5, 41) for j in range(12)])
    RA0 = sum((time_connection[j]*rho70[j] for j in range(12)), s.zeros(70))
    U0 = clean((momentum-b)/h00)
    actual_velocity = U0-RA0*phi
    covariant = [U0, *U]
    L = s.expand(sum(h[mu, nu]*dot(covariant[mu], covariant[nu])/2 for mu in range(4) for nu in range(4))-volume*dot(phi-v, phi-v))
    original_H = s.expand(dot(momentum, actual_velocity)-L)
    A0_term = -dot(momentum, RA0*phi)
    zero(original_H-(dot(momentum-b, momentum-b)/(2*h00)+potential_value+A0_term))
    assert A0_term != 0
    # D cancels exactly from w because the stabilizer annihilates every
    # point of the scalar constraint slice in the normal pairing.
    stabilizer = s.Matrix.hstack(*orbit.nullspace())
    reader = select.row_join(stabilizer).inv()[:9, :]
    expected_w = sum((h[0, i+1]*reader*A[i, :].T for i in range(3)), s.zeros(9, 1))
    eq(w, expected_w)
    print('PASS original scalar kinetic/spatial/potential Legendre density, nonzero normal shift and explicit retained nonzero A0 scalar term', flush=True)
    paths = [Path(__file__), path, HERE/'source_scalar_shift_quantum.py',
        HERE/'source_gauss_live_ordering.json', HERE/'independent_source_gauss_live_ordering.json',
        HERE/'source_scalar_gauss_reduction.json', HERE/'source_gauss_quantum_current.json',
        HERE/'independent_source_gauss_quantum_current.py', HERE/'independent_source_gauge_legendre.py',
        BASE/'active-gauge/receipt.json']
    result = {'verdict': 'CERTIFIED_COMPLETE_SOURCE_SCALAR_SHIFTED_MOMENTUM_SQUARE_ON_LIVE_GAUSS_CCR_CAR_GRAPH',
        'root': ROOT_ID, 'source_sha256': hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks': count, 'candidate_constructor_or_nested_action_imported': False,
        'independent_method': 'occupation-bit raw source representations; all97 partial derivatives of the original momentum coefficients; full70 second/first/zero differential coefficients; exterior-slot CAR action',
        'source_metric_h01': '1/5', 'normal_current_shift': encode(w), 'normal_shift_commutator': str(commutator),
        'all97_partial_derivatives_paid': True, 'all70_shifted_momentum_squares_composed': True,
        'all8_wavepacket_components_match': True, 'full504_original_real_two_branch_CAR_retained': True,
        'normal_shift_operator_action_nonzero': encode_vector(full_normal_shift_action),
        'normal_shift_coefficient_current_commutator_nonzero': True,
        'entire_shift_omission_changes_operator': True,
        'original_scalar_Legendre_density_readback': {'kinetic_shift': True, 'spatial_and_potential': True,
            'nonzero_A0_scalar_term_retained': str(A0_term), 'A0_removed_only_in_common_Gauss_bulk': True},
        'domain': 'C_c^infinity(det D!=0 in61 scalar and36 gauge coordinates) tensor algebraic original real504 CAR; coframe parameters remain fixed',
        'fixed_coframe_promoted_to_quantum_geometry': False,
        'full_joint_evolution_spectrum_or_lifetime_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_scalar_shift_quantum.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS independent complete scalar shifted quantum energy', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
