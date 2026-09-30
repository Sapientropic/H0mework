#!/usr/bin/env python3
"""Independent original coframe Legendre/primary and six-CCR CAR audit.

The original16 momentum equations determine the metric inverse and primary
section. Symbolic polynomials supply actual six CCR derivatives; exterior-slot
CAR independently recovers the source current square and its normal ordering.
"""
from __future__ import annotations

from collections import defaultdict
import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_lorentz_contact import (
    HERE, BASE, ROOT, ROOT_ID, GENERATORS, original_hessian, geometric_load,
    original_gamma, original_density_ports, real_linear, real_bilinear)
from independent_source_gauge_legendre import bindings, clean, decode, ETA
from independent_source_joint_temporal_rates import encode, eq, zero, dot
from independent_source_gauss_quantum_current import exterior_current, distinct_slot_product


SPATIAL = [k for k in range(16) if k % 4]
TIME = [0, 4, 8, 12]
q = s.symbols('free_coframe0:6', real=True)


def normalize(state): return {key: s.expand(value) for key, value in state.items() if s.expand(value) != 0}


def terms(items):
    output = defaultdict(lambda: s.S.Zero)
    for coefficient, value in items:
        for state, polynomial in value.items(): output[state] += coefficient*polynomial
    return normalize(output)


def derivative(j, state): return normalize({key: -s.I*s.diff(value, q[j]) for key, value in state.items()})


def position(j, state): return normalize({key: q[j]*value for key, value in state.items()})


def current(Q, state):
    output = defaultdict(lambda: s.S.Zero)
    for incoming, polynomial in state.items():
        for outgoing, value in exterior_current(Q, incoming).items(): output[outgoing] += value*polynomial
    return normalize(output)


def quartic(A, B, state):
    output = defaultdict(lambda: s.S.Zero)
    for incoming, polynomial in state.items():
        for outgoing, value in distinct_slot_product(A, B, incoming).items(): output[outgoing] += value*polynomial
    return normalize(output)


def read_state(rows):
    output = defaultdict(lambda: s.S.Zero)
    for powers, fermions, coefficient in rows:
        output[tuple(fermions)] += s.sympify(coefficient)*s.prod(x**int(n) for x, n in zip(q, powers))
    return normalize(output)


def compare(actual, rows): assert terms([(1, actual), (-1, read_state(rows))]) == {}


def main():
    began = time.monotonic(); candidate_path = HERE/'source_coframe_quantum_kinetic.json'
    candidate = json.loads(candidate_path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    active = json.loads((BASE/'active-gauge/receipt.json').read_text()); count += bindings(active)
    e = s.Matrix(active['actual_background']['coframe']).applyfunc(s.sympify); N = e[0, 0]
    eq(e, decode(candidate['source_coframe']))
    e_symbol = s.Matrix(4, 4, s.symbols('original_e0:16', real=True))
    H = original_hessian(e); Hi = H.inv()
    G = clean(geometric_load(e_symbol).xreplace(dict(zip(e_symbol, e)))); Gt = G[:, :16]
    M = clean(-Gt.T*Hi*Gt)
    h_symbol = e_symbol[:, 1:].T*ETA*e_symbol[:, 1:]
    metric_slots = ((0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (1, 2))
    Dh = clean(s.Matrix([h_symbol[i, j] for i, j in metric_slots]).jacobian(list(e_symbol)).xreplace(dict(zip(e_symbol, e))))
    symmetric_section = s.zeros(16, 6)
    for a, (i, j) in enumerate(metric_slots):
        symmetric_section[4*(i+1)+j+1, a] = 1; symmetric_section[4*(j+1)+i+1, a] = 1
    R = clean(symmetric_section*(Dh*symmetric_section).inv())
    eq(Dh*R, s.eye(6))
    Qinverse = clean(R*(R.T*M*R).inv()*R.T)
    spatial = e.copy(); spatial[:, 0] = s.zeros(4, 1)
    Z = s.Matrix.hstack(*((T*spatial).reshape(16, 1) for T in GENERATORS))
    primary = Z.T[:, SPATIAL]; dependent = list(primary.rref()[1]); free = [j for j in range(12) if j not in dependent]
    free_indices = [SPATIAL[j] for j in free]; dependent_indices = [SPATIAL[j] for j in dependent]
    right_hand = (-primary[:, free]).row_join(-s.eye(6))
    solved, parameters = primary[:, dependent].gauss_jordan_solve(right_hand)
    assert parameters.rows == 0
    free_map, spin_map = s.zeros(16, 6), s.zeros(16, 6)
    for j, index in enumerate(free_indices): free_map[index, j] = 1
    for j, index in enumerate(dependent_indices):
        free_map[index, :] = solved[j, :6]; spin_map[index, :] = solved[j, 6:]
    time_reader = s.eye(24)[:6, :]
    L = clean(spin_map*time_reader+Gt.T*Hi)
    eq(M*Qinverse*free_map, free_map); eq(M*Qinverse*L, L)
    kinetic = clean(free_map.T*Qinverse*free_map/2)
    mixed = clean(free_map.T*Qinverse*L)
    weight = clean((L.T*Qinverse*L+Hi)/2)
    constant = 3*e.det()
    graph = candidate['primary_graph']; ordered = candidate['ordered_Hamiltonian']
    for name, value in [('free_momentum_embedding', free_map), ('spin_current_embedding', spin_map), ('shifted_current_embedding', L)]: eq(value, decode(graph[name]))
    for name, value in [('CCR_kinetic_weight', kinetic), ('CCR_CAR_mixed_current_weight', mixed), ('whole_current_square_weight', weight)]: eq(value, decode(ordered[name]))
    assert kinetic.det() != 0
    # The actual raw reduced Lagrangian, rather than an assumed Hamiltonian
    # formula, generates the complete source primary-graph energy.
    kappa = s.Matrix(s.symbols('canonical_momentum0:6', real=True))
    j = s.Matrix(s.symbols('original_real_current0:24', real=True))
    Pi = free_map*kappa+spin_map*j[:6, :]
    shift = -Gt.T*Hi*j
    velocity = clean(Qinverse*(Pi-shift))
    force = Gt*velocity+j
    raw_L = -3*e.det()-(force.T*Hi*force)[0]/2
    raw_H = s.expand(dot(Pi, velocity)-raw_L)
    expanded_H = (kappa.T*kinetic*kappa)[0]+(kappa.T*mixed*j)[0]+(j.T*weight*j)[0]+constant
    zero(raw_H-expanded_H)
    eq(Z.T*Pi+j[:6, :], s.zeros(6, 1)); eq(Pi.extract(TIME, [0]), s.zeros(4, 1))
    slice_lift = s.eye(16)[:, free_indices]; dependent_reader = s.eye(16)[dependent_indices, :]
    transverse = dependent_reader*Z
    eq(free_map.T*slice_lift, s.eye(6)); eq(spin_map.T*slice_lift, s.zeros(6))
    slice_velocity = clean(slice_lift.T-slice_lift.T*Z*transverse.inv()*dependent_reader)
    eq(slice_velocity, free_map.T)
    geometry_saved = candidate['original_graph_consumer']['canonical_slice']
    assert geometry_saved['free_coframe_coordinates'] == free_indices
    assert geometry_saved['fixed_dependent_coframe_coordinates'] == dependent_indices
    eq(transverse, decode(geometry_saved['original_Lorentz_transverse_minor']))
    eq(slice_lift, decode(geometry_saved['coordinate_lift']))
    print('PASS raw original16 momentum/Legendre equations, six solved primary rows and actual canonical slice one-form', flush=True)

    gamma = original_gamma(); E, vertices = original_density_ports(e, gamma)
    native = [clean(E.inv()*V) for V in vertices]
    quantum8 = [clean(s.diag(s.I*T, s.I*T.conjugate())) for T in native]
    quantum = [s.kronecker_product(T, s.eye(63)) for T in quantum8]
    I = s.eye(4); U = s.Matrix.vstack(s.Matrix.hstack(I, s.I*I), s.Matrix.hstack(I, -s.I*I))/s.sqrt(2)
    Pmap = s.Matrix.vstack(s.Matrix.hstack(s.zeros(4), -I), s.Matrix.hstack(-I, s.zeros(4)))
    for a, T in enumerate(native):
        eq(Pmap*real_linear(T), real_bilinear(s.I*T))
        eq(U*(s.I*real_linear(T))*U.H, quantum8[a])
        eq(quantum8[a], decode(candidate['source_quantum_current_spin8_tensor_identity63'][a]))
    psi = s.Matrix([s.Rational((3*k+2)%11-5, 31)+s.I*s.Rational((5*k+1)%13-6, 37) for k in range(252)])
    p = s.Matrix([[s.Rational((7*k+3)%17-8, 41)+s.I*s.Rational((2*k+5)%11-5, 43) for k in range(252)]])
    chi = clean(s.I*p*s.kronecker_product(E.inv(), s.eye(63)))
    actual = clean(s.Matrix([s.re((chi*s.kronecker_product(V, s.eye(63))*psi)[0]).expand() for V in vertices]))
    plus_minus_psi = psi.col_join(psi.conjugate())/s.sqrt(2)
    plus_minus_p = p.row_join(-p.conjugate())/s.sqrt(2)
    for a in range(24): zero((plus_minus_p*quantum[a]*plus_minus_psi)[0]-actual[a])
    saved_actual = candidate['original_graph_consumer']
    eq(actual, decode(saved_actual['actual_full24_current']))
    eq(psi, decode(saved_actual['actual_independent_primal'])); eq(p, decode(saved_actual['actual_independent_p']))
    one_body8 = clean(sum((c*quantum8[a]*quantum8[b] for (a, b), c in weight.todok().items()), s.zeros(8)))
    eq(one_body8, -9*N*s.eye(8)/8); eq(one_body8, decode(ordered['one_body_spin8_matrix']))
    one_body = s.kronecker_product(one_body8, s.eye(63))
    mixed8 = [clean(sum((mixed[r, a]*quantum8[a] for a in range(24)), s.zeros(8))) for r in range(6)]
    mixed_quantum = [s.kronecker_product(T, s.eye(63)) for T in mixed8]
    for value, record in zip(mixed8, ordered['mixed_spin8_matrices']): eq(value, decode(record))
    assert all(C.todok() for C in mixed8)
    print('PASS original24 Re currents and normalized independent dual branches; exact one-body -9N/8 identity504', flush=True)

    def shifted(index, state):
        return terms([(free_map[index, r], derivative(r, state)) for r in range(6)]+
            [(L[index, a], current(quantum[a], state)) for a in range(24)])

    def original_operator(state):
        result = [(constant, state)]
        for (i, j0), coefficient in Qinverse.todok().items(): result.append((coefficient/2, shifted(i, shifted(j0, state))))
        for (a, b), coefficient in Hi.todok().items(): result.append((coefficient/2, current(quantum[a], current(quantum[b], state))))
        return terms(result)

    readouts = candidate['actual_operator_consumer']['actual_polynomial_CCR_tensor_CAR_readouts']
    for record in readouts:
        state = read_state(record['input'])
        direct = original_operator(state)
        pieces = {
            'kinetic': terms((coefficient, derivative(r, derivative(t, state))) for (r, t), coefficient in kinetic.todok().items()),
            'mixed': terms((1, derivative(r, current(mixed_quantum[r], state))) for r in range(6)),
            'normal_quartic': terms((coefficient, quartic(quantum[a], quantum[b], state)) for (a, b), coefficient in weight.todok().items()),
            'one_body': current(one_body, state), 'constant': terms([(constant, state)])}
        assert terms([(1, direct)]+[(-1, v) for v in pieces.values()]) == {}
        compare(direct, record['direct_original_square'])
        for name, value in pieces.items(): compare(value, record['ordered_terms'][name])
    state = read_state(readouts[0]['input'])
    for r in range(6):
        for t in range(6):
            assert terms([(1, position(r, derivative(t, state))), (-1, derivative(t, position(r, state))),
                (-s.I if r == t else 0, state)]) == {}
    for r in range(6):
        actual_velocity = terms([(s.I, original_operator(position(r, state))), (-s.I, position(r, original_operator(state)))])
        expected_velocity = terms([(2*kinetic[r, t], derivative(t, state)) for t in range(6)]+[(1, current(mixed_quantum[r], state))])
        assert terms([(1, actual_velocity), (-1, expected_velocity)]) == {}
        compare(actual_velocity, candidate['actual_operator_consumer']['six_generated_Heisenberg_coordinate_velocities'][r])
    print('PASS polynomial sixCCR/exterior504 CAR original square, independent distinct-slot normal quartic and allsix Heisenberg velocities', flush=True)
    paths = [Path(__file__), candidate_path, HERE/'source_coframe_quantum_kinetic.py',
        HERE/'independent_source_lorentz_contact.py', HERE/'independent_source_gauge_legendre.py',
        HERE/'independent_source_gauss_quantum_current.py', HERE/'source_homogeneous_canonical_flow.json',
        BASE/'active-gauge/receipt.json', ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/Fermion/NormalOrder.lean']
    result = {'verdict': 'CERTIFIED_ORIGINAL_COFRAME_PRIMARY_LEGENDRE_SIX_CCR_AND_REAL504_CAR_KINETIC',
        'root': ROOT_ID, 'source_sha256': candidate['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks': count, 'candidate_constructor_imported': False,
        'independent_method': 'original BF16 momentum Hessian and full primary linear solve; raw reduced-L Legendre transform; symbolic polynomial derivatives and exterior-slot CAR',
        'primary_and_one_form': {'all10_rows': True, 'six_free_momenta_symbolic': True,
            'fixed_dependent_coordinates': dependent_indices, 'free_coordinates': free_indices,
            'spin_graph_one_form_term_zero': True, 'Lorentz_corrected_velocity_reader': True},
        'original_real_current': {'all24_rows': True, 'all252_independent_primal_and_p_entries': True,
            'normalized_real504_two_branch_identity': True, 'p_identified_with_Hilbert_adjoint': False},
        'ordered_operator': {'source_kinetic_and_mixed_weights': True,
            'whole_Lorentz_elimination_consumed_once': True, 'extra_72_or571_Contact_added': False,
            'full_one_body_matrix': '-9N/8 identity504', 'all3_actual_operator_readouts': True,
            'normal_quartic_by_distinct_exterior_slots': True,
            'all36_actual_CCR': True, 'all6_actual_Heisenberg_coordinate_velocities': True},
        'domain': 'Polynomials in six canonical source-slice coframe coordinates tensor algebraic real504 CAR, with source coefficient matrices fixed; momenta remain -i partial',
        'general_live_coframe_coefficient_ordering_or_full_quantum_evolution_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_coframe_quantum_kinetic.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS independent source coframe quantum kinetic', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
