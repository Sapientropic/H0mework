#!/usr/bin/env python3
"""Independent raw real-Gauss/CAR coefficient and ordered tensor audit.

Exterior representations are rebuilt by occupation bits. Fock consumers use
exterior-slot replacements, with the quartic operator acting on two distinct
slots, independently of the candidate's ordered creation/annihilation words.
"""
from __future__ import annotations

from collections import defaultdict
import hashlib
import itertools
import json
import time

import sympy as s

from independent_source_gauge_legendre import (
    HERE, BASE, ROOT, ROOT_ID, source, bindings, clean, decode, encode, equal,
    matrix_coordinates, read)


def zero(value):
    assert s.expand(value) == 0, value


def exterior_bits(T, degree):
    states = [sum(1 << j for j in word) for word in itertools.combinations(range(7), degree)]
    index = {word: k for k, word in enumerate(states)}
    result = s.MutableSparseMatrix.zeros(len(states), len(states))
    for column, word in enumerate(states):
        for (i, j), coefficient in T.todok().items():
            if not word & (1 << j):
                continue
            cleared = word ^ (1 << j)
            if cleared & (1 << i):
                continue
            parity = (word & ((1 << j)-1)).bit_count()+(cleared & ((1 << i)-1)).bit_count()
            result[index[cleared | (1 << i)], column] += (-1)**parity*coefficient
    return clean(result)


def polynomial_real_action(T):
    I = s.eye(T.rows)
    injections = s.Matrix.hstack(I, s.I*I)
    images = T*injections
    return clean(s.Matrix.vstack(images.applyfunc(s.re), images.applyfunc(s.im)))


def normalize_state(values):
    return {key: s.expand(value) for key, value in values.items() if s.expand(value) != 0}


def wedge_sort(values):
    if len(set(values)) != len(values):
        return None, 0
    sign = (-1)**sum(values[i] > values[j] for i in range(len(values)) for j in range(i+1, len(values)))
    return tuple(sorted(values)), sign


def columns(A):
    result = defaultdict(list)
    for (i, j), value in A.todok().items():
        result[int(j)].append((int(i), value))
    return result


def exterior_current(A, state):
    result = defaultdict(lambda: s.S.Zero)
    entries = columns(A)
    for position, incoming in enumerate(state):
        for outgoing, value in entries[incoming]:
            replaced = list(state); replaced[position] = outgoing
            target, sign = wedge_sort(replaced)
            if sign:
                result[target] += sign*value
    return normalize_state(result)


def distinct_slot_product(A, B, state):
    result = defaultdict(lambda: s.S.Zero)
    left, right = columns(A), columns(B)
    for i in range(len(state)):
        for j in range(len(state)):
            if i == j:
                continue
            for a, ca in left[state[i]]:
                for b, cb in right[state[j]]:
                    replaced = list(state); replaced[i] = a; replaced[j] = b
                    target, sign = wedge_sort(replaced)
                    if sign:
                        result[target] += sign*ca*cb
    return normalize_state(result)


def apply_state(A, vector):
    result = defaultdict(lambda: s.S.Zero)
    for state, coefficient in vector.items():
        for target, value in exterior_current(A, state).items():
            result[target] += coefficient*value
    return normalize_state(result)


def add_terms(terms):
    result = defaultdict(lambda: s.S.Zero)
    for coefficient, vector in terms:
        for target, value in vector.items():
            result[target] += coefficient*value
    return normalize_state(result)


def decoded_state(rows):
    return {tuple(state): s.sympify(value) for state, value in rows}


def tensor_apply(B, Q, vector):
    result = defaultdict(lambda: s.S.Zero)
    boson = columns(B)
    for (polynomial, fermions), coefficient in vector.items():
        for output, value in boson[polynomial]:
            result[(output, fermions)] += coefficient*value
        for output, value in exterior_current(Q, fermions).items():
            result[(polynomial, output)] += coefficient*value
    return normalize_state(result)


def main():
    began = time.monotonic()
    path = HERE/'source_gauss_quantum_current.json'
    saved = read(path); count = bindings(saved)
    assert saved['root'] == ROOT_ID
    _, vacuum, degrees, hashes = source.parse_source(ROOT)
    assert hashes == saved['source_sha256']
    fundamental = [s.SparseMatrix(M)*(s.I if imaginary else 1)
                   for _, imaginary, M in source.generators([(0, 1, 2), (3, 4)])]
    rho70 = [polynomial_real_action(exterior_bits(T, 4)) for T in fundamental]
    rho252 = [clean(s.kronecker_product(s.eye(4), s.diag(*[exterior_bits(T, k) for k in degrees]))) for T in fundamental]
    adjoint = [s.Matrix.hstack(*[matrix_coordinates(T*S-S*T) for S in fundamental]) for T in fundamental]
    v = s.Matrix([vacuum.get(word, 0) for word in itertools.combinations(range(7), 4)]+[0]*35)
    orbit = clean(s.Matrix.hstack(*[T*v for T in rho70]))
    broken = list(orbit.rref()[1]); select = s.eye(12)[:, broken]; O = orbit*select
    gram = clean(O.T*O)
    active_path = BASE/'active-gauge/receipt.json'; active = read(active_path)
    N = s.sympify(active['source_lapse']); zero(N**2-s.Rational(54, 125))
    h00 = -1/N
    weight = clean(gram.inv()/(2*h00))
    normal_data = saved['source_normal_momentum']
    equal(gram, decode(normal_data['broken_Gram']))
    equal(weight, decode(normal_data['normal_energy_weight']))
    assert gram.det() == 256 and '+div Pi_A' in normal_data['graph_current']
    assert normal_data['old_Contact_added_again'] is False
    g = s.Matrix(s.symbols('charge0:9', real=True))
    normal, free = gram.gauss_jordan_solve(-g)
    assert free.rows == 0
    zero((normal.T*gram*normal)[0]/(2*h00)-(g.T*weight*g)[0])

    I = s.eye(252); C = s.Matrix.hstack(I, s.I*I)
    U = s.Matrix.vstack(C, C.conjugate())/s.sqrt(2)
    Pmap = s.Matrix.vstack(s.Matrix.hstack(s.zeros(252), -I), s.Matrix.hstack(-I, s.zeros(252)))
    dual_map = -s.I*Pmap*U.H
    charges, Q = [], []
    for a, rho in enumerate(rho252):
        action = polynomial_real_action(rho)
        pair = clean((C.T*(s.I*rho)*C).applyfunc(s.re))
        equal(Pmap*action, pair)
        charge = clean(s.I*action)
        branches = clean(U*charge*U.H)
        equal(branches, s.diag(s.I*rho, s.I*rho.conjugate()))
        equal(branches, decode(saved['real_CAR_current']['all12_matrices_in_complex_branch_basis'][a]))
        equal(branches.H, branches); equal(charge.H, charge)
        equal(s.I*dual_map*U, Pmap)
        zero(s.trace(charge))
        charges.append(charge); Q.append(branches)
    u, vv, x, y, a, b = s.symbols('p_re p_im psi_re psi_im rho_re rho_im', real=True)
    p, psi, rho = u+s.I*vv, x+s.I*y, a+s.I*b
    direct = s.re(s.I*p*rho*psi)
    doubled = ((p/s.sqrt(2))*(s.I*rho)*(psi/s.sqrt(2))+
               (-s.conjugate(p)/s.sqrt(2))*(s.I*s.conjugate(rho))*(s.conjugate(psi)/s.sqrt(2)))
    zero(direct-doubled)
    for aa in range(12):
        for bb in range(12):
            f = adjoint[aa][:, bb]
            equal(Q[aa]*Q[bb]-Q[bb]*Q[aa], s.I*sum((f[c]*Q[c] for c in range(12)), s.zeros(504)))
    print('PASS occupation-bit raw252/real504 source currents, true half normalization and all144 CAR Lie identities', flush=True)

    for collection in (rho70, [s.diag(A, A, A) for A in adjoint]):
        for aa, T in enumerate(collection):
            zero(s.trace(T))
            for bb, S in enumerate(collection):
                f = adjoint[aa][:, bb]
                equal(T*S-S*T, sum((f[c]*collection[c] for c in range(12)), s.zeros(T.rows)))
    null = s.Matrix.hstack(*orbit.T.nullspace())
    projector = clean(null*(null.T*null).inv()*null.T)
    R = projector[:, list(projector.rref()[1])]
    dual_R = clean(R.row_join(O).inv().T[:, :61])
    equal(R, decode(read(HERE/'scalar_canonical_phase.json')['scalar_coordinate_embedding']))
    equal(dual_R.T*O, s.zeros(61, 9))
    projected = [clean(dual_R.T*T*R) for T in rho70]
    defects = []
    for aa in range(12):
        zero(s.trace(projected[aa]))
        for bb in range(12):
            f = adjoint[aa][:, bb]
            defect = clean(projected[aa]*projected[bb]-projected[bb]*projected[aa]-
                           sum((f[c]*projected[c] for c in range(12)), s.zeros(61)))
            if defect.todok():
                defects.append([aa, bb, len(defect.todok())])
    assert len(defects) == saved['CCR_moment_maps']['compression_defect_count']
    assert defects[0] == saved['CCR_moment_maps']['compression_defect_witness']
    kernel = s.Matrix.hstack(*orbit.nullspace())
    for j in range(3):
        T = sum((kernel[a, j]*rho70[a] for a in range(12)), s.zeros(70))
        equal(projector*T, T*projector)
    assert saved['CCR_moment_maps']['scalar61_compression_full12_Lie_claimed'] is False
    print('PASS raw full70/full36 CCR moment maps and exact distinction of stabilizer61 from full native12 compression', flush=True)

    energy = saved['quantum_normal_energy']; broken_Q = [Q[a] for a in broken]
    assert energy['broken_native_indices'] == broken
    factors = {(row['a'], row['b']): s.sympify(row['coefficient']) for row in energy['ordered_factors']}
    assert factors == dict(weight.todok())
    contraction = clean(sum((coefficient*broken_Q[a]*broken_Q[b] for (a, b), coefficient in factors.items()), s.zeros(504)))
    equal(contraction, decode(energy['one_body_matrix'])); equal(contraction.H, contraction)
    assert len(contraction.todok()) == 480
    for row in energy['actual_CAR_word_readouts']:
        state = tuple(row['input'])
        composed = add_terms((k, apply_state(broken_Q[a], exterior_current(broken_Q[b], state))) for (a, b), k in factors.items())
        quartic = add_terms((k, distinct_slot_product(broken_Q[a], broken_Q[b], state)) for (a, b), k in factors.items())
        one_body = exterior_current(contraction, state)
        assert composed == decoded_state(row['charge_square'])
        assert quartic == decoded_state(row['normal_quartic'])
        assert one_body == decoded_state(row['one_body'])
        assert add_terms([(1, composed), (-1, quartic), (-1, one_body)]) == {}
    singleton = energy['single_particle_omission_control']
    assert not singleton['normal_quartic'] and singleton['one_body']
    zero(decoded_state(singleton['one_body'])[(0,)]+9*s.sqrt(30)/200)
    mixed = energy['mixed_branch_quartic_witness']
    assert any(i < 252 for i in mixed['input']) and any(i >= 252 for i in mixed['input'])
    assert mixed['quartic_image']
    print('PASS complete source one-body480 and distinct-slot quartic, including true cross-branch occupied states', flush=True)

    B = [clean(-s.I*s.diag(adjoint[a], adjoint[a], adjoint[a], projected[a]).T) for a in broken]
    assert any(clean(A*D-D*A).todok() for A in B for D in B)
    tensor = energy['actual_CCR_tensor_CAR_consumer']
    initial = {(int(boson), tuple(state)): s.sympify(coefficient) for boson, state, coefficient in tensor['input']}
    direct_tensor = add_terms((k, tensor_apply(B[a], broken_Q[a], tensor_apply(B[b], broken_Q[b], initial)))
                              for (a, b), k in factors.items())
    boson_part, cross, matter_part = defaultdict(lambda: s.S.Zero), defaultdict(lambda: s.S.Zero), defaultdict(lambda: s.S.Zero)
    for (a, b), k in factors.items():
        boson_square = columns(B[a]*B[b])
        for (boson, state), coefficient in initial.items():
            for target, value in boson_square[boson]:
                boson_part[(target, state)] += k*coefficient*value
            for T, Wq in ((B[a], broken_Q[b]), (B[b], broken_Q[a])):
                for target, value in columns(T)[boson]:
                    for target_state, car in exterior_current(Wq, state).items():
                        cross[(target, target_state)] += k*coefficient*value*car
            for target, value in distinct_slot_product(broken_Q[a], broken_Q[b], state).items():
                matter_part[(boson, target)] += k*coefficient*value
    for (boson, state), coefficient in initial.items():
        for target, value in exterior_current(contraction, state).items():
            matter_part[(boson, target)] += coefficient*value
    cross = normalize_state(cross)
    assert cross and cross == {(int(boson), tuple(state)): s.sympify(value) for boson, state, value in tensor['nonzero_mixed_cross_image']}
    assert add_terms([(1, direct_tensor), (-1, boson_part), (-1, matter_part), (-1, cross)]) == {}
    zero(cross[(1, (0,))]+3*s.sqrt(30)*s.I/100)
    print('PASS actual noncommuting97-polynomial CCR tensor real CAR ordered energy and nonzero mixed coefficient', flush=True)

    formal_path = HERE/'fock_raising_audit.json'; formal = read(formal_path)
    assert all(row['exit_code'] == 0 and row['trust'] == 0 for row in formal['strict_checks'])
    bindings(formal)
    normal_order = ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/Fermion/NormalOrder.lean'
    assert formal['input_sha256'][str(normal_order.relative_to(ROOT))] == hashlib.sha256(normal_order.read_bytes()).hexdigest()
    assert energy['universal_ordering_theorem'].endswith('.quantize_normal_order')
    paths = [path, HERE/'source_gauss_quantum_current.py', HERE/'independent_source_gauss_quantum_current.py',
             HERE/'independent_source_gauge_legendre.py', HERE/'independent_source_scalar_gauss_reduction.json',
             HERE/'scalar_canonical_phase.json', formal_path, normal_order, active_path, BASE/'exact_readout.py']
    result = {'root': ROOT_ID, 'source_sha256': hashes,
        'verdict': 'CERTIFIED_SOURCE_REAL_GAUSS_CAR_CURRENT_AND_ORDERED_NORMAL_MOMENTUM_ENERGY',
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'candidate_bindings_checked': count,
        'raw_native12_occupation_bit_exterior_all252_and_real504': True,
        'original_Re_independent_p_half_and_branch_signs': True,
        'all144_matter_Lie_and_all288_full_boson_Lie_identities': True,
        'original_Gram9_source_weight': encode(weight),
        'full_source_one_body_nonzero_count': len(contraction.todok()),
        'normal_quartic_independent_distinct_slot_consumers': len(energy['actual_CAR_word_readouts']),
        'actual_noncommuting_boson_tensor_CAR_consumer': True,
        'actual_mixed_boson1_CAR0_coefficient': str(cross[(1, (0,))]),
        'full70_CCR_and_stabilizer61_scope_preserved': True,
        'universal_CAR_normal_order_consumer': energy['universal_ordering_theorem'],
        'existing_strict_formal_receipt_reused_at_exact_NormalOrder_bytes': True,
        'live_variable_K_ordering_or_full_joint_quantum_evolution_claimed': False,
        'Contact_added_again_or_decay_measure_claimed': False,
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_gauss_quantum_current.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print(result['verdict'], result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
