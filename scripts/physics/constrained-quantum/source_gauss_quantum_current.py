#!/usr/bin/env python3
"""Original real Gauss moment maps and the normal-momentum CAR ordering.

The bosonic current remains an operator. The constant quadratic coefficient
below is read at the actual source; the live Gauss graph retains D(phi).
No eliminated Contact is added a second time.
"""
from __future__ import annotations

from collections import defaultdict
import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_joint_temporal_rates import RawSource, HERE, BASE, ROOT, ROOT_ID, clean, eq, zero, encode, decode, bindings, dot
from real_scalar_car_source import realify, real_bilinear
from scalar_dyson_peierls import annihilate_basis, create_basis


def add_state(output, state, value):
    output[state] += value


def apply_current(matrix, state):
    result = defaultdict(lambda: s.S.Zero)
    for (i, j), coefficient in matrix.todok().items():
        after, first = annihilate_basis(int(j), state)
        if first:
            final, second = create_basis(int(i), after)
            if second: add_state(result, final, first*second*coefficient)
    return {state: s.expand(v) for state, v in result.items() if s.expand(v) != 0}


def apply_superposition(matrix, state):
    output = defaultdict(lambda: s.S.Zero)
    for incoming, coefficient in state.items():
        for outgoing, value in apply_current(matrix, incoming).items(): add_state(output, outgoing, coefficient*value)
    return {state: s.expand(v) for state, v in output.items() if s.expand(v) != 0}


def normal_pair(A, B, state):
    """Direct original four-CAR word, not a difference of charge products."""
    result = defaultdict(lambda: s.S.Zero)
    left, right = defaultdict(list), defaultdict(list)
    for (i, j), value in A.todok().items(): left[int(j)].append((int(i), value))
    for (k, ell), value in B.todok().items(): right[int(ell)].append((int(k), value))
    for j in state:
        after_j, sign_j = annihilate_basis(j, state)
        for ell in after_j:
            after_l, sign_l = annihilate_basis(ell, after_j)
            for k, b in right[ell]:
                after_k, sign_k = create_basis(k, after_l)
                if not sign_k: continue
                for i, a in left[j]:
                    after_i, sign_i = create_basis(i, after_k)
                    if sign_i: add_state(result, after_i, sign_j*sign_l*sign_k*sign_i*a*b)
    return {state: s.expand(v) for state, v in result.items() if s.expand(v) != 0}


def weighted_sum(terms):
    output = defaultdict(lambda: s.S.Zero)
    for coefficient, values in terms:
        for state, value in values.items(): add_state(output, state, coefficient*value)
    return {state: s.expand(value) for state, value in output.items() if s.expand(value) != 0}


def encode_state(state): return [[list(k), str(v)] for k, v in sorted(state.items())]


def tensor_current(B, Q, state):
    """Pi=-i partial on actual linear boson polynomials, tensor original CAR."""
    result = defaultdict(lambda: s.S.Zero)
    for (boson, fermions), coefficient in state.items():
        for (i, j), value in B.todok().items():
            if int(j) == boson: result[(int(i), fermions)] += coefficient*value
        for outgoing, value in apply_current(Q, fermions).items():
            result[(boson, outgoing)] += coefficient*value
    return {key: s.expand(value) for key, value in result.items() if s.expand(value) != 0}


def main():
    began = time.monotonic(); raw = RawSource()
    graph_path = HERE/'source_scalar_gauss_reduction.json'
    graph = json.loads(graph_path.read_text())
    real_path = HERE/'real_scalar_car_source.json'
    real_record = json.loads(real_path.read_text())
    phase_path = HERE/'scalar_canonical_phase.json'
    phase = json.loads(phase_path.read_text())
    count = 0
    for record in (graph, real_record, phase):
        assert record['root'] == ROOT_ID and record['source_sha256'] == raw.hashes
        count += bindings(record)
    N = s.sympify(raw.active['source_lapse']); zero(N*N-s.Rational(54, 125))
    gram = clean(raw.Ob.T*raw.Ob); inverse = clean(gram.inv())
    source_weight = clean(-N*inverse/2)
    assert gram.det() == 256
    h00 = -1/N
    symbolic_current = s.Matrix(s.symbols('G0:9', real=True))
    normal = -inverse*symbolic_current
    zero(dot(raw.Ob*normal, raw.Ob*normal)/(2*h00)-(symbolic_current.T*source_weight*symbolic_current)[0])
    eq(raw.Ob.T*raw.Ob*normal+symbolic_current, s.zeros(9, 1))

    # Preserve the independent-dual real pairing and its actual half factors.
    I, Z = s.eye(252), s.zeros(252)
    momentum_map = decode(real_record['complex_momentum_parts_to_real_P'])
    U = decode(real_record['complex_branch_unitary'])
    branch_dual = decode(real_record['complex_branch_dual_map_from_p_real_imag'])
    eq(U, s.Matrix.vstack(s.Matrix.hstack(I, s.I*I), s.Matrix.hstack(I, -s.I*I))/s.sqrt(2))
    eq(branch_dual, s.Matrix.vstack(s.Matrix.hstack(I, -I), s.Matrix.hstack(s.I*I, s.I*I))/s.sqrt(2))
    charges, branches = [], []
    for a, rho in enumerate(raw.rho252):
        real_action = realify(rho)
        quantum = clean(s.I*real_action)
        W = clean(s.I*rho)
        branch = clean(s.diag(W, -W.conjugate()))
        eq(momentum_map*real_action, real_bilinear(W))
        eq(s.I*branch_dual*U, momentum_map)
        eq(U*quantum*U.H, branch)
        eq(quantum.H, quantum)
        eq(branch.H, branch)
        zero(s.trace(quantum))
        charges.append(quantum); branches.append(branch)
    for a in range(12):
        for b in range(12):
            structure = raw.adjoint[a][:, b]
            eq(charges[a]*charges[b]-charges[b]*charges[a],
                s.I*sum((structure[c]*charges[c] for c in range(12)), s.zeros(504)))
    print('PASS original Re(i p rho psi), actual normalized real504 two branches and all144 Gauss CAR Lie identities', flush=True)

    # These are the original CCR moment maps before the broken graph.
    # Weyl ordering of Pi^T T q has no c-number because Tr(T)=0.
    scalar_matrices = raw.rho70
    gauge_matrices = [s.kronecker_product(s.eye(3), ad) for ad in raw.adjoint]
    for collection in (scalar_matrices, gauge_matrices):
        for a in range(12):
            zero(s.trace(collection[a]))
            for b in range(12):
                structure = raw.adjoint[a][:, b]
                eq(collection[a]*collection[b]-collection[b]*collection[a],
                    sum((structure[c]*collection[c] for c in range(12)), s.zeros(collection[a].rows)))
    R = decode(phase['scalar_coordinate_embedding'])
    dual_R = clean(R*(R.T*R).inv())
    eq(dual_R.T*raw.Ob, s.zeros(61, 9)); eq(R*dual_R.T, raw.P61)
    projected = [clean(dual_R.T*rho*R) for rho in raw.rho70]
    projected_defects = []
    for a in range(12):
        for b in range(12):
            structure = raw.adjoint[a][:, b]
            defect = clean(projected[a]*projected[b]-projected[b]*projected[a]-sum((structure[c]*projected[c] for c in range(12)), s.zeros(61)))
            if defect.todok(): projected_defects.append((a, b, len(defect.todok())))
    assert projected_defects
    stabilizer = clean(s.Matrix.hstack(*raw.O.nullspace()))
    for j in range(3):
        rho = clean(sum((stabilizer[a, j]*raw.rho70[a] for a in range(12)), s.zeros(70)))
        eq(raw.P61*rho, rho*raw.P61)
    print('PASS full70 scalar/full36 gauge CCR moment maps; broken scalar61 compression retains its graph correction', flush=True)

    broken = raw.broken
    Q = [branches[a] for a in broken]
    contraction = clean(sum((source_weight[a, b]*(Q[a]*Q[b]) for a, b in source_weight.todok()), s.zeros(504)))
    eq(contraction.H, contraction)
    assert contraction.todok()
    # Symmetric source weight makes the ordered square equal to its Weyl
    # symmetrization even though the native charge operators do not commute.
    antisymmetric_contraction = clean(sum((source_weight[a, b]*(Q[a]*Q[b]-Q[b]*Q[a]) for a, b in source_weight.todok()), s.zeros(504)))
    eq(antisymmetric_contraction, s.zeros(504))
    # A universal CAR-word identity pays arbitrary occupation number; these
    # actual states exercise both branches, their cross term and one-body term.
    states = [(), (0,), (252,), (0, 1), (0, 252), (0, 253), (0, 1, 252), (126, 135, 378, 387)]
    rows = []
    mixed_witness = None
    for state in states:
        composed = weighted_sum((source_weight[a, b], apply_superposition(Q[a], apply_current(Q[b], state))) for a, b in source_weight.todok())
        quartic = weighted_sum((source_weight[a, b], normal_pair(Q[a], Q[b], state)) for a, b in source_weight.todok())
        one_body = apply_current(contraction, state)
        assert weighted_sum([(1, composed), (-1, quartic), (-1, one_body)]) == {}
        if any(i < 252 for i in state) and any(i >= 252 for i in state) and quartic:
            mixed_witness = {'input': list(state), 'quartic_image': encode_state(quartic)}
        rows.append({'input': list(state), 'charge_square': encode_state(composed), 'one_body': encode_state(one_body), 'normal_quartic': encode_state(quartic)})
    assert mixed_witness
    singleton = rows[1]
    assert singleton['one_body'] and not singleton['normal_quartic']
    # Generic bosonic B commutes with the entire CAR factor. Its cross term
    # is retained, without assuming that different B_a commute with each other.
    # The actual graph base current is a first-order CCR differential
    # operator. Linear coordinate polynomials form an invariant test space;
    # the original Pi=-i partial representation itself has arbitrary degree.
    B = [clean(-s.I*s.diag(gauge_matrices[a], projected[a]).T) for a in broken]
    assert any((B[a]*B[b]-B[b]*B[a]).todok() for a in range(9) for b in range(9))
    boson_index = next(j for j in range(97) if any(Ba[:, j].todok() for Ba in B))
    tensor_input = {(boson_index, (0,)): s.S.One}
    tensor_composed = weighted_sum((source_weight[a, b], tensor_current(B[a], Q[a],
        tensor_current(B[b], Q[b], tensor_input))) for a, b in source_weight.todok())
    tensor_ordered = defaultdict(lambda: s.S.Zero)
    tensor_cross = defaultdict(lambda: s.S.Zero)
    for a, b in source_weight.todok():
        weight = source_weight[a, b]
        for (boson, fermions), coefficient in tensor_input.items():
            for (i, j), value in (B[a]*B[b]).todok().items():
                if int(j) == boson: tensor_ordered[(int(i), fermions)] += weight*coefficient*value
            for left, right in ((a, b), (b, a)):
                for (i, j), value in B[left].todok().items():
                    if int(j) == boson:
                        for outgoing, car_value in apply_current(Q[right], fermions).items():
                            tensor_cross[(int(i), outgoing)] += weight*coefficient*value*car_value
            for outgoing, value in normal_pair(Q[a], Q[b], fermions).items():
                tensor_ordered[(boson, outgoing)] += weight*coefficient*value
    for (boson, fermions), coefficient in tensor_input.items():
        for outgoing, value in apply_current(contraction, fermions).items():
            tensor_ordered[(boson, outgoing)] += coefficient*value
    tensor_cross = {key: s.expand(value) for key, value in tensor_cross.items() if s.expand(value) != 0}
    assert tensor_cross
    assert weighted_sum([(1, tensor_composed), (-1, tensor_ordered), (-1, tensor_cross)]) == {}
    factors = [{'a': int(a), 'b': int(b), 'coefficient': str(source_weight[a, b])} for a, b in sorted(source_weight.todok())]
    print('PASS source normal-momentum energy: complete real504 ordering, mixed branches and actual nonzero CCR/CAR cross current', flush=True)

    normal_order = ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/Fermion/NormalOrder.lean'
    source_car = ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/FullQuantum/CAR.lean'
    body = normal_order.read_text()
    assert 'theorem quantize_normal_order' in body and 'theorem original_secondQuantize_normal_order' in body
    paths = [Path(__file__), graph_path, HERE/'source_scalar_gauss_reduction.py', real_path, HERE/'real_scalar_car_source.py', phase_path,
        HERE/'independent_source_joint_temporal_rates.py', HERE/'independent_source_gauge_legendre.py',
        normal_order, source_car]
    result = {'root': ROOT_ID, 'source_sha256': raw.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'scope': 'SOURCE_REAL_GAUSS_MOMENT_MAPS_AND_NORMAL_SCALAR_MOMENTUM_CAR_ORDERING',
        'source_binding_checks': count,
        'source_normal_momentum': {'h00': str(h00), 'broken_Gram': encode(gram), 'normal_energy_weight': encode(source_weight),
            'formula': 'zeta=-Gram9^-1 G_base,b; H_normal=-N/2 G_base,b^T Gram9^-1 G_base,b',
            'live_graph_coefficient': 'K(e,phi)=(1/(2 h00)) D(phi)^-1 Gram9 D(phi)^-T; the coefficient reduces to -N/2 Gram9^-1 only at the actual source',
            'graph_current': 'G_base = +div Pi_A - ad(A_i)^T Pi_Ai + pi^T Rdual^T rho(phi) + Re(i p rho psi)',
            'old_Contact_added_again': False},
        'real_CAR_current': {'dimension': 504, 'native_rows': 12,
            'matrix_rule': 'Q_a=i realify(rho_a); U Q_a U^dagger=diag(i rho_a,i conjugate(rho_a))',
            'primal_branches': '(psi,conjugate(psi))/sqrt2', 'dual_branches': '(p,-conjugate(p))/sqrt2',
            'independent_p_identified_with_adjoint': False,
            'all144_native_Lie_identities': True,
            'all12_matrices_in_complex_branch_basis': [encode(Qa) for Qa in branches]},
        'CCR_moment_maps': {'full_scalar70': True, 'homogeneous_gauge36': True,
            'all144_Lie_identities_each': True, 'Weyl_ordering_trace_constants_all_zero': True,
            'scalar61_compression_full12_Lie_claimed': False,
            'compression_defect_count': len(projected_defects), 'compression_defect_witness': list(projected_defects[0]),
            'all3_source_stabilizer_preserve_scalar61': True},
        'quantum_normal_energy': {'ordered_factors': factors, 'broken_native_indices': broken,
            'full_tensor_formula': 'sum_ab K_ab [B_a B_b tensor 1 + B_a tensor J_b + B_b tensor J_a + 1 tensor normalProduct(Q_a,Q_b) + 1 tensor dGamma(Q_a Q_b)]',
            'matter_current': 'J_a=dGamma(Q_a); B_a is the retained gauge/scalar CCR current, commuting only with the matter factor',
            'one_body_matrix': encode(contraction),
            'quartic_factorization_complete': True, 'one_body_term_nonzero': True,
            'single_particle_omission_control': singleton, 'mixed_branch_quartic_witness': mixed_witness,
            'actual_CAR_word_readouts': rows,
            'actual_CCR_tensor_CAR_consumer': {'boson_polynomial_space': 'linear polynomials in36 gauge and61 scalar coordinates',
                'boson_operator': '-i sum_j (T_a q)_j partial_j with T_a=diag(ad_a x3,Rdual^T rho_a R)',
                'noncommuting_boson_currents_retained': True, 'normal_ordered_tensor_identity': True,
                'input': [[int(boson), list(fermions), str(value)] for (boson, fermions), value in tensor_input.items()],
                'nonzero_mixed_cross_image': [[int(boson), list(fermions), str(value)] for (boson, fermions), value in sorted(tensor_cross.items())]},
            'universal_ordering_theorem': 'SaturationMonoid.PhysicsCore.LowEnergy.Fermion.quantize_normal_order',
            'formal_new_full_joint_Hamiltonian_installed': False},
        'downstream_producer': 'Install the live K(e,phi) and retained B_a on the common scalar/gauge/coframe CCR algebra tensor original real504 CAR; use the Gauss graph ordering and original bulk Hamiltonian once, retaining the residual3 Gauss constraints.',
        'continuous_momentum_scope': 'For continuous one-particle labels the same normal-order identity uses operator composition of smeared current kernels. This finite internal coefficient receipt does not define a coincident unsmeared field square or its ultraviolet measure.',
        'bosons_frozen_or_scalar_probe_promoted_to_full_quantum': False,
        'physical_vacuum_or_decay_measure_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'source_gauss_quantum_current.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS source Gauss quantum current and ordering', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
