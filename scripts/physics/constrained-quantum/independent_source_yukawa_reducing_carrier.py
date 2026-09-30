#!/usr/bin/env python3
"""Original exterior/Dirac audit of the canonical Yukawa-null Fock carrier.

The carrier producer is not imported. The positive Gram is rebuilt from
occupation-bit exterior maps, then every original vertex is checked using
the kinetic-generated primal/dual pair. Raw same-projector closure is an
explicitly stronger comparison, not the physical canonical carrier mouth.
"""
from __future__ import annotations

from collections import defaultdict
from functools import lru_cache
import hashlib
import itertools
import json
import time
import sympy as s

from independent_source_common_hamiltonian import original_inventory, raw_matter
from independent_source_quantum_gauss_section import (
    RawGaussSection, RawLiveCoefficients, raw_whole_action, compound,
    terms, current, state_encode, decoded_state)
from independent_source_spatial_active_phase_splice import exact, field_number
from independent_retained_hamiltonian_reduction import (
    HERE, BASE, ROOT, ROOT_ID, DOMAIN, decode, encode, check_bindings)

N = 3*s.sqrt(30)/25


def clean(A): return s.SparseMatrix(A).applyfunc(s.cancel)
def eq(A, B): assert not clean(A-B).todok()


def preserving(matrix, mask):
    for (i, j), value in matrix.todok().items():
        assert s.cancel((mask[i]-mask[j])*value) == 0


def original_kernel(candidate):
    inventory = original_inventory()
    labels = [(degree, word) for degree in inventory['degrees'] for word in itertools.combinations(range(7), degree)]
    gamma0 = s.SparseMatrix(s.kronecker_product(inventory['gamma'][0], s.eye(63)))
    active = json.loads((BASE/'active-gauge/receipt.json').read_text())
    background = active['actual_background']
    e = s.Matrix(background['coframe']).applyfunc(s.sympify)
    connection = s.Matrix(background['gauge_connection']).applyfunc(s.sympify)
    raw = raw_matter(e, inventory['vacuum'], connection)
    E = raw['E']; eq(E, s.I*gamma0)
    assert s.simplify(e.det()-N) == 0
    prefactor = clean(-s.I*raw['volume']*raw['E_inverse'])
    eq(prefactor, N*gamma0)
    eq(E*E, s.eye(252))
    matrices = [clean(prefactor*(s.I**imaginary)*Y) for imaginary in range(2) for Y in inventory['scalar']]
    assert len(matrices) == 70
    gram = s.SparseMatrix.zeros(252)
    for Y in matrices: gram += Y.H*Y+Y*Y.H
    assert gram.is_diagonal()
    values = list(gram.diagonal()); mask = [int(v == 0) for v in values]
    assert sum(mask) == 196
    assert sum(value == 10*N*N for value in values) == 42
    assert sum(value == 30*N*N for value in values) == 14
    assert all(value >= 0 for value in values)
    P = s.SparseMatrix(s.diag(*mask)); dual = clean(E*P*E.inv())
    eq(P*P, P); eq(P.H, P); eq(dual*dual, dual); eq(dual.H, dual)
    for Y in matrices:
        eq(Y*P, s.zeros(252)); eq(Y.H*P, s.zeros(252))
        eq(P*Y, s.zeros(252)); eq(P*Y.H, s.zeros(252))
    saved = candidate['all70_original_Hamiltonian_Yukawa_and_adjoint_kernel']
    eq(gram, decode(saved['positive_Gram'])); eq(P, decode(saved['projector']))
    eq(P, decode(candidate['generated_reducing_projector_complex252']))
    eq(dual, decode(candidate['generated_raw_dual_companion']))
    fullP = s.diag(P, P.conjugate()); eq(fullP, decode(candidate['generated_reducing_projector_real504']))
    for i, kept in enumerate(mask):
        spin, degree = i//63, labels[i % 63][0]
        assert bool(kept) == (degree == 4 or degree == 2 and spin < 2 or degree == 6 and spin >= 2)
    # Kinetic pairing stays unchanged with the original independent momentum
    # p=-i chi E: p=pP implies chi=i p E^-1=chi Pdual, not chi=chi P.
    eq(E*P, dual*E); eq(P*E.inv(), E.inv()*dual)
    assert P != dual
    return inventory, matrices, E, P, dual, mask


def original_vertices(candidate, inventory, E, P, dual, mask):
    vertex = json.loads((BASE/'matter-vertices/receipt.json').read_text())
    phase = json.loads((BASE/'full-phase/receipt.json').read_text())
    checks = check_bindings(vertex)+check_bindings(phase)
    operators = [decode(row['operator']) for row in vertex['primitive_vertices']]
    assert len(operators) == 158
    coefficient_count = 0
    for V in operators:
        variables = sorted(V.free_symbols, key=str)
        powers = set()
        for value in V.todok().values():
            if variables: powers.update(monomial for monomial, coefficient in s.Poly(value, *variables).terms() if coefficient)
            else: powers.add(())
        coefficient_count += max(len(powers), 1)
    assert coefficient_count == candidate['original_canonical_vertex_closure']['independent_momentum_coefficient_matrices']
    operators += list(map(decode, phase['principal_coefficients']))
    operators += [decode(vertex['full_stationary_Dirac_operator'])]
    operators += [s.SparseMatrix(s.kronecker_product(gamma, s.eye(63))) for gamma in inventory['gamma']]
    dual_mask = list(dual.diagonal())
    raw_failure = None
    for V in operators:
        # Every momentum monomial is covered: the mask is constant, and the
        # original polynomial entry itself must obey the exact two-side law.
        for (i, j), value in V.todok().items():
            assert s.cancel((dual_mask[i]-mask[j])*value) == 0
            if raw_failure is None and s.cancel((mask[i]-mask[j])*value) != 0:
                raw_failure = [i, j, str(value)]
        preserving(clean(-s.I*E.inv()*V), mask)
    assert raw_failure is not None
    assert candidate['original_canonical_vertex_closure']['minimal_excluded_span_chain'] == [{'dimension': 56, 'generated_new_dimension': 0}]
    assert candidate['original_canonical_vertex_closure']['first_canonical_leak_of_initial_kernel_complement'] == []
    # For the optional stronger common-raw demand, the original gamma0 alone
    # generates every opposite-chirality missing direction. Their actual
    # span has dimension112, and its complement reduces all raw vertices.
    excluded = [i for i in range(252) if not mask[i]]
    frame = s.SparseMatrix(252, len(excluded), {(i, j): 1 for j, i in enumerate(excluded)})
    generated = s.SparseMatrix.hstack(frame, s.kronecker_product(inventory['gamma'][0], s.eye(63))*frame)
    assert len(exact(generated).rref()[1]) == 112
    degrees = [degree for degree in inventory['degrees'] for _ in itertools.combinations(range(7), degree)]
    rawmask = [int(degrees[i % 63] == 4) for i in range(252)]
    rawP = s.diag(*rawmask)
    eq(rawP, decode(candidate['common_raw_projector_comparison']['projector']))
    for V in operators: preserving(V, rawmask)
    assert sum(rawmask) == 140
    return checks, {'original_vertices': 158, 'all_momentum_coefficients': coefficient_count,
        'same_E_primal_dual_original_vertex_and_Dirac_identity': True,
        'all_original_canonical_matrices_and_adjoints_reduce196': True,
        'canonical_excluded_carrier_dimension': 56,
        'raw_common_projector_extra_requirement_dimension': 140,
        'raw_common_requirement_strict_nonzero_failure': raw_failure,
        'raw_excluded112_span_generated_by_actual_gamma0': True}


def actual_external_legs(inventory, P, dual):
    S = s.kronecker_product(inventory['gamma'][0]*s.diag(-1, -1, 1, 1), s.eye(63))
    eq(P*S, S*dual)
    residue = json.loads((BASE/'kinetic-residue/receipt.json').read_text())
    kinetic = decode(residue['kinetic_pair_matrix'])
    assert s.sympify(residue['source_spin_scale']) == s.sqrt(2)
    reports = []; bindings = check_bindings(residue)
    for name in ('source_onshell_phase_forcing.json', 'source_nonzero_frequency_onshell_response.json'):
        source = json.loads((HERE/name).read_text()); bindings += check_bindings(source)
        assert source['root'] == ROOT_ID
        for i, leg in enumerate(source['legs']):
            v = decode(leg['action_vector']); degree = int(leg['degree'])
            primal_defect = clean(v-P*v); dual_defect = clean(v.H*S-v.H*S*dual)
            assert s.simplify((v.H*kinetic*v)[0]) == 1
            norm_squared = s.simplify((primal_defect.H*primal_defect)[0])
            if degree == 4:
                eq(primal_defect, s.zeros(252, 1)); eq(dual_defect, s.zeros(1, 252))
                assert norm_squared == 0
            else:
                assert degree == 2
                eq(P*v, s.zeros(252, 1)); eq(v.H*S*dual, s.zeros(1, 252))
                assert norm_squared == s.sqrt(2)/2
            reports.append({'source': name, 'leg': i, 'exterior_degree': degree,
                'inside_canonical_and_dual_carrier': degree == 4,
                'action_norm_squared': '1', 'coordinate_projection_defect_norm_squared': str(norm_squared)})
    assert len(reports) == 8
    return bindings, reports


def generic_hamiltonian(model, inventory, mask):
    fullmask = mask*2
    cf = RawLiveCoefficients()
    matrices = cf.J+cf.T+cf.M+[cf.correction, cf.one_body]+[value for row in cf.dT for value in row]
    for spin in matrices:
        for (i, j), value in spin.todok().items():
            for internal in range(63): assert s.cancel((fullmask[63*i+internal]-fullmask[63*j+internal])*value) == 0
    gamma5 = s.diag(-1, -1, 1, 1)
    for gamma in inventory['gamma']: eq(gamma5*gamma+gamma*gamma5, s.zeros(4))
    for left in inventory['gamma']:
        for right in inventory['gamma']: eq(gamma5*left*right-left*right*gamma5, s.zeros(4))
    for M in model.native.matter: preserving(M, mask)
    for M in model.native.Qb+model.native.Qs+model.r: preserving(M, fullmask)
    # Regenerate finite group matrices by exterior determinants. Since each
    # group factor is spin identity and degree diagonal, the same identity
    # holds for every group element, not only these two exact witnesses.
    K = [clean(sum((model.native.S[j, h]*model.native.fund[j] for j in range(12)), s.zeros(7))) for h in range(3)]
    active = -K[0]*K[0]
    for u in ((s.Rational(3, 5), s.Rational(4, 5), 0, 0), (-1, 0, 0, 0)):
        group = clean(s.eye(7)-active+u[0]*active+sum((u[j+1]*K[j] for j in range(3)), s.zeros(7)))
        internal = s.diag(*(compound(group, degree) for degree in inventory['degrees']))
        mother = s.kronecker_product(s.eye(4), internal)
        preserving(clean(s.diag(mother, mother.conjugate())), fullmask)
    return cf, fullmask, len(matrices)


def free_add(*values):
    output = defaultdict(lambda: DOMAIN.zero)
    for polynomial in values:
        for word, coefficient in polynomial.items(): output[word] += coefficient
    return {word: coefficient for word, coefficient in output.items() if coefficient}


def free_scale(value, poly):
    value = field_number(s.sympify(value))
    return {word: value*coefficient for word, coefficient in poly.items() if value*coefficient}


def free_multiply(left, right):
    output = defaultdict(lambda: DOMAIN.zero)
    for a, x in left.items():
        for b, y in right.items(): output[a+b] += x*y
    return {word: coefficient for word, coefficient in output.items() if coefficient}


def independent_ordered_counts():
    # Direct first/second implicit coefficients and the cubic energy jet,
    # instead of the producer's recursive arbitrary-order evaluator.
    n = s.Symbol('n', positive=True); b = s.symbols('b0:3', real=True); ys = (n, *b)
    at = dict(zip(ys, (N, 0, 0, 0))); delta = n*n-sum(v*v for v in b)
    pairs = ((0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (1, 2))
    weights = [*ys, *[(n*n-b[i]*b[j])/(2*n*delta) if i == j else -b[i]*b[j]/(n*delta) for i, j in pairs], *[-v/delta for v in b]]
    source_values = [s.Rational(9, 5), 0, 0, 0]+[s.Rational(324, 625)]*3+[0]*6
    Hs = s.factor(sum(value*weight for value, weight in zip(source_values, weights)))
    atoms = [{(j,): DOMAIN.one} for j in range(13)]
    atoms[0] = free_add(atoms[0], {(13,): DOMAIN.one})
    J = [-s.diff(Hs, y, y).subs(at) for y in ys]
    @lru_cache(None)
    def derivative(part, indices):
        expression = Hs if part == -1 else weights[part]
        for index in indices: expression = s.diff(expression, ys[index])
        return s.simplify(expression.subs(at))
    u1 = []
    for a in range(4):
        force = free_add(*(free_scale(-derivative(j, (a,)), atoms[j]) for j in range(13)))
        u1.append(free_scale(-1/J[a], force))
    # Fixed y0,y1,y2,y3 order is paid by sorted repeated indices; factorials
    # are the Taylor multiindex factors, not symmetric word averaging.
    def monomial(indices, terms):
        result = {(): DOMAIN.one}
        for i in indices: result = free_multiply(result, terms[i])
        return result
    def divisor(indices):
        return s.prod(s.factorial(indices.count(i)) for i in range(4))
    quadratic = list(itertools.combinations_with_replacement(range(4), 2))
    cubic = list(itertools.combinations_with_replacement(range(4), 3))
    u2 = []
    for a in range(4):
        terms0 = [free_scale(-derivative(-1, tuple(sorted((a, *indices))))/divisor(indices), monomial(indices, u1)) for indices in quadratic]
        terms0 += [free_scale(-derivative(j, tuple(sorted((a, r)))), free_multiply(atoms[j], u1[r])) for j in range(13) for r in range(4)]
        u2.append(free_scale(-1/J[a], free_add(*terms0)))
    K0 = {(): field_number(s.simplify(Hs.subs(at)))}
    K1 = free_add(*(free_scale(derivative(j, ()), atoms[j]) for j in range(13)))
    K2 = free_add(*[free_scale(derivative(-1, indices)/divisor(indices), monomial(indices, u1)) for indices in quadratic],
        *[free_scale(derivative(j, (r,)), free_multiply(atoms[j], u1[r])) for j in range(13) for r in range(4)])
    energy3 = [free_scale(derivative(-1, indices)/divisor(indices), monomial(indices, u1)) for indices in cubic]
    for a, b0 in quadratic:
        expansion = free_add(free_multiply(u1[a], u2[b0]), free_multiply(u2[a], u1[b0]))
        energy3.append(free_scale(derivative(-1, (a, b0))/divisor((a, b0)), expansion))
    energy3 += [free_scale(derivative(j, (r,)), free_multiply(atoms[j], u2[r])) for j in range(13) for r in range(4)]
    energy3 += [free_scale(derivative(j, indices)/divisor(indices), free_multiply(atoms[j], monomial(indices, u1))) for j in range(13) for indices in quadratic]
    energies = [K0, K1, K2, free_add(*energy3)]
    return [sum(13 in word for word in row) for row in energies], [sum(13 not in word for word in row) for row in energies]


def actual_Fock_consumer(model, inventory, cf, mask, candidate):
    expected = candidate['complete_Fock_consumer']; fullmask = mask*2
    q = (s.Rational(7, 6), s.Rational(1, 11), s.Rational(9, 8), s.Rational(-1, 13), s.Rational(1, 17), s.Rational(11, 10))
    x = s.Matrix([s.Rational((3*j+1)%7-3, 1000) for j in range(61)])
    A = model.source[67:, :].reshape(3, 12).copy(); A[0, 2] += s.Rational(1, 17); A[1, 7] += s.Rational(1, 19)
    e = cf.at(cf.e, q); phi = model.native.v+model.native.R*x
    connection = s.zeros(4, 12); connection[1:, :] = A
    raw = raw_matter(e, phi, connection)
    H = clean(-s.I*raw['E_inverse']*raw['lower']); Y = clean(-s.I*raw['volume']*raw['E_inverse']*raw['Y'])
    HH, YY = clean(s.diag(H, -H.conjugate())), clean(s.diag(Y, -Y.conjugate()))
    preserving(HH, fullmask)
    for (i, j), value in YY.todok().items(): assert value and not fullmask[i] and not fullmask[j]
    incoming = tuple(expected['actual_two_particle_input'])
    kept = [i for i in range(252) if mask[i]]
    first = next(word for word in itertools.combinations(kept, 2) if current(HH, {word: 1}))
    assert incoming == first
    gradient = s.Matrix([s.I*s.Rational(j%11+1, 67) for j in range(103)])
    v = s.Matrix([s.Rational(j%7-3, 53) for j in range(103)])
    y = s.Matrix(q).col_join(x).col_join(A.reshape(36, 1))
    parts = raw_whole_action(model, y, {incoming: [s.S.One, gradient, v*v.T-s.eye(103)]})
    assert all(parts.values())
    for key, part in parts.items():
        assert all(len(word) == 2 and all(fullmask[i] for i in word) for word in part)
        assert terms([(1, part), (-1, decoded_state(expected['complete_four_component_action'][key]))]) == {}
    image = terms((1, part) for part in parts.values())
    assert terms([(1, image), (-1, decoded_state(expected['complete_Hamiltonian_image']))]) == {}
    assert not current(YY, {incoming: 1}) and not current(YY.H, {incoming: 1})
    grad = s.Matrix([s.Rational(j%3-1, 41) for j in range(100)])
    _, jet = model.extension_jet(model.source, {incoming: 1}, {incoming: grad}, {incoming: grad*grad.T-s.eye(100)})
    Gauss = model.Gauss_checks(model.source, jet)
    assert all(all(fullmask[i] for i in word) for word in jet)
    discarded, retained = independent_ordered_counts()
    assert discarded == expected['actual_ordered_energy_words_with_Y_vanish']
    assert retained == expected['remaining_ordered_energy_word_counts']
    return {'actual_input': list(incoming), 'full_four_energy_action_nonzero_and_restricted': True,
        'actual_Gauss_extension': Gauss, 'zero_value_nonzero_jet_words_retained': True,
        'both_Y_and_Y_adjoint_Fock_actions_zero': True,
        'independent_cubic_energy_counts_with_Y': discarded,
        'independent_cubic_energy_counts_without_Y': retained}


def main():
    began = time.monotonic(); path = HERE/'source_yukawa_reducing_carrier.json'
    candidate = json.loads(path.read_text()); checks = check_bindings(candidate)
    assert candidate['root'] == ROOT_ID
    inventory, yukawa, E, P, dual, mask = original_kernel(candidate)
    assert inventory['source_hashes'] == candidate['source_sha256']
    count, vertices = original_vertices(candidate, inventory, E, P, dual, mask); checks += count
    count, external_legs = actual_external_legs(inventory, P, dual); checks += count
    print('PASS independent complete70 positive Gram, canonical196 maximal carrier and original158 same-E dual identity', flush=True)
    model = RawGaussSection()
    cf, fullmask, spin_count = generic_hamiltonian(model, inventory, mask)
    expected = candidate['complete_Fock_consumer']['generic_live_spin_coefficients_and_all_derivatives_reducing']
    assert spin_count == expected['actual_q_generic_spin_matrices_checked']
    print('PASS actual generic live spin matrices, complete native currents, finite group and original center reducing', flush=True)
    consumer = actual_Fock_consumer(model, inventory, cf, mask, candidate)
    print('PASS full nonzero four-energy exterior-CAR action, complete Gauss jet and independent cubic ordered-word counts', flush=True)
    assert candidate['complete_Fock_consumer']['formal_symmetry_or_positive_spectrum_of_restriction_proved'] is False
    paths = [path]+[HERE/name for name in ('source_yukawa_reducing_carrier.py',
        'independent_source_yukawa_reducing_carrier.py', 'independent_source_common_hamiltonian.py',
        'independent_source_quantum_gauss_section.py', 'independent_source_quantum_stabilizer.py',
        'independent_source_coframe_live_ordering.py', 'source_quantum_ordered_temporal.py',
        'source_quantum_ordered_temporal.json')]+[BASE/'matter-vertices/receipt.json', BASE/'full-phase/receipt.json',
        BASE/'active-gauge/receipt.json', BASE/'kinetic-residue/receipt.json',
        HERE/'source_onshell_phase_forcing.json', HERE/'source_nonzero_frequency_onshell_response.json',
        ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/Fermion/Charge.lean']
    result = {'root': ROOT_ID, 'source_sha256': candidate['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'verdict': 'CERTIFIED_MAXIMAL_CANONICAL_YUKAWA_NULL_CARRIER_AND_SAME_E_FOCK_RESTRICTION',
        'scope': candidate['scope'], 'checked_input_bindings': checks, 'candidate_constructor_imported': False,
        'positive_Gram': {'complex_kernel': sum(mask), 'real_CAR_kernel': sum(fullmask),
            'eigenvalue_multiplicities': {'0': 196, '10*N^2': 42, '30*N^2': 14}},
        'original_vertex_and_dual_consumer': vertices, 'actual_generic_spin_matrices': spin_count,
        'actual_eight_external_legs': external_legs,
        'complete_current_external_leg_inventory_replaced_by_restriction': False,
        'full_Fock_consumer': consumer,
        'maximality_review': 'The Gram quadratic form is the sum of all70 squared Y and Y-adjoint norms, so every simultaneous null subspace lies in its exact196 kernel. This entire kernel already reduces every canonical coefficient; its orthogonal complement needs no enlargement. Thus it is maximal at the stated Yukawa-null canonical reducing scope.',
        'same_E_kinetic_pairing': 'Original p=-i chi E gives chi=i p E^-1. The checked E P=Pdual E implies p=pP and psi=P psi yield chi=chi Pdual and preserve the original kinetic pairing. Raw vertices satisfy V P=Pdual V; imposing Pdual=P adds a different condition and yields the strictly smaller raw140 comparison.',
        'whole_Fock_argument': 'The complement projector is a0/1 one-particle charge. Every non-Y coefficient and its adjoint has zero charge difference at each nonzero entry, paying occupationCharge_quantize and occupationCharge_normalProduct. occupationCharge_preserves_eigenstate then preserves its zero eigenspace, exactly algebraic Fock(K). Boson derivatives and coefficient multiplication commute with the constant charge. Y and Y-adjoint have only outside-K columns, so their annihilators kill every Fock(K) occupation; every interleaved word containing Y vanishes while all other source words preserve the carrier. Native group extension/restriction and scalar half-density preserve the same projector.',
        'scope_boundary': 'Complete local Cc-infinity bosonic chart tensor algebraic CAR392, with the whole coframe/scalar61/gauge36 retained. This signs reducing closure and actual interaction, not formal symmetry, self-adjoint evolution, a spectrum, the external-current Ward kernel, proton identification or a proton no-go.',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_yukawa_reducing_carrier.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent canonical Yukawa reducing carrier', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
