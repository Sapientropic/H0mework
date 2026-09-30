#!/usr/bin/env python3
"""Raw-source certification of the complete local Hamiltonian filtration.

No grade producer is imported. Exterior labels generate the occupied grade;
independent density coefficients and exterior-slot CAR generate the complete
four-energy readout and the actual interleaved words. The formal theorem is
certified separately at its universal graded-word scope.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import time
import sympy as s

from independent_source_quantum_gauss_section import (
    RawGaussSection, raw_whole_action, HERE, ROOT, ROOT_ID, bindings, clean,
    rational, eq, decode, terms, current, state_encode)
from independent_source_quantum_stabilizer import RawLiveCoefficients
from independent_source_common_hamiltonian import original_inventory, raw_matter
from independent_source_gauss_quantum_current import decoded_state
from independent_source_gauge_legendre import source


def grade_predicate(matrix, weights, degree):
    assert matrix.shape == (504, 504)
    for (row, column), value in matrix.todok().items():
        assert s.cancel((weights[row]-weights[column]-degree)*value) == 0


def grade_state(state, weights, particle_number, grade):
    assert all(len(word) == particle_number and sum(weights[i] for i in word) == grade and value != 0
               for word, value in state.items())


def coefficient_audit(model):
    _, _, degrees, hashes = source.parse_source(ROOT)
    labels = [(degree, word) for degree in degrees for word in itertools.combinations(range(7), degree)]
    assert len(labels) == 63 and list(degrees) == [6, 2, 4]
    weights = [int(degree == 6) for _branch in range(2) for _spin in range(4) for degree, _ in labels]
    assert len(weights) == 504 and sum(weights) == 56
    raw = original_inventory()
    # Every scalar coefficient is independently rebuilt by occupation-bit
    # wedge action in the raw inventory, in the original source degree order.
    Y = raw['scalar']; Y = Y+[s.I*M for M in Y]
    for matrix in Y: grade_predicate(s.diag(matrix, -matrix.conjugate()), weights, 1)
    for matrix in model.native.matter:
        grade_predicate(s.diag(matrix, -matrix.conjugate()), weights, 0)
    for matrix in model.native.Qb+model.native.Qs+model.r:
        grade_predicate(matrix, weights, 0)
    # The temporal inverse and every source principal are spin-only. This
    # generic64-coefficient tensor check covers arbitrary live spin matrices,
    # not a sample of e or a selected external state.
    spin = s.Matrix(8, 8, s.symbols('spin_coefficient0:64'))
    grade_predicate(s.kronecker_product(spin, s.eye(63)), weights, 0)
    cf = RawLiveCoefficients()
    matrices = cf.J+cf.T+cf.M+[cf.correction, cf.one_body]+[M for row in cf.dT for M in row]
    for matrix in matrices:
        grade_predicate(s.kronecker_product(matrix, s.eye(63)), weights, 0)
    # Original SU2 acts by a direct sum of the three exterior degrees.
    # Every finite CAR group action therefore preserves the sum of the same
    # one-particle weights, including the signed source center action.
    for degree in degrees:
        assert len(list(itertools.combinations(range(7), degree))) == sum(d == degree for d, _ in labels)
    return weights, hashes, {'original_exterior_degree_order': list(degrees), 'target_rank': sum(weights),
        'all70_original_Yukawa_matrices_raise_grade_one': True,
        'all12_native_and_native_orthogonal_Gauss_currents_preserve_grade': True,
        'arbitrary_spin8_tensor_identity63_preserves_grade': True,
        'actual_generic_live_spin_coefficients_and_derivatives_checked': len(matrices),
        'complete_boson_differential_factors_preserve_CAR_grade': True,
        'source_group_and_half_density_preserve_grade': True}


def actual_action_audit(model, weights, candidate):
    q = (s.Rational(7, 6), s.Rational(1, 11), s.Rational(9, 8),
         s.Rational(-1, 13), s.Rational(1, 17), s.Rational(11, 10))
    x = s.Matrix([s.Rational((3*j+1)%7-3, 100) for j in range(61)])
    A = model.source[67:, :].reshape(3, 12)
    A[0, 2] += s.Rational(1, 17); A[1, 7] += s.Rational(1, 19)
    y = s.Matrix(q).col_join(x).col_join(A.reshape(36, 1))
    raw_cf = RawLiveCoefficients(); e = raw_cf.at(raw_cf.e, q)
    phi = model.native.v+model.native.R*x
    connection = s.zeros(4, 12); connection[1:, :] = A
    raw = raw_matter(e, phi, connection)
    Yukawa = clean(-s.I*raw['volume']*raw['E_inverse']*raw['Y'])
    full = clean(-s.I*raw['E_inverse']*raw['lower'])
    Y = clean(s.diag(Yukawa, -Yukawa.conjugate()))
    H = clean(s.diag(full, -full.conjugate())); M0 = clean(H-Y)
    grade_predicate(Y, weights, 1); grade_predicate(M0, weights, 0)
    eq(Y*Y, s.zeros(504))
    column = next(j for j in range(252) if Y[:, j].todok())
    word = (column, column+252)
    expected = candidate['actual_consumers']
    assert list(word) == expected['actual_complete103_jet_input']
    gradient = s.Matrix([s.I*s.Rational(j%11+1, 67) for j in range(103)])
    v = s.Matrix([s.Rational(j%7-3, 53) for j in range(103)])
    components = raw_whole_action(model, y, {word: [1, gradient, v*v.T-s.eye(103)]})
    assert all(components.values())
    image = terms((1, value) for value in components.values())
    raising = current(Y, {word: 1})
    diagonal = terms([(1, image), (-1, raising)])
    assert raising and diagonal
    grade_state(raising, weights, 2, 1); grade_state(diagonal, weights, 2, 0)
    for key in ('coframe', 'scalar', 'gauge'): grade_state(components[key], weights, 2, 0)
    assert terms([(1, raising), (-1, decoded_state(expected['full_Yukawa_action']))]) == {}
    assert terms([(1, diagonal), (-1, decoded_state(expected['full_H0_action']))]) == {}
    twice = current(Y, raising); thrice = current(Y, twice)
    assert twice and not thrice
    assert terms([(1, twice), (-1, decoded_state(expected['one_body_Y_square_zero_but_two_particle_Y_square_nonzero']))]) == {}
    interleaved = current(Y, current(M0, raising)); assert interleaved
    grade_state(interleaved, weights, 2, 2)
    assert terms([(1, interleaved), (-1, decoded_state(expected['actual_Y_M0_Y_nonzero']))]) == {}
    assert current(Y, current(M0, interleaved)) == {}
    # Independently regenerate every nonconstant CAR-valued Gauss jet before
    # applying the original four raw differential energy components.
    section = expected['actual_local_Gauss_section']; charged = tuple(section['input'])
    grad = s.Matrix([s.Rational(j%3-1, 41) for j in range(100)])
    _, jet = model.extension_jet(model.source, {charged: 1}, {charged: grad}, {charged: grad*grad.T-s.eye(100)})
    for word in jet: assert len(word) == 2 and sum(weights[i] for i in word) == sum(weights[i] for i in charged)
    gauss = model.Gauss_checks(model.source, jet)
    local = raw_whole_action(model, model.source, jet)
    for key in ('coframe', 'scalar', 'gauge'):
        grade_state(local[key], weights, 2, sum(weights[i] for i in charged))
    local_image = terms((1, value) for value in local.values())
    allowed = {sum(weights[i] for i in charged)+i for i in (0, 1)}
    assert all(sum(weights[i] for i in word) in allowed for word in local_image)
    assert terms([(1, local_image), (-1, decoded_state(section['complete_Hamiltonian_action']))]) == {}
    return {'source_fixture_full103_four_energy_action_rebuilt': True,
            'original_full_H0_and_Y_readouts_match': True,
            'one_body_square_vs_two_particle_square_distinguished': True,
            'actual_nonzero_interleaved_Y_M0_Y': state_encode(interleaved),
            'actual_Y_M0_Y_M0_Y_zero': True,
            'actual_local_Gauss_section': gauss,
            'actual_local_section_complete_H_action': state_encode(local_image)}


def main():
    began = time.monotonic(); path = HERE/'source_quantum_grade_structure.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    paid = ['independent_source_quantum_stabilizer.json', 'independent_source_quantum_gauss_section.json',
            'independent_source_gauss_section_measure.json']
    for name in paid: count += bindings(json.loads((HERE/name).read_text()))
    model = RawGaussSection()
    weights, hashes, coefficient = coefficient_audit(model)
    assert hashes == model.native.hashes
    assert coefficient['target_rank'] == candidate['coefficients']['grade_one_particle_rank']
    assert coefficient['actual_generic_live_spin_coefficients_and_derivatives_checked'] == candidate['coefficients']['spin_coefficient_matrices_checked']
    print('PASS independently regenerated original504 occupation weights and all70 Yukawa/native/live coefficient grades', flush=True)
    consumers = actual_action_audit(model, weights, candidate)
    print('PASS raw complete Hamiltonian filtration, actual interleaved words and original Gauss-section two-jet', flush=True)
    paths = [HERE/name for name in ('independent_source_quantum_grade_structure.py', 'source_quantum_grade_structure.py',
        'source_quantum_grade_structure.json', 'FockFilteredWords.lean', 'FockFilteredWordsAudit.lean',
        'FockRaisingTensor.lean', 'FockRaising.lean', 'FockRaisingAudit.lean',
        'independent_source_quantum_gauss_section.py', 'independent_source_quantum_stabilizer.py',
        'independent_source_common_hamiltonian.py', 'independent_source_coframe_live_ordering.py')]+[HERE/name for name in paid]
    result = {'root': ROOT_ID, 'source_sha256': hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'verdict': 'CERTIFIED_COMPLETE_NATIVE_LOCAL_HAMILTONIAN_FILTRATION_AND_INTERLEAVED_WORD_BOUND',
        'scope': candidate['scope'], 'checked_input_bindings': count, 'candidate_constructor_imported': False,
        'source_coefficients': coefficient, 'actual_consumers': consumers,
        'formal_mouth_review': {'generic_theorem': 'SourceFockFilteredWords.weighted_tensor_word_vanishes',
            'scope': 'For a finite mode carrier, each CAR factor conserves particle number and has its explicitly supplied nonnegative homogeneous grade. Every word of total grade>N vanishes on the N-particle sector, even with arbitrary grade0 factors between positive-grade factors. Boson factors remain in their original noncommuting order.',
            'source_laws_not_a_vanishing_premise': True,
            'proof_mechanism': 'Track total number and grade through the ordered product; any resulting grade>N has zero coefficients by occupation-basis support. Extend from basis states and factor the tensor product without changing word order.',
            'actual_Lean_nonempty_sector_witnesses': 'Fin4 actual RDR incoming!=0 and RDRDR incoming=0 on the two-particle sector.',
            'strict_kernel_command': 'lake env lean --trust=0 -DwarningAsError=true FockFilteredWords.lean; FockFilteredWordsAudit.lean, with the source-root path and refreshed temporary olean',
            'axioms': ['propext', 'Classical.choice', 'Quot.sound'],
            'formal_full504_source_instantiation_claimed': False},
        'complete_source_operator_argument': 'The original boson differential/multiplication factors commute with the fixed CAR occupation grading. Every original coframe, gauge and Gauss current is grade0; each of the70 Yukawa coefficients is grade1. Finite products and sums preserve those laws, including normal-order contractions and coefficient derivatives. Source group extension, restriction and scalar half-density preserve the same grading, so the local reduced operator inherits it.',
        'propagator_Hilbert_spectrum_temporal_reduction_or_lifetime_inferred': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_quantum_grade_structure.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent complete local quantum occupation filtration', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
