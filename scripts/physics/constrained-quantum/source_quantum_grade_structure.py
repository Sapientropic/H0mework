#!/usr/bin/env python3
"""Occupation filtration of the complete native local quantum Hamiltonian.

The grade counts original Lambda6 modes on both independent-real CAR
branches. Every non-Yukawa factor preserves it; the full Yukawa raises it.
Boson differential factors keep their original order, including live
coframe and Gauss coefficient derivatives. This constructs the filtration
of the operator, not an assumed time propagator for its diagonal blocks.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_quantum_gauss_section import SourceQuantumGaussSection
from source_coframe_live_ordering import full
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state
from source_lorentz_contact import clean, equal


def occupation_grade(word):
    return sum(i % 63 < 7 for i in word)


def matrix_grade(matrix, weight):
    """Entrywise commutator with the original Lambda6 occupation projector."""
    assert matrix.shape == (504, 504)
    for (i, j), value in matrix.todok().items():
        assert s.cancel((int(i % 63 < 7)-int(j % 63 < 7)-weight)*value) == 0


def state_grade(state, particles, grade):
    for word, value in state.items():
        assert value != 0 and len(word) == particles and occupation_grade(word) == grade


def full_coefficients(section):
    m, joint = section.native, section.native.joint
    # Parse the source inventory, rather than naming a selected sector a particle.
    from source_gauge_legendre import source
    _, _, degrees, _ = source.parse_source(ROOT)
    assert list(degrees) == [6, 2, 4]
    for M in joint.common.rho:
        matrix_grade(clean(s.diag(M, -M.conjugate())), 0)
    for M in m.Q_b+m.Q_s:
        matrix_grade(M, 0)
    cf = joint.coframe
    spin_coefficients = cf.J+cf.T+cf.M+[cf.correction, cf.one_body]
    spin_coefficients += [M for row in cf.dT for M in row]
    for M in spin_coefficients:
        matrix_grade(full(M), 0)
    # E^-1 and every principal act only on spin. Thus this identity pays the
    # variable-coframe multiplier of all70 original scalar coefficients too.
    for Y in joint.common.yukawa_basis:
        for Yreal in (Y, s.I*Y):
            matrix_grade(clean(s.diag(Yreal, -Yreal.conjugate())), 1)
    for R in section.R:
        matrix_grade(R, 0)
    # Exterior powers never mix the original three degrees, for every group
    # element. Check the actual finite source group, including its center.
    for quaternion in ((s.Rational(3, 5), s.Rational(4, 5), 0, 0), (-1, 0, 0, 0)):
        matrix_grade(section.matter_group(section.group(s.Matrix(quaternion))), 0)
    return {'original_internal_degrees': list(degrees), 'CAR_modes': 504,
        'grade_one_particle_rank': 56, 'all70_original_Yukawa_coefficients_raise_one': True,
        'all12_native_and9_broken_and3_stabilizer_currents_preserve_grade': True,
        'all_live_spin_currents_and_coefficient_derivatives_preserve_grade': True,
        'spin_coefficient_matrices_checked': len(spin_coefficients),
        'scalar_and_gauge_boson_multipliers_and_derivatives_have_grade_zero': True,
        'Gauss_extension_restriction_and_scalar_half_density_preserve_grade': True,
        'same_group_center_preserves_grade_without_being_trivial_on_all_states': True}


def actual_consumers(section):
    m = section.native
    q = (s.Rational(7, 6), s.Rational(1, 11), s.Rational(9, 8),
         s.Rational(-1, 13), s.Rational(1, 17), s.Rational(11, 10))
    x = s.Matrix([s.Rational((3*j+1) % 7-3, 100) for j in range(61)])
    A = section.A0.copy(); A[0, 2] += s.Rational(1, 17); A[1, 7] += s.Rational(1, 19)
    data = m.joint.coefficients(q, x, A)
    Y = clean(-s.I*data['e'].det()*data['matter']['inverse_E']*data['matter']['Y'])
    Y = clean(s.diag(Y, -Y.conjugate()))
    M0 = clean(data['matter_CAR']-Y)
    matrix_grade(Y, 1); matrix_grade(M0, 0)
    equal(Y*Y, s.zeros(504))
    column = next(j for j in range(252) if Y[:, j].todok())
    incoming = (column, column+252)
    assert occupation_grade(incoming) == 0
    f1 = s.Matrix([s.I*s.Rational(j % 11+1, 67) for j in range(103)])
    v = s.Matrix([s.Rational(j % 7-3, 53) for j in range(103)])
    parts, image = m.joint.action(data, incoming, f1, v*v.T-s.eye(103))
    assert all(parts.values())
    raising = apply_superposition(Y, {incoming: 1})
    diagonal = weighted_sum([(1, image), (-1, raising)])
    state_grade(diagonal, 2, 0); state_grade(raising, 2, 1)
    for name in ('coframe', 'scalar', 'gauge'):
        state_grade(parts[name], 2, 0)
    twice = apply_superposition(Y, raising)
    thrice = apply_superposition(Y, twice)
    assert twice and not thrice
    interleaved = apply_superposition(Y, apply_superposition(M0, raising))
    assert interleaved
    state_grade(interleaved, 2, 2)
    assert not apply_superposition(Y, apply_superposition(M0, interleaved))

    # The same filtered action consumes an actual arbitrary charged local
    # Gauss section; zero-value words with nonzero derivatives are retained.
    charged = (5, 258)
    grad = s.Matrix([s.Rational(j % 3-1, 41) for j in range(100)])
    jet = section.extend_jet({charged: 1}, {charged: grad}, {charged: grad*grad.T-s.eye(100)})
    for word in jet:
        assert len(word) == 2 and occupation_grade(word) == occupation_grade(charged)
    Gauss = section.verify_Gauss_jet(jet)
    local_parts, local_image = section.Hamiltonian_action(jet)
    for name in ('coframe', 'scalar', 'gauge'):
        state_grade(local_parts[name], 2, occupation_grade(charged))
    assert {occupation_grade(word) for word in local_image} <= {occupation_grade(charged), occupation_grade(charged)+1}
    return {'actual_complete103_jet_input': list(incoming),
        'all4_energy_components_nonzero': True, 'full_H0_action': encode_state(diagonal),
        'full_Yukawa_action': encode_state(raising),
        'one_body_Y_square_zero_but_two_particle_Y_square_nonzero': encode_state(twice),
        'actual_Y_M0_Y_nonzero': encode_state(interleaved),
        'actual_Y_M0_Y_M0_Y_zero': True,
        'actual_local_Gauss_section': {'input': list(charged), **Gauss,
            'complete_Hamiltonian_action': encode_state(local_image),
            'all_output_grades_are_m_or_m_plus_one': True}}


def main():
    started = time.monotonic(); section = SourceQuantumGaussSection()
    coefficients = full_coefficients(section)
    print('PASS original full504 grading of all live coframe, native Gauss and70 Yukawa coefficients', flush=True)
    consumers = actual_consumers(section)
    print('PASS complete four-energy action, interleaved nonzero second word and actual Gauss section filtration', flush=True)
    names = ('source_quantum_grade_structure.py', 'FockFilteredWords.lean', 'FockFilteredWordsAudit.lean',
        'source_quantum_stabilizer.py', 'source_joint_local_quantum.py', 'source_quantum_gauss_section.py',
        'source_gauss_section_measure.py', 'source_common_hamiltonian.py', 'source_coframe_live_ordering.py')
    result = {'root': ROOT_ID, 'scope': 'COMPLETE_NATIVE_LOCAL_QUANTUM_HAMILTONIAN_OCCUPATION_FILTRATION',
        'input_sha256': {str((HERE/name).relative_to(ROOT)): hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in names},
        'coefficients': coefficients, 'actual_consumers': consumers,
        'operator_decomposition': 'H_native=H0+Y; [N,H0]=[N,Y]=0, [grade_Lambda6,H0]=0, [grade_Lambda6,Y]=Y on the common compact smooth103-coordinate domain',
        'local_reduction': 'Gauss extension, slice restriction and source half-density conjugation commute with grade; the same filtered decomposition descends to the actual100-coordinate local section',
        'finite_word_consequence': 'On particle number N, every ordered word with more than N Yukawa factors vanishes, with arbitrarily many grade-zero factors between them; all noncommuting boson factors retain their original order.',
        'formal_generic_consumer': 'FockFilteredWords.weighted_tensor_word_vanishes; source coefficient laws above instantiate grade0 and grade1 factors; finite sums distribute without commuting factors.',
        'scope_exclusions': 'No propagator for H0, temporal second-class quantum reduction, global quotient, spectral measure, pole or lifetime is inferred from the algebraic filtration.',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_quantum_grade_structure.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS complete source quantum occupation filtration', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
