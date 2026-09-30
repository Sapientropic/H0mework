#!/usr/bin/env python3
"""Full504 source form and its adjoint test domain, retaining the original Y.

The adjoint is a separate operator mouth. It is never substituted for the
original Yukawa term in the Hamiltonian. The shared compact domain supplies
the adjoint pair needed for the minimal closed graph, including the complement
of the source392 reducing carrier.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID, decode
from source_joint_form_hamiltonian import SourceJointFormHamiltonian, read_bound, complete_matter_adjoint
from source_scalar_form_hamiltonian import relocate_section
from source_quantum_grade_structure import matrix_grade, state_grade, occupation_grade
from source_coframe_legendre import rational
from source_lorentz_contact import clean, equal, encode, GAMMA
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state


def inner(left, right):
    return s.simplify(sum(s.conjugate(value)*right.get(word, 0) for word, value in left.items()))


def split_matter(data):
    original = clean(-s.I*data['e'].det()*data['matter']['inverse_E']*data['matter']['Y'])
    raising = clean(s.diag(original, -original.conjugate()))
    diagonal = clean(data['matter_CAR']-raising)
    equal(diagonal.H, diagonal)
    matrix_grade(diagonal, 0); matrix_grade(raising, 1); matrix_grade(raising.H, -1)
    return diagonal, raising


def complete_action(model, data, jet):
    """Actual H, H0 and Hsharp on the same full504 CAR-valued Gauss jet."""
    diagonal, Y = split_matter(data)
    pieces, original = model.action(data, jet)
    value = {w: item['value'] for w, item in jet.items() if item['value']}
    raising = apply_superposition(Y, value)
    lowering = apply_superposition(Y.H, value)
    grade_zero = weighted_sum([(1, original), (-1, raising)])
    adjoint = weighted_sum([(1, grade_zero), (1, lowering)])
    return {'components': pieces, 'H': original, 'H0': grade_zero,
            'Y': raising, 'Ysharp': lowering, 'Hsharp': adjoint}


def main():
    started = time.monotonic()
    shared = read_bound('source_joint_form_hamiltonian')
    grade = json.loads((HERE/'source_quantum_grade_structure.json').read_text())
    assert grade['root'] == ROOT_ID
    for path, digest in grade['input_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    read_bound('source_yukawa_reducing_carrier')
    m = SourceJointFormHamiltonian(); section = m.section; c = m.coframe
    matter = complete_matter_adjoint(m)
    ports = c.model.lorentz.raw_matter_ports(c.e)
    prefactor = rational(-s.I*c.e.det()*ports['E'].inv())
    equal(prefactor, c.N*GAMMA[0])
    coefficients = []
    canonical_spin = s.SparseMatrix(s.kronecker_product(c.N*GAMMA[0], s.eye(63)))
    for Yraw in m.native.graph.common.yukawa_basis:
        for factor in (s.S.One, s.I):
            Y = clean(canonical_spin*s.SparseMatrix(Yraw)*factor)
            Y = clean(s.diag(Y, -Y.conjugate()))
            matrix_grade(Y, 1); matrix_grade(Y.H, -1)
            equal(Y*m.P, s.zeros(504)); equal(Y.H*m.P, s.zeros(504))
            coefficients.append(Y)
    assert len(coefficients) == 70
    # These scalar number-sector weights commute with every actual Y. Since
    # Y contains no boson derivative, no density derivative occurs in its adjoint.
    print('PASS full504 Hermitian H0 matter and all70 original raising/lowering adjoint coefficients', flush=True)
    actual = shared['actual_consumer']
    q = tuple(map(s.sympify, actual['q'])); x = decode(actual['x61']); A = decode(actual['A36'])
    A[0, 2] += s.Rational(1, 17); A[1, 7] += s.Rational(1, 19)
    point = s.Matrix(q).col_join(x).col_join(A.reshape(36, 1))
    relocate_section(section, point)
    data = m.coefficients(q, x, A)
    M0, Y = split_matter(data)
    equal(Y*Y, s.zeros(504))
    column = next(j for j in range(252) if Y[:, j].todok())
    word = (column, column+252)
    assert occupation_grade(word) == 0 and any(m.P[i, i] == 0 for i in word)
    g = s.Matrix([s.I*s.Rational(j % 5-2, 47) for j in range(100)])
    u = s.Matrix([s.Rational(j % 3-1, 43) for j in range(100)])
    H = u*u.T-s.eye(100)
    jet = section.extend_jet({word: 1}, {word: g}, {word: H})
    gauss = section.verify_Gauss_jet(jet)
    output = complete_action(m, data, jet)
    assert all(output['components'].values())
    assert output['Y'] and not output['Ysharp']
    state_grade(output['H0'], 2, 0); state_grade(output['Y'], 2, 1)
    assert weighted_sum([(1, output['H']), (-1, output['Hsharp'])]) == output['Y']
    assert any(any(m.P[i, i] == 0 for i in w) for w in output['H'])
    twice = apply_superposition(Y, output['Y']); thrice = apply_superposition(Y, twice)
    assert twice and not thrice
    state_grade(twice, 2, 2)
    interleaved = apply_superposition(Y, apply_superposition(M0, output['Y']))
    assert interleaved and not apply_superposition(Y, apply_superposition(M0, interleaved))
    print('PASS full504 complement actual Gauss jet, four energies and nonzero grade1/grade2 outputs', flush=True)
    v = s.prod(q[j] for j in (0, 2, 5)); density = 8*A[0, 1]**2*A[1, 0]*v**4
    unit = {word: s.S.One}; raised = output['Y']
    norm2 = s.simplify(density*inner(raised, raised)); assert norm2 > 0
    adjoint_readback = s.simplify(density*inner(apply_superposition(Y.H, raised), unit))
    assert s.simplify(norm2-adjoint_readback) == 0
    reverse = s.simplify(density*inner(apply_superposition(Y, raised), unit)); assert reverse == 0
    source_support = sorted({i for w in output['H'] for i in w})
    paths = [HERE/name for name in ('source_full_quantum_adjoint.py', 'source_joint_form_hamiltonian.py',
        'source_joint_form_hamiltonian.json', 'source_quantum_grade_structure.py', 'source_quantum_grade_structure.json',
        'source_yukawa_reducing_carrier.json', 'source_scalar_form_hamiltonian.json', 'source_quantum_gauss_section.py')]
    result = {'root': ROOT_ID, 'scope': 'FULL504_ORIGINAL_YUKAWA_FORM_AND_COMMON_DENSE_ADJOINT_DOMAIN',
        'source_sha256': m.native.graph.common.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_H0': 'Original coframe+specified scalar kinetic form+original gauge+nonY matter, on the whole CAR504. Each component is symmetric for rho3*v^(2+Number); no392 projection is needed for H0.',
        'matter_adjoint': matter, 'generic_Yukawa_prefactor': encode(prefactor),
        'all70_original_Y_raise_and_adjoint_lower': True,
        'source_operator_and_adjoint': 'H=H0+Y, Hsharp=H0+Ydagger on the same Cc-infinity(Omega100) tensor Fock(C504). Y is the original n*gamma0 Yukawa matrix at n=N, not (Y+Ydagger).',
        'density_adjoint': 'Y preserves Number and has no boson derivatives; the source metric is scalar on each number sector. Thus the weighted adjoint is exactly dGamma(Ydagger), with no v factor.',
        'common_domain': 'All original coefficients and inverseD9 are smooth on the source chart. H and Hsharp preserve compact support and the residual3 equivariant section. This domain is dense in the source positive L2 pairing, and integration by parts gives <Hf,g>=<f,Hsharp g>.',
        'graph_closure_consumer': 'If f_n tends to0 and H f_n tends to h, pairing with every compact smooth g gives <h,g>=lim <f_n,Hsharp g>=0. Density forces h=0. The graph closure therefore defines the unique minimal closed extension of this specified source H, retaining all504 modes. This argument does not supply self-adjointness, a nonempty resolvent or a spectral measure.',
        'actual_complete_consumer': {'q': list(map(str, q)), 'x61': encode(x), 'A36': encode(A),
            'input_CAR': list(word), 'input_outside392': True,
            'gradient100': encode(g), 'Hessian100': encode(H), 'Gauss': gauss,
            'all_four_component_images': {k: encode_state(val) for k, val in output['components'].items()},
            'H': encode_state(output['H']), 'H0': encode_state(output['H0']),
            'Y': encode_state(raised), 'Hsharp': encode_state(output['Hsharp']),
            'Y_squared_Fock': encode_state(twice), 'Y_M0_Y': encode_state(interleaved),
            'third_raise_vanishes': not thrice, 'whole_output_CAR_support': source_support},
        'actual_pairing_consumer': {'positive_density_at_point': str(density), 'Y_pairing_norm_squared': str(norm2),
            'adjoint_readback': str(adjoint_readback), 'original_reverse_pairing': str(reverse),
            'compact_domain_argument': 'Choose a compact smooth Gauss section f of grade0 with the displayed nonzero value; g=Yf has grade1 and is in the same domain. H0 preserves grade, so <g,Hf>=integral rho3*v^4*|Yf|^2>0 and <Hg,f>=0. Hsharp supplies the exact opposite-slot adjoint, rather than changing H.'},
        'preserved_392_restriction': 'All70 Y and Ydagger annihilate K392 and the full source reduces it; the previously signed symmetric restriction is unchanged.',
        'formal_grade_consumer': 'FockFilteredWords.weighted_tensor_word_vanishes: each new scalar adjoint correction contains only original grade0 currents, so all ordered words with more than N original Y factors still vanish on particle number N. Diagonal resolvents or propagators are not premises of a claimed existence theorem.',
        'time_scope': shared['time_scope'], 'selfadjoint_or_quantum_spectrum_Gamma_tau_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_full_quantum_adjoint.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source full quantum adjoint domain', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
