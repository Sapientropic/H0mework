#!/usr/bin/env python3
"""An original-Dirac antiunitary of the complete source H0 test action.

H0 is the full504 symmetric part of the specified source form realization.
The original Yukawa term is retained separately; neither its symmetry nor a
choice of self-adjoint extension is inferred from this intertwiner.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID, decode
from source_joint_form_hamiltonian import SourceJointFormHamiltonian, read_bound
from source_scalar_form_hamiltonian import relocate_section
from source_full_quantum_adjoint import complete_action, split_matter, inner
from source_coframe_legendre import rational
from source_lorentz_contact import clean, equal, encode, GAMMA, ETA
from source_gauss_quantum_current import weighted_sum, encode_state


class SourceQuantumAntiunitary:
    def __init__(self, model):
        self.model = model
        self.spin = s.SparseMatrix(s.BlockMatrix([[s.zeros(4), GAMMA[0]], [GAMMA[0], s.zeros(4)]]).as_explicit())
        equal(self.spin.H*self.spin, s.eye(8))
        equal(self.spin*self.spin.conjugate(), -s.eye(8))
        self.U = s.SparseMatrix(s.kronecker_product(self.spin, s.eye(63)))
        self.columns = {}
        for j in range(504):
            items = list(self.U[:, j].todok().items()); assert len(items) == 1
            (i, _), value = items[0]
            assert value in (-1, 1) and i % 63 == j % 63
            self.columns[j] = i, value

    def word(self, word):
        images = [self.columns[j][0] for j in word]
        sign = s.prod(self.columns[j][1] for j in word)
        sign *= (-1)**sum(images[i] > images[j] for i in range(len(word)) for j in range(i+1, len(word)))
        return tuple(sorted(images)), sign

    def state(self, state):
        return weighted_sum((sign*s.conjugate(value), {image: 1})
            for word, value in state.items() for image, sign in (self.word(word),))

    def jet(self, jet):
        return {self.word(w)[0]: {key: self.word(w)[1]*value.conjugate()
                                  for key, value in row.items()} for w, row in jet.items()}


def generic_coefficients(C):
    m, U = C.model, C.spin; cf = m.coframe
    for Mh in m.metric['hermitian']:
        equal(rational(U*Mh.conjugate()*U.H+Mh), s.zeros(8))
    constant = cf.one_body+cf.correction
    equal(rational(U*constant.conjugate()*U.H-constant), s.zeros(8))
    transformed = [rational(U*J.conjugate()*U.H) for J in cf.J]
    flat = s.Matrix.hstack(*(J.reshape(64, 1) for J in transformed))
    tensor = rational(flat*cf.W.conjugate()*flat.T)
    equal(rational(tensor-m.metric['tensor']), s.zeros(64))
    # Number, grade, all boson coordinates and the original source chart are
    # fixed. This transports every live real derivative coefficient too.
    for Q in m.native.Q_b+m.native.Q_s:
        equal(C.U*Q.conjugate()*C.U.H, -Q)
    for R in m.section.R:
        equal(C.U*R.conjugate()*C.U.H, R)
    for quaternion in ((s.Rational(3, 5), s.Rational(4, 5), 0, 0), (-1, 0, 0, 0)):
        group = m.section.matter_group(m.section.group(s.Matrix(quaternion)))
        equal(C.U*group.conjugate()*C.U.H, group)
    metric = rational(cf.e.det()*(cf.e.T*ETA*cf.e).inv())
    equal(metric[0, 1:], s.zeros(1, 3))
    gauge = m.native.joint.gauge.coefficients(cf.e)
    equal(gauge['momentum_shift'], s.zeros(36, 1))
    equal(gauge['weight'].conjugate(), gauge['weight'])
    assert s.expand(s.conjugate(gauge['magnetic_potential'])-gauge['magnetic_potential']) == 0
    ports = cf.model.lorentz.raw_matter_ports(cf.e)
    for i in range(1, 4):
        S = rational(-s.I*ports['E'].inv()*ports['oriented_principals'][i])
        equal(rational(GAMMA[0]*S*GAMMA[0].H+S), s.zeros(4))
    return {'whole_six_q_coframe_mixed_coefficients': True, 'complete64_normal_current_tensor': True,
        'coframe_onebody_and_live_correction': True, 'all9_broken_and3_stabilizer_currents': True,
        'actual_residual3_group_and_center': True, 'generic_scalar_real_graph_and_zero_shift': True,
        'generic_original_gauge_real_and_zero_shift': True, 'all3_original_gauge_matter_spin_factors': True}


def main():
    started = time.monotonic()
    source = read_bound('source_full_quantum_adjoint')
    read_bound('independent_source_full_quantum_adjoint')
    m = SourceJointFormHamiltonian(); C = SourceQuantumAntiunitary(m)
    facts = generic_coefficients(C)
    print('PASS original Dirac antiunitary and all full504 H0 coefficient identities', flush=True)
    row = source['actual_complete_consumer']
    q = tuple(map(s.sympify, row['q'])); x, A = decode(row['x61']), decode(row['A36'])
    point = s.Matrix(q).col_join(x).col_join(A.reshape(36, 1))
    relocate_section(m.section, point)
    data = m.coefficients(q, x, A); M0, Y = split_matter(data)
    equal(C.U*M0.conjugate()*C.U.H, M0)
    transformed_Y = clean(C.U*Y.conjugate()*C.U.H)
    assert clean(transformed_Y-Y).todok()
    # The original source392 restriction is kept; this additional symmetry
    # belongs to H0 on the full504 carrier, not to that selected restriction.
    assert clean(C.U*m.P.conjugate()*C.U.H-m.P).todok()
    word = tuple(row['input_CAR']); value = {word: s.S.One}
    g, H = decode(row['gradient100']), decode(row['Hessian100'])
    jet = m.section.extend_jet(value, {word: g}, {word: H})
    transformed_jet = C.jet(jet)
    gauss = m.section.verify_Gauss_jet(transformed_jet)
    image_word, sign = C.word(word)
    extended = m.section.extend_jet(C.state(value), {image_word: sign*g.conjugate()},
                                  {image_word: sign*H.conjugate()})
    assert set(extended) == set(transformed_jet)
    for w in extended:
        for key in ('gradient', 'Hessian'): equal(extended[w][key], transformed_jet[w][key])
        assert s.cancel(extended[w]['value']-transformed_jet[w]['value']) == 0
    actual = complete_action(m, data, transformed_jet)
    original_H0 = {tuple(w): s.sympify(v) for w, v in row['H0']}
    expected = C.state(original_H0)
    assert weighted_sum([(1, actual['H0']), (-1, expected)]) == {}
    assert all(actual['components'].values())
    for state in (value, original_H0, C.state(value)):
        assert weighted_sum([(1, C.state(C.state(state))), (-1, state)]) == {}
    for j in range(504):
        assert C.state(C.state({(j,): s.S.One})) == {(j,): -1}
    assert C.state(C.state({(): s.S.One})) == {(): 1}
    assert s.simplify(inner(C.state(value), C.state(original_H0))-s.conjugate(inner(value, original_H0))) == 0
    print('PASS full Gauss two-jet antiunitary intertwiner, complete H0 image and Fock parity square', flush=True)
    files = [HERE/n for n in ('source_quantum_antiunitary.py', 'source_full_quantum_adjoint.py',
        'source_full_quantum_adjoint.json', 'independent_source_full_quantum_adjoint.json',
        'source_joint_form_hamiltonian.py', 'source_reducing_coframe_metric.json', 'source_quantum_grade_structure.json')]
    result = {'root': ROOT_ID, 'scope': 'SOURCE_FULL504_H0_ANTIUNITARY_AND_DEFECT_CONJUGATION_ENTRY',
        'source_sha256': m.native.graph.common.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'spin8_matrix': encode(C.spin), 'one_particle_CAR504_matrix': encode(C.U),
        'antiunitary': 'C=Gamma(U) complex_conjugation, U=[[0,gamma0],[gamma0,0]] tensor I63, using the original independent-dual pairing and original Dirac gamma0.',
        'Fock_square': 'U*conj(U)=-I504, hence C^2=(-1)^Number on every exterior degree; the explicit signed monomial permutation generates the action on every CAR word.',
        'pairing': 'C fixes q,x,A and Number, so the positive rho3*v^(2+Number) pairing is conjugated exactly. Its source chart and compact support are fixed.',
        'complete_coefficient_identities': facts,
        'operator_intertwiner': 'H0 C=C H0 on the entire source Cc-infinity residual3 domain tensor CAR504. Scalar Pi transforms to -Pi and so does its formal adjoint; all real second-class coefficients are unchanged. Gauge shift is0 at the fixed source time column. The full coframe and original nonY matter identities are retained.',
        'actual_consumer': {'input_CAR': list(word), 'C_input_CAR': list(image_word), 'C_input_coefficient': str(sign),
            'Gauss': gauss, 'extension_commutes_through_all103_second_jets': True,
            'all_four_C_input_images': {k: encode_state(v) for k, v in actual['components'].items()},
            'H0_C_input_image': encode_state(actual['H0']), 'C_H0_input_image': encode_state(expected),
            'all504_one_particle_squares_minus_identity': True, 'actual_N2_square_identity': True},
        'closed_graph_and_defect_consumer': 'The continuous isometry C carries the H0 test graph onto itself, hence preserves its graph closure. On its adjoint test equations it sends the spectral parameter z to conjugate(z); in particular the +i and -i defect spaces are paired. This supplies a source symmetry for the subsequent domain/spectral construction, not a selected self-adjoint extension.',
        'original_Y_is_C_invariant': False, 'C_preserves_selected392_carrier': False,
        'scope_separation': 'The full original H=H0+Y and its392 reducing restriction retain their own domains. Neither a whole-H antiunitary symmetry nor a proton quantum number is inferred.',
        'time_scope': source['time_scope'], 'selfadjoint_extension_or_quantum_spectral_measure_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_quantum_antiunitary.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source quantum antiunitary', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
