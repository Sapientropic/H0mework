#!/usr/bin/env python3
"""Raw-source audit of the full504 H0 antiunitary and its complete Gauss jet.

The candidate is not imported. Original Dirac matrices, Kronecker current
tensors and determinant exterior powers supply a separate coefficient and
CAR algorithm; raw differential actions test the actual source section.
"""
from __future__ import annotations

from functools import lru_cache
import hashlib
import json
from pathlib import Path
import time

import sympy as s

from independent_source_joint_form_hamiltonian import (
    RawGaussSection, RawLiveCoefficients, HERE, ROOT, ROOT_ID, bindings,
    rational, eq, decode, encode, terms, current, state_encode, decoded_state,
    zero, state_equal, build_operators, whole_action, raw_gauge_coefficients,
    original_kernel)
from independent_source_quantum_gauss_section import compound
from independent_source_full_quantum_adjoint import sparse, dual_pair, inner
from independent_source_gauge_legendre import ETA


class RawAntiunitary:
    def __init__(self, gamma0):
        self.spin = sparse(s.kronecker_product(s.Matrix([[0, 1], [1, 0]]), gamma0))
        self.U = sparse(s.kronecker_product(self.spin, s.eye(63)))
        eq(self.spin.H*self.spin, s.eye(8))
        eq(self.spin*self.spin.conjugate(), -s.eye(8))
        eq(self.U.H*self.U, s.eye(504)); eq(self.U*self.U.H, s.eye(504))
        eq(self.U*self.U.conjugate(), -s.eye(504))
        self.destination = {}
        for (i, j), coefficient in self.U.todok().items():
            assert j not in self.destination and coefficient in (-1, 1)
            assert i % 63 == j % 63
            self.destination[j] = i
        assert len(set(self.destination.values())) == 504

    @lru_cache(None)
    def wedge(self, word):
        """The actual exterior minor, without a permutation-parity formula."""
        rows = tuple(sorted(self.destination[j] for j in word))
        coefficient = self.U.extract(rows, word).det()
        assert coefficient in (-1, 1)
        return rows, coefficient

    def state(self, values):
        return terms((coefficient*s.conjugate(value), {row: 1})
                     for word, value in values.items()
                     for row, coefficient in (self.wedge(tuple(word)),))

    def jet(self, values):
        result = {}
        for word, (value, gradient, Hessian) in values.items():
            row, coefficient = self.wedge(tuple(word))
            assert row not in result
            result[row] = (coefficient*s.conjugate(value),
                           coefficient*gradient.conjugate(), coefficient*Hessian.conjugate())
        return result


def generic_coefficients(raw, section, inventory, C):
    U = C.spin; q = raw.q
    eq(raw.K.conjugate(), raw.K)
    scalar_drift = rational(-s.I*raw.drift)
    eq(scalar_drift.conjugate(), scalar_drift)
    for M in raw.M:
        Mh = rational((M+M.H)/2)
        eq(U*Mh.conjugate()*U.H, -Mh)
        # This is the original mixed coefficient before half-density
        # conjugation, so the actual coordinate action is covered too.
        eq(U*M.conjugate()*U.H, -M)
    constants = []
    for constant in (raw.one_body, raw.correction):
        eq(U*constant.conjugate()*U.H, constant)
        constants.append(len(constant.todok()))
    tensor = rational(sum((value*s.kronecker_product(raw.J[a], raw.J[b])
                           for (a, b), value in raw.W.todok().items()), s.zeros(64)))
    U2 = sparse(s.kronecker_product(U, U))
    eq(U2*tensor.conjugate()*U2.H, tensor)
    for Q in section.native.Qb+section.native.Qs:
        eq(C.U*Q.conjugate()*C.U.H, -Q)
    for R in section.r: eq(C.U*R.conjugate()*C.U.H, R)
    K = [sparse(sum((section.native.S[a, h]*section.native.fund[a]
                    for a in range(12)), s.zeros(7))) for h in range(3)]
    active = -K[0]*K[0]
    for quaternion in ((s.Rational(3, 5), s.Rational(4, 5), 0, 0), (-1, 0, 0, 0)):
        group = sparse(s.eye(7)-active+quaternion[0]*active+
                       sum((quaternion[i+1]*K[i] for i in range(3)), s.zeros(7)))
        eq(group.H*group, s.eye(7))
        internal = s.diag(*(compound(group, d) for d in inventory['degrees']))
        matter = sparse(s.kronecker_product(s.eye(4), internal))
        full = sparse(s.diag(matter, matter.conjugate()))
        eq(C.U*full.conjugate()*C.U.H, full)
    metric = rational(raw.e.det()*(raw.e.T*ETA*raw.e).inv())
    eq(metric[0, 1:], s.zeros(1, 3)); eq(metric.conjugate(), metric)
    for real_map in [section.native.R, section.native.Rd, section.native.O,
                     *section.native.rho, *section.native.Tb, *section.native.Ts]:
        eq(real_map.conjugate(), real_map)
    A = s.Matrix(3, 12, s.symbols('antiunitary_A0:36', real=True))
    gauge = raw_gauge_coefficients(raw.e, A, section.native)
    eq(gauge['shift'], s.zeros(36, 1))
    eq(gauge['weight'].conjugate(), gauge['weight'])
    zero(s.im(gauge['potential']))
    inverse = raw.e.inv(); volume = raw.e.det(); gamma = inventory['gamma']
    principals = [rational(s.I*volume*sum((inverse[mu, a]*gamma[a]
                   for a in range(4)), s.zeros(4))) for mu in range(4)]
    E_inverse, free = principals[0].gauss_jordan_solve(s.eye(4)); assert free.rows == 0
    spin = [rational(-s.I*E_inverse*principals[i]) for i in (1, 2, 3)]
    for S in spin: eq(gamma[0]*S*gamma[0].H, -S)
    return {'generic_live_sixq_original_K_and_scalar_drift_real': True,
        'all6_original_and_Hermitian_mixed_coefficients_anti_invariant': True,
        'separate_onebody_and_live_correction_nonzero_counts': constants,
        'complete_normal_product_Kronecker_tensor_entries': len(tensor.todok()),
        'all64_by64_normal_product_tensor_intertwines': True,
        'all9_broken_and3_residual_currents_change_sign': True,
        'original_residual_generators_and_two_full_exterior_group_elements_fixed': True,
        'all_real_scalar_graph_maps_and_generic_zero_shift_verified': True,
        'original_generic_gauge_shift_zero_and_weight_potential_real': True,
        'original_three_matter_spin_coefficients': [encode(S) for S in spin],
        'generic_Pi_rule': 'C Pi_j C^-1=-Pi_j and C Pi_j^dagger C^-1=-Pi_j^dagger. The real graph has zero shift at fixed source time, and every full504 Hermitian current changes sign. Thus the specified sum Pi-dagger Pi and original real potential are invariant.'}


def main():
    started = time.monotonic(); path = HERE/'source_quantum_antiunitary.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    names = ('source_full_quantum_adjoint', 'independent_source_full_quantum_adjoint',
             'source_yukawa_reducing_carrier', 'independent_source_yukawa_reducing_carrier',
             'independent_source_joint_form_hamiltonian', 'independent_source_scalar_form_hamiltonian',
             'independent_source_reducing_coframe_metric')
    records = {}
    for name in names:
        records[name] = json.loads((HERE/(name+'.json')).read_text())
        count += bindings(records[name]); assert records[name]['root'] == ROOT_ID
    section = RawGaussSection(); raw = RawLiveCoefficients()
    assert section.native.hashes == candidate['source_sha256']
    inventory, Ys, _, P, _, _ = original_kernel(records['source_yukawa_reducing_carrier'])
    C = RawAntiunitary(inventory['gamma'][0])
    eq(C.spin, decode(candidate['spin8_matrix']))
    eq(C.U, decode(candidate['one_particle_CAR504_matrix']))
    generic = generic_coefficients(raw, section, inventory, C)
    print('PASS independent original antiunitary and complete generic H0 coefficient intertwiners', flush=True)

    source = records['source_full_quantum_adjoint']['actual_complete_consumer']
    saved = candidate['actual_consumer']
    q = tuple(map(s.sympify, source['q'])); x, A = decode(source['x61']), decode(source['A36'])
    point = s.Matrix(q).col_join(x).col_join(A.reshape(36, 1))
    data = build_operators(section, raw, q, x, A)
    Y = dual_pair(sum((data['scalar']['phi'][j]*Ys[j] for j in range(70)), s.zeros(252)))
    M0 = sparse(data['matter']-Y)
    eq(C.U*M0.conjugate()*C.U.H, M0)
    Y_defect = sparse(C.U*Y.conjugate()*C.U.H-Y); assert Y_defect.todok()
    fullP = sparse(s.diag(P, P.conjugate()))
    P_defect = sparse(C.U*fullP.conjugate()*C.U.H-fullP); assert P_defect.todok()
    word = tuple(source['input_CAR']); unit = {word: s.S.One}
    assert word == tuple(saved['input_CAR'])
    gradient, Hessian = decode(source['gradient100']), decode(source['Hessian100'])
    _, jets = section.extension_jet(point, unit, {word: gradient}, {word: Hessian})
    section.Gauss_checks(point, jets)
    Cword, sign = C.wedge(word)
    assert Cword == tuple(saved['C_input_CAR']) and sign == s.sympify(saved['C_input_coefficient'])
    changed = C.jet(jets)
    _, rebuilt = section.extension_jet(point, C.state(unit),
        {Cword: sign*gradient.conjugate()}, {Cword: sign*Hessian.conjugate()})
    assert set(rebuilt) == set(changed)
    for w in rebuilt:
        zero(rebuilt[w][0]-changed[w][0])
        eq(rebuilt[w][1], changed[w][1]); eq(rebuilt[w][2], changed[w][2])
    gauss = section.Gauss_checks(point, changed)
    original_pieces, H = whole_action(data, jets)
    original_H0 = terms([(1, H), (-1, current(Y, unit))])
    state_equal(original_H0, decoded_state(source['H0']))
    pieces, image = whole_action(data, changed)
    H0_C = terms([(1, image), (-1, current(Y, C.state(unit)))])
    expected = C.state(original_H0)
    state_equal(H0_C, expected)
    assert all(pieces.values())
    for name, component in pieces.items():
        state_equal(component, decoded_state(saved['all_four_C_input_images'][name]))
    state_equal(H0_C, decoded_state(saved['H0_C_input_image']))
    state_equal(expected, decoded_state(saved['C_H0_input_image']))
    for j in range(504): state_equal(C.state(C.state({(j,): 1})), {(j,): -1})
    state_equal(C.state(C.state({(): 1})), {(): 1})
    for value in (unit, original_H0, C.state(unit)):
        state_equal(C.state(C.state(value)), value)
    number_mixed = terms([(1+s.I, unit), (2-s.I, original_H0)])
    zero(inner(C.state(number_mixed), C.state(original_H0))-
         s.conjugate(inner(number_mixed, original_H0)))
    density = s.sympify(records['independent_source_full_quantum_adjoint']['positive_pairing']['density_on_N2'])
    assert density > 0 and s.conjugate(density) == density
    whole_H_defect = terms([(1, image), (-1, C.state(H))]); assert whole_H_defect
    state_equal(whole_H_defect, terms([(1, current(Y, C.state(unit))), (-1, C.state(current(Y, unit)))]))
    print('PASS determinant-CAR Gauss two-jet, complete actual H0 image and original Y/carrier countercontrols', flush=True)

    paths = [Path(__file__), path, HERE/'source_quantum_antiunitary.py',
             HERE/'independent_source_joint_form_hamiltonian.py', HERE/'independent_source_full_quantum_adjoint.py',
             HERE/'independent_source_quantum_gauss_section.py', HERE/'independent_source_common_hamiltonian.py',
             HERE/'independent_source_coframe_live_ordering.py']+[HERE/(name+'.json') for name in names]
    result = {'verdict': 'CERTIFIED_ORIGINAL_FULL504_H0_ANTIUNITARY_AND_COMPLETE_GAUSS_INTERTWINER',
        'root': ROOT_ID, 'source_sha256': section.native.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks': count, 'candidate_constructor_imported': False,
        'independent_method': 'Original Clifford gamma0 and independent-dual exchange; raw epsilon/coframe and BF coefficients; full Kronecker normal-product tensor; determinant exterior minors; implicit Gauss two-jets and raw four-component differential action.',
        'spin8_matrix': encode(C.spin), 'generic_full_H0_intertwiners': generic,
        'Fock_antiunitarity': 'U is unitary, preserves each internal exterior label, and U conjugate(U)=-I504. Determinant exterior powers give C=Gamma(U) conjugation, conjugate the full positive number-sector pairing and square to (-1)^Number. All504 N1 basis vectors, vacuum and the actual complete N2 images are checked directly.',
        'actual_consumer': {'input_CAR': list(word), 'C_input_CAR': list(Cword), 'C_input_coefficient': str(sign),
            'Gauss': gauss, 'all103_twojet_coefficients_commute_with_C': True,
            'all_four_nonzero_C_input_images': {name: state_encode(value) for name, value in pieces.items()},
            'H0_C_input_image': state_encode(H0_C), 'C_H0_input_image': state_encode(expected),
            'actual_weighted_pairing_conjugated': True, 'N2_square_identity': True},
        'source_countercontrols': {'actual_Y_matrix_intertwining_defect': encode(Y_defect),
            'same_392_projection_defect': encode(P_defect),
            'actual_whole_H_C_minus_C_H': state_encode(whole_H_defect),
            'scope': 'The new C acts on H0 on all504 modes. It neither intertwines the original complete H=H0+Y nor preserves its selected392 reducing carrier.'},
        'domain_consumer': 'C fixes all boson coordinates and compact support, is an isometry for the same real positive number-sector weight, and commutes with the residual3 extension. Thus it preserves the H0 test graph and its closure; the corresponding adjoint test equations exchange z and conjugate(z). No particular self-adjoint extension is selected here.',
        'scope': 'Literal source time column with zero scalar and gauge shifts, complete local H0 from the specified scalar form. The original Y and the392 restriction remain distinct consumers. No full-H antiunitary symmetry, quantum spectrum or lifetime is generated.',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'independent_source_quantum_antiunitary.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent source quantum antiunitary', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
