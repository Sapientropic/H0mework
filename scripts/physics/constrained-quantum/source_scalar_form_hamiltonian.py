#!/usr/bin/env python3
"""Source scalar kinetic form on the actual second-class momentum graph.

The graph and classical symbol are unchanged. Polarizing the original scalar
contraction on the canonical pairing puts the generated formal adjoint on its
left factor. This is a specified form realization, not an identification with
the earlier coefficient-left square or with a twelve-dimensional gauge quotient.
"""
from __future__ import annotations

import hashlib
import json
import time
from functools import lru_cache

import sympy as s
from dynamic import HERE, ROOT, ROOT_ID
from source_lorentz_contact import clean, equal, encode
from source_coframe_legendre import rational
from source_quantum_gauss_section import SourceQuantumGaussSection, linear_matrices, zero
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state


def relocate_section(section, point):
    """The same residual3 slice at an actual new point, with all inverse jets."""
    equal(section.Ip.T*point, section.Ip.T*section.b0)
    section.b0 = point
    section.A0 = point[67:, :].reshape(3, 12)
    section.V = clean(s.Matrix.hstack(*(L*point for L in section.L)))
    section.M = clean(section.Ip.T*section.V)
    section.alpha = rational(section.M.inv()*section.Ip.T)
    section.z = rational(section.If.T*(s.eye(103)-section.V*section.alpha))
    forward = section.V.row_join(section.If)
    inverse = section.alpha.col_join(section.z)
    equal(forward*inverse, s.eye(103)); equal(inverse*forward, s.eye(103))
    curvature = [s.zeros(103) for _ in range(103)]
    for a in range(3):
        row = section.alpha[a, :]
        mixed = clean(section.L[a]*section.If*section.z)
        for k in range(103):
            if mixed[k, :].todok():
                curvature[k] += row.T*mixed[k, :]+mixed[k, :].T*row
        for b in range(3):
            acceleration = clean((section.L[a]*section.L[b]+section.L[b]*section.L[a])*point/2)
            for (k, _), value in acceleration.todok().items():
                curvature[k] += value*row.T*section.alpha[b, :]
    curvature = [rational(H) for H in curvature]
    section.forward_curvature = curvature
    section.alpha2 = [-linear_matrices(curvature, section.alpha[a, :], (103, 103)) for a in range(3)]
    section.z2 = [-linear_matrices(curvature, section.z[j, :], (103, 103)) for j in range(100)]
    for k in range(103):
        zero(linear_matrices(section.alpha2+section.z2, forward[k, :], (103, 103))+curvature[k])


class SourceScalarFormHamiltonian:
    def __init__(self):
        self.section = SourceQuantumGaussSection()
        self.native = self.section.native
        self.scalar = self.native.scalar
        self.graph = self.native.graph
        for Q in self.scalar.Q:
            equal(Q.H, Q)
        for T in self.scalar.T:
            assert s.trace(T) == 0

    @lru_cache(maxsize=None)
    def current_word(self, a, word):
        return apply_superposition(self.scalar.Q[a], {word: 1})

    def current(self, a, state):
        return weighted_sum((v, self.current_word(a, w)) for w, v in state.items())

    def coefficients(self, e, x, A):
        d = self.scalar.coefficients(e, x, A)
        # F depends only on x; all original scalar/gauge linear currents have
        # zero divergence. This traces the actual inverse derivative, not a
        # supplied density or a proposed adjoint coefficient.
        divergence = rational(-self.graph.O*sum((d['directional_F'][a][:, a]
            for a in range(9)), s.zeros(9, 1)))
        derivative = rational(d['momentum_vectors'].T*divergence)
        current = rational(-d['normal_embedding'].T*divergence)
        shift = s.cancel((divergence.T*d['shift'])[0])
        return {**d, 'divergence': divergence, 'adjoint_derivative': derivative,
                'adjoint_current': current, 'adjoint_shift': shift}

    def verify_coordinate_divergence(self, data):
        """Direct coordinate trace, independent of the nine current directions."""
        result = s.zeros(70, 1)
        F = data['F']
        for u in range(61):
            dD = clean(self.graph.O.T*s.Matrix.hstack(
                *(T*self.graph.R[:, u] for T in self.native.rho_b)))
            dF = rational(-F*dD.T*F)
            result -= self.graph.O*dF*data['vectors'][:, u]
        # The remaining trace is exactly trace(T_b)=0, including all36 A.
        equal(rational(result), data['divergence'])

    def correction(self, data, value, gradient):
        h = data['h00']
        terms = [(s.I*data['adjoint_shift']/(2*h), value)]
        for word, g in gradient.items():
            terms.append((-(data['adjoint_derivative'].T*g)[0]/(2*h), {word: 1}))
        for a in range(9):
            terms.append((-s.I*data['adjoint_current'][a]/(2*h), self.current(a, value)))
        return weighted_sum(terms)

    def old_square(self, data, value, gradient, Hessian):
        """The paid original expanded70-square, on complete CAR-valued jets.

        At the fixed time-column the scalar shift is zero. Contraction before
        CAR action preserves all97 mixed derivatives without repeatedly
        rebuilding the same large one-body matrices for every scalar port.
        """
        zero(data['shift'])
        V, K, linear = data['vectors'], data['quadratic'], data['linear']
        principal = rational(V.T*K*V)
        principal[:61, :61] += self.scalar.peripheral_inverse_gram/(2*data['h00'])
        transport = rational(-sum((K[a, b]*self.scalar.T[b]*V[a, :].T
            for a, b in K.todok()), s.zeros(97, 1))-s.I*V.T*linear.T)
        mixed = rational(-2*s.I*V.T*K)
        terms = [(data['spatial_potential'], value)]
        for word in set(gradient)|set(Hessian):
            g = gradient.get(word, s.zeros(97, 1))
            H = Hessian.get(word, s.zeros(97))
            scalar = -sum(v*H[i, j] for (i, j), v in principal.todok().items())+(transport.T*g)[0]
            terms.append((scalar, {word: 1}))
            for a in range(9):
                terms.append(((mixed[:, a].T*g)[0], self.current_word(a, word)))
        for a in range(9):
            terms.append((linear[a], self.current(a, value)))
            for b in range(9):
                if K[a, b]: terms.append((K[a, b], self.current(a, self.current(b, value))))
        return weighted_sum(terms)

    def action(self, data, value, gradient, Hessian):
        return weighted_sum([(1, self.old_square(data, value, gradient, Hessian)),
                             (1, self.correction(data, value, gradient))])


def main():
    started = time.monotonic(); m = SourceScalarFormHamiltonian()
    measure = json.loads((HERE/'source_full_gauss_section.json').read_text())
    assert measure['root'] == ROOT_ID
    for group in ('source_sha256', 'input_sha256'):
        for name, digest in measure[group].items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    for name in ('source_second_class_measure', 'live_second_class_measure'):
        assert measure[name]['measure_cancellation'] == '1'
        assert measure[name]['both_inverse_identities_and_unit_triangular_factor_checked']
    section = m.section
    e = section.e0
    original_point = section.b0.copy()
    source = m.coefficients(e, s.zeros(61, 1), section.A0)
    zero(source['divergence'])
    x = s.Matrix([s.Rational((3*j+1) % 7-3, 100) for j in range(61)])
    data = m.coefficients(e, x, section.A0)
    m.verify_coordinate_divergence(data)
    assert data['divergence'].todok() and data['adjoint_derivative'].todok()
    print('PASS original scalar graph formal-adjoint coefficients and full61 direct inverse derivative trace', flush=True)
    word = (7, 8)
    g = s.Matrix([s.I*s.Rational(j % 5-2, 47) for j in range(97)])
    u = s.Matrix([s.Rational(j % 3-1, 43) for j in range(97)])
    H = u*u.T-s.eye(97)
    old = m.native.joint.scalar_action({'scalar': data}, word, g, H)
    equal_old = m.old_square(data, {word: 1}, {word: g}, {word: H})
    assert weighted_sum([(1, old), (-1, equal_old)]) == {}
    correction = m.correction(data, {word: 1}, {word: g})
    assert correction
    print('PASS complete original70 nested-square versus efficient97 expansion and nonzero form correction', flush=True)
    point = original_point.copy(); point[6:67, :] = x
    relocate_section(section, point)
    # Select an actual transverse derivative paid by the newly generated
    # scalar correction. No gauge-compatible wavepacket is a premise.
    tangent = rational(section.z[:, 6:]*data['adjoint_derivative'])
    direction = next(i for i in range(100) if tangent[i] != 0)
    dg = s.zeros(100, 1); dg[direction] = s.I
    jet = section.extend_jet({word: 1}, {word: dg}, {word: s.zeros(100)})
    gauss = section.verify_Gauss_jet(jet)
    values = {w: j['value'] for w, j in jet.items() if j['value']}
    gradients = {w: j['gradient'][6:, :] for w, j in jet.items()}
    Hessians = {w: j['Hessian'][6:, 6:] for w, j in jet.items()}
    restricted_correction = m.correction(data, values, gradients)
    assert restricted_correction
    old_image = m.old_square(data, values, gradients, Hessians)
    new_image = m.action(data, values, gradients, Hessians)
    assert weighted_sum([(1, new_image), (-1, old_image), (-1, restricted_correction)]) == {}
    print('PASS actual residual3 full Gauss section and nonzero complete scalar form action', flush=True)
    paths = [HERE/name for name in ('source_scalar_form_hamiltonian.py', 'source_scalar_shift_quantum.py',
        'source_gauss_live_ordering.py', 'source_quantum_stabilizer.py', 'source_quantum_stabilizer.json',
        'source_quantum_gauss_section.py', 'source_gauss_section_measure.json',
        'source_reducing_coframe_metric.json', 'source_constraint_preservation.py',
        'source_full_gauss_section.py', 'source_full_gauss_section.json')]
    result = {'root': ROOT_ID, 'source_sha256': m.graph.common.scalar.exchange.vertices['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'scope': 'SOURCE_SCALAR_KINETIC_FORM_ON_ORIGINAL_SECOND_CLASS_GRAPH_AND_RESIDUAL3_SECTION',
        'original_graph': 'Pi_j=-i a_j.partial+c_j-b_j; a=Rdual-O D^-T V; c=-O D^-T Q. The original graph is not replaced.',
        'source_generated_adjoint': 'Pi_j^dagger=Pi_j-i div(a_j); Q_b are Hermitian, all original linear scalar/gauge vector fields have trace0, F=D^-T depends only on x.',
        'source_form': 'q(f,g)=Integral sum_j inner(Pi_j f,Pi_j g)/(2h00)+inner(f,V_original g) in the canonical103 pairing, optionally with the already generated coframe Number metric.',
        'original_second_class_measure': {'source_and_live_Dirac_cancellation': '1',
            'canonical_phase_measure': measure['source_second_class_measure']['canonical_phase_measure'],
            'residual3_pairing': 'The existing103 configuration pairing and its source residual3 rho are consumed; the full12 geometric Jacobian is not substituted for the actual Dirac reduction.'},
        'form_representative': 'Hform=sum_j Pi_j^dagger Pi_j/(2h00)+V_original; the original sign of h00 is retained.',
        'ordering_difference': 'Hform-Hold=-i sum_j div(a_j) Pi_j/(2h00). The two operators have the same original classical quadratic symbol, but are not identified as quantum operators.',
        'all_original_current_matrices_Hermitian': True, 'all_original_linear_vectors_divergence_zero': True,
        'original_source_point_correction_zero': True,
        'actual_off_source': {'scalar': encode(x), 'divergence70': encode(data['divergence']),
            'derivative97': encode(data['adjoint_derivative']), 'current9': encode(data['adjoint_current']),
            'all61_coordinate_inverse_derivatives_checked': True,
            'full70_old_square_equals_full97_expansion': True, 'N2_plain_correction': encode_state(correction)},
        'actual_residual3_consumer': {'input': list(word), 'transverse_derivative': direction,
            'whole_Gauss_jet': gauss, 'old_action': encode_state(old_image), 'new_form_action': encode_state(new_image),
            'nonzero_ordering_difference': encode_state(restricted_correction),
            'zero_value_nonzero_derivative_words_retained': True},
        'formal_symmetry_argument': 'The original real h00 depends only on q, not on the97 derivative coordinates. Compact support and the explicitly generated divergences give the stated formal adjoints by integration by parts. Polarization with these adjoints is Hermitian. Native residual3 acts unitarily and rotates the complete70 momenta orthogonally, so the same form descends through its actual equivariant section to rho3; no broken9 first-class quotient is assumed.',
        'uniqueness_scope': 'Unique differential representative of the displayed sesquilinear form and pairing, not a claim of unique quantization of a classical symbol.',
        'energy_sign': 'No positive-energy claim: original h00 and potential signs are unchanged.',
        'closed_operator_evolution_spectrum_or_lifetime_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_scalar_form_hamiltonian.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source scalar form Hamiltonian', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
