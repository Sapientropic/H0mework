#!/usr/bin/env python3
"""Original odd canonical observables in the current common Hilbert pairing.

The source sector density U_m supplies the v^(-1/2) primal and v^(1/2)
canonical-dual factors. Their complete two-jets enter the same four-energy H.
The independent chi field is reconstructed through the original E inverse;
the background cotangent matrix is retained as a separate linear transporter.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
import hashlib
import json
import time

import sympy as s
from dynamic import HERE, BASE, ROOT, ROOT_ID, decode
from source_joint_ccr_car_ports import NormalSymbol, SourceJointCCRCarPorts, linear_car, simplified, same
from source_joint_current_hilbert_section import current_weyl_action
from source_joint_current_heisenberg import patch_symbolic_equal
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state
from source_common_phase_time import OriginalCanonicalPhase
from source_full_linear_split import real_pair, realify
from source_lorentz_contact import clean, equal, encode
from source_joint_form_hamiltonian import read_bound


@dataclass
class SourceGerm:
    value: dict
    gradient: dict
    Hessian: dict

    def words(self):
        return set(self.value)|set(self.gradient)|set(self.Hessian)


def add_states(*states):
    return simplified(weighted_sum(states))


def scalar_product_jet(germ, value, gradient, Hessian):
    values, gradients, Hessians = {}, {}, {}
    for word in germ.words():
        f = germ.value.get(word, 0)
        g = germ.gradient.get(word, s.zeros(100, 1))
        h = germ.Hessian.get(word, s.zeros(100))
        v = s.expand(value*f)
        dg = clean(value*g+gradient*f)
        dh = clean(value*h+gradient*g.T+g*gradient.T+Hessian*f)
        if v: values[word] = v
        if dg.todok(): gradients[word] = dg
        if dh.todok(): Hessians[word] = dh
    return SourceGerm(values, gradients, Hessians)


def car_product_jet(germ, row, creation):
    values, gradients, Hessians = {}, {}, {}
    for word in germ.words():
        images = linear_car(row, {word: s.S.One}, creation)
        for output, coefficient in images.items():
            values[output] = values.get(output, 0)+coefficient*germ.value.get(word, 0)
            gradients[output] = gradients.get(output, s.zeros(100, 1))+coefficient*germ.gradient.get(word, s.zeros(100, 1))
            Hessians[output] = Hessians.get(output, s.zeros(100))+coefficient*germ.Hessian.get(word, s.zeros(100))
    return SourceGerm(simplified(values),
        {word: clean(value) for word, value in gradients.items() if clean(value).todok()},
        {word: clean(value) for word, value in Hessians.items() if clean(value).todok()})


class SourceCanonicalEulerFeedback:
    def __init__(self):
        patch_symbolic_equal()
        self.model = SourceJointCCRCarPorts()
        self.z = tuple(self.model.leaf.source_point[i] for i in self.model.leaf.free)
        self.data = self.model.coefficients(self.z)
        self.phase = OriginalCanonicalPhase()
        self.real_source = read_bound('real_scalar_car_source')
        self.U = decode(self.real_source['complex_branch_unitary'])
        self.E = self.phase.E
        self.Cchi = real_pair(self.E.T)
        self.Cchi_inverse = clean(self.Cchi.inv(method='DM'))
        equal(self.Cchi*self.Cchi_inverse, s.eye(504))
        self.psi_matrix = self.U.H
        self.P_matrix = clean(s.I*self.U.T)
        self.chi_matrix = clean(self.Cchi_inverse*self.P_matrix)
        equal(self.Cchi*self.chi_matrix, self.P_matrix)
        self.chi0_real = self.phase.chi0.T.applyfunc(s.re).col_join(self.phase.chi0.T.applyfunc(s.im))
        self.Ce0 = clean(s.Matrix.hstack(*(real_pair(dE.T)*self.chi0_real for dE in self.phase.dE)))
        self.phase_generators = {
            'primal': realify(s.I*self.phase.omega*self.phase.Rp),
            'momentum': self.phase.Kpsi,
            'chi': realify(s.I*self.phase.omega*self.phase.Rd.T)}
        equal(self.Cchi*self.phase_generators['chi'], self.phase_generators['momentum']*self.Cchi)
        self.divergence = s.zeros(100, 1)
        qsub = dict(zip(self.model.leaf.weyl.native.joint.coframe.q, self.z[:6]))
        self.divergence[:6, :] = self.model.at_time(self.model.leaf.pairing['divergence'].subs(qsub))
        self.divergence[6:, :] = self.model.at_time(self.data['scalar']['div_principal']+
                                                  self.data['gauge']['div_principal'])
        variables = self.model.leaf.weyl.native.joint.coframe.q
        divdiv = self.model.at_time(sum(s.diff(self.model.leaf.pairing['K'][i, j], variables[i], variables[j])
            for i in range(6) for j in range(6)).subs(qsub))
        divdiv += self.model.at_time(self.data['scalar']['divdiv_principal']+self.data['gauge']['divdiv_principal'])
        divlinear = self.model.at_time(self.data['scalar']['div_momentum_identity']+self.data['gauge']['div_momentum_identity'])
        spin_divergence = clean(sum((self.model.leaf.pairing['Mh'][j].diff(variables[j]) for j in range(6)), s.zeros(8)))
        divmatrix = self.model.at_time(s.kronecker_product(spin_divergence.subs(qsub), s.eye(63)))
        weights = self.model.at_time(self.data['scalar']['div_momentum_current']+self.data['gauge']['div_momentum_current'])
        divmatrix += sum((coefficient*charge for coefficient, charge in zip(weights, self.model.leaf.charges) if coefficient), s.zeros(504))
        self.current_divergence = clean(divmatrix)
        original = self.data['zero']
        self.differential_zero = NormalSymbol(s.factor(original.scalar-divdiv/4-s.I*divlinear/2),
            clean(original.one_body-s.I*self.current_divergence/2), original.pairs)
        self._zero_word_cache = {}

    @staticmethod
    def volume_weight_jet(power):
        power = s.sympify(power)
        gradient, Hessian = s.zeros(100, 1), s.zeros(100)
        for i in (0, 2, 5):
            gradient[i] = power
            for j in (0, 2, 5):
                Hessian[i, j] = power*(power-1) if i == j else power**2
        return s.S.One, gradient, Hessian

    def specification(self, kind):
        if kind == 'primal': return self.psi_matrix, False, -s.Rational(1, 2)
        if kind == 'momentum': return self.P_matrix, True, s.Rational(1, 2)
        if kind == 'chi': return self.chi_matrix, True, -s.Rational(1, 2)
        raise ValueError('Use original primal, canonical momentum or independent chi.')

    def observable_jet(self, kind, index, germ, keep_density_derivatives=True):
        matrix, creation, power = self.specification(kind)
        if index not in range(504):
            raise ValueError('Use one of the original504 independent real field coordinates.')
        output = car_product_jet(germ, matrix[index, :], creation)
        value, gradient, Hessian = self.volume_weight_jet(power)
        if not keep_density_derivatives:
            gradient, Hessian = s.zeros(100, 1), s.zeros(100)
        return scalar_product_jet(output, value, gradient, Hessian)

    def H(self, germ):
        # Germ dictionaries and their matrices may be updated by a caller.
        # Only immutable CAR words under the fixed source operator are cached.
        scalar, terms = {}, []
        for word in germ.words():
            gradient = germ.gradient.get(word, s.zeros(100, 1))
            Hessian = germ.Hessian.get(word, s.zeros(100))
            scalar[word] = -sum(value*Hessian[i, j] for (i, j), value in self.data['principal'].todok().items())
            scalar[word] -= ((self.divergence+s.I*self.data['linear_identity']).T*gradient)[0]
        terms.append((1, scalar))
        for word, value in germ.value.items():
            if word not in self._zero_word_cache:
                self._zero_word_cache[word] = self.differential_zero.apply({word: s.S.One})
            terms.append((value, self._zero_word_cache[word]))
        for coordinate, matrix in enumerate(self.data['linear_current']):
            gradient = {word: value[coordinate] for word, value in germ.gradient.items() if value[coordinate]}
            if gradient and matrix.todok():
                terms.append((-s.I, apply_superposition(matrix, gradient)))
        return add_states(*terms)

    def literal_H(self, germ):
        return current_weyl_action(self.model, self.data, germ.value, germ.gradient, germ.Hessian)

    def observable(self, kind, index, state):
        matrix, creation, _ = self.specification(kind)
        return linear_car(matrix[index, :], state, creation)

    def heisenberg(self, kind, index, germ, keep_density_derivatives=True):
        """Literal i[H,O] on the current core, with the original source O."""
        first = self.H(self.observable_jet(kind, index, germ, keep_density_derivatives))
        second = self.observable(kind, index, self.H(germ))
        return add_states((s.I, first), (-s.I, second))

    def velocity(self, coordinate, germ):
        """Exact i[H,z_j], in the original flat-pairing Weyl order."""
        data = self.data
        scalar = {}
        for word in germ.words():
            gradient = germ.gradient.get(word, s.zeros(100, 1))
            scalar[word] = -2*s.I*(data['principal'][coordinate, :]*gradient)[0]
            scalar[word] += (data['linear_identity'][coordinate]-s.I*self.divergence[coordinate])*germ.value.get(word, 0)
        return add_states((1, scalar), (1, apply_superposition(data['linear_current'][coordinate], germ.value)))

    def weight_derivation(self, power, germ):
        _, gradient, Hessian = self.volume_weight_jet(power)
        ordering = -s.I*sum(value*Hessian[i, j] for (i, j), value in self.data['principal'].todok().items())
        return add_states(*[(gradient[j], self.velocity(j, germ)) for j in (0, 2, 5)],
                          (ordering, germ.value))

    def independent_chain(self, kind, index, germ):
        matrix, creation, power = self.specification(kind)
        bare = car_product_jet(germ, matrix[index, :], creation)
        unit = self.heisenberg(kind, index, germ, keep_density_derivatives=False)
        correction = self.weight_derivation(power, bare)
        actual = self.heisenberg(kind, index, germ)
        same(actual, add_states((1, unit), (1, correction)))
        return {'actual': actual, 'unit_CAR_part': unit, 'volume_derivative_part': correction}

    def stationary_heisenberg(self, kind, index, germ):
        """Original-time source epoch: subtract the paid basis velocity."""
        generator = self.phase_generators[kind]
        phase_action = add_states(*[(value, self.observable(kind, j, germ.value))
            for (i, j), value in generator.todok().items() if i == index])
        return add_states((1, self.heisenberg(kind, index, germ)), (-1, phase_action))

    def _full_chi_coframe_product(self, axis, real_primal_velocity_residual):
        """Ordered chi-hat times E_e times the complete source odd residual.

        This algebraic consumer is separate from the linear reference
        transporter. The residual is generated by this source's Heisenberg
        producer before this internal contraction is called.
        """
        coefficient = real_pair(self.phase.dE[axis])
        actual, linear = [], []
        for (i, j), value in coefficient.todok().items():
            if j not in real_primal_velocity_residual:
                continue
            residual = real_primal_velocity_residual[j]
            actual.append((-value, self.observable('chi', i, residual)))
            linear.append((-value*self.chi0_real[i], residual))
        full, background = add_states(*actual), add_states(*linear)
        return {'full_fixed_p_minus_fixed_chi_correction': full,
            'background_Ce0_transporter': background,
            'nonlinear_chi_minus_chi0_remainder': add_states((1, full), (-1, background))}


def source_germ():
    pair = (5, 257)
    return SourceGerm({(): s.Rational(2, 3), pair: s.I/7},
        {(): s.SparseMatrix(100, 1, {(0, 0): s.Rational(1, 11), (2, 0): s.I/13, (7, 0): s.Rational(2, 17)}),
         pair: s.SparseMatrix(100, 1, {(5, 0): -s.I/19, (74, 0): s.Rational(1, 23)}),
         (144,): s.SparseMatrix(100, 1, {(2, 0): s.Rational(1, 29), (95, 0): -s.I/31})},
        {(): s.SparseMatrix(100, 100, {(0, 0): s.Rational(1, 37), (0, 2): s.I/41, (2, 0): s.I/41}),
         pair: s.SparseMatrix(100, 100, {(5, 5): s.Rational(1, 43), (7, 7): -s.Rational(1, 47)}),
         (144,): s.SparseMatrix(100, 100, {(0, 5): s.I/53, (5, 0): s.I/53})})


def mutable_germ_consumer(model):
    word = (5,)
    germ = SourceGerm({word: s.S.One}, {word: s.zeros(100, 1)}, {word: s.zeros(100)})
    first = model.H(germ)
    germ.value[word] = 2
    expected = add_states((2, first))
    same(model.H(germ), expected)
    germ.gradient[word][0] = s.Rational(1, 11)
    expected = add_states((1, expected),
        (-(model.divergence[0]+s.I*model.data['linear_identity'][0])/11, {word: 1}),
        (-s.I/11, apply_superposition(model.data['linear_current'][0], {word: 1})))
    same(model.H(germ), expected)
    germ.Hessian[word][0, 0] = s.Rational(2, 13)
    expected = add_states((1, expected), (-2*model.data['principal'][0, 0]/13, {word: 1}))
    same(model.H(germ), expected)
    copy = SourceGerm(germ.value.copy(), {w: g.copy() for w, g in germ.gradient.items()},
                      {w: H.copy() for w, H in germ.Hessian.items()})
    same(model.heisenberg('primal', 5, germ), model.heisenberg('primal', 5, copy))
    return {'same_object_value_update': True, 'nested_gradient_update': True,
        'nested_Hessian_update': True, 'updated_commutator_matches_fresh_equal_germ': True}


def main():
    started = time.monotonic()
    model = SourceCanonicalEulerFeedback()
    q = tuple(s.Symbol('q'+str(j), positive=True) if j in (0, 2, 5)
              else s.Symbol('q'+str(j), real=True) for j in range(6))
    v = q[0]*q[2]*q[5]
    cf = model.model.leaf.weyl.native.joint.coframe
    e = cf.e.copy()
    for index, value in zip((5, 9, 10, 13, 14, 15), q): e[index] = value
    # This uses the original temporal coefficient on the same Lorentz slice.
    raw_E = cf.model.lorentz.raw_matter_ports(e)['E']
    equal(clean(s.kronecker_product(raw_E, s.eye(63))), v*model.E)
    for power in (-s.Rational(1, 2), s.Rational(1, 2)):
        value, gradient, Hessian = model.volume_weight_jet(power)
        point = dict(zip(q, (1, 0, 1, 0, 0, 1)))
        expression = v**power
        assert expression.subs(point) == value
        for i in range(6):
            assert s.diff(expression, q[i]).subs(point) == gradient[i]
            for j in range(6): assert s.diff(expression, q[i], q[j]).subs(point) == Hessian[i, j]
    m = s.Symbol('source_particle_number', integer=True)
    assert s.simplify((v**(1+(m-1)/2)/v**(1+m/2))**2-1/v) == 0
    assert s.simplify((v**(1+(m+1)/2)/v**(1+m/2))**2-v) == 0
    print('PASS source Number-shift density, original E(q), full504 independent-dual maps and two-jets', flush=True)
    germ = source_germ()
    same(model.H(germ), model.literal_H(germ))
    for kind in ('primal', 'momentum', 'chi'):
        transformed = model.observable_jet(kind, 5, germ)
        same(model.H(transformed), model.literal_H(transformed))
    print('PASS complete coefficient-left H equals all four original energy actions on cross-N and all three odd germs', flush=True)
    rows = []
    for kind in ('primal', 'momentum', 'chi'):
        for index in (5, 144, 257, 396):
            result = model.independent_chain(kind, index, germ)
            assert result['volume_derivative_part']
            stationary = model.stationary_heisenberg(kind, index, germ)
            rows.append({'kind': kind, 'real_coordinate': index,
                'original_source_Heisenberg': encode_state(result['actual']),
                'unit_CAR_omission_defect': encode_state(result['volume_derivative_part']),
                'stationary_reference_velocity': encode_state(stationary),
                'nonzero_basis_velocity_term': stationary != result['actual'],
                'actual_output_numbers': sorted({len(word) for word in result['actual']})})
            print('PASS actual same-H odd observable', kind, index, flush=True)
    zero = SourceGerm({}, {}, {})
    assert model.heisenberg('primal', 5, zero) == model.heisenberg('chi', 131, zero) == {}
    mutation = mutable_germ_consumer(model)
    print('PASS same germ value, nested gradient and Hessian updates with fresh commutator', flush=True)
    # The reference tangent still has its exact source meaning. Its all16
    # correction is not identified with the full chi-hat contraction above.
    equal(model.Ce0[:, (0, 4, 8, 12)], s.zeros(504, 4))
    paths = ['source_canonical_euler_feedback.py', 'source_joint_ccr_car_ports.py',
        'source_joint_current_hilbert_section.py', 'source_joint_current_hilbert_section.json',
        'source_common_phase_time.py', 'source_common_phase_time.json',
        'source_common_hamiltonian.py', 'real_scalar_car_source.py', 'real_scalar_car_source.json',
        'source_common_weyl_symbol.py', 'source_scalar_weyl_symbol.py']
    reference = read_bound('source_joint_ccr_car_ports')
    result = {'root': ROOT_ID, 'scope': 'SOURCE_CURRENT_H_NATIVE_ODD_CANONICAL_OBSERVABLES_AND_TRUE_HEISENBERG_TWOJETS',
        'source_sha256': reference['source_sha256'],
        'input_sha256': {str((HERE/name).relative_to(ROOT)): hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in paths},
        'public_mouth': 'observable_jet(kind,index,source100_germ) and heisenberg consume the same full four-energy current H. No Hamiltonian, source state, phase matrix or derivative output is caller-supplied.',
        'normalization': 'U_m=sqrt(rho3)*v^(1+m/2); U a U^-1=v^-1/2 a and U eta U^-1=v^1/2 eta. The common rho3 cancels between particle sectors, while both v derivatives remain.',
        'original_fields': {'primal_real504_matrix': encode(model.psi_matrix),
            'canonical_momentum_real504_matrix': encode(model.P_matrix),
            'independent_chi_real504_matrix': encode(model.chi_matrix),
            'kinetic_covector_matrix_Cchi': encode(model.Cchi),
            'background_only_Ce0': encode(model.Ce0)},
        'source_operator_rule': 'i[H,f O]=f i[H,O]+(sum_j f_j i[H,z_j]-i sum_ij K_ij f_ij)O; O is the original ordered CAR action. The last contraction and every first derivative are actual source coefficients.',
        'original_full_H_comparison': 'The complete coefficient-left differential normal form, including divK, divdivK, divell and divM, equals the literal four-energy action on the original cross-N germ and its primal, canonical-dual and chi observable germs.',
        'actual_cross_N_source': {'values': encode_state(germ.value),
            'gradients100': [[list(word), encode(value)] for word, value in germ.gradient.items()],
            'Hessians100': [[list(word), encode(value)] for word, value in germ.Hessian.items()],
            'zero_valued_N1_derivative_retained': True, 'consumers': rows},
        'mutable_germ_consumer': mutation,
        'phase': {'actual_source_frequency': str(model.phase.omega), 'proper_clock': 'tau=N*t, N='+str(model.phase.N),
            'derivative_rule': 'At the original source epoch, dot O_stationary=dot O_original-K_phase O; the old source phase supplies K_phase and the two endpoint rotations.',
            'independent_dual_uses_original_Rd_not_negative_Rp': True},
        'classification': {'background_canonical_to_chi_tangent': 'transporter',
            'native_odd_H_action_with_density_twojets': 'source producer',
            'full_quantum_chi_Euler_Ward_and_retarded289_feed': 'next consumer; not inferred from the background tangent'},
        'seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_canonical_euler_feedback.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source native odd Heisenberg producer', result['seconds'], flush=True)


if __name__ == '__main__': main()
