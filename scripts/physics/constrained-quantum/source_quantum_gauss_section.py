#!/usr/bin/env python3
"""Source-generated local equivariant sections and their full Hamiltonian jet.

The original SU(2) orbit map and three actual connection coordinates generate
the local extension; Gauss zero is its output. All103 second derivatives are
kept when the native orthogonal Hamiltonian consumes the extended section.
This is a germ construction, not a global quotient or a Hilbert measure.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import time
from collections import defaultdict
import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, decode
from source_quantum_stabilizer import SourceQuantumStabilizer
from source_stabilizer_phase_reduction import block_diagonal
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state
from source_gauge_legendre import realify
from source_lorentz_contact import clean, equal, encode
from source_coframe_legendre import rational
from source_coframe_live_ordering import FREE


def zero(A):
    equal(rational(A), s.zeros(*A.shape))


def state_clean(vector):
    return {word: value for word, old in vector.items() if (value := s.cancel(old)) != 0}


def exterior(matrix, degree):
    words = list(itertools.combinations(range(matrix.rows), degree))
    values = {}
    for i, row in enumerate(words):
        for j, col in enumerate(words):
            minor = matrix.extract(row, col)
            if any(all(v == 0 for v in minor.row(k)) for k in range(degree)):
                continue
            value = s.expand(minor.det())
            if value != 0:
                values[i, j] = value
    return s.MutableSparseMatrix(len(words), len(words), values)


def exterior_word(matrix, word):
    """The actual finite CAR functor on an arbitrary occupied word."""
    vector = {(): s.S.One}
    for column in word:
        new = defaultdict(lambda: s.S.Zero)
        entries = {i: v for (i, _), v in matrix[:, column].todok().items()}
        for occupied, coefficient in vector.items():
            for i, value in entries.items():
                if i in occupied:
                    continue
                sign = (-1)**sum(j > i for j in occupied)
                new[tuple(sorted((*occupied, i)))] += sign*coefficient*value
        vector = state_clean(new)
    return vector


def linear_matrices(matrices, coefficients, shape):
    return rational(sum((value*matrices[j] for j, value in enumerate(coefficients) if value),
                        s.zeros(*shape)))


class SourceQuantumGaussSection:
    def __init__(self):
        self.native = SourceQuantumStabilizer()
        m = self.native
        self.L = [block_diagonal(s.zeros(6), T) for T in m.T_s]
        self.R = [clean(Q/s.I) for Q in m.Q_s]
        saved = json.loads((HERE/'source_stabilizer_phase_reduction.json').read_text())
        self.pivots = tuple(saved['slice']['whole_coordinate_pivots'])
        self.free = tuple(j for j in range(103) if j not in self.pivots)
        self.Ip = s.SparseMatrix(103, 3, {(row, j): 1 for j, row in enumerate(self.pivots)})
        self.If = s.SparseMatrix(103, 100, {(row, j): 1 for j, row in enumerate(self.free)})
        bg = m.graph.common.scalar.exchange.active['actual_background']
        self.e0 = s.Matrix(bg['coframe']).applyfunc(s.sympify)
        self.A0 = s.Matrix(bg['gauge_connection']).applyfunc(s.sympify)[1:, :]
        self.b0 = s.Matrix.vstack(s.Matrix([self.e0[j] for j in FREE]), s.zeros(61, 1), self.A0.reshape(36, 1))
        self.V = clean(s.Matrix.hstack(*(L*self.b0 for L in self.L)))
        self.M = clean(self.Ip.T*self.V)
        equal(self.M, decode(saved['slice']['source_orbit_minor']))
        self.alpha = rational(self.M.inv()*self.Ip.T)
        self.z = rational(self.If.T*(s.eye(103)-self.V*self.alpha))
        forward = self.V.row_join(self.If)
        inverse = self.alpha.col_join(self.z)
        equal(forward*inverse, s.eye(103)); equal(inverse*forward, s.eye(103))
        self.forward_curvature = [s.zeros(103) for _ in range(103)]
        for a in range(3):
            row = self.alpha[a, :]
            mixed = clean(self.L[a]*self.If*self.z)
            for k in range(103):
                if mixed[k, :].todok():
                    self.forward_curvature[k] += row.T*mixed[k, :]+mixed[k, :].T*row
            for b in range(3):
                acceleration = clean((self.L[a]*self.L[b]+self.L[b]*self.L[a])*self.b0/2)
                outer = row.T*self.alpha[b, :]
                for (k, _), value in acceleration.todok().items():
                    self.forward_curvature[k] += value*outer
        self.forward_curvature = [rational(H) for H in self.forward_curvature]
        self.alpha2 = [-linear_matrices(self.forward_curvature, self.alpha[a, :], (103, 103)) for a in range(3)]
        self.z2 = [-linear_matrices(self.forward_curvature, self.z[j, :], (103, 103)) for j in range(100)]
        inverse2 = self.alpha2+self.z2
        for k in range(103):
            zero(linear_matrices(inverse2, forward[k, :], (103, 103))+self.forward_curvature[k])
        self.K = [clean(sum((m.S[a, j]*m.gauge.fundamental[a] for a in range(12)), s.zeros(7))) for j in range(3)]
        self.P = clean(-self.K[0]*self.K[0])
        equal(self.P*self.P, self.P); assert self.P.rank() == 2
        for a in range(3):
            equal(self.K[a].H, -self.K[a]); equal(self.P*self.K[a], self.K[a])
            for b in range(3):
                rhs = (-self.P if a == b else s.zeros(7))+sum(
                    (m.structure[a][c, b]*self.K[c]/2 for c in range(3)), s.zeros(7))
                equal(self.K[a]*self.K[b], rhs)

    def group(self, quaternion):
        return clean(s.eye(7)-self.P+quaternion[0]*self.P+
                     sum((quaternion[a+1]*self.K[a] for a in range(3)), s.zeros(7)))

    def compose(self, u, v):
        scalar = u[0]*v[0]-sum(u[j]*v[j] for j in range(1, 4))
        vector = [u[0]*v[c+1]+v[0]*u[c+1]+sum(
            (self.native.structure[a][c, b]*u[a+1]*v[b+1]/2 for a in range(3) for b in range(3))) for c in range(3)]
        return s.Matrix([scalar, *vector])

    def matter_group(self, g):
        from source_gauge_legendre import source
        _, _, degrees, _ = source.parse_source(ROOT)
        internal = block_diagonal(*(exterior(g, degree) for degree in degrees))
        rho = block_diagonal(*([internal]*4))
        return block_diagonal(rho, rho.conjugate())

    def boson_group(self, g):
        m = self.native
        scalar = clean(m.graph.dual_R.T*realify(exterior(g, 4))*m.graph.R)
        ad = s.Matrix(12, 12, lambda a, b: m.gauge.native_pair(m.gauge.fundamental[a],
                    g*m.gauge.fundamental[b]*g.H))
        ad = clean(m.gauge.gram_inverse*ad)
        return block_diagonal(s.eye(6), scalar, ad, ad, ad)

    def extend_jet(self, value, gradient, Hessian):
        """Input: finite CAR-valued100-coordinate germ, with no Gauss premise.

        Dictionaries gradient[word] and Hessian[word] carry the actual scalar
        coefficients of each CAR word. Their derivatives may have support
        different from the zeroth-order section value.
        """
        result = {}
        def add(vector, v=0, g=None, H=None):
            for word, coefficient in vector.items():
                item = result.setdefault(word, {'value': s.S.Zero, 'gradient': s.zeros(103, 1), 'Hessian': s.zeros(103)})
                item['value'] += coefficient*v
                if g is not None:
                    item['gradient'] += coefficient*g
                if H is not None:
                    item['Hessian'] += coefficient*H
        for word in set(value)|set(gradient)|set(Hessian):
            dg = gradient.get(word, s.zeros(100, 1)); d2g = Hessian.get(word, s.zeros(100))
            full_gradient = self.z.T*dg
            full_Hessian = self.z.T*d2g*self.z+linear_matrices(self.z2, dg, (103, 103))
            add({word: 1}, value.get(word, 0), full_gradient, full_Hessian)
            for a in range(3):
                crossed = self.alpha[a, :].T*full_gradient.T+full_gradient*self.alpha[a, :]
                add(apply_superposition(self.R[a], {word: 1}), H=crossed)
        for a in range(3):
            add(apply_superposition(self.R[a], value), g=self.alpha[a, :].T, H=self.alpha2[a])
            for b in range(a, 3):
                ab = apply_superposition(self.R[a], apply_superposition(self.R[b], value))
                if a == b:
                    add(ab, H=self.alpha[a, :].T*self.alpha[b, :])
                else:
                    ba = apply_superposition(self.R[b], apply_superposition(self.R[a], value))
                    add(weighted_sum([(s.Rational(1, 2), ab), (s.Rational(1, 2), ba)]),
                        H=self.alpha[a, :].T*self.alpha[b, :]+self.alpha[b, :].T*self.alpha[a, :])
        for item in result.values():
            item['value'] = s.cancel(item['value'])
            item['gradient'] = rational(item['gradient']); item['Hessian'] = rational(item['Hessian'])
            equal(item['Hessian'], item['Hessian'].T)
        return result

    def verify_Gauss_jet(self, jet):
        value = {w: j['value'] for w, j in jet.items() if j['value']}
        for a in range(3):
            residual = {w: -s.I*(self.V[:, a].T*j['gradient'])[0] for w, j in jet.items()}
            residual = weighted_sum([(1, residual), (s.I, apply_superposition(self.R[a], value))])
            assert state_clean(residual) == {}
            derivatives = {w: clean(-s.I*(self.L[a].T*j['gradient']+j['Hessian']*self.V[:, a])) for w, j in jet.items()}
            for w, j in jet.items():
                for out, coefficient in apply_superposition(self.R[a], {w: 1}).items():
                    derivatives.setdefault(out, s.zeros(103, 1))
                    derivatives[out] += s.I*coefficient*j['gradient']
            for derivative in derivatives.values():
                zero(derivative)
        return {'all3_Gauss_values_zero': True, 'all309_first_derivatives_of_Gauss_zero': True,
                'all103_by103_Hessian_entries_retained': True}

    def Hamiltonian_action(self, jet):
        """Actual linear action, including words whose zeroth-order value is0."""
        m = self.native
        data = m.joint.coefficients(tuple(self.b0[:6, 0]), self.b0[6:67, :], self.A0)
        components = {name: {} for name in ('coframe', 'scalar', 'gauge', 'matter_without_Lorentz')}
        for word, item in jet.items():
            pieces, _ = m.joint.action(data, word, item['gradient'], item['Hessian'])
            if item['value'] != 1:
                constant, _ = m.joint.action(data, word, s.zeros(103, 1), s.zeros(103))
                pieces = {name: weighted_sum([(1, value), (item['value']-1, constant[name])]) for name, value in pieces.items()}
            components = {name: weighted_sum([(1, value), (1, pieces[name])]) for name, value in components.items()}
        return components, weighted_sum((1, value) for value in components.values())


def main():
    started = time.monotonic(); m = SourceQuantumGaussSection()
    u = s.Matrix(s.symbols('u0:4', real=True)); v = s.Matrix(s.symbols('v0:4', real=True))
    gu, gv = m.group(u), m.group(v); w = m.compose(u, v)
    equal(gu*gv, m.group(w))
    norm = sum(x*x for x in u)
    equal(gu.H*gu-s.eye(7), (norm-1)*m.P)
    assert s.expand(gu.det()-norm) == 0
    assert s.expand(sum(x*x for x in w)-norm*sum(x*x for x in v)) == 0
    # The actual full exterior group coefficients, in their original order,
    # differentiate to all252 source matter generators on both real branches.
    from source_gauge_legendre import source
    _, _, degrees, _ = source.parse_source(ROOT)
    unit = {u[0]: 1, u[1]: 0, u[2]: 0, u[3]: 0}
    compound = {degree: exterior(gu, degree) for degree in set(degrees)|{4}}
    internal = block_diagonal(*(compound[degree] for degree in degrees))
    for a in range(3):
        derivative = clean(internal.diff(u[a+1]).subs(unit))
        equal(block_diagonal(*([derivative]*4)), m.native.rho_s252[a])
        equal(realify(compound[4].diff(u[a+1]).subs(unit)), m.native.rho_s[a])
    print('PASS original seven-dimensional SU2 quaternion law and all full exterior/matter group derivatives', flush=True)

    chosen = next(j for j in range(252) if all(R[:, j].todok() for R in m.R))
    partner = next(i for (i, _), entry in m.R[0][:252, chosen].todok().items() if i != chosen and entry)
    word = (chosen, 252+partner)
    value = {word: s.S.One}
    assert all(apply_superposition(R, value) for R in m.R)
    ell = s.Matrix([s.Rational((j % 11)+1, 31) for j in range(100)])
    radial = s.Matrix([s.Rational((j % 7)-3, 37) for j in range(100)])
    gradient = {word: s.I*ell}; Hessian = {word: radial*radial.T-s.eye(100)}
    jet = m.extend_jet(value, gradient, Hessian)
    gauss = m.verify_Gauss_jet(jet)
    # E followed by R is the identity on every part of the input second jet.
    for out, item in jet.items():
        zero(m.If.T*item['gradient']-gradient.get(out, s.zeros(100, 1)))
        zero(m.If.T*item['Hessian']*m.If-Hessian.get(out, s.zeros(100)))
        assert item['value'] == value.get(out, 0)
    assert any(j['gradient'][p] != 0 for j in jet.values() for p in m.pivots)
    print('PASS actual charged finite-CAR section, all three Gauss equations, all309 differentiated equations and complete slice-jet roundtrip', flush=True)

    parts, image = m.Hamiltonian_action(jet)
    assert image and all(parts.values())
    naive = {word: {'value': 1, 'gradient': m.If*gradient[word], 'Hessian': m.If*Hessian[word]*m.If.T}}
    naive_parts, naive_image = m.Hamiltonian_action(naive)
    defect = weighted_sum([(1, image), (-1, naive_image)])
    assert defect
    spin_jet = m.extend_jet(value, {}, {})
    _, spin_image = m.Hamiltonian_action(spin_jet)
    _, constant_image = m.Hamiltonian_action({word: {'value': 1, 'gradient': s.zeros(103, 1), 'Hessian': s.zeros(103)}})
    spin_defect = weighted_sum([(1, spin_image), (-1, constant_image)])
    assert spin_defect
    print('PASS complete native Hamiltonian on the extended true jet and nonzero spin/gauge-connection correction', flush=True)

    small = s.Matrix([s.Rational(9999, 10001), s.Rational(200, 10001), 0, 0])
    g = m.group(small)
    def matter_group(g7):
        rho = block_diagonal(*([block_diagonal(*(exterior(g7, d) for d in degrees))]*4))
        return block_diagonal(rho, rho.conjugate())
    group_CAR = matter_group(g)
    moved = exterior_word(group_CAR, word)
    assert moved != value
    gb = m.boson_group(g)
    center = m.group(s.Matrix([-1, 0, 0, 0]))
    center_boson = m.boson_group(center); center_CAR = matter_group(center)
    equal(center_boson*m.b0, m.b0)
    odd = exterior_word(center_CAR, (chosen,))
    assert odd == {(chosen,): -1}
    assert center_boson != s.eye(103)
    print('PASS actual finite charged group section and original central action retained at the source', flush=True)

    paths = [HERE/name for name in ('source_quantum_gauss_section.py', 'source_quantum_stabilizer.py',
        'source_quantum_stabilizer.json', 'independent_source_quantum_stabilizer.json',
        'source_stabilizer_phase_reduction.py', 'source_stabilizer_phase_reduction.json',
        'independent_source_stabilizer_phase_reduction.json', 'source_joint_local_quantum.py',
        'source_coframe_live_ordering.py', 'source_scalar_shift_quantum.py', 'source_gauss_live_ordering.py',
        'source_gauge_quantum_energy.py', 'source_gauss_quantum_current.py')]
    result = {'root': ROOT_ID, 'source_sha256': m.native.graph.common.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'scope': 'SOURCE_LOCAL_EQUIVARIANT_FINITE_CAR_SECTION_AND_ACTUAL_REDUCED_HAMILTONIAN_JET',
        'group': {'original_fundamental_generators': [encode(K) for K in m.K], 'active_projector': encode(m.P),
            'quaternion_law': 'g(u)=I-P+u0 P+sum_a ua K_a; ||u||=1; K_a K_b=-delta_ab P+f_ab^c K_c/2, f=-2epsilon',
            'generic_group_product_unitarity_and_determinant_checked': True,
            'original_exterior_degrees_in_order': degrees, 'all_original_exterior_generators_differentiated': True,
            'CAR_group': 'Gamma(diag(I4 tensor exterior_source(g),conjugate(I4 tensor exterior_source(g)))) on every finite occupied word; exterior composition is the Cauchy-Binet identity'},
        'source_boson_configuration': encode(m.b0),
        'slice': {'coordinate_pivots': list(m.pivots), 'remaining_coordinates': list(m.free),
            'source_orbit_minor': encode(m.M), 'source_minor_determinant': str(s.factor(m.M.det()))},
        'extension': 'For q=exp(sum alpha_s L_s) z, with z on the same actual source slice and alpha near0: E(f)(q)=Gamma(exp(sum alpha_s R_s)) f(z). The inverse orbit map is generated by the local analytic implicit-function theorem from the displayed nonzero minor.',
        'Gauss_output': 'G_s E(f)=(-i V_s+dGamma(i R_s))E(f)=0; no Gauss-zero input or singlet condition is supplied',
        'inverse_first_derivatives': {'alpha': encode(m.alpha), 'slice': encode(m.z)},
        'inverse_second_derivatives': {'alpha': [encode(H) for H in m.alpha2], 'slice': [encode(H) for H in m.z2]},
        'arbitrary_finite_CAR_jet_API': 'extend_jet(value[word],gradient[word]:100x1,Hessian[word]:100x100)',
        'actual_input': {'CAR': list(word), 'gradient': encode(gradient[word]), 'Hessian': encode(Hessian[word])},
        'actual_extended_jet': [{'CAR': list(w), 'value': str(j['value']), 'gradient': encode(j['gradient']), 'Hessian': encode(j['Hessian'])} for w, j in sorted(jet.items())],
        'Gauss_jet_checks': gauss, 'restriction_extension_all_second_jet_components_identity': True,
        'Hamiltonian': {'definition': 'H_reduced=Restriction H_native_orthogonal Extension on these local equivariant germs',
            'descent': 'The independently signed exact [G_s,H_native]=0 makes H_native E(f) equivariant; uniqueness of the same local extension gives E R H_native E=H_native E.',
            'actual_four_components': {name: encode_state(component) for name, component in parts.items()},
            'actual_complete_image': encode_state(image), 'omit_orbit_derivatives_defect': encode_state(defect),
            'constant_slice_section_spin_connection_correction': encode_state(spin_defect),
            'zero_value_nonzero_derivative_CAR_words_handled_linearly': True},
        'actual_finite_group_consumer': {'unit_quaternion': list(map(str, small)),
            'moved_source_configuration': encode(gb*m.b0), 'CAR_image': encode_state(moved)},
        'center': {'source_boson_fixed': True, 'full_boson_representation_center_identity': False,
            'original_CAR_odd_word': [chosen], 'odd_word_image': encode_state(odd),
            'arbitrary_local_sections_declared_global_physical_states': False},
        'domain': 'Smooth germs near the actual source slice times finite algebraic CAR504. Slice data may use local compact cutoffs; no cutoff in the group variable is imposed. A global orbit atlas, isotropy-compatible descent and Hilbert measure are separate consumers.',
        'second_class_temporal_branch_or_full_Hilbert_evolution_spectrum_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_quantum_gauss_section.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS original local quantum Gauss section', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
