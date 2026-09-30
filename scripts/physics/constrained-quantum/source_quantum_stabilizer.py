#!/usr/bin/env python3
"""Native orthogonal Gauss reduction and the remaining source quantum symmetry.

The native Gram first selects the invariant broken complement. The original
Gauss momentum graph is then pulled back and ordered. This order matters:
changing an already ordered rref square by a classical zero constraint is not
an operator identity. All four energies act on the existing 103-coordinate
compact smooth domain and the original independent-dual CAR504.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_joint_local_quantum import SourceJointLocalQuantum
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state, tensor_current
from source_lorentz_contact import clean, equal, encode


def combine(columns, vector):
    return clean(sum((value*columns[a] for a, value in enumerate(vector) if value),
                     s.zeros(*columns[0].shape)))


class SourceQuantumStabilizer:
    def __init__(self):
        self.joint = SourceJointLocalQuantum()
        self.scalar = self.joint.scalar
        self.graph, self.c = self.scalar.graph, self.scalar.c
        self.gauge = self.graph.common.gauge
        self.S = self.graph.stabilizer
        self.J = clean((self.S.T*self.gauge.gram*self.S).inv()*self.S.T*self.gauge.gram*self.c.select)
        self.B = clean(self.c.select-self.S*self.J)
        self.W = self.B.row_join(self.S)
        equal(self.S.T*self.gauge.gram*self.B, s.zeros(3, 9))
        equal(self.c.orbit*self.B, self.graph.O)
        self.rho_s = [combine(self.c.rho, self.S[:, h]) for h in range(3)]
        self.rho_b = [combine(self.c.rho, self.B[:, a]) for a in range(9)]
        self.ad_s = [self.gauge.ad(self.S[:, h]) for h in range(3)]
        self.C = [clean(self.W.inv()*ad*self.W)[:9, :9] for ad in self.ad_s]
        self.structure = [clean(self.W.inv()*ad*self.W)[9:, 9:] for ad in self.ad_s]
        self.T_s = [clean(s.diag(self.graph.dual_R.T*T*self.graph.R, *[ad]*3))
                    for T, ad in zip(self.rho_s, self.ad_s)]
        self.T_b = [clean(s.diag(self.graph.dual_R.T*T*self.graph.R,
                               *[self.gauge.ad(self.B[:, a])]*3)) for a, T in enumerate(self.rho_b)]
        rho252 = self.graph.common.rho
        self.rho_s252 = [combine(rho252, self.S[:, h]) for h in range(3)]
        self.Q_s = [clean(s.diag(s.I*T, s.I*T.conjugate())) for T in self.rho_s252]
        self.Q_b = [clean(s.diag(s.I*T, s.I*T.conjugate()))
                    for T in [combine(rho252, self.B[:, a]) for a in range(9)]]
        self.old_T, self.old_Q = self.scalar.T, self.scalar.Q
        self.scalar.T, self.scalar.Q = self.T_b, self.Q_b
        self.scalar.live.rho = self.rho_b
        self.scalar.live.compressed = [clean(self.graph.dual_R.T*T*self.graph.R) for T in self.rho_b]

    def constraint_action(self, h, x, A, state, value, gradient):
        """The actual residual Gauss operator on the same 103-coordinate jet."""
        vector = self.T_s[h]*x.col_join(A.reshape(36, 1))
        return weighted_sum([(-s.I*(vector.T*gradient[6:, :])[0], state),
                             (value, apply_superposition(self.Q_s[h], state))])

    def action(self, q, x, A, state, gradient, Hessian):
        data = self.joint.coefficients(q, x, A)
        components, image = self.joint.action(data, state, gradient, Hessian)
        return data, components, image


def verify_native_algebra(m):
    c, R, Rd, O = m.c, m.graph.R, m.graph.dual_R, m.graph.O
    gr = clean(R.T*R)
    for h in range(3):
        ad, T, C = m.ad_s[h], m.rho_s[h], m.C[h]
        equal(ad*m.B, m.B*C)
        equal(ad*m.S, m.S*m.structure[h])
        equal(ad.T*m.gauge.gram+m.gauge.gram*ad, s.zeros(12))
        equal(T+T.T, s.zeros(70)); equal(T*c.vacuum, s.zeros(70, 1))
        equal(T*O, O*C)
        equal(T*R, R*m.T_s[h][:61, :61])
        equal(T*Rd, -Rd*m.T_s[h][:61, :61].T)
        equal(C.T*c.gram+c.gram*C, s.zeros(9))
        equal(m.T_s[h][:61, :61].T*gr+gr*m.T_s[h][:61, :61], s.zeros(61))
        assert s.trace(C) == s.trace(m.T_s[h]) == 0
        for k in range(3):
            f = m.structure[h][:, k]
            equal(m.T_s[h]*m.T_s[k]-m.T_s[k]*m.T_s[h], combine(m.T_s, f))
            equal(m.Q_s[h]*m.Q_s[k]-m.Q_s[k]*m.Q_s[h], s.I*combine(m.Q_s, f))
        for a in range(9):
            equal(m.T_s[h]*m.T_b[a]-m.T_b[a]*m.T_s[h], combine(m.T_b, C[:, a]))
            equal(m.Q_s[h]*m.Q_b[a]-m.Q_b[a]*m.Q_s[h], s.I*combine(m.Q_b, C[:, a]))
    equal(m.structure[0][:, 1], s.Matrix([0, 0, -2]))
    equal(m.structure[1][:, 2], s.Matrix([-2, 0, 0]))
    equal(m.structure[2][:, 0], s.Matrix([0, -2, 0]))
    return {'stabilizer_embedding': encode(m.S), 'native_Gram': encode(m.gauge.gram),
            'native_orthogonal_broken_embedding': encode(m.B), 'rref_to_orthogonal_correction': encode(m.J),
            'brackets': '[s0,s1]=-2 s2; [s1,s2]=-2 s0; [s2,s0]=-2 s1',
            'real_Lie_algebra': 'compact simple three-dimensional su(2), derived from the original native brackets',
            'all9_residual_Lie_and27_broken_covariance_identities': True,
            'original70_61_36_504_representations_checked': True}


def verify_graph_and_energies(m):
    """Coefficient identities cover every field, not just the displayed state.

    D is affine in all61 scalar coordinates. Differentiating D^T F=1 after
    the exact identities below gives V_s F=C_s F+F C_s^T on det D!=0.
    The universal CCR/CAR commutator derivation then covers arbitrary smooth
    functions and all particle sectors; no finite jet is a covariance premise.
    """
    x = s.Matrix(s.symbols('x0:61', real=True))
    phi = m.c.vacuum+m.graph.R*x
    D = clean(m.graph.O.T*s.Matrix.hstack(*[T*phi for T in m.rho_b]))
    oldD = clean(m.c.select.T*m.c.consistency_matrix(phi)*m.c.select)
    equal(D, oldD)
    for h, T in enumerate(m.rho_s):
        C = m.C[h]
        dD = clean(m.graph.O.T*s.Matrix.hstack(*[B*T*phi for B in m.rho_b]))
        equal(dD, -C.T*D-D*C)
        # The same identity also makes det D invariant (Tr C=0).
        equal(m.graph.O.T*T*phi, s.zeros(9, 1))
        # Scalar kinetic/shift/potential covariance follows before squaring:
        # [G_s,Pi_j]=-i rho_s[j,k] Pi_k, V_s b=rho_s b.
        # Check every gauge coefficient in U_i=rho(A_i)phi, including the
        # fixed vacuum; bilinearity then pays every A_i and all x.
        for a in range(12):
            equal(combine(m.c.rho, m.ad_s[h][:, a])*phi+m.c.rho[a]*T*phi,
                  T*m.c.rho[a]*phi)
        # The native pairing and the complete bracket tensor pay all gauge
        # curvature coefficients, hence magnetic and electric shifted squares.
        for a in range(12):
            for b in range(12):
                ea, eb = s.eye(12)[:, a], s.eye(12)[:, b]
                equal(m.ad_s[h]*m.gauge.bracket(ea, eb),
                      m.gauge.bracket(m.ad_s[h]*ea, eb)+m.gauge.bracket(ea, m.ad_s[h]*eb))
    # Full original Yukawa, all70 real scalar coefficients and all252 modes.
    Y = m.graph.common.yukawa_basis
    Y = Y+[s.I*M for M in Y]
    for h, T in enumerate(m.rho_s252):
        for a in range(70):
            equal(T*Y[a]-Y[a]*T, combine(Y, m.rho_s[h][:, a]))
        # The full live coframe currents, inverse principal and their q
        # derivatives are spin-only tensor I63. Check the exact tensor factor
        # at the source of the coefficient construction, for both branches.
        internal = T[:63, :63]
        equal(T, s.kronecker_product(s.eye(4), internal))
        for a in range(12):
            equal(T*m.graph.common.rho[a]-m.graph.common.rho[a]*T,
                  combine(m.graph.common.rho, m.ad_s[h][:, a]))
    cf = m.joint.coframe
    for matrix in cf.J+cf.T+cf.M+[cf.correction, cf.one_body]:
        equal(matrix[:4, 4:], s.zeros(4)); equal(matrix[4:, :4], s.zeros(4))
    return {'all61_scalar_coefficients_symbolic': True,
            'same_D9_and_same_original_scalar61': True,
            'D_covariance': 'V_s(D)=-C_s^T D-D C_s',
            'inverse_covariance': 'Differentiate D^T F=1 and multiply by its existing inverse: V_s(F)=C_s F+F C_s^T.',
            'normal_current_covariance': '[G_s,G_B]=i C_s^T G_B; zeta=-F G_B gives [G_s,zeta]=-i C_s zeta.',
            'complete_scalar_momentum_covariance': '[G_s,Pi_phi]=-i rho_s Pi_phi for Pi_phi=Rdual*(-i partial_x)+O*zeta.',
            'scalar_energy': 'The original rho_s is real skew and fixes v. The shifted momentum transforms in the same70 representation; contracting the ordered square and all U_i dot U_j cancels termwise, without reordering momenta.',
            'gauge_energy': 'All432 native bracket derivation identities and native Gram invariance preserve B(A), the dual shift C and its ordered electric square for every coframe coefficient.',
            'coframe_energy': 'Gauge currents act on internal63; every original live coframe current is block-diagonal spin4 tensor I63 on both branches. q and all its derivatives are gauge invariant, so the complete ordered live square commutes.',
            'matter_energy': 'All210 full252 Yukawa covariance identities and all36 native representation identities give V_s Hm=[rho_s,Hm]. Thus [-i V_s+dGamma(i rho_s),dGamma(Hm)]=0 on both original branches.',
            'operator_identity': '[G_s,H_native_orthogonal]=0 for s=0,1,2 on the common103 compact smooth CCR-CAR domain',
            'domain_kernel_preservation': 'Every G_s and H preserves the same compact support and particle sector. The displayed identity gives G_s(H f)=H(G_s f), hence the simultaneous three-Gauss kernel is invariant under every finite power of H.',
            'time_evolution_or_Hilbert_spectral_measure_inferred': False}


def rref_difference(m, x):
    phi = m.c.vacuum+m.graph.R*x
    D = clean(m.c.select.T*m.c.consistency_matrix(phi)*m.c.select)
    F = clean(D.T.inv())
    oldW = m.c.select.row_join(m.S)
    residuals = []; nonzero = []
    for h in range(3):
        E = clean(oldW.inv()*m.ad_s[h]*oldW)[9:, :9]
        anomaly = s.zeros(1, 9)
        for k in range(3):
            anomaly += (m.graph.O*F*E[k, :].T).T*m.rho_s[k]*m.graph.O*F
        anomaly = clean(anomaly)
        nonzero.append(bool(anomaly.todok()))
        residuals.append({'generator': h, 'complement_defect': encode(E),
                          'scalar_square_reordering_coefficient_before_1_over_2h00': encode(anomaly)})
    assert nonzero == [True, True, False]
    # No constraint is dropped in the corrected normal momentum. On the
    # complete classical Gauss surface the two embeddings coincide exactly.
    equal(m.B, m.c.select-m.S*m.J)
    return {'normal_momentum_difference': 'Pi_new-Pi_rref=O F J^T G_stabilizer',
            'classical_full_Gauss_surface_same_original_energy': True,
            'quantization_sequence': 'native Gram orthogonal complement -> original momentum graph -> coefficient-left ordered square',
            'old_quantum_square_equivalent_on_constraint_kernel_claimed': False,
            'old_rref_ordering_retained_as_previously_signed_operator': True,
            'actual_nonzero_rref_reordering_coefficients': residuals}


def actual_consumers(m):
    q = (s.Rational(7, 6), s.Rational(1, 11), s.Rational(9, 8),
         s.Rational(-1, 13), s.Rational(1, 17), s.Rational(11, 10))
    x = s.Matrix([s.Rational((3*j+1) % 7-3, 100) for j in range(61)])
    active = m.scalar.graph.common.scalar.exchange.active['actual_background']
    A = s.Matrix(active['gauge_connection']).applyfunc(s.sympify)[1:, :]
    A[0, 2] += s.Rational(1, 17); A[1, 7] += s.Rational(1, 19)
    y = x.col_join(A.reshape(36, 1))
    metric = clean(s.diag(m.graph.R.T*m.graph.R, *[m.gauge.gram]*3))
    gradient = s.Matrix.vstack(s.Matrix([s.Rational(j+1, 29) for j in range(6)]), -2*metric*y)
    Hessian = gradient*gradient.T-s.diag(s.eye(6), 2*metric)
    state = (7, 259)
    # A stabilizer-invariant compact cutoff of q and the native quadratic
    # scalar/gauge norm realizes this same nonzero jet on the actual chart.
    for h in range(3):
        equal(m.T_s[h].T*metric+metric*m.T_s[h], s.zeros(97))
        assert m.constraint_action(h, x, A, {state: 1}, 1, gradient) == {}
    data, components, image = m.action(q, x, A, state, gradient, Hessian)
    assert image and all(components.values())
    # All residual operators really act; a charged CAR germ is not silently
    # treated as a physical state. Universal matrix Lie checks above cover
    # arbitrary degree; this tensor-polynomial consumer checks actual words.
    boson = next(j for j in range(97) if any(T[:, j].todok() for T in m.T_s))
    input_state = {(boson, (5,)): s.S.One}
    matrices = [clean(-s.I*T.T) for T in m.T_s]
    images = [tensor_current(T, Q, input_state) for T, Q in zip(matrices, m.Q_s)]
    assert all(images)
    for h in range(3):
        for k in range(3):
            lhs = weighted_sum([(1, tensor_current(matrices[h], m.Q_s[h], images[k])),
                                (-1, tensor_current(matrices[k], m.Q_s[k], images[h]))])
            rhs = weighted_sum((s.I*f, images[j]) for j, f in enumerate(m.structure[h][:, k]))
            assert weighted_sum([(1, lhs), (-1, rhs)]) == {}
    return {'configuration': {'q': list(map(str, q)), 'x': encode(x), 'A': encode(A)},
            'nonzero_simultaneous_Gauss_kernel_state': {'CAR': list(state),
                'function': 'eta_q(q) eta_inv(x,A) exp(-x^T(R^T R)x-sum_i A_i^T Gram A_i), with invariant compact eta_inv supported inside det D!=0 and equal1 near the displayed orbit',
                'all_three_constraint_actions_exact_zero': True,
                'complete_new_Hamiltonian_image': encode_state(image),
                'all_four_energy_components_nonzero': True},
            'charged_tensor_polynomial': {'boson_coordinate': boson, 'CAR': [5],
                'all_three_constraints_nonzero': True, 'all9_actual_CAR_CCR_Lie_words_checked': True},
            'rref_difference': rref_difference(m, x)}


def main():
    started = time.monotonic(); model = SourceQuantumStabilizer()
    algebra = verify_native_algebra(model)
    print('PASS original stabilizer su(2), native orthogonal complement and complete Gauss Lie identities', flush=True)
    covariance = verify_graph_and_energies(model)
    print('PASS generic original D^-T and all four energy covariance identities on103 coordinates', flush=True)
    consumers = actual_consumers(model)
    print('PASS actual nonzero three-Gauss kernel state and complete covariant Hamiltonian action', flush=True)
    inputs = [HERE/name for name in ('source_quantum_stabilizer.py', 'source_joint_local_quantum.py',
        'source_joint_local_quantum.json', 'source_coframe_live_ordering.py', 'source_scalar_shift_quantum.py',
        'source_gauss_live_ordering.py', 'source_scalar_gauss_reduction.py', 'source_constraint_preservation.py',
        'source_gauge_legendre.py', 'source_gauge_quantum_energy.py', 'source_common_hamiltonian.py',
        'source_gauss_quantum_current.py')]
    result = {'root': ROOT_ID, 'source_sha256': model.graph.common.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs},
        'scope': 'NATIVE_ORTHOGONAL_GAUSS_ORDERED_HAMILTONIAN_AND_THREE_STABILIZER_KERNEL_INVARIANCE',
        'native_stabilizer': algebra, 'generic_covariance': covariance, 'actual_consumers': consumers,
        'domain': 'the same Cc_infinity(U_q times U_x times R36) tensor algebraic CAR(Fin504); U_x:det D9!=0',
        'four_temporal_constraints_solved': False, 'full_spatial_quantum_evolution_or_spectrum_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_quantum_stabilizer.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source stabilizer constraint-preserving ordered Hamiltonian', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
