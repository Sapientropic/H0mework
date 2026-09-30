#!/usr/bin/env python3
"""Actual remaining source Gauss slice on the common classical phase space.

Three source connection coordinates fix the residual stabilizer orbit. The
complete moment map solves their three conjugate momenta; its pullback keeps
the other604 canonical pairs. This is a local classical symplectic chart,
not a quantum measure or a comparison with the linear-response coordinates.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, decode
from source_scalar_gauss_reduction import SourceScalarGaussReduction
from source_coframe_live_ordering import SourceCoframeLiveOrdering, FREE
from source_gauge_legendre import realify
from source_common_hamiltonian import real
from source_coframe_legendre import rational
from source_lorentz_contact import clean, equal, encode


def block_diagonal(*blocks):
    result = s.MutableSparseMatrix(sum(B.rows for B in blocks), sum(B.cols for B in blocks), {})
    row = col = 0
    for B in blocks:
        for (i, j), value in B.todok().items():
            result[row+i, col+j] = value
        row += B.rows; col += B.cols
    return result


def zero_matrix(A):
    equal(rational(A), s.zeros(*A.shape))


def canonical_J(n):
    J = s.MutableSparseMatrix(2*n, 2*n, {})
    for j in range(n):
        J[j, n+j] = 1; J[n+j, j] = -1
    return J


class SourceStabilizerPhaseReduction:
    def __init__(self):
        self.graph = SourceScalarGaussReduction()
        self.common, self.gauge = self.graph.common, self.graph.common.gauge
        self.S = self.graph.stabilizer
        self.native_reader = rational((self.S.T*self.gauge.gram*self.S).inv()*self.S.T*self.gauge.gram)
        self.scalar, self.adjoint, self.matter, self.L = [], [], [], []
        for j in range(3):
            rho = clean(sum((self.S[a, j]*self.graph.constraints.rho[a] for a in range(12)), s.zeros(70)))
            X = clean(self.graph.dual_R.T*rho*self.graph.R)
            zero_matrix(rho*self.graph.constraints.vacuum)
            zero_matrix(rho*self.graph.R-self.graph.R*X)
            zero_matrix(self.graph.O.T*rho*self.graph.R)
            ad = self.gauge.ad(self.S[:, j])
            full = clean(sum((self.S[a, j]*self.common.rho[a] for a in range(12)), s.zeros(252)))
            self.scalar.append(X); self.adjoint.append(ad); self.matter.append(full)
            self.L.append(block_diagonal(s.zeros(6), X, ad, ad, ad, realify(full)))
        self.n = 607
        self.J = canonical_J(self.n)
        self.lie = {(a, b): clean(self.native_reader*self.gauge.bracket(self.S[:, a], self.S[:, b]))
                    for a in range(3) for b in range(3)}
        for (a, b), coefficients in self.lie.items():
            zero_matrix(self.gauge.bracket(self.S[:, a], self.S[:, b])-self.S*coefficients)
            zero_matrix(self.L[a]*self.L[b]-self.L[b]*self.L[a]-
                        sum((coefficients[c]*self.L[c] for c in range(3)), s.zeros(self.n)))
        for L in self.L:
            lift = block_diagonal(L, -L.T)
            zero_matrix(lift.T*self.J+self.J*lift)
        background = self.common.scalar.exchange.active['actual_background']
        self.e0 = s.Matrix(background['coframe']).applyfunc(s.sympify)
        self.A0 = s.Matrix(background['gauge_connection']).applyfunc(s.sympify)
        occupied = json.loads((BASE/'occupied-response/receipt.json').read_text())
        self.psi0 = clean(decode(occupied['occupied_frame'])*s.Matrix(background['primal_H']).applyfunc(s.sympify))
        self.chi0 = clean(s.sympify(background['dual_multiple'])*self.psi0.T)
        self.source_momenta = self.common.momenta(self.e0, s.zeros(64, 1),
            self.graph.constraints.vacuum, [s.zeros(70, 1)]*4,
            self.A0, s.zeros(4, 48), self.psi0, self.chi0)
        for key, shape in [('coframe', (16, 1)), ('scalar', (70, 1)), ('gauge', (3, 12))]:
            equal(self.source_momenta[key], s.zeros(*shape))
        self.p0 = self.source_momenta['matter']
        self.q0 = clean(s.Matrix.vstack(s.Matrix([self.e0[j] for j in FREE]), s.zeros(61, 1),
            self.A0[1:, :].reshape(36, 1), self.psi0.applyfunc(s.re), self.psi0.applyfunc(s.im)))
        self.P0 = clean(s.Matrix.vstack(s.zeros(103, 1), -self.p0.T.applyfunc(s.im), -self.p0.T.applyfunc(s.re)))
        source_orbit = self.orbit(self.q0)
        gauge_orbit = source_orbit[67:103, :]
        self.gauge_pivots = tuple(gauge_orbit.T.rref()[1])
        assert len(self.gauge_pivots) == 3
        self.pivots = tuple(67+j for j in self.gauge_pivots)
        self.free = tuple(j for j in range(self.n) if j not in self.pivots)
        self.Ip = s.SparseMatrix(self.n, 3, {(row, j): 1 for j, row in enumerate(self.pivots)})
        self.If = s.SparseMatrix(self.n, 604, {(row, j): 1 for j, row in enumerate(self.free)})
        self.source_minor = clean(self.Ip.T*source_orbit)
        assert self.source_minor.det() != 0
        equal(self.If.T*self.If, s.eye(604)); equal(self.Ip.T*self.Ip, s.eye(3))
        zero_matrix(self.If.T*self.Ip)
        equal(self.If*self.If.T+self.Ip*self.Ip.T, s.eye(self.n))

    def orbit(self, q):
        return clean(s.Matrix.hstack(*(L*q for L in self.L)))

    def moment(self, q, P):
        return rational(self.orbit(q).T*P)

    def gauge_fix(self, q):
        return clean(self.Ip.T*(q-self.q0))

    def embed(self, q_free, P_free):
        """Original full moment map, with no constraint on the604 free pairs."""
        q = clean(self.If*q_free+self.Ip*self.Ip.T*self.q0)
        V = self.orbit(q); M = clean(self.Ip.T*V)
        determinant = s.factor(M.det())
        if determinant == 0:
            raise ValueError('The source stabilizer slice requires det orbit_minor != 0.')
        inverse = rational(M.adjugate()/determinant)
        rest = clean(V.T*self.If*P_free)
        dependent = rational(-inverse.T*rest)
        P = rational(self.If*P_free+self.Ip*dependent)
        zero_matrix(self.moment(q, P)); zero_matrix(self.gauge_fix(q))
        return {'q': q, 'P': P, 'minor': M, 'minor_inverse': inverse,
                'dependent_momenta': dependent, 'complete_remaining_current': rest}

    def retract(self, q, P):
        return {'q': clean(self.If.T*q), 'P': clean(self.If.T*P)}

    def constraint_matrix(self, q, P):
        """All six canonical brackets, including the off-level Gauss block."""
        V = self.orbit(q); M = clean(self.Ip.T*V)
        G = self.moment(q, P)
        U = s.Matrix(3, 3, lambda a, b: (self.lie[a, b].T*G)[0])
        C = rational(U.row_join(-M.T).col_join(M.row_join(s.zeros(3))))
        determinant = s.factor(M.det())
        if determinant == 0:
            raise ValueError('The source constraint/gauge-fixing matrix is singular outside its chart.')
        inverse = rational(M.adjugate()/determinant)
        D = rational(s.zeros(3).row_join(inverse).col_join(
            (-inverse.T).row_join(inverse.T*U*inverse)))
        zero_matrix(C*D-s.eye(6)); zero_matrix(D*C-s.eye(6))
        gradG = s.Matrix.vstack(*[(self.L[a].T*P).T.row_join(V[:, a].T) for a in range(3)])
        gradients = s.SparseMatrix(gradG.col_join(self.Ip.T.row_join(s.zeros(3, self.n))))
        zero_matrix(gradients*self.J*gradients.T-C)
        return {'matrix': C, 'inverse': D, 'Gauss': G, 'gradients': gradients}

    def original_readback(self, q, P):
        """Restore all original scalar/gauge/matter fields and the broken graph."""
        e = self.e0.copy()
        for j, value in zip(FREE, q[:6, 0]):
            e[j] = value
        x, pi = q[6:67, :], P[6:67, :]
        A = s.zeros(4, 12); A[1:, :] = q[67:103, :].reshape(3, 12)
        Pi_A = P[67:103, :].reshape(3, 12)
        psi = clean(q[103:355, :]+s.I*q[355:607, :])
        p = clean((-P[355:607, :]-s.I*P[103:355, :]).T)
        scalar = self.graph.embed(x, pi, A, Pi_A, [s.zeros(3, 12)]*3, psi, p)
        raw = self.common.gauss(e, scalar['phi'], scalar['Pi_phi'], A, Pi_A,
                                [s.zeros(3, 12)]*3, psi, p)
        zero_matrix(self.S.T*raw['total']-self.moment(q, P))
        zero_matrix(self.graph.select.T*raw['total'])
        # The original independent complex dual has no adjoint premise.
        v = s.Matrix([s.Rational((3*j+1) % 11-5, 19)+s.I*s.Rational((5*j+2) % 13-6, 23)
                      for j in range(252)])
        real_velocity = s.Matrix.vstack(v.applyfunc(s.re), v.applyfunc(s.im))
        assert s.expand(real((s.I*p*v)[0])-(P[103:, :].T*real_velocity)[0]) == 0
        return {'e': e, 'psi': psi, 'p': p, 'A': A, 'Pi_A': Pi_A,
                'scalar': scalar, 'raw_Gauss': raw['total']}


def main():
    started = time.monotonic(); m = SourceStabilizerPhaseReduction()
    source = m.original_readback(m.q0, m.P0)
    zero_matrix(source['raw_Gauss']); equal(source['p'], m.p0)
    zero_matrix(m.moment(m.q0, m.P0)); zero_matrix(m.gauge_fix(m.q0))
    source_chart = m.embed(m.If.T*m.q0, m.If.T*m.P0)
    equal(source_chart['q'], m.q0); equal(source_chart['P'], m.P0)
    source_constraints = m.constraint_matrix(m.q0, m.P0)
    print('PASS original source momenta/full12 Gauss, actual stabilizer orbit rank3 and all607-pair moment-map Lie/symplectic identities', flush=True)

    # The exact local chart retains every other coordinate, rather than
    # accepting a ready-made1208-dimensional carrier or a solution of Gauss.
    qf = m.If.T*m.q0+s.Matrix([s.Rational((7*j+3) % 17-8, 10000) for j in range(604)])
    Pf = m.If.T*m.P0+s.Matrix([s.Rational((11*j+2) % 19-9, 1000) for j in range(604)])
    fixture = m.embed(qf, Pf)
    assert fixture['dependent_momenta'].todok()
    back = m.retract(fixture['q'], fixture['P'])
    equal(back['q'], qf); equal(back['P'], Pf)
    raw = m.original_readback(fixture['q'], fixture['P'])
    zero_matrix(raw['raw_Gauss'])
    # Reconstruct the six already-solved Spin primary momenta at the same
    # genuinely live coframe and independent full matter configuration.
    cf = SourceCoframeLiveOrdering(); coefficients = cf.coefficients(tuple(fixture['q'][:6, 0]))
    spin = s.Matrix([real((s.I*raw['p']*s.kronecker_product(S, s.eye(63))*raw['psi'])[0])
                     for S in cf.model.lorentz.spin])
    Pi_e = clean(coefficients['A']*fixture['P'][:6, :]+coefficients['S']*spin)
    spatial = raw['e'].copy(); spatial[:, 0] = s.zeros(4, 1)
    Z = s.Matrix.hstack(*[(T*spatial).reshape(16, 1) for T in cf.model.lorentz.basis])
    zero_matrix(Z.T*Pi_e+spin)
    equal(Pi_e.extract([0, 4, 8, 12], [0]), s.zeros(4, 1))
    equal(s.eye(16)[:, FREE].T*Pi_e, fixture['P'][:6, :])
    equal(m.graph.R.T*raw['scalar']['Pi_phi'], fixture['P'][6:67, :])

    # The bracket matrix is verified both on and off its constraint level.
    reduced_brackets = m.constraint_matrix(fixture['q'], fixture['P'])
    ambientP = fixture['P']+m.Ip*s.Matrix([s.Rational(1, 13), s.Rational(-2, 17), s.Rational(3, 19)])
    ambient = m.constraint_matrix(fixture['q'], ambientP)
    assert ambient['Gauss'].todok() and ambient['matrix'][:3, :3].todok()
    # Canonical Dirac brackets of the surviving pairs are exactly J604.
    readout = block_diagonal(m.If.T, m.If.T)
    G = reduced_brackets['gradients']
    correction = readout*m.J*G.T*reduced_brackets['inverse']*G*m.J*readout.T
    zero_matrix(correction)
    equal(readout*m.J*readout.T, canonical_J(604))
    print('PASS actual604-pair gauge slice, full original broken/stabilizer Gauss and Spin readback, off-level six-constraint inverse and canonical Dirac brackets', flush=True)

    # Universal pullback: all derivatives of the solved momenta disappear
    # because the corresponding configuration differentials are zero.
    equal(m.If.T*m.If, s.eye(604)); zero_matrix(m.If.T*m.Ip)
    gauge_coordinates = s.Matrix(s.symbols('a0:36', real=True))
    for pivot in m.gauge_pivots:
        gauge_coordinates[pivot] = m.q0[67+pivot]
    M = s.Matrix.hstack(*(block_diagonal(ad, ad, ad)*gauge_coordinates for ad in m.adjoint))
    M = M[list(m.gauge_pivots), :]
    inverse = rational(M.adjugate()/M.det())
    equal(rational(M*inverse), s.eye(3)); equal(rational(inverse*M), s.eye(3))
    symbolic_current = s.Matrix(s.symbols('complete_current0:3', real=True))
    equal(rational(M.T*(-inverse.T*symbolic_current)+symbolic_current), s.zeros(3, 1))
    paths = [HERE/name for name in ('source_stabilizer_phase_reduction.py',
        'source_scalar_gauss_reduction.py', 'source_scalar_gauss_reduction.json',
        'independent_source_scalar_gauss_reduction.json', 'source_common_hamiltonian.py',
        'source_coframe_live_ordering.py', 'source_coframe_live_ordering.json',
        'independent_source_coframe_live_ordering.json', 'source_constraint_preservation.py',
        'source_gauge_legendre.py', 'source_lorentz_contact.py',
        'source_joint_local_quantum.json', 'independent_source_joint_local_quantum.json')]
    paths += [BASE/'active-gauge/receipt.json', BASE/'occupied-response/receipt.json']
    result = {'root': ROOT_ID, 'source_sha256': m.common.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'scope': 'ACTUAL_LOCAL_STABILIZER_SYMPLECTIC_REDUCTION_OF_COMMON1214_PHASE_TO1208',
        'coordinates': {'configuration607': 'coframe6, scalar61, gauge36, Re(psi252), Im(psi252)',
            'canonical_momenta': 'kappa6, pi61, Pi_A36, -Im(p252), -Re(p252)',
            'source_independent_p': encode(m.p0), 'source_all_boson_momenta_zero': True,
            'source_all12_raw_Gauss_zero': True},
        'stabilizer': encode(m.S), 'native_Lie': {str(pair): encode(value) for pair, value in m.lie.items()},
        'all9_full607_moment_map_Lie_identities': True,
        'all3_full1214_cotangent_lifts_symplectic': True,
        'moment_map': 'G_s=Pi^T L_s q, with original scalar Gauss graph and full independent canonical matter; no spatial divergence in this homogeneous phase chart',
        'slice': {'gauge_coordinate_pivots': list(m.gauge_pivots), 'whole_coordinate_pivots': list(m.pivots),
            'fixed_values': encode(m.Ip.T*m.q0), 'source_orbit_minor': encode(m.source_minor),
            'source_minor_determinant': str(s.factor(m.source_minor.det())),
            'generic_slice_minor': encode(M), 'generic_slice_minor_determinant': str(s.factor(M.det())),
            'generic_both_inverse_and_all_current_solution_checked': True},
        'embedding': 'q=If*q_free+Ip*Ip^T*q_source; Pi=If*Pi_free-Ip*M(q)^(-T)*V(q)^T*If*Pi_free',
        'retraction': '(q_free,Pi_free)=(If^T q,If^T Pi)',
        'one_form': 'Pi^T dq=Pi_free^T dq_free; If^T Ip=0 kills every derivative of the generated dependent momenta',
        'symplectic_form': 'pullback sum607 dPi_j wedge dq_j = sum604 dPi_free_j wedge dq_free_j',
        'constraint_bracket': 'C=[[f_ab^c G_c,-M^T],[M,0]], inverse=[[0,M^-1],[-M^-T,M^-T(fG)M^-1]]',
        'source_constraint_matrix': encode(source_constraints['matrix']),
        'source_constraint_inverse': encode(source_constraints['inverse']),
        'actual_full_configuration': encode(fixture['q']), 'actual_free_momenta': encode(Pf),
        'actual_generated_dependent_momenta': encode(fixture['dependent_momenta']),
        'actual_off_level_Gauss_control': encode(ambient['Gauss']),
        'actual_original_all12_Gauss_and10_coframe_primary_zero': True,
        'actual_remaining_pairs_canonical_Dirac_brackets': True,
        'local_quotient': 'The linear source stabilizer representation integrates analytically near identity. The derivative of alpha -> gauge_fix(exp(sum alpha_s L_s)q) at (0,q_source) is the displayed invertible source minor; the local analytic implicit-function theorem generates a unique small group parameter placing each nearby configuration in the slice. The solved momenta then give every nearby Gauss-zero orbit its local604-pair representative.',
        'domain': 'original coframe and scalar D9 source charts, det M(q)!=0; source itself and the displayed nontrivial full-field configuration both lie in this chart',
        'phase_dimension_before': 1214, 'phase_dimension_after': 1208,
        'retained126_plus_tail1082_congruence_claimed': False,
        'quantum_Hilbert_measure_or_gauge_physical_state_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_stabilizer_phase_reduction.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS original stabilizer phase reduction', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
