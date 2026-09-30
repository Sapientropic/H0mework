#!/usr/bin/env python3
"""Actual tail tangent of the original nonlinear physical source chart.

The independent dual is converted by the original temporal principal, not
by a Hilbert adjoint. The nonzero scalar-dual Hamiltonian coupling and the
source co-rotating Noether shift remain in the symplectic identification.
The active126 complement still requires its original BF/Ward slice map.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID
from source_full_linear_split import SourceFullLinearSplit, K, P, realify, real_pair, assemble, coefficients
from source_stabilizer_phase_reduction import SourceStabilizerPhaseReduction, canonical_J, block_diagonal
from source_lorentz_contact import clean, equal, encode


def zero(A): equal(clean(A), s.zeros(*A.shape))


class SourcePhysicalPhaseSplice:
    def __init__(self):
        self.chart = SourceStabilizerPhaseReduction()
        self.split = SourceFullLinearSplit()
        c, m = self.chart, self.split
        equal(c.e0, m.e); equal(c.psi0, m.psi0); equal(c.chi0, m.chi0)
        equal(c.graph.R, m.R)
        E0 = c.common.matter_data(c.e0, c.graph.constraints.vacuum, c.A0)['E']
        equal(E0, m.E); equal(c.p0, -s.I*m.chi0*m.E)
        self.V0 = c.orbit(c.q0)
        Gq = s.Matrix.vstack(*((L.T*c.P0).T for L in c.L))
        self.Ggrad = clean(Gq.row_join(self.V0.T))
        Mi = clean(c.source_minor.inv())
        top = c.If.row_join(s.zeros(607, 604))
        bottom = (-c.Ip*Mi.T*Gq*c.If).row_join(c.If-c.Ip*Mi.T*self.V0.T*c.If)
        self.chart_tangent = clean(top.col_join(bottom))
        self.chart_reader = block_diagonal(c.If.T, c.If.T)
        equal(self.chart_reader*self.chart_tangent, s.eye(1208))
        zero(self.Ggrad*self.chart_tangent)
        zero(c.Ip.T*self.chart_tangent[:607, :])
        equal(self.chart_tangent.T*c.J*self.chart_tangent, canonical_J(604))
        # beta is the independent complex240 row-coordinate of chi. Its
        # canonical momentum is (Re(beta E_C),-Im(beta E_C)), whereas q is
        # (Re psi,Im psi). No condition identifies beta with psi^*.
        self.Creal = block_diagonal(m.C, m.C)
        EC = clean(m.C.H*m.E*m.C)
        self.dual_momentum = real_pair(EC.T)
        conjugation = s.diag(s.eye(240), -s.eye(240))
        self.dual_reader = clean(realify(EC.inv().T)*conjugation)
        equal(self.dual_reader*self.dual_momentum, s.eye(480))
        equal(self.dual_momentum*self.dual_reader, s.eye(480))
        X = assemble(1214, 1082, [(6, 480, s.eye(61)), (607+6, 541, s.eye(61)),
            (103, 602, self.Creal), (607+103, 0, self.Creal*self.dual_momentum)])
        L = assemble(1082, 1214, [(480, 6, s.eye(61)), (541, 607+6, s.eye(61)),
            (602, 103, self.Creal.T), (0, 607+103, self.dual_reader*self.Creal.T)])
        equal(L*X, s.eye(1082))
        zero(self.Ggrad*X); zero(c.Ip.T*X[:607, :])
        self.tail_embedding = clean(self.chart_reader*X)
        self.tail_reader = clean(L*self.chart_tangent)
        equal(self.tail_reader*self.tail_embedding, s.eye(1082))
        equal(self.chart_tangent*self.tail_embedding, X)
        self.ambient_tail = X
        self.omega = clean(-X.T*c.J*X)
        expected = assemble(1082, 1082, [(0, 602, self.dual_momentum.T),
            (602, 0, -self.dual_momentum), (480, 480, -canonical_J(61))])
        equal(self.omega, expected)
        self.omega_inverse = assemble(1082, 1082, [(0, 602, -self.dual_reader),
            (602, 0, self.dual_reader.T), (480, 480, canonical_J(61))])
        equal(self.omega*self.omega_inverse, s.eye(1082))
        equal(self.omega_inverse*self.omega, s.eye(1082))
        # The affine source one-form has no tail term: source momenta are in
        # occupied12, while every tail matter coordinate lies in its complement.
        zero(c.P0.T*X[:607, :])
        self.blocks = m.tail_blocks()
        self.generator = m.tail_generator(K)

    def original_constraints(self):
        m, c = self.split, self.chart
        # Every source non-scalar transition connecting the occupied background
        # to the matter complement vanishes before any momentum substitution.
        checked = 0
        for row, V in zip(m.vertices['primitive_vertices'], m.V):
            if row['group'] == 'scalar':
                zero(m.chi0*V*m.psi0)
                continue
            for W in coefficients(V):
                zero(m.C.H*W*m.psi0); zero(m.chi0*W*m.C)
                checked += 1
        # Scalar/gauge first variations come from the same original mixed
        # density. D_mu v=0 and P61 invariance make the peripheral source zero.
        h = m.N*m.e.inv()*s.diag(-1, 1, 1, 1)*m.e.inv().T
        RA = [clean(sum((m.A[mu, a]*m.common.scalar.rho[a] for a in range(12)), s.zeros(70))) for mu in range(4)]
        for T in RA:
            zero(T*m.common.scalar.vacuum)
            equal(T*m.P61, m.P61*T)
        for nu in range(4):
            for a in range(12):
                mixed = clean(-sum((h[mu, nu]*(P[mu]*s.eye(70)+RA[mu])*m.common.scalar.rho[a]*m.common.scalar.vacuum
                                   for mu in range(4)), s.zeros(70, 1)))
                zero(m.R.T*mixed)
        zero(self.ambient_tail[67:103, :]); zero(self.ambient_tail[607+67:607+103, :])
        # Thus the extra spatial divergence in every original Gauss equation
        # vanishes on this very tangent, at arbitrary real spatial momentum.
        for i in range(3): zero(K[i]*self.ambient_tail[607+67+12*i:607+79+12*i, :])
        return {'all_nonscalar_current_coefficients_checked': checked,
            'all48_original_scalar_gauge_mixed_columns_zero': True,
            'full12_Gauss_tangent_and_all_spatial_divergences_zero': True,
            'temporal_F4_tail_restriction': 'The original time-coframe Jacobi rows have no tail columns: all their coframe vertices have zero occupied/complement transitions, scalar background covariant derivatives vanish, and every chi0 Y(phi) psi0 scalar coefficient is zero.',
            'original_spin_and_broken_Gauss_momentum_shifts': 'Their linear matter currents vanish by the same source vertex identities. Thus delta kappa=0 and the scalar normal momentum variation is zero on this full tail; only the original scalar61 momentum remains.'}

    def hamiltonian_and_phase(self):
        m, B = self.split, self.blocks
        minus = dict(zip(K, [-k for k in K]))
        star = lambda A: clean(A.subs(minus, simultaneous=True).T)
        KC = clean(m.C.H*m.K0*m.C)
        Ei = [clean(m.C.H*M*m.C) for M in m.Ei]
        pair = clean(real_pair(KC)+sum((s.I*k*real_pair(M) for k, M in zip(K, Ei)), s.zeros(480)))
        scalar_hessian = clean(-canonical_J(61)*B['scalar'])
        Jchi = B['dual_to_scalar'][61:, :]
        H = assemble(1082, 1082, [(480, 480, scalar_hessian), (0, 602, -pair),
            (602, 0, -star(pair)), (0, 480, -Jchi.T), (480, 0, -Jchi)])
        # These are original density coefficients, assembled before comparing
        # to the existing source response. In particular the cross is nonzero.
        assert Jchi.todok()
        equal(self.omega*self.generator, H)
        equal(star(H), H)
        zero(star(self.generator)*self.omega+self.omega*self.generator)
        equal(self.omega_inverse*H, self.generator)
        phase = json.loads((HERE/'source_stationary_cauchy_orbit.json').read_text())
        omega = s.sympify(phase['source_frequency'])
        Rp, Rd = s.diag(*phase['primal_integer_rates']), s.diag(*phase['independent_dual_integer_rates'])
        zero(Rd*m.E+m.E*Rp)
        Qp = clean(s.I*omega*m.C.H*Rp*m.C)
        Qd = clean(s.I*omega*m.C.H*Rd*m.C)
        Ap, Ad = realify(Qp), realify(Qd)
        equal(self.dual_momentum*Ad, -Ap.T*self.dual_momentum)
        phase_generator = assemble(1082, 1082, [(0, 0, Ad), (602, 602, Ap)])
        zero(phase_generator.T*self.omega+self.omega*phase_generator)
        EC = clean(m.C.H*m.E*m.C)
        original_constant = clean(KC-EC*Qp)
        original_pair = clean(real_pair(original_constant)+sum((s.I*k*real_pair(M) for k, M in zip(K, Ei)), s.zeros(480)))
        original_H = assemble(1082, 1082, [(480, 480, scalar_hessian), (0, 602, -original_pair),
            (602, 0, -star(original_pair)), (0, 480, -Jchi.T), (480, 0, -Jchi)])
        equal(original_H-H, self.omega*phase_generator)
        self.hessian = H
        return {'original_density_Hamiltonian_hessian': encode(H), 'nonzero_scalar_dual_cross': encode(Jchi),
            'all_real_three_momenta_Hamiltonian_identity': 'Omega_tail A_tail(k)=H_tail(k), H_tail(-k)^T=H_tail(k)',
            'actual_canonical_intertwining': 'X_tail A_tail = (X_tail Omega_tail^-1 H_tail R_tail) X_tail, with R_tail X_tail=I1082 in the actual1208 source tangent',
            'phase_generator': encode(phase_generator),
            'Noether_shift': 'H_original-H_stationary=Omega_tail Q_phase; the original canonical momentum transforms by the inverse transpose of the primal phase. The scalar-dual cross is unchanged and nonzero.',
            'proper_clock': 'tau=N*t with N='+str(m.N),
            'Fourier_reality': 'Internal coefficients are realified before d_i=i*k_i; nonzero k fibers pair with their conjugate at -k.'}


def main():
    started = time.monotonic(); m = SourcePhysicalPhaseSplice()
    print('PASS actual nonlinear604-pair chart tangent, full independent-dual momentum map and1082-dimensional source one-form pullback', flush=True)
    constraints = m.original_constraints()
    print('PASS complete source tail tangent Gauss/Spin/time restrictions and all spatial Gauss divergences', flush=True)
    energy = m.hamiltonian_and_phase()
    # Apply the same canonical map to the actual nonzero two-stage scalar
    # response, rather than reporting only its matrix size.
    cascade = m.blocks['third_time_cascade']
    column = min(j for _, j in cascade.todok())
    initial = s.eye(1082)[:, column]
    triple = clean(m.generator.subs(dict.fromkeys(K, 0))**3*initial)
    expected_primal = cascade[:, column]
    equal(triple[602:, :], expected_primal)
    assert expected_primal.todok()
    lifted = clean(m.tail_embedding*triple)
    equal(m.tail_reader*lifted, triple)
    print('PASS original full-k tail Hamiltonian, canonical phase Noether shift and actual nonzero third-time response in the reduced chart', flush=True)
    paths = [HERE/name for name in ('source_physical_phase_splice.py', 'source_stabilizer_phase_reduction.py',
        'source_stabilizer_phase_reduction.json', 'independent_source_stabilizer_phase_reduction.json',
        'source_temporal_dirac_reduction.json', 'independent_source_temporal_dirac_reduction.json',
        'source_full_linear_split.py', 'source_full_linear_split.json', 'independent_source_full_linear_split.json',
        'source_stationary_cauchy_orbit.json', 'independent_source_stationary_cauchy_orbit.json',
        'retained_hamiltonian_reduction.json', 'scalar_canonical_phase.json')]
    result = {'root': ROOT_ID, 'source_sha256': m.chart.common.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'scope': 'ACTUAL1082_TAIL_SYMPLECTIC_SUBSPACE_OF_SOURCE1208_REDUCED_TANGENT',
        'original_nonlinear_chart_tangent': encode(m.chart_tangent), 'tail_embedding_into_actual1208': encode(m.tail_embedding),
        'tail_reader_from_actual1208': encode(m.tail_reader), 'tail_original_symplectic_form': encode(m.omega),
        'same_original_one_form': 'theta=Pi^T dq; at source its constant tail term vanishes, and its derivative pulls back to Omega_tail=dtheta. beta is the independent chi complement, with delta p=-i delta chi E because tail delta e=0.',
        'original_constraints': constraints, 'original_tail_Hamiltonian': energy,
        'actual_response_consumer': {'input_dual_coordinate': column, 'third_time_primal': encode(expected_primal),
            'third_time_actual1208_chart': encode(lifted), 'exact_round_trip': True},
        'active126_return_contract': 'Generate original121 consistent field/velocity representatives from the paid126 quotient, apply the full289 auxiliary lift, and place them in the same six-Lorentz/three-stabilizer slice using the original Ward jets. Read back delta Pi_e=Gt^T delta Omega+(delta Gt)^T Omega_source with original BF boundary, delta Pi_A from the original Hodge, and delta p=-i delta chi E-i chi_source delta E. Prove the remaining126 map preserves the original phase form and intertwines the co-rotating generator; its existence is not inferred from1208-1082.',
        'complete_active126_splice_claimed': False, 'new_nonlinear_phase_occurrence_created': False,
        'interacting_quantum_measure_or_lifetime_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_physical_phase_splice.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS original physical phase tail splice', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
