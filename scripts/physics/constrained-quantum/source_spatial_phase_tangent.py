#!/usr/bin/env python3
"""Whole source canonical tangent at every real spatial Fourier momentum.

The same recovered gauge parameter acts on the full source matter pair.
Native Gram selects the gauge slice; the original Gauss divergence and
canonical covectors retain their original signs and their -k pairing.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_stabilizer_phase_reduction import SourceStabilizerPhaseReduction, canonical_J
from source_spatial_stabilizer_orbit import SourceSpatialStabilizerOrbit
from source_gauge_legendre import realify
from source_coframe_legendre import rational
from source_lorentz_contact import clean, equal, encode


def zero(A):
    equal(rational(A), s.zeros(*A.shape))


def sparse_identity(n):
    return s.MutableSparseMatrix(n, n, {(j, j): 1 for j in range(n)})


class SourceSpatialPhaseTangent:
    def __init__(self):
        self.phase = SourceStabilizerPhaseReduction()
        self.spatial = SourceSpatialStabilizerOrbit()
        self.k = self.spatial.k
        self.n = 607; self.dimension = 1214
        self.J = canonical_J(self.n)
        self.Omega = -self.J
        self.reversal = dict(zip(self.k, -self.k))
        equal(self.phase.S, self.spatial.S)
        self.gauge_q = s.SparseMatrix(36, self.dimension, {(j, 67+j): 1 for j in range(36)})
        self.gauge_P = s.SparseMatrix(36, self.dimension, {(j, self.n+67+j): 1 for j in range(36)})
        self.scalar_P = s.SparseMatrix(61, self.dimension, {(j, self.n+6+j): 1 for j in range(61)})

        q_orbit = s.SparseMatrix(self.phase.orbit(self.phase.q0))
        q_orbit[67:103, :] = self.spatial.V
        P_orbit = s.SparseMatrix(s.Matrix.hstack(*(-L.T*self.phase.P0 for L in self.phase.L)))
        zero(q_orbit[:67, :]); zero(P_orbit[:103, :])
        self.orbit = s.SparseMatrix(q_orbit.col_join(P_orbit))
        self.Gauss = rational(self.minus(self.orbit).T*self.J)
        self.slice = rational(self.spatial.reader*self.gauge_q)

        # All original12 current rows, before adding the scalar momentum.
        # Canonical matter coordinates are (Re psi,Im psi), with covectors
        # (-Im p,-Re p), exactly as in the original source one-form.
        base = s.MutableSparseMatrix(12, self.dimension, {})
        for i in range(3):
            coefficient = s.I*self.k[i]*s.eye(12)-self.phase.gauge.ad(self.phase.A0[i+1, :]).T
            base[:, self.n+67+12*i:self.n+67+12*(i+1)] = coefficient
        q0, P0 = self.phase.q0[103:, :], self.phase.P0[103:, :]
        for a, rho in enumerate(self.phase.common.rho):
            R = realify(rho)
            base[a, 103:607] = (R.T*P0).T
            base[a, self.n+103:self.dimension] = (R*q0).T
        self.base_current = clean(base)
        self.matter_current = self.base_current.copy()
        self.matter_current[:, self.n+67:self.n+103] = s.zeros(12, 36)
        zero(self.phase.S.T*self.base_current-self.Gauss)
        graph = self.phase.graph
        self.broken_normal = rational(-graph.constraints.gram.inv()*graph.select.T*self.base_current)
        self.broken_map = rational(graph.dual_R*self.scalar_P+graph.O*self.broken_normal)
        self.full_Gauss_matrix = rational(self.base_current+graph.constraints.orbit.T*self.broken_map)
        zero(graph.select.T*self.full_Gauss_matrix)
        zero(self.phase.S.T*self.full_Gauss_matrix-self.Gauss)

        self.Q = self.Gauss.col_join(self.slice)
        self.constraint_Poisson = s.zeros(3).row_join(-s.eye(3)).col_join(s.eye(3).row_join(s.zeros(3)))
        self.constraint_inverse = -self.constraint_Poisson
        zero(self.Q*self.J*self.minus(self.Q).T-self.constraint_Poisson)
        self.momentum_normal = rational(self.J*self.minus(self.slice).T)
        expected = -self.gauge_P.T*self.spatial.G*self.spatial.V*self.spatial.inverse
        zero(self.momentum_normal-expected)
        self.T = rational(sparse_identity(self.dimension)-self.orbit*self.slice+self.momentum_normal*self.Gauss)

    def minus(self, matrix):
        return matrix.xreplace(self.reversal)

    def at(self, matrix, momentum):
        # After substituting an actual momentum, expand the algebraic numbers
        # before cancel: signsimp otherwise repeatedly orders large unevaluated
        # complex sums in the original source matter coefficients.
        return rational(clean(matrix.subs(dict(zip(self.k, momentum)))))

    def broken_scalar_momentum(self, momentum, tangent):
        return rational(clean(self.at(self.broken_map, momentum)*tangent))

    def full_Gauss(self, momentum, tangent):
        return rational(clean(self.at(self.full_Gauss_matrix, momentum)*tangent))

    def project(self, momentum, tangent):
        parameter = rational(clean(self.at(self.slice, momentum)*tangent))
        old_current = rational(clean(self.at(self.Gauss, momentum)*tangent))
        output = rational(clean(self.at(self.T, momentum)*tangent))
        zero(self.at(self.Q, momentum)*output)
        zero(self.full_Gauss(momentum, output))
        return {'tangent': output, 'gauge_parameter': parameter, 'original_residual_Gauss': old_current,
                'broken_scalar_momentum': self.broken_scalar_momentum(momentum, output)}

    def lift_transverse(self, momentum, q, P):
        """Frame-free canonical carrier:571 other pairs plus transverse33.

        The two supplied gauge vectors are projected to the native transverse
        configuration/covector spaces; their solved normal momentum consumes
        the whole source matter current, including both independent variations.
        """
        q = q.copy(); P = P.copy()
        projector = self.at(self.spatial.P, momentum)
        dual_projector = self.at(self.minus(self.spatial.P).T, momentum)
        q[67:103, :] = rational(clean(projector*q[67:103, :]))
        P[67:103, :] = rational(clean(dual_projector*P[67:103, :]))
        transverse_covector = P[67:103, :].copy()
        residual = rational(clean(self.at(self.Gauss, momentum)*q.col_join(P)))
        normal = rational(clean(-self.spatial.G*self.at(self.spatial.V, momentum)*
                          self.at(self.spatial.inverse, momentum)*residual))
        P[67:103, :] += normal
        tangent = rational(clean(q.col_join(P)))
        zero(self.at(self.Q, momentum)*tangent)
        zero(self.full_Gauss(momentum, tangent))
        return {'tangent': tangent, 'gauge_configuration': q[67:103, :],
                'gauge_transverse_covector': transverse_covector, 'gauge_normal_covector': normal,
                'source_matter_current': residual,
                'broken_scalar_momentum': self.broken_scalar_momentum(momentum, tangent)}


def verify_all_momentum(model):
    m = model
    zero(m.slice*m.orbit-s.eye(3)); zero(m.Gauss*m.orbit)
    zero(m.slice*m.momentum_normal); zero(m.Gauss*m.momentum_normal+s.eye(3))
    zero(m.Q*m.T)
    zero(m.T*m.orbit); zero(m.T*m.momentum_normal)
    # These exact six-column contractions prove T^2=T on the entire1214
    # carrier, without discarding any matter coordinates or selecting a mode.
    finite = m.orbit.row_join(m.momentum_normal)
    reader = m.slice.col_join(-m.Gauss)
    zero(reader*finite-s.eye(6))
    zero(sparse_identity(m.dimension)-m.T-finite*reader)
    assert s.simplify(s.trace(m.T)-1208) == 0
    zero(m.minus(m.T).T*m.Omega-m.Omega*m.T)
    zero(m.minus(m.T)-m.T.conjugate())
    zero(m.minus(m.broken_map)-m.broken_map.conjugate())
    # The original scalar normal graph has no hidden cross symplectic term.
    zero(m.phase.graph.R.T*m.phase.graph.O)
    equal(m.phase.graph.R.T*m.phase.graph.dual_R, s.eye(61))
    # Gauge normal covectors annihilate the complete native horizontal plane
    # in the -k transpose pairing, including derivatives of their matter source.
    zero(m.minus(m.momentum_normal).T*m.gauge_P.T*m.spatial.P)
    return {'all_real_three_momentum': True,
        'six_constraint_canonical_Poisson_matrix': encode(m.constraint_Poisson),
        'exact_full_source_matter_configuration_and_momentum_orbits': True,
        'T_idempotence': 'I-T=[E,B] [F;-C], [F;-C][E,B]=I6; hence T^2=T, rank T=1214-6=1208.',
        'symplectic_projection': 'T(-k)^T Omega=Omega T(k); the six removed directions carry the displayed nondegenerate canonical constraint matrix, so the pairing on range T is nondegenerate.',
        'source_canonical_Gauss_contains_no_extra_native_Gram': True,
        'both_real_Fourier_partner_and_broken_scalar_partner_identities': True,
        'frame_free_carrier': '571 unaffected canonical coordinate/covector pairs together with native-transverse33 gauge coordinates and their -k-dual covectors; the solved gauge-normal momentum annihilates every transverse configuration variation.'}


def actual_consumers(m):
    momenta = [s.zeros(3, 1), s.Matrix([-3*s.sqrt(2)/8, 0, 3*s.sqrt(2)/4])]
    vector = s.Matrix([s.Rational((7*j+2) % 17-8, 31)+s.I*s.Rational((11*j+3) % 19-9, 37)
                       for j in range(m.dimension)])
    records = []
    for k in momenta:
        data = m.project(k, vector)
        assert data['gauge_parameter'].todok() and data['original_residual_Gauss'].todok()
        E, F, C, T = [m.at(matrix, k) for matrix in (m.orbit, m.slice, m.Gauss, m.T)]
        zero(T*T-T)
        partner = m.project(-k, vector.conjugate())
        zero(partner['tangent']-data['tangent'].conjugate())
        zero(clean(partner['broken_scalar_momentum']-data['broken_scalar_momentum'].conjugate()))
        # Both source matter variables use the same parameter read from A.
        shifted = rational(vector-E*data['gauge_parameter'])
        zero(shifted[103:607, :]-data['tangent'][103:607, :])
        zero(shifted[m.n+103:, :]-data['tangent'][m.n+103:, :])
        assert (E[103:607, :]*data['gauge_parameter']).todok()
        assert (E[m.n+103:, :]*data['gauge_parameter']).todok()

        first = m.lift_transverse(k, vector[:m.n, :], vector[m.n:, :])
        second_input = s.Matrix([s.Rational((13*j+1) % 23-11, 41)+s.I*s.Rational((5*j+7) % 13-6, 43)
                                 for j in range(m.dimension)])
        second = m.lift_transverse(-k, second_input[:m.n, :], second_input[m.n:, :])
        u, v = first['tangent'], second['tangent']
        canonical = (v.T*m.Omega*u)[0]
        free = list(range(67))+list(range(103, 607))
        qo, po = u[:607, :].extract(free, [0]), u[607:, :].extract(free, [0])
        qr, pr = v[:607, :].extract(free, [0]), v[607:, :].extract(free, [0])
        expected = (pr.T*qo-qr.T*po)[0]
        expected += (second['gauge_transverse_covector'].T*first['gauge_configuration']-
                     second['gauge_configuration'].T*first['gauge_transverse_covector'])[0]
        zero(clean(s.Matrix([[canonical-expected]])))
        assert first['gauge_normal_covector'].todok() and first['broken_scalar_momentum'].todok()
        # A finite k divergence omission really changes the original broken
        # scalar momentum graph, rather than being an unused symbolic port.
        difference = rational(m.broken_scalar_momentum(k, u)-m.broken_scalar_momentum(s.zeros(3, 1), u))
        if k != s.zeros(3, 1):
            assert difference.todok()
        records.append({'momentum': encode(k), 'source_gauge_parameter': encode(data['gauge_parameter']),
            'source_residual_Gauss_before_projection': encode(data['original_residual_Gauss']),
            'projected_tangent': encode(data['tangent']),
            'projected_broken_scalar_momentum': encode(data['broken_scalar_momentum']),
            'transverse_lift_gauge_normal_covector': encode(first['gauge_normal_covector']),
            'spatial_divergence_omission_scalar_defect': encode(difference),
            'original_full12_Gauss_zero': True, 'full_matter_pair_same_parameter_checked': True,
            'paired_native_canonical_form_matches_571_plus33': True,
            'direct_T_squared_T_and_conjugate_partner_checked': True})
    return records


def main():
    started = time.monotonic(); m = SourceSpatialPhaseTangent()
    contract = verify_all_momentum(m)
    print('PASS original spatial divergence/full matter Gauss, whole1214 symplectic projection and frame-free1208 carrier for all real3k', flush=True)
    consumers = actual_consumers(m)
    print('PASS zero/nonaxis plus-minus source consumers, true broken scalar momentum, same matter gauge parameter and canonical transverse pairing', flush=True)
    paths = [HERE/name for name in ('source_spatial_phase_tangent.py', 'source_spatial_stabilizer_orbit.py',
        'source_spatial_stabilizer_orbit.json', 'independent_source_spatial_stabilizer_orbit.json',
        'source_stabilizer_phase_reduction.py', 'source_stabilizer_phase_reduction.json',
        'independent_source_stabilizer_phase_reduction.json', 'source_scalar_gauss_reduction.py',
        'source_scalar_gauss_reduction.json', 'source_common_hamiltonian.py')]
    result = {'root': ROOT_ID, 'source_sha256': m.phase.common.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'scope': 'ALL_REAL_SPATIAL_MOMENTUM_WHOLE_SOURCE_CANONICAL_GAUSS_TANGENT_AND_NATIVE_HORIZONTAL_CARRIER',
        'canonical_coordinates': 'u=(delta q607,delta P607), q=(coframe6,scalar61,gauge36,Repsi252,Impsi252), P_matter=(-Im p,-Re p).',
        'pairing': 'u(-k)^T Omega v(k), Omega=[[0,-I],[I,0]]; Poisson J=-Omega. Fourier amplitudes are complexifications of these original real coordinates.',
        'all_momentum_contract': contract,
        'original_Gauss': 'C(k)=E(-k)^T J. Its gauge-covector coefficient is V(-k)^T=V(k)^H without native Gram; its source matter coordinate and canonical-momentum terms are both retained.',
        'slice': 'F(k)u=R(k) delta A, R=N^-1 V^H G36; same recovered parameter acts through the entire source orbit E(k).',
        'projection': 'T=I-E F+B C, B=J F(-k)^T=-inject_gauge_momentum G36 V N^-1.',
        'broken_scalar_momentum': 'delta Pi_phi=Rdual delta pi-O_b Gram9^-1 select^T (i k_i delta Pi_Ai-ad(A_i)^T delta Pi_Ai+full independent source matter current).',
        'orbit': encode(m.orbit), 'Gauss': encode(m.Gauss), 'slice_reader': encode(m.slice),
        'source_matter_current': encode(m.matter_current), 'broken_scalar_map': encode(m.broken_map),
        'canonical_carrier': 'delta A=P_A a; delta Pi_A=P_A(-k)^T pi-G36 V N^-1 j_matter. All571 other canonical pairs are retained; the normal covector has zero -k pairing with the full transverse gauge plane.',
        'actual_consumers': consumers,
        'public_API': 'SourceSpatialPhaseTangent: phase, spatial, k, J, Omega, orbit, Gauss, slice, T, broken_map, full_Gauss_matrix; at(matrix,k), project(k,u), lift_transverse(k,q,P), broken_scalar_momentum(k,u), full_Gauss(k,u).',
        'same_source_full252_independent_dual_and_original_divergence_preserved': True,
        'global33_coordinate_frame_supplied': False,
        'full_active126_dynamic_generator_spliced': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_spatial_phase_tangent.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source spatial phase tangent', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
