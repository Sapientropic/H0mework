#!/usr/bin/env python3
"""Raw original spatial Gauss audit on the complete canonical source tangent.

The tangent producer is not imported. All607 source canonical pairs and all12
currents are rebuilt before the spatial stabilizer is removed. The independent
normal-equation inverse is used only in the gauge-coordinate slice, while
canonical momenta retain the original -k transpose pairing.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from independent_source_stabilizer_phase_reduction import RawStabilizerPhase
from independent_source_spatial_stabilizer_orbit import RawSpatialOrbit
from independent_source_physical_phase_splice import canonical, rectangular
from independent_retained_hamiltonian_reduction import exact
from independent_source_joint_temporal_rates import (
    HERE, ROOT, ROOT_ID, bindings, clean, rational, zero, eq, decode, encode, realify)


def point(A):
    return s.SparseMatrix(A).applyfunc(lambda value: s.cancel(s.expand(value)))


class RawSpatialPhase:
    def __init__(self):
        self.graph = RawStabilizerPhase()
        self.spatial = RawSpatialOrbit()
        self.raw = self.graph.raw
        self.k = self.spatial.k
        self.J = canonical(607); self.Omega = -self.J
        eq(self.graph.S, self.spatial.S)
        self.q0, self.p0 = self.graph.source_pair()
        q_orbit = s.Matrix.hstack(*(L*self.q0 for L in self.graph.generators))
        p_orbit = s.Matrix.hstack(*(-L.T*self.p0 for L in self.graph.generators))
        q_orbit[67:103, :] = self.spatial.V
        self.E = s.SparseMatrix(q_orbit.col_join(p_orbit))
        self.C = rational(self.star(self.E)*self.J)
        self.F = rectangular(3, 1214, [(0, 67, self.spatial.reader)])
        self.B = rational(self.J*self.star(self.F))
        # Independently regenerate all12 original source currents. No native
        # Gram is applied to the covector coefficient of the divergence.
        entries = {}
        for i in range(3):
            gauge = s.I*self.k[i]*s.eye(12)-self.raw.ad(self.raw.A[i+1, :]).T
            for (a, b), value in gauge.todok().items(): entries[a, 607+67+12*i+b] = value
        for a, rho in enumerate(self.raw.rho252):
            T = realify(rho)
            dq = clean(T.T*self.p0[103:, :]).T
            dp = clean(T*self.q0[103:, :]).T
            for (_, j), value in dq.todok().items(): entries[a, 103+j] = value
            for (_, j), value in dp.todok().items(): entries[a, 607+103+j] = value
        self.G12base = s.SparseMatrix(12, 1214, entries)
        eq(self.graph.S.T*self.G12base, self.C)
        self.matter = self.G12base.copy(); self.matter[:, 674:710] = s.zeros(12, 36)
        # The nine original normal scalar momenta solve their own current
        # equations. Tangential scalar61 momenta have zero orbit pairing.
        O, select = self.raw.Ob, self.raw.S
        gram = O.T*O
        normal, params = gram.gauss_jordan_solve(-select.T*self.G12base)
        assert params.rows == 0
        scalar_reader = rectangular(61, 1214, [(0, 613, s.eye(61))])
        self.Piphi = rational(self.graph.Rd*scalar_reader+O*normal)
        self.G12 = rational(self.G12base+self.raw.O.T*self.Piphi)
        eq(select.T*self.G12, s.zeros(9, 1214)); eq(self.graph.S.T*self.G12, self.C)
        eq(self.graph.R.T*O, s.zeros(61, 9)); eq(self.graph.R.T*self.graph.Rd, s.eye(61))

    def minus(self, matrix): return matrix.xreplace(dict(zip(self.k, -self.k)))
    def star(self, matrix): return self.minus(matrix).T
    def at(self, matrix, k): return point(matrix.subs(dict(zip(self.k, k))))

    def projection(self, k):
        E, F, B, C = [self.at(M, k) for M in (self.E, self.F, self.B, self.C)]
        return s.SparseMatrix.eye(1214)-E*F+B*C

    def project(self, k, u):
        E, F, B, C = [self.at(M, k) for M in (self.E, self.F, self.B, self.C)]
        parameter, current = point(F*u), point(C*u)
        result = point(u-E*parameter+B*current)
        eq(C*result, s.zeros(3, u.cols)); eq(F*result, s.zeros(3, u.cols))
        eq(self.at(self.G12, k)*result, s.zeros(12, u.cols))
        return result, parameter, current

    def lift_transverse(self, k, q, p):
        q, p = q.copy(), p.copy()
        P = self.spatial.at(self.spatial.P, k)
        dualP = self.spatial.at(self.spatial.P, -k).T
        q[67:103, :] = rational(P*q[67:103, :])
        p[67:103, :] = rational(dualP*p[67:103, :])
        transverse_p = p[67:103, :].copy()
        residual = rational(self.at(self.C, k)*q.col_join(p))
        # Solve the actual3x3 normal equations, independently of B's formula.
        coeff, params = self.spatial.at(self.spatial.N, k).gauss_jordan_solve(-residual)
        assert params.rows == 0
        normal = rational(self.spatial.G*self.spatial.at(self.spatial.V, k)*coeff)
        p[67:103, :] += normal
        out = rational(q.col_join(p))
        eq(self.at(self.C, k)*out, s.zeros(3, out.cols))
        eq(self.at(self.F, k)*out, s.zeros(3, out.cols))
        eq(self.at(self.G12, k)*out, s.zeros(12, out.cols))
        return out, q[67:103, :], transverse_p, normal


def verify_universal(m):
    E, F, B, C, J = m.E, m.F, m.B, m.C, m.J
    eq(F*E, s.eye(3)); eq(C*E, s.zeros(3))
    eq(F*B, s.zeros(3)); eq(C*B, -s.eye(3))
    Q = C.col_join(F)
    target = s.zeros(3).row_join(-s.eye(3)).col_join(s.eye(3).row_join(s.zeros(3)))
    eq(Q*J*m.star(Q), target)
    eq(target*(-target), s.eye(6)); eq((-target)*target, s.eye(6))
    K, L = E.row_join(B), F.col_join(-C)
    eq(L*K, s.eye(6))
    # This pays the all1214 projection, its six-dimensional kernel and the
    # whole1208 image without copying a proposed global coordinate frame.
    # (I-KL)^2=I-KL and its trace is1214-Tr(LK)=1208.
    eq(m.star(E)*m.Omega, -C)
    eq(m.star(B)*m.Omega, -F)
    eq(m.Omega*E, m.star(C)); eq(m.Omega*B, m.star(F))
    # The four preceding exact factors cancel T^*Omega-Omega*T termwise.
    for A in (E, F, B, C, m.Piphi): eq(m.minus(A), A.conjugate())
    expected_normal = rectangular(1214, 3, [(674, 0, -m.spatial.G*m.spatial.V*m.spatial.inverse)])
    eq(B, expected_normal)
    # -k pairing of every solved gauge-normal momentum with the complete
    # transverse plane vanishes; no source matter differential is omitted.
    eq(s.eye(3)-m.spatial.N*m.spatial.inverse, s.zeros(3))
    return {'complete_original_607_pairs_and_spatial_derivative_sign': True,
            'full12_original_broken_scalar_normal_equations': True,
            'canonical_covectors_no_extra_native_Gram': True,
            'source_six_constraint_Poisson': encode(target),
            'all_momentum_1214_to1208_projection': 'T=I-KL, K=[E,B], L=[F;-C], LK=I6. Thus T^2=T, ker(T)=im(K), rank(T)=1208.',
            'all_momentum_paired_symplectic_projection': 'E^*Omega=-C; B^*Omega=-F; Omega E=C^*; Omega B=F^*. These identities give T^*Omega=Omega T. The removed six-dimensional carrier has the checked nondegenerate constraint pairing, so range T carries the original nondegenerate paired form.',
            'all_momentum_real_Fourier_and_scalar_partner': True,
            'all571_other_pairs_and33_transverse_pairs_preserved': True}


def main():
    began = time.monotonic(); path = HERE/'source_spatial_phase_tangent.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    paid = ['independent_source_spatial_stabilizer_orbit.json', 'independent_source_stabilizer_phase_reduction.json']
    for name in paid: count += bindings(json.loads((HERE/name).read_text()))
    m = RawSpatialPhase(); assert m.raw.hashes == candidate['source_sha256']
    symbols = {str(k): k for k in m.k}
    for actual, key in [(m.E, 'orbit'), (m.C, 'Gauss'), (m.F, 'slice_reader'),
                        (m.matter, 'source_matter_current'), (m.Piphi, 'broken_scalar_map')]:
        eq(actual, decode(candidate[key], symbols))
    universal = verify_universal(m)
    print('PASS raw all12 source spatial Gauss, full independent matter orbit and original scalar normal solve for all real3k', flush=True)
    u = s.Matrix([s.Rational((7*j+2)%17-8, 31)+s.I*s.Rational((11*j+3)%19-9, 37) for j in range(1214)])
    v = s.Matrix([s.Rational((13*j+1)%23-11, 41)+s.I*s.Rational((5*j+7)%13-6, 43) for j in range(1214)])
    reports = []
    free = list(range(67))+list(range(103, 607))
    for row in candidate['actual_consumers']:
        k = decode(row['momentum'])
        out, alpha, current = m.project(k, u)
        eq(out, decode(row['projected_tangent']))
        eq(alpha, decode(row['source_gauge_parameter']))
        eq(current, decode(row['source_residual_Gauss_before_projection']))
        scalar = rational(m.at(m.Piphi, k)*out)
        eq(scalar, decode(row['projected_broken_scalar_momentum']))
        T = m.projection(k)
        Td = exact(T); partner_T = exact(m.projection(-k)); od = exact(m.Omega)
        assert (Td*exact(out)-exact(out)).is_zero_matrix
        assert (Td*Td-Td).is_zero_matrix
        assert (partner_T.transpose()*od-od*Td).is_zero_matrix
        partner, _, _ = m.project(-k, u.conjugate())
        eq(partner, out.conjugate())
        eq(m.at(m.Piphi, -k)*partner, scalar.conjugate())
        E = m.at(m.E, k); direct = u-E*alpha
        eq(direct[103:607, :], out[103:607, :]); eq(direct[710:, :], out[710:, :])
        assert (E[103:607, :]*alpha).todok() and (E[710:, :]*alpha).todok()
        first, aq, ap, normal = m.lift_transverse(k, u[:607, :], u[607:, :])
        second, bq, bp, _ = m.lift_transverse(-k, v[:607, :], v[607:, :])
        eq(normal, decode(row['transverse_lift_gauge_normal_covector']))
        original_pair = exact(second).transpose()*exact(m.Omega)*exact(first)
        q1, p1 = first[:607, :][free, :], first[607:, :][free, :]
        q2, p2 = second[:607, :][free, :], second[607:, :][free, :]
        expected_pair = (exact(p2).transpose()*exact(q1)-exact(q2).transpose()*exact(p1)+
                         exact(bp).transpose()*exact(aq)-exact(bq).transpose()*exact(ap))
        assert (original_pair-expected_pair).is_zero_matrix
        difference = point((m.at(m.Piphi, k)-m.at(m.Piphi, s.zeros(3, 1)))*first)
        eq(difference, decode(row['spatial_divergence_omission_scalar_defect']))
        if any(k): assert difference.todok()
        reports.append({'momentum': encode(k), 'full12_Gauss_and_slice_zero': True,
                        'full_source_matter_pair_same_parameter': True,
                        'true_broken_scalar_momentum_and_partner': True,
                        'complete571_plus33_paired_form': True,
                        'nonzero_divergence_omission_defect': bool(difference.todok())})
    print('PASS independent zero/nonaxis complex tangent, whole-field same parameter, paired1208 form and divergence negative control', flush=True)
    assert candidate['global33_coordinate_frame_supplied'] is False
    assert candidate['full_active126_dynamic_generator_spliced'] is False
    paths = [HERE/name for name in ('independent_source_spatial_phase_tangent.py', 'source_spatial_phase_tangent.py',
        'source_spatial_phase_tangent.json', 'independent_source_stabilizer_phase_reduction.py',
        'independent_source_spatial_stabilizer_orbit.py', 'independent_source_physical_phase_splice.py',
        'independent_source_joint_temporal_rates.py', 'independent_retained_hamiltonian_reduction.py')]+[HERE/name for name in paid]
    output = {'root': ROOT_ID, 'source_sha256': m.raw.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'verdict': 'CERTIFIED_ALL_REAL_SPATIAL_MOMENTUM_WHOLE_SOURCE_CANONICAL_TANGENT',
        'scope': candidate['scope'], 'checked_input_bindings': count, 'candidate_constructor_imported': False,
        'generic_source_identities': universal, 'actual_consumers': reports,
        'homogeneous_carrier_substituted_for_spatial_divergence': False,
        'global_transverse_coordinate_frame_or_full_dynamic_intertwining_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_spatial_phase_tangent.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS independent original spatial phase tangent', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
