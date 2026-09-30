#!/usr/bin/env python3
"""All94 current native forces through the original106 fixed-Pi forces.

The original112 inverse third jet is contracted before it is generated. The
same scalar/gauge principal, full12 native currents and positive rho3 pairing
then differentiate the source100-to122 input, without a supplied third jet.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import lru_cache
import hashlib
import json
import time
import sympy as s
from dynamic import HERE, ROOT, ROOT_ID
from source_bosonic_second_order_feedback import SourcePrincipalJet
from source_joint_current_hilbert_section import SourceJointCurrentHilbertSection
from source_joint_current_heisenberg import patch_symbolic_equal
from source_joint_ccr_car_ports import SourceJointCCRCarPorts, simplified, same
from source_full_native_quantum_force import SourceFullNativeQuantumForce
from source_full_gauss_section import DOMAIN, dm, sparse_domain
from source_coframe_legendre import rational
from source_lorentz_contact import equal, encode
from source_gauss_quantum_current import weighted_sum, encode_state
from source_joint_form_hamiltonian import read_bound


def product(A, B):
    return sparse_domain(dm(A)*dm(B))


def contraction(A, B):
    return sum(c*B[i, j] for (i, j), c in A.todok().items())


@dataclass
class NativeDifferentialCurrent:
    second: s.MatrixBase
    first: s.MatrixBase
    identity: s.Expr
    current_first: s.MatrixBase
    current_zero: s.MatrixBase
    current_pair: s.MatrixBase

    def apply(self, currents, values, gradients, Hessians):
        terms = []
        for word in set(values)|set(gradients)|set(Hessians):
            f = values.get(word, 0)
            g = gradients.get(word, s.zeros(100, 1))[6:, :]
            H = Hessians.get(word, s.zeros(100))[6:, 6:]
            central = contraction(self.second, H)+(self.first.T*g)[0]+self.identity*f
            terms.append((central, {word: 1}))
            q = self.current_first.T*g+self.current_zero*f
            for a, c in enumerate(q):
                if c: terms.append((c, currents.current_word(a, word)))
            if f:
                for (a, b), c in self.current_pair.todok().items():
                    terms.append((f*c, currents.current(a, currents.current_word(b, word))))
        return simplified(weighted_sum(terms))

    def difference(self, other):
        return NativeDifferentialCurrent(*(rational(a-b) if isinstance(a, s.MatrixBase)
            else s.cancel(a-b) for a, b in zip(self.fields(), other.fields())))

    def fields(self):
        return (self.second, self.first, self.identity, self.current_first,
                self.current_zero, self.current_pair)

    def verify_equal(self, other):
        for a, b in zip(self.fields(), other.fields()):
            if isinstance(a, s.MatrixBase): equal(a, b)
            else: assert s.cancel(a-b) == 0


class SourceCurrentNativeForceTransport:
    """The source raw100 two-jet is the only external input."""
    def __init__(self):
        patch_symbolic_equal()
        self.current = SourceJointCurrentHilbertSection()
        self.full = self.current.section.gauge
        self.chart = self.full.source
        self.model = SourceJointCCRCarPorts()
        self.point = tuple(self.current.point)
        self.data = self.model.coefficients(self.point)
        self.principal = SourcePrincipalJet(self.model, self.data)
        self.raw = SourceFullNativeQuantumForce()
        self.raw_data = self.raw.coefficients(self.raw.phi0, self.raw.A0)
        self._source_geometry()
        self._affine_second_divergences()
        self._inverse_third_and_force_coefficients()

    def _source_geometry(self):
        full, chart, p = self.full, self.chart, self.principal
        equal(chart.minor.T, p.L)
        self.Z1 = [rational(s.Matrix.hstack(*(L*full.embedding[:, 6+k]
            for L in full.L))) for k in range(94)]
        for k, dZ in enumerate(self.Z1):
            equal((full.constraint*dZ).T, p.L1[k])
        G = s.zeros(112)
        G[6:76, 6:76] = s.eye(70)/self.model.at_time(self.data['scalar']['raw']['h00'])
        G[76:, 76:] = self.model.at_time(self.data['gauge']['original']['weight'])
        self.G = G
        alpha, z = chart.alpha, chart.z
        self.K = rational((z*G*z.T/2)[6:, 6:])
        self.C = rational((-z*G*alpha.T)[6:, :])
        self.P = rational(alpha*G*alpha.T/2)
        equal(self.K, p.K)
        equal(self.C, rational(p.H*p.inverse))
        equal(self.P, rational(p.inverse.T*p.C*p.inverse/2))
        for field, actual in (('momentum_current', self.C), ('square_current', self.P)):
            equal(actual, self.model.at_time(self.data['scalar'][field]+self.data['gauge'][field]))
        for Q, R in zip(self.model.leaf.charges, full.R): equal(Q, s.I*R)
        equal(self.raw_data['H_native_principal'], -G[6:, 6:]/2)
        assert not self.raw_data['H_native_first'].todok()
        assert not self.raw_data['first_force'].todok()
        self.u = self._contract_inverse(G)
        self.Kdiv = rational(sum((K[:, i] for i, K in enumerate(p.K1)), s.zeros(94, 1)))
        self.alpha1, self.C1, self.P1 = [], [], []
        for k, dZ in enumerate(self.Z1):
            da = rational(-p.inverse.T*p.L1[k].T*alpha)
            dz = rational(-full.retraction*(dZ*alpha+chart.orbit*da))
            dc = rational((-dz*G*alpha.T-z*G*da.T)[6:, :])
            dp = rational((da*G*alpha.T+alpha*G*da.T)/2)
            equal(rational((dz*G*z.T+z*G*dz.T)[6:, 6:]/2), p.K1[k])
            A = rational(-p.inverse*p.L1[k]); dF = A*p.inverse
            equal(dc, rational((p.X1[k].T*p.C+p.H*A)*p.inverse))
            equal(dp, rational((dF.T*p.C*p.inverse+p.inverse.T*p.C*dF)/2))
            self.alpha1.append(da); self.C1.append(dc); self.P1.append(dp)
        self.Cdiv = rational(sum((C[i, :].T for i, C in enumerate(self.C1)), s.zeros(12, 1)))
        for field, actual in (('div_principal', self.Kdiv), ('div_momentum_current', self.Cdiv)):
            equal(actual, self.model.at_time(self.data['scalar'][field]+self.data['gauge'][field]))
        self.ell = self.model.at_time(self.data['scalar']['ell'])
        self.logH = self.model.at_time(self.data['scalar']['log_Hessian'])
        equal(self.ell, self.current.rho_log_half_gradient[6:, :])
        equal(self.logH, self.current.rho_log_half_Hessian[6:, 6:])
        self.logH1 = [s.zeros(94) for _ in range(94)]
        for j, e in enumerate(self.ell):
            if e: self.logH1[j][j, j] = -2*self.logH[j, j]/self.point[6+j]
        self.density = s.cancel((self.ell.T*self.K*self.ell)[0]+(self.Kdiv.T*self.ell)[0]+contraction(self.K, self.logH))
        assert s.cancel(self.density-self.model.at_time(sum(self.data[x]['half_density_potential']
            for x in ('scalar', 'gauge')))) == 0
        D = self.data['scalar']['raw']['D']; Di = [L[:9, :9].T for L in p.L1]
        invD = rational(D.inv())
        self.nu = s.Matrix([s.trace(invD*d) for d in Di])
        self.nu1 = s.Matrix(94, 94, lambda i, j: -s.trace(invD*Di[i]*invD*Di[j]))
        equal(rational(-self.u[18:, :]/2+2*self.K*self.ell+self.Kdiv), -self.K*self.nu)
        equal(rational(s.I*(self.u[:12, :]+2*self.C.T*self.ell+self.Cdiv)/2), -s.I*self.C.T*self.nu/2)

    def _contract_inverse(self, weight):
        weights = {(i, j): DOMAIN.from_sympy(c) for (i, j), c in weight.todok().items()}
        return s.Matrix([DOMAIN.to_sympy(sum((v*weights.get((ij//112, ij % 112), DOMAIN.zero)
            for ij, v in self.chart.inverse_second.rep.get(a, {}).items()), DOMAIN.zero)) for a in range(112)])

    def _affine_second_divergences(self):
        p = self.principal; n, r = 94, 12
        F, H, C = p.inverse, p.H, p.C
        A = [rational(-F*d) for d in p.L1]; X = p.X1
        v = sum((X[i][:, i] for i in range(n)), s.zeros(r, 1))
        q = rational(v.T*C+sum((H[i, :]*A[i] for i in range(n)), s.zeros(1, r)))
        Xflat = s.Matrix.vstack(*(Xi.T.reshape(1, n*r) for Xi in X))
        Dflat = s.Matrix.vstack(*((X[k].T*C+H*A[k]).reshape(1, n*r) for k in range(n)))
        ddivX = product(Xflat, s.Matrix.vstack(*(a.T for a in A)))+s.Matrix.vstack(*((a*v).T for a in A))
        self.ddivK = rational((product(Dflat, s.Matrix.vstack(*X))+product(ddivX, H.T)+
            s.Matrix.vstack(*(q*x for x in X)))/2)
        self.ddivC = product(rational(product(ddivX, C)+product(Dflat, s.Matrix.vstack(*A))+
            s.Matrix.vstack(*(q*a for a in A))), F)
        equal((q*F).T, self.Cdiv)
        for k in (0, 1, 8, 61, 93):
            equal(sum((p.second(k, i)[:, i] for i in range(n)), s.zeros(n, 1)), self.ddivK[k, :].T)

    def _inverse_third_and_force_coefficients(self):
        full, chart, p = self.full, self.chart, self.principal
        alpha, z, G, ell, logH = chart.alpha, chart.z, self.G, self.ell, self.logH
        products = {(a, b): rational((full.L[a]*full.L[b]+full.L[b]*full.L[a])/2)
            for a in range(12) for b in range(a, 12)}
        groupop = sum((2*self.P[a, b]*(1 if a == b else 2)*M
            for (a, b), M in products.items()), s.zeros(112))
        mixed = [L*full.embedding for L in full.L]
        self.third, self.connection, self.gap_derivative, self.current_derivative = [], [], [], []
        for k, dZ in enumerate(self.Z1):
            da = self.alpha1[k]
            dz = rational(-full.retraction*(dZ*alpha+chart.orbit*da))
            dcurve = sum((2*mixed[a]*(dz*G*alpha[a, :].T+z*G*da[a, :].T)
                for a in range(12)), s.zeros(112, 1))
            dcurve += groupop*full.embedding[:, 6+k]
            dcurve += sum((2*self.P1[k][a, b]*(1 if a == b else 2)*M*chart.base
                for (a, b), M in products.items()), s.zeros(112, 1))
            third = rational(-chart.inverse*(dZ*self.u[:12, :]+dcurve))
            Af = dZ*alpha
            other = rational(-chart.inverse*dZ*self.u[:12, :]-
                chart.inverse*groupop*full.embedding[:, 6+k]-self._contract_inverse(rational(Af*G+G*Af.T)))
            equal(third, other)
            self.third.append(third)
            dk, dc, dp = p.K1[k], self.C1[k], self.P1[k]
            ek, nk, h3 = logH[:, k], self.nu1[:, k], self.logH1[k]
            dz2, da2 = third[18:, :], third[:12, :]
            first = rational(2*dk*ell+2*self.K*ek-dz2/2)
            identity = s.cancel(-(ell.T*dk*ell)[0]+contraction(dk, logH)-
                2*(ek.T*self.K*ell)[0]+contraction(self.K, h3)+
                (dz2.T*ell)[0]/2+(self.u[18:, :].T*ek)[0]/2)
            zero_current = rational(s.I*(dc.T*ell+self.C.T*ek+da2/2))
            connection = NativeDifferentialCurrent(-dk, first, identity, -s.I*dc, zero_current, dp)
            density1 = s.cancel(2*(ek.T*self.K*ell)[0]+(ell.T*dk*ell)[0]+
                (self.ddivK[k, :]*ell)[0]+(self.Kdiv.T*ek)[0]+
                contraction(dk, logH)+contraction(self.K, h3))
            current = NativeDifferentialCurrent(-dk, -self.ddivK[k, :].T, density1,
                -s.I*dc, -s.I*self.ddivC[k, :].T/2, dp)
            gap = connection.difference(current)
            drift = rational(-dk*self.nu-self.K*nk)
            expected = NativeDifferentialCurrent(s.zeros(94), drift,
                s.cancel(-(drift.T*ell)[0]+(self.nu.T*self.K*ek)[0]), s.zeros(94, 12),
                rational(-s.I*(dc.T*self.nu+self.C.T*nk)/2), s.zeros(12))
            gap.verify_equal(expected)
            self.connection.append(connection); self.current_derivative.append(current); self.gap_derivative.append(gap)

    def generate(self, value, gradient, Hessian):
        source122 = self.current.section.extend_jet(*self.current.inverse_half_density_jet(value, gradient, Hessian))
        raw106 = self.raw.apply(self.raw_data, source122)
        embedding = self.full.embedding[6:, 6:]
        raw94 = [simplified(weighted_sum((c, raw106[j]) for j, c in enumerate(embedding[:, k]) if c))
            for k in range(94)]
        currents = self.model.leaf.weyl
        rows = []
        for k in range(94):
            chain = self.connection[k].apply(currents, value, gradient, Hessian)
            gap = self.gap_derivative[k].apply(currents, value, gradient, Hessian)
            transported = simplified(weighted_sum(((1, raw94[k]), (-1, chain), (1, gap))))
            direct = simplified(weighted_sum(((1, raw94[k]),
                (-1, self.current_derivative[k].apply(currents, value, gradient, Hessian)))))
            same(transported, direct)
            rows.append({'current_axis': 6+k, 'projected_fixed_Pi_force': raw94[k],
                'inverse_jet_and_half_density_chain': chain, 'source_ordering_gap_derivative': gap,
                'current_native_force': direct, 'transported_current_native_force': transported})
        return {'source122_jet': source122, 'raw106_forces': raw106, 'native_forces': rows}


def main():
    began = time.monotonic()
    bound = read_bound('source_full_native_quantum_force')
    for name in ('source_current_coframe_force_transport', 'source_joint_current_hilbert_section',
                 'source_bosonic_second_order_feedback'):
        read_bound(name)
    model = SourceCurrentNativeForceTransport()
    print('PASS original inverse3 contractions and all94 differential-current coefficients', flush=True)
    word = (5, 144, 396); values = {word: s.S.One}
    gradients = {word: s.Matrix([s.I*s.Rational(j % 7-3, 31) for j in range(100)])}
    v = s.Matrix([s.Rational(j % 5-2, 37) for j in range(100)])
    Hessians = {word: v*v.T-s.eye(100)}
    result = model.generate(values, gradients, Hessians)
    assert any(row['inverse_jet_and_half_density_chain'] for row in result['native_forces'])
    assert any(row['source_ordering_gap_derivative'] for row in result['native_forces'])
    original = bound['actual_source_consumer']
    raw = original['raw_scalar70_forces']+original['raw_spatial_gauge36_forces']
    for actual, encoded in zip(result['raw106_forces'], raw):
        same(actual, {tuple(w): s.sympify(c) for w, c in encoded})
    print('PASS source N3 all94 force transport and original106 readback', flush=True)
    zero = model.generate({}, {}, {})
    assert not zero['source122_jet'] and not any(zero['raw106_forces'])
    assert all(not row[key] for row in zero['native_forces'] for key in
        ('projected_fixed_Pi_force', 'inverse_jet_and_half_density_chain',
         'source_ordering_gap_derivative', 'current_native_force', 'transported_current_native_force'))
    mixed_values = {(): s.Rational(2, 3), (16, 268): s.I/7}
    mixed_gradients = {(): s.SparseMatrix(100, 1, {(7, 0): -s.Rational(1, 13), (74, 0): s.I/17}),
        (16, 268): s.SparseMatrix(100, 1, {(7, 0): s.Rational(1, 23), (95, 0): -s.Rational(2, 29)}),
        (5,): s.SparseMatrix(100, 1, {(67, 0): s.Rational(1, 31), (97, 0): s.I/37})}
    mixed_Hessians = {(): s.SparseMatrix(100, 100, {(7, 7): s.Rational(1, 43)}),
        (16, 268): s.SparseMatrix(100, 100, {(7, 84): s.Rational(1, 53), (84, 7): s.Rational(1, 53)}),
        (5,): s.SparseMatrix(100, 100, {(6, 95): s.I/59, (95, 6): s.I/59})}
    mixed = model.generate(mixed_values, mixed_gradients, mixed_Hessians)
    assert {len(w) for row in mixed['native_forces'] for w in row['current_native_force']} == {0, 1, 2}
    print('PASS empty and mixed N0/N2 with zero-valued N1 derivative germs', flush=True)
    def rows(result):
        return [{k: encode_state(v) if isinstance(v, dict) else v for k, v in row.items()}
            for row in result['native_forces']]
    paths = ('source_current_native_force_transport.py', 'source_full_native_quantum_force.py',
        'source_full_native_quantum_force.json', 'source_joint_current_hilbert_section.py',
        'source_joint_current_hilbert_section.json', 'source_full_gauss_section.py',
        'source_bosonic_second_order_feedback.py', 'source_joint_ccr_car_ports.py',
        'source_scalar_weyl_symbol.py', 'source_common_weyl_symbol.py')
    out = {'root': ROOT_ID, 'scope': 'SOURCE_NATIVE94_FORCE_TRANSPORT_THROUGH_ORIGINAL106_WITH_CONTRACTED_INVERSE3',
        'source_sha256': bound['source_sha256'],
        'input_sha256': {str((HERE/p).relative_to(ROOT)): hashlib.sha256((HERE/p).read_bytes()).hexdigest() for p in paths},
        'source_mouth': 'generate(raw100 CAR-valued two-jet) builds the original122 input and returns all original106 fixed-Pi forces plus all94 current native forces. No caller third jet, Hf derivative, target force or constraint solution is accepted.',
        'force_identity': 'Fcurrent_native = E106x94.T Fraw106 - Hraw_native(partial_native Phi) + partial_native Delta_current',
        'inverse_geometry': {'same_original_minor_transpose_equals_affine12': True,
            'all94_original_group_column_derivatives_equal_affine12': True,
            'original_inverse_third_principal_contraction_two_algorithms_all94': True,
            'second_affine_divergence_direct_check_axes': [0, 1, 8, 61, 93],
            'inverse_third_nonzero_entries': [len(t.todok()) for t in model.third]},
        'source_ordering_gap': {'nu_equals_gradient_log_det_D9': encode(model.nu),
            'full94_Hessian_log_det_D9': encode(model.nu1),
            'source_value': '-(K nu).partial + ((K nu).ell) I - (i/2) Q(C.T nu)',
            'all94_actual_derivatives_checked_against_original_inverse3': True,
            'nonzero_derivative_drift_columns': sum(bool(d.first.todok()) for d in model.gap_derivative),
            'nonzero_derivative_current_columns': sum(bool(d.current_zero.todok()) for d in model.gap_derivative),
            'nonzero_derivative_identity_columns': sum(bool(d.identity) for d in model.gap_derivative),
            'pairing': 'The unchanged rho3 and v^(Number+2) pairing is used. detD9 is an original configuration-Jacobian readout, not a replacement physical phase density.'},
        'all_finite_CAR': 'The complete principal, first, identity, full12 current and ordered-current-pair coefficients agree in every one of94 directions; the matrices act on all504 modes and preserve each Number sector.',
        'actual_source_consumer': {'word': list(word), 'source122_words': len(result['source122_jet']),
            'original106_forces_match_bound_producer': True, 'all94_force_returns': rows(result)},
        'zero_consumer': 'Empty raw100 germ passes the same producer and returns the zero122 jet and zero106/94 forces.',
        'mixed_consumer': {'values': encode_state(mixed_values),
            'gradients100': [[list(w), encode(g)] for w, g in mixed_gradients.items()],
            'Hessians100': [[list(w), encode(H)] for w, H in mixed_Hessians.items()],
            'output_numbers': [0, 1, 2], 'all94_force_returns': rows(mixed)},
        'classification': 'Subordinate source-generated coordinate and ordering transporter. The original even raw forces and the unchanged current H are its two consumers; it supplies their missing94-coordinate derivative chain.',
        'spatial_scope': 'Original homogeneous/K=0 source, fixed time column (N,0,0,0), proper clock tau=N*t unchanged.',
        'physical_Ward9_or_complete_retarded289_feed_claimed': False,
        'seconds': round(time.monotonic()-began, 3)}
    (HERE/'source_current_native_force_transport.json').write_text(json.dumps(out, indent=2)+'\n')
    print('PASS all94 current native force transport', out['seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
