#!/usr/bin/env python3
"""Original scalar70/gauge36 forces, all12 A0 ports and native source torque.

The complete scalar shift and spatial potential are differentiated before
specialization. The source potential breaks nine native directions; its
nonzero torque is retained separately from the three residual Gauss laws and
from the six Lorentz plus three residual null Ward directions of active289.
"""
from __future__ import annotations
from functools import lru_cache
import hashlib
import json
import time
import sympy as s
from dynamic import HERE, ROOT, ROOT_ID
from source_quantum_stabilizer import SourceQuantumStabilizer
from source_joint_current_hilbert_section import SourceJointCurrentHilbertSection
from source_coframe_live_ordering import full
from source_coframe_legendre import rational
from source_lorentz_contact import clean, equal, encode
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state
from source_joint_ccr_car_ports import simplified, same
from source_joint_form_hamiltonian import read_bound
from source_quantum_temporal_symbol import N


def real_car(M):
    return clean(s.diag(M, -M.conjugate()))


class SourceFullNativeQuantumForce:
    def __init__(self):
        self.native = SourceQuantumStabilizer()
        self.common, self.gauge = self.native.graph.common, self.native.joint.gauge
        self.rho, self.ad = self.native.c.rho, self.native.gauge.adjoint
        self.R = [clean(s.diag(M, M.conjugate())) for M in self.common.rho]
        self.L = [s.diag(r, a, a, a) for r, a in zip(self.rho, self.ad)]
        self.Y = self.common.yukawa_basis+[s.I*M for M in self.common.yukawa_basis]
        source = self.common.scalar.exchange.active['actual_background']
        self.e0 = s.Matrix(source['coframe']).applyfunc(s.sympify)
        self.A0 = s.Matrix(source['gauge_connection']).applyfunc(s.sympify)[1:, :]
        self.phi0 = self.native.c.vacuum
        self.torque_gradient_without_volume = clean(s.Matrix.vstack(*(-2*(r*self.phi0).T for r in self.rho)))
        assert self.torque_gradient_without_volume.rank() == 9
        equal(self.native.S.T*self.torque_gradient_without_volume, s.zeros(3, 70))
        equal(self.native.B.T*self.torque_gradient_without_volume, -2*self.native.graph.O.T)
        self.scalar_frame = self.native.graph.O.row_join(self.native.graph.R)
        self.scalar_force_lift = rational(self.scalar_frame.T.inv())
        equal(self.scalar_frame.T*self.scalar_force_lift, s.eye(70))

    @lru_cache(None)
    def _time_coefficients(self, time_column):
        e = self.e0.copy(); e[:, 0] = s.Matrix(time_column)
        h, volume = self.common.scalar.metric_density(e)
        gauge = self.gauge.coefficients(e)
        connection = s.zeros(4, 12)
        original = self.common.matter_data(e, self.phi0, connection)
        inverse = original['inverse_E']
        scalar = tuple(real_car(-s.I*volume*inverse*Y) for Y in self.Y)
        ports = tuple(tuple(real_car(-s.I*inverse*original['principal'][mu]*rho)
            for rho in self.common.rho) for mu in range(4))
        return e, h, volume, gauge, scalar, ports

    def coefficients(self, phi, A, time_column=(N, 0, 0, 0)):
        """All106 -partial H rows at fixed original scalar/gauge momenta."""
        phi, A = s.Matrix(phi), s.Matrix(A)
        assert phi.shape == (70, 1) and A.shape == (3, 12)
        e, h, volume, raw, Mphi, MA = self._time_coefficients(tuple(time_column))
        Rs = [clean(sum((A[i, a]*self.rho[a] for a in range(12)), s.zeros(70))) for i in range(3)]
        U = [R*phi for R in Rs]
        B = sum((h[0, i+1]*Rs[i] for i in range(3)), s.zeros(70))
        b = B*phi
        assert s.trace(B) == 0
        scalar_potential = (b.T*b)[0]/(2*h[0, 0])
        scalar_potential -= sum(h[i+1, j+1]*(U[i].T*U[j])[0]/2 for i in range(3) for j in range(3))
        scalar_potential += volume*((phi-self.phi0).T*(phi-self.phi0))[0]
        dphi = B.T*b/h[0, 0]-sum((h[i+1, j+1]*Rs[i].T*U[j]
            for i in range(3) for j in range(3)), s.zeros(70, 1))+2*volume*(phi-self.phi0)
        substitutions = dict(zip(self.gauge.coordinates, A.reshape(36, 1)))
        def at(M):
            return rational(M.xreplace(substitutions)) if isinstance(M, s.MatrixBase) else s.cancel(M.xreplace(substitutions))
        W, C, dC = raw['weight'], at(raw['momentum_shift']), at(raw['shift_derivative'])
        gauge_potential = (raw['momentum_shift'].T*W*raw['momentum_shift'])[0]/2
        gauge_potential += raw['derivative_ordering_constant']+raw['magnetic_potential']
        dgauge = at(s.Matrix([s.diff(gauge_potential, z) for z in self.gauge.coordinates]))
        identity = -dphi.col_join(s.zeros(36, 1))
        first = s.zeros(106)
        first[:70, :70] = -s.I*B.T/h[0, 0]
        for k in range(3):
            for a in range(12):
                j = 12*k+a; v = self.rho[a]*phi; db = h[0, k+1]*v
                identity[70+j] = -(db.T*b)[0]/h[0, 0]+sum(h[k+1, l+1]*(v.T*U[l])[0] for l in range(3))-dgauge[j]
                first[70+j, :70] = -s.I*db.T/h[0, 0]
                first[70+j, 70:] = -s.I*(W*dC[:, j]).T
        one = tuple(-M for M in Mphi)+tuple(-MA[k+1][a] for k in range(3) for a in range(12))
        connection = s.zeros(4, 12); connection[1:, :] = A
        original = self.common.matter_data(e, phi, connection)
        HM = real_car(-s.I*original['inverse_E']*original['lower_without_Lorentz'])
        reconstruction = sum((phi[j]*Mphi[j] for j in range(70)), s.zeros(504))
        reconstruction += sum((A[k, a]*MA[k+1][a] for k in range(3) for a in range(12)), s.zeros(504))
        equal(clean(HM-reconstruction), s.zeros(504))
        return {'e': e, 'h': h, 'volume': volume, 'phi': phi, 'A': A,
            'identity_force': rational(identity), 'first_force': rational(first), 'onebody_force': one,
            'H_native_principal': s.diag(-s.eye(70)/(2*h[0, 0]), -W/2),
            'H_native_first': rational((s.I*b/h[0, 0]).col_join(s.I*W*C)),
            'H_native_identity': s.cancel(scalar_potential+at(gauge_potential)), 'H_matter': HM,
            'A0_matter_derivative': MA[0], 'scalar_shift': rational(b), 'gauge_shift': C}

    def apply(self, data, jet122):
        """Ordinary action of the generated even force operators."""
        values = {w: row['value'] for w, row in jet122.items() if row['value']}
        result = []
        for a in range(106):
            boson = {w: data['identity_force'][a]*row['value']+
                (data['first_force'][a, :]*row['gradient'][16:, :])[0] for w, row in jet122.items()}
            result.append(simplified(weighted_sum(((1, boson),
                (1, apply_superposition(data['onebody_force'][a], values))))))
        return result

    def gauss(self, data, jet122):
        """Actual -partial_A0 H at K=0, without a Gauss-zero input."""
        values = {w: row['value'] for w, row in jet122.items() if row['value']}
        field = data['phi'].col_join(data['A'].reshape(36, 1))
        result = []
        for L, R in zip(self.L, self.R):
            V = L*field
            boson = {w: -s.I*(V.T*row['gradient'][16:, :])[0] for w, row in jet122.items()}
            result.append(simplified(weighted_sum(((1, boson), (s.I, apply_superposition(R, values))))))
        return result

    def scalar_readback(self, forces):
        mapped = [simplified(weighted_sum((self.scalar_frame[i, j], forces[i])
            for i in range(70) if self.scalar_frame[i, j])) for j in range(70)]
        recovered = [simplified(weighted_sum((self.scalar_force_lift[i, j], mapped[j])
            for j in range(70) if self.scalar_force_lift[i, j])) for i in range(70)]
        for a, b in zip(recovered, forces[:70]): same(a, b)
        return {'scalar_J9': mapped[:9], 'peripheral61': mapped[9:]}

    def verify_structure(self):
        for a in range(12):
            R, r, ad = self.common.rho[a], self.rho[a], self.ad[a]
            equal(R, s.kronecker_product(s.eye(4), R[:63, :63]))
            equal(r+r.T, s.zeros(70))
            equal(ad.T*self.native.gauge.gram+self.native.gauge.gram*ad, s.zeros(12))
            for j in range(70):
                target = sum((v*self.Y[k] for (k, _), v in r[:, j].todok().items()), s.zeros(252))
                equal(clean(R*self.Y[j]-self.Y[j]*R-target), s.zeros(252))
            for b in range(12):
                weights = ad[:, b]
                equal(clean(r*self.rho[b]-self.rho[b]*r),
                    clean(sum((v*self.rho[k] for k, v in enumerate(weights) if v), s.zeros(70))))
                equal(clean(ad*self.ad[b]-self.ad[b]*ad),
                    clean(sum((v*self.ad[k] for k, v in enumerate(weights) if v), s.zeros(12))))
                internal = R[:63, :63]; other = self.common.rho[b][:63, :63]
                equal(clean(internal*other-other*internal),
                    clean(sum((v*self.common.rho[k][:63, :63] for k, v in enumerate(weights) if v), s.zeros(63))))
        span = []
        for branch in (0, 4):
            for i in range(4):
                for j in range(4):
                    E = s.zeros(8); E[branch+i, branch+j] = 1
                    span.append(full(E))
        for R in self.R:
            for C in span: equal(clean(R*C-C*R), s.zeros(504))
        cf = self.native.joint.coframe
        for M in cf.J+cf.T+cf.M+[cf.correction, cf.one_body]:
            equal(M[:4, 4:], s.zeros(4)); equal(M[4:, :4], s.zeros(4))
        phi = s.Matrix(s.symbols('native_phi0:70', real=True))
        potential = ((phi-self.phi0).T*(phi-self.phi0))[0]
        torque = clean(s.Matrix([-sum((r*phi)[i]*s.diff(potential, phi[i])
            for i in range(70)) for r in self.rho]))
        equal(torque, self.torque_gradient_without_volume*(phi-self.phi0))
        return {'all840_original_Yukawa_coefficients': True,
            'all144_scalar70_adjoint12_internal63_Lie_coefficients': True,
            'all12_native_Gram_invariance': True,
            'coframe_complete32_spin_block_basis_times12_commutators': 384,
            'actual_original_coframe_factors_lie_in_that_span': True,
            'normal_quartic_native_commutator': 'The full original factors commute before normal multiplication; the CAR derivation therefore annihilates every original Lorentz pair on every finite occupation.',
            'literal_potential_torque_gradient': encode(self.torque_gradient_without_volume)}

    def verify_noether(self, data):
        field = data['phi'].col_join(data['A'].reshape(36, 1))
        results = []
        for a, (L, R) in enumerate(zip(self.L, self.R)):
            V = L*field; K = data['H_native_principal']; H = data['H_matter']
            equal(rational(L*K+K*L.T), s.zeros(106))
            equal(rational(L*data['H_native_first']+data['first_force'].T*V), s.zeros(106, 1))
            car = sum((V[j]*data['onebody_force'][j] for j in range(106)), s.zeros(504))+R*H-H*R
            equal(clean(car), s.zeros(504))
            torque = s.cancel((V.T*data['identity_force'])[0])
            expected = s.cancel(data['volume']*(self.torque_gradient_without_volume[a, :]*(data['phi']-self.phi0))[0])
            assert s.cancel(torque-expected) == 0
            equal(data['A0_matter_derivative'][a], -s.I*R)
            results.append(torque)
        torques = s.Matrix(results)
        equal(clean(self.native.S.T*torques), s.zeros(3, 1))
        equal(clean(self.native.B.T*torques), clean(-2*data['volume']*self.native.graph.O.T*(data['phi']-self.phi0)))
        return torques

    def verify_A0(self, data):
        a0 = s.Matrix(1, 12, s.symbols('native_A_time0:12', real=True))
        Pi = s.Matrix(s.symbols('full_scalar_Pi0:70', real=True))
        PA = s.Matrix(3, 12, s.symbols('full_gauge_Pi0:36', real=True))
        connection = s.zeros(4, 12); connection[0, :], connection[1:, :] = a0, data['A']
        H = self.common.scalar.hamiltonian(data['e'], data['phi'], Pi, [s.zeros(70, 1)]*3, connection)
        H += self.common.gauge.hamiltonian(data['e'], connection, s.zeros(3, 48), PA)
        for a in range(12):
            expected = -(Pi.T*self.rho[a]*data['phi'])[0]
            expected -= sum((PA[k, :]*self.ad[a]*data['A'][k, :].T)[0] for k in range(3))
            assert s.expand(s.diff(H, a0[a])-expected) == 0
        return {'original_scalar70_gauge36_A0_coefficients': 12,
            'original_full504_A0_current_coefficients': 12,
            'sign': '-partial_A0 H = -i V_native.partial + i dGamma(rho_native)',
            'spatial_scope': 'K=0; the original spatial Gauss divergence and A0 boundary flux remain in the existing full local source producer.'}

    def verify_literal_forces(self, data):
        """Differentiate original full Legendre energies, retaining every Pi."""
        Pi = s.Matrix(s.symbols('literal_phi_Pi0:70', real=True))
        PA = s.Matrix(3, 12, s.symbols('literal_A_Pi0:36', real=True))
        momentum = Pi.col_join(PA.reshape(36, 1))
        t = s.Symbol('literal_native_variation', real=True)
        connection = s.zeros(4, 12); connection[1:, :] = data['A']
        counts = [0, 0]
        for a in range(106):
            phi, A = data['phi'].copy(), connection.copy()
            if a < 70: phi[a] += t
            else: A[1+(a-70)//12, (a-70) % 12] += t
            H = self.common.scalar.hamiltonian(data['e'], phi, Pi, [s.zeros(70, 1)]*3, A)
            if a >= 70: H += self.common.gauge.hamiltonian(data['e'], A, s.zeros(3, 48), PA)
            actual = -s.diff(H, t).subs(t, 0)
            expected = data['identity_force'][a]+s.I*(data['first_force'][a, :]*momentum)[0]
            assert s.expand(actual-expected) == 0, a
            counts[int(a >= 70)] += 1
        return {'literal_scalar70_force_columns': counts[0], 'literal_spatial_gauge36_force_columns': counts[1],
            'canonical_momenta_remain_symbolic': True}


def main():
    began = time.monotonic()
    bound = read_bound('source_full_coframe_quantum_force')
    for name in ('source_common_hamiltonian', 'source_scalar_legendre', 'source_gauge_quantum_energy',
                 'source_joint_current_hilbert_section'):
        read_bound(name)
    model = SourceFullNativeQuantumForce(); structure = model.verify_structure()
    print('PASS complete native Lie/Yukawa/current coefficients and actual rank9 potential torque', flush=True)
    phi = model.phi0+s.Matrix([s.Rational(j % 5-2, 101) for j in range(70)])
    A = model.A0+s.Matrix(3, 12, lambda i, j: s.Rational((i+2*j) % 7-3, 113))
    shifted = model.coefficients(phi, A, (N, N/11, -N/13, N/17))
    torque = model.verify_noether(shifted)
    A0 = model.verify_A0(shifted)
    literal = model.verify_literal_forces(shifted)
    assert shifted['scalar_shift'].todok() and shifted['gauge_shift'].todok()
    assert shifted['first_force'][:70, :70].todok()
    print('PASS all106 literal fixed-Pi forces, actual shifts and all12 original A0/Noether ports', flush=True)
    current = SourceJointCurrentHilbertSection()
    word = (5, 144, 396); value = {word: s.S.One}
    gradient = {word: s.Matrix([s.I*s.Rational(j % 7-3, 31) for j in range(100)])}
    u = s.Matrix([s.Rational(j % 5-2, 37) for j in range(100)])
    Hessian = {word: u*u.T-s.eye(100)}
    jet = current.section.extend_jet(*current.inverse_half_density_jet(value, gradient, Hessian))
    source = model.coefficients(model.phi0, model.A0)
    model.verify_noether(source)
    forces = model.apply(source, jet); gauss = model.gauss(source, jet)
    assert not any(gauss)
    scalar = model.scalar_readback(forces)
    assert any(forces[:70]) and any(forces[70:])
    print('PASS source122 all106 even forces, actual12 Gauss and complete J9/R61 readback', flush=True)
    paths = ('source_full_native_quantum_force.py', 'source_full_coframe_quantum_force.json',
        'source_common_hamiltonian.py', 'source_common_hamiltonian.json', 'source_scalar_legendre.py',
        'source_scalar_legendre.json', 'source_gauge_quantum_energy.py', 'source_gauge_quantum_energy.json',
        'source_quantum_stabilizer.py', 'source_joint_current_hilbert_section.py',
        'source_joint_current_hilbert_section.json', 'source_joint_quantum_section.py')
    out = {'root': ROOT_ID, 'scope': 'FULL70_SCALAR_36_GAUGE_EVEN_FORCES_A0_GAUSS12_AND_SOURCE_BROKEN_TORQUE',
        'source_sha256': bound['source_sha256'],
        'input_sha256': {str((HERE/p).relative_to(ROOT)): hashlib.sha256((HERE/p).read_bytes()).hexdigest() for p in paths},
        'source_mouth': 'coefficients(phi70,A36,time4) differentiates the complete original scalar and gauge energies at fixed native canonical Pi and the same full504 matter Hamiltonian. apply acts on any122 jet; the actual consumer obtains that jet from the existing source100 producer.',
        'structure': structure, 'original_A0_readback': A0, 'literal_derivatives': literal,
        'shifted_consumer': {'coframe': encode(shifted['e']), 'phi70': encode(phi), 'A36': encode(A),
            'scalar_shift70': encode(shifted['scalar_shift']), 'gauge_shift36': encode(shifted['gauge_shift']),
            'all106_identity_forces': encode(shifted['identity_force']), 'all106_first_derivative_forces': encode(shifted['first_force']),
            'all12_actual_torques': encode(torque)},
        'broken_native9_contact': {'operator_identity': 'i[H,G_a]=-2 abs(det e)*(phi-v)^T rho_a v times identity. The source vacuum is fixed and the potential is unchanged.',
            'source_phi_gradient12x70': encode(N*model.torque_gradient_without_volume),
            'rank': 9, 'native_B9_projection': encode(N*model.native.B.T*model.torque_gradient_without_volume),
            'residual_S3_projection_zero': True,
            'contact_identity': 'B^T i[H,G] = -2 abs(det e) O^T(phi-v); these are the original broken-native scalar consistency/contact directions.'},
        'actual_source_consumer': {'word': list(word), 'generated122_words': len(jet),
            'raw_scalar70_forces': [encode_state(F) for F in forces[:70]],
            'raw_spatial_gauge36_forces': [encode_state(F) for F in forces[70:]],
            'actual_A0_Gauss12_on_input': [encode_state(G) for G in gauss],
            'same_full70_scalar_J9': [encode_state(F) for F in scalar['scalar_J9']],
            'same_full70_peripheral61': [encode_state(F) for F in scalar['peripheral61']],
            'whole70_reconstruction_checked': True},
        'null_Ward9_status': 'The active289 null Ward directions are Lorentz6 plus residual su(2)3. They are distinct from the rank9 broken-native scalar/contact rows above; no complete289 source or its compatibility is claimed here.',
        'matter_convention': 'Original full252 canonical p and its paired real504 CAR, with Y included once. The existing canonical p to independent chi tangent and fixed-p coframe Euler correction are required by the subsequent original-field consumer.',
        'spatial_scope': 'Original homogeneous/K=0 coefficient operators; source proper clock remains tau=N*t.',
        'seconds': round(time.monotonic()-began, 3)}
    (HERE/'source_full_native_quantum_force.json').write_text(json.dumps(out, indent=2)+'\n')
    print('PASS full source native quantum force', out['seconds'], 'seconds', flush=True)

if __name__ == '__main__': main()
