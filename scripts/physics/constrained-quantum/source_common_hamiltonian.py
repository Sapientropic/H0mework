#!/usr/bin/env python3
"""The common local Hamiltonian of the untruncated repaired source action.

Lorentz elimination has already consumed its complete matter current.  The
remaining matter term is the original Omega=0 restriction.  Canonical p changes
the independent dual, not psi; fixed-p coframe derivatives retain that chain.
"""
from __future__ import annotations

from collections import Counter
from functools import cached_property
import hashlib
import itertools
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, decode
from source_coframe_legendre import SourceCoframeLegendre, rational
from source_scalar_legendre import SourceScalarLegendre, source, dot
from source_lorentz_contact import GAMMA, clean, equal, encode


def real(value):
    return s.expand(s.re(value))


class SourceCommonHamiltonian:
    def __init__(self):
        self.coframe = SourceCoframeLegendre()
        self.scalar = SourceScalarLegendre()
        _, _, degrees, self.source_hashes = source.parse_source(ROOT)
        self.rho = []
        for _, imaginary, matrix in source.generators([(0, 1, 2), (3, 4)]):
            internal = s.diag(*[s.SparseMatrix(source.exterior_action(matrix, degree))
                                for degree in degrees])*(s.I if imaginary else 1)
            self.rho.append(clean(s.kronecker_product(s.eye(4), internal)))
        self.yukawa_basis = []
        for word in itertools.combinations(range(7), 4):
            _, _, wedge, _ = source.yukawa(Counter({word: 1}))
            internal = s.zeros(63)
            internal[:7, 7:28] = s.SparseMatrix(wedge)
            self.yukawa_basis.append(clean(s.kronecker_product(s.diag(0, 0, 1, 1), internal)))

    @cached_property
    def gauge(self):
        from source_gauge_legendre import SourceGaugeLegendre
        return SourceGaugeLegendre()

    def matter_data(self, e, phi, connection):
        """Raw position-space coefficients, before any Fourier or rotating frame."""
        ports = self.coframe.lorentz.matter_ports(e)
        principal = [clean(s.kronecker_product(ports['orientation']*C, s.eye(63)))
                     for C in ports['oriented_principals']]
        inverse4 = rational(ports['E'].inv())
        inverse = clean(s.kronecker_product(inverse4, s.eye(63)))
        Y = clean(sum(((phi[j]+s.I*phi[j+35])*matrix
                       for j, matrix in enumerate(self.yukawa_basis)), s.zeros(252)))
        gauge = [clean(sum((connection[mu, a]*self.rho[a] for a in range(12)), s.zeros(252)))
                 for mu in range(4)]
        lower = clean(sum((principal[mu]*gauge[mu] for mu in range(4)), s.zeros(252))
                      +s.Abs(e.det())*Y)
        V = [clean(s.kronecker_product(matrix, s.eye(63))) for matrix in ports['V']]
        return {'E': principal[0], 'inverse_E': inverse, 'principal': principal,
                'lower_without_Lorentz': lower, 'Y': Y, 'Lorentz_ports': V}

    def canonical_dual(self, data, p):
        return clean(s.I*p*data['inverse_E'])

    def matter_lower(self, data, psi, spatial_psi):
        return clean(data['lower_without_Lorentz']*psi+
                     sum((data['principal'][i+1]*spatial_psi[i] for i in range(3)), s.zeros(252, 1)))

    def remaining_matter_hamiltonian(self, data, psi, p, spatial_psi):
        chi = self.canonical_dual(data, p)
        return -real((chi*self.matter_lower(data, psi, spatial_psi))[0])

    def matter_euler(self, e, de, phi, A, psi, chi, dpsi, dchi, connection):
        """Both original full252 Euler rows, including all live principal jets."""
        data = self.matter_data(e, phi, A)
        lower = clean(data['lower_without_Lorentz']+
                      sum((connection[a]*V for a, V in enumerate(data['Lorentz_ports'])), s.zeros(252)))
        primal = clean(lower*psi+sum((data['principal'][mu]*dpsi[mu] for mu in range(4)), s.zeros(252, 1)))
        divergence = s.zeros(1, 252)
        for mu in range(4):
            dadj = self.coframe.at(sum((de[16*mu+a]*self.coframe.dadj[a]
                                      for a in range(16)), s.zeros(4)), e)
            dC = clean(s.kronecker_product(s.sign(e.det())*sum(
                (s.I*dadj[mu, a]*GAMMA[a] for a in range(4)), s.zeros(4)), s.eye(63)))
            divergence += dchi[mu]*data['principal'][mu]+chi*dC
        return {'primal': primal, 'dual': clean(chi*lower-divergence), 'data': data}

    def fixed_p_coframe_correction(self, e, chi, primal_residual):
        """EL_e at fixed p minus EL_e at fixed chi, off shell."""
        ports = self.coframe.lorentz.matter_ports(e)
        inverse = clean(s.kronecker_product(ports['E'].inv(), s.eye(63)))
        result = []
        for a in range(16):
            adj_a = self.coframe.at(self.coframe.dadj[a], e)
            E_a = clean(s.kronecker_product(s.sign(e.det())*sum(
                (s.I*adj_a[0, b]*GAMMA[b] for b in range(4)), s.zeros(4)), s.eye(63)))
            result.append(-real((chi*E_a*inverse*primal_residual)[0]))
        return clean(s.Matrix(result))

    def matter_canonical_flow(self, e, de, phi, A, psi, p, spatial_psi,
                              spatial_p, connection):
        """Original real canonical equations, retaining spatial coefficient divergence."""
        data = self.matter_data(e, phi, A)
        inverse = data['inverse_E']
        lower = clean(data['lower_without_Lorentz']+
                      sum((connection[a]*V for a, V in enumerate(data['Lorentz_ports'])), s.zeros(252)))
        psi_dot = clean(-inverse*(lower*psi+sum(
            (data['principal'][i+1]*spatial_psi[i] for i in range(3)), s.zeros(252, 1))))
        p_dot = p*inverse*lower
        coefficient_divergence = s.zeros(252)
        for i in range(3):
            mu = i+1
            dadj = self.coframe.at(sum((de[16*mu+a]*self.coframe.dadj[a]
                                      for a in range(16)), s.zeros(4)), e)
            dprincipal = [clean(s.kronecker_product(s.sign(e.det())*sum(
                (s.I*dadj[nu, a]*GAMMA[a] for a in range(4)), s.zeros(4)), s.eye(63)))
                          for nu in (0, mu)]
            dcoefficient = clean(-inverse*dprincipal[0]*inverse*data['principal'][mu]+
                                 inverse*dprincipal[1])
            coefficient_divergence += dcoefficient
            p_dot -= spatial_p[i]*inverse*data['principal'][mu]+p*dcoefficient
        return {'primal_velocity': psi_dot, 'canonical_dual_velocity': clean(p_dot),
                'spatial_coefficient_divergence': clean(coefficient_divergence)}

    def chart(self, e):
        assert e.det() != 0, 'the original coframe must be invertible'
        h, _ = self.scalar.metric_density(e)
        gauge = self.gauge.constitutive(e)
        assert h[0, 0] != 0, 'scalar/matter/coframe temporal chart is characteristic'
        assert gauge['metric'][0, 0] != 0, 'the original gauge electric chart is characteristic'
        return {'scalar_h00': h[0, 0], 'gauge_g00': gauge['metric'][0, 0]}

    def lagrangian(self, e, de, phi, dphi, A, dA, psi, dpsi, chi):
        """Original reduced local density, before changing chi to canonical p."""
        data = self.matter_data(e, phi, A)
        h, volume = self.scalar.metric_density(e)
        temporal, spatial = self.scalar.covariant(phi, dphi[1:], A)
        U = [dphi[0]+temporal, *spatial]
        scalar_density = sum(h[mu, nu]*dot(U[mu], U[nu])/2
                             for mu in range(4) for nu in range(4))
        scalar_density -= volume*dot(phi-self.scalar.vacuum, phi-self.scalar.vacuum)
        coframe_density = self.coframe.lagrangian(e, de[:16, :], de[16:, :], psi, chi)
        matter_density = real((chi*(data['E']*dpsi[0]+self.matter_lower(data, psi, dpsi[1:])))[0])
        return s.expand(coframe_density+scalar_density+self.gauge.lagrangian(e, A, dA)+matter_density)

    def momenta(self, e, de, phi, dphi, A, dA, psi, chi):
        self.chart(e)
        data = self.matter_data(e, phi, A)
        return {'coframe': self.coframe.momentum(e, de[:16, :], de[16:, :], psi, chi),
                'scalar': self.scalar.momentum(e, phi, dphi[0], dphi[1:], A),
                'gauge': self.gauge.momentum(e, A, dA),
                'gauge_temporal': s.zeros(1, 12), 'matter': clean(-s.I*chi*data['E'])}

    def hamiltonian(self, e, Pi_e, spatial_e, phi, Pi_phi, spatial_phi,
                    A, Pi_A, spatial_A, psi, p, spatial_psi, multipliers):
        self.chart(e)
        data = self.matter_data(e, phi, A)
        chi = self.canonical_dual(data, p)
        components = {
            'coframe_Lorentz_matter': self.coframe.hamiltonian(e, Pi_e, spatial_e, psi, chi, multipliers),
            'scalar': self.scalar.hamiltonian(e, phi, Pi_phi, spatial_phi, A),
            'gauge': self.gauge.hamiltonian(e, A, spatial_A, Pi_A),
            'matter_without_Lorentz': self.remaining_matter_hamiltonian(data, psi, p, spatial_psi)}
        return {'value': s.expand(sum(components.values())), 'components': components,
                'dual': chi, 'coframe_primary': self.coframe.constraints(e, Pi_e, spatial_e, psi, chi),
                'gauge_temporal_primary': 'Pi_A0=0 (12 original native coordinates)'}

    def boson_velocities(self, e, Pi_e, spatial_e, phi, Pi_phi, spatial_phi,
                         A, Pi_A, spatial_A, psi, p, multipliers):
        self.chart(e)
        data = self.matter_data(e, phi, A)
        chi = self.canonical_dual(data, p)
        h, _ = self.scalar.metric_density(e)
        temporal, w = self.scalar.covariant(phi, spatial_phi, A)
        b = sum((h[0, i+1]*w[i] for i in range(3)), s.zeros(70, 1))
        return {'coframe': self.coframe.velocity(e, Pi_e, spatial_e, psi, chi, multipliers),
                'scalar': clean((Pi_phi-b)/h[0, 0]-temporal),
                'gauge_spatial': self.gauge.velocity(e, A, spatial_A, Pi_A)}

    def gauss(self, e, phi, Pi_phi, A, Pi_A, spatial_Pi_A, psi, p):
        data = self.matter_data(e, phi, A)
        chi = self.canonical_dual(data, p)
        pure = self.gauge.gauss(A, Pi_A, spatial_Pi_A)
        scalar = s.Matrix([dot(Pi_phi, R*phi) for R in self.scalar.rho])
        matter = s.Matrix([real((chi*data['E']*R*psi)[0]) for R in self.rho])
        return {'pure': pure, 'scalar': clean(scalar), 'matter': clean(matter),
                'total': clean(pure+scalar+matter),
                'spatial_boundary_flux': clean(Pi_A*A[0, :].T)}


def verify_matter_source(model):
    exchange = model.scalar.exchange
    background = exchange.active['actual_background']
    e = s.Matrix(background['coframe']).applyfunc(s.sympify)
    A = s.Matrix(background['gauge_connection']).applyfunc(s.sympify)
    O = s.Matrix(background['lowered_Lorentz_connection']).applyfunc(s.sympify).reshape(24, 1)
    phi = model.scalar.vacuum
    data = model.matter_data(e, phi, A)
    phase = json.loads((BASE/'full-phase/receipt.json').read_text())
    equal(data['Y'], decode(phase['original_Y']))
    full_lower = clean(data['lower_without_Lorentz']+sum(
        (O[a]*V for a, V in enumerate(data['Lorentz_ports'])), s.zeros(252)))
    original = exchange.N*(decode(phase['original_constant_B'])+decode(phase['original_Y']))
    equal(full_lower, original)
    H = clean(-s.I*data['inverse_E']*full_lower)
    equal(H, decode(json.loads((BASE/'full-quantum/receipt.json').read_text())['original_H_full']))
    equal(data['E']*(-s.I*H)+full_lower, s.zeros(252))
    scalar_ports = [decode(row['operator']) for row in exchange.vertices['primitive_vertices']
                    if row['group'] == 'scalar']
    for j in range(70):
        equal(exchange.N*(s.I if j >= 35 else 1)*model.yukawa_basis[j % 35], scalar_ports[j])
    gauge_ports = [decode(row['operator']) for row in exchange.vertices['primitive_vertices']
                   if row['group'] == 'gauge_A']
    for mu in range(4):
        for a in range(12):
            equal(data['principal'][mu]*model.rho[a], gauge_ports[12*mu+a])
    stationary = clean(H-exchange.omega*decode(phase['phase_generator']))
    assert clean(H-stationary).todok()
    return {'all70_original_Yukawa_ports': True, 'all48_original_gauge_ports': True,
            'full252_original_Hamiltonian_at_source': True,
            'original_chart0_not_stationary_rotating_frame': True}


def example_fields(e):
    phi = s.Matrix([s.Rational(j+1, 71) for j in range(70)])
    dphi = [s.Matrix([s.Rational((mu+1)*(j % 7-3), 19) for j in range(70)]) for mu in range(4)]
    A = s.Matrix(4, 12, lambda mu, a: s.Rational((mu+1)*(a-5), 17))
    dA = s.Matrix(4, 48, lambda mu, a: s.Rational((mu+2)*(a % 11-5), 23))
    de = s.Matrix([s.Rational((j % 13)-6, 29) for j in range(64)])
    psi = s.Matrix([s.Rational(j % 17-8, 31)+s.I*s.Rational(j % 7-3, 37) for j in range(252)])
    chi = s.Matrix(1, 252, lambda _, j: s.Rational(j % 11-5, 41)+s.I*s.Rational(j % 13-6, 43))
    dpsi = [s.Matrix([s.Rational((mu+1)*(j % 5-2), 47)+s.I*s.Rational(j % 3-1, 53)
                      for j in range(252)]) for mu in range(4)]
    return e, de, phi, dphi, A, dA, psi, dpsi, chi


def verify_common_density(model, fields, full_velocity_derivatives=False):
    e, de, phi, dphi, A, dA, psi, dpsi, chi = fields
    canonical = model.momenta(e, de, phi, dphi, A, dA, psi, chi)
    _, multipliers = model.coframe.velocity_coordinates(e, de[:16, :])
    args = (e, canonical['coframe'], de[16:, :], phi, canonical['scalar'], dphi[1:],
            A, canonical['gauge'], dA[1:, :], psi, canonical['matter'])
    output = model.hamiltonian(*args, dpsi[1:], multipliers)
    L = model.lagrangian(*fields)
    pairing = (dot(canonical['coframe'], de[:16, :])+dot(canonical['scalar'], dphi[0])+
               sum(a*b for a, b in zip(canonical['gauge'], dA[0, 12:].reshape(3, 12)))+
               real((s.I*canonical['matter']*dpsi[0])[0]))
    assert s.simplify(output['value']-pairing+L) == 0
    equal(output['coframe_primary'], s.zeros(10, 1))
    velocities = model.boson_velocities(*args, multipliers)
    equal(velocities['coframe'], de[:16, :])
    equal(velocities['scalar'], dphi[0])
    equal(velocities['gauge_spatial'], dA[0, 12:].reshape(3, 12))
    equal(output['dual'], chi)
    if full_velocity_derivatives:
        ve = s.Matrix(s.symbols('ve0:16', real=True))
        vf = s.Matrix(s.symbols('vf0:70', real=True))
        va = s.Matrix(3, 12, s.symbols('va0:36', real=True))
        replacement_de = ve.col_join(de[16:, :])
        replacement_dA = dA.copy()
        replacement_dA[0, 12:] = va.reshape(1, 36)
        varying = (e, replacement_de, phi, [vf, *dphi[1:]], A, replacement_dA, psi, dpsi, chi)
        varying_L = model.lagrangian(*varying)
        measured = model.momenta(e, replacement_de, phi, [vf, *dphi[1:]], A, replacement_dA, psi, chi)
        for variables, expected in [(ve, measured['coframe']), (vf, measured['scalar']), (va, measured['gauge'])]:
            equal(s.Matrix([s.diff(varying_L, v) for v in variables]), s.Matrix(list(expected)))
        # All504 independent real matter velocities are linear in the original
        # density. This is its full coefficient identity, not an occupied probe.
        data = model.matter_data(e, phi, A)
        kinetic_row = chi*data['E']
        equal(kinetic_row, s.I*canonical['matter'])
    j = model.coframe.lorentz.matter_current(e, psi, chi)
    Omega = model.coframe.lorentz.eliminate(e, de, psi, chi)['connection']
    repeated = -real((j.T*Omega)[0])
    assert repeated != 0
    return {'determinant': str(e.det()), 'all_block_Legendre_identity': True,
            'coframe_primary_count': 10, 'gauge_temporal_primary_count': 12,
            'all122_bosonic_momentum_derivatives': full_velocity_derivatives,
            'all504_real_matter_kinetic_coefficients': full_velocity_derivatives,
            'all122_bosonic_velocities_restored': True,
            'repeated_Lorentz_term_negative_control': str(repeated)}


def verify_matter_euler_and_chain(model, fields):
    e, de, phi, dphi, A, dA, psi, dpsi, chi = fields
    data = model.matter_data(e, phi, A)
    p = clean(-s.I*chi*data['E'])
    dp = [s.Matrix(1, 252, lambda _, j: s.Rational((mu+1)*(j % 7-3), 59)+
                   s.I*s.Rational((mu+2)*(j % 5-2), 61)) for mu in range(4)]
    dchi = []
    inverse = data['inverse_E']
    for mu in range(4):
        dadj = model.coframe.at(sum((de[16*mu+a]*model.coframe.dadj[a]
                                  for a in range(16)), s.zeros(4)), e)
        dE = clean(s.kronecker_product(s.sign(e.det())*sum(
            (s.I*dadj[0, a]*GAMMA[a] for a in range(4)), s.zeros(4)), s.eye(63)))
        dchi.append(clean(s.I*dp[mu]*inverse-chi*dE*inverse))
        equal(dchi[-1]*data['E']+chi*dE, s.I*dp[mu])
    Omega = model.coframe.lorentz.eliminate(e, de, psi, chi)['connection']
    original = model.matter_euler(e, de, phi, A, psi, chi, dpsi, dchi, Omega)
    canonical = model.matter_canonical_flow(e, de, phi, A, psi, p, dpsi[1:], dp[1:], Omega)
    equal(original['primal'], data['E']*(dpsi[0]-canonical['primal_velocity']))
    equal(original['dual'], s.I*(canonical['canonical_dual_velocity']-dp[0]))
    assert original['primal'].todok() and original['dual'].todok()
    assert canonical['spatial_coefficient_divergence'].todok()
    correction = model.fixed_p_coframe_correction(e, chi, original['primal'])
    assert correction.todok()
    t = s.Symbol('dual_variation', real=True)
    fixed_L = model.coframe.lagrangian(e, de[:16, :], de[16:, :], psi, chi)
    for a in range(16):
        adj_a = model.coframe.at(model.coframe.dadj[a], e)
        E_a = clean(s.kronecker_product(s.sign(e.det())*sum(
            (s.I*adj_a[0, b]*GAMMA[b] for b in range(4)), s.zeros(4)), s.eye(63)))
        delta_chi = clean(-chi*E_a*inverse)
        moved = chi+t*delta_chi
        # Only chi differs between the two fixed-variable variations; the
        # common explicit e derivative cancels. Envelope supplies Omega*.
        moved_L = model.coframe.lagrangian(e, de[:16, :], de[16:, :], psi, moved)-fixed_L
        moved_L += real((t*delta_chi*(data['E']*dpsi[0]+model.matter_lower(data, psi, dpsi[1:])))[0])
        assert s.simplify(s.diff(moved_L, t).subs(t, 0)-correction[a]) == 0
    return {'original_primal_entries_checked': 252, 'original_dual_entries_checked': 252,
            'live_principal_derivatives_retained': True, 'spatial_divergence_nonzero': True,
            'fixed_p_coframe_chain_components': 16,
            'freeze_chi_negative_control': encode(correction)}


def verify_common_gauss(model, fields):
    e, de, phi, dphi, A, dA, psi, dpsi, chi = fields
    canonical = model.momenta(e, de, phi, dphi, A, dA, psi, chi)
    scalar_current, _ = model.gauge.scalar_current(e, phi, dphi, A)
    matter_current = model.gauge.matter_current(e, psi, chi)
    second_A = [s.Matrix(4, 48, lambda mu, a: s.Rational((rho+mu+1)*(a % 7-3), 67))
                for rho in range(4)]
    original = model.gauge.euler(e, de.reshape(4, 16), A, dA, second_A, scalar_current, matter_current)
    dPi = [original['momentum_derivatives'][i+1][:3, :] for i in range(3)]
    result = model.gauss(e, phi, canonical['scalar'], A, canonical['gauge'], dPi, psi, canonical['matter'])
    equal(result['total'], original['Gauss'])
    equal(result['scalar'], scalar_current[0, :].T)
    equal(result['matter'], matter_current[0, :].T)
    a0 = s.Matrix(1, 12, s.symbols('A_time0:12', real=True))
    varied_A = A.copy()
    varied_A[0, :] = a0
    # The coframe/Lorentz term is independent of A0 in the original chart.
    data = model.matter_data(e, phi, varied_A)
    H = (model.gauge.hamiltonian(e, varied_A, dA[1:, :], canonical['gauge'])+
         model.scalar.hamiltonian(e, phi, canonical['scalar'], dphi[1:], varied_A)+
         model.remaining_matter_hamiltonian(data, psi, canonical['matter'], dpsi[1:]))
    partial = s.Matrix([s.diff(H, x) for x in a0])
    divergence = sum((dPi[i][i, :].T for i in range(3)), s.zeros(12, 1))
    equal(partial-divergence, -result['total'])
    return {'all12_original_temporal_connection_Euler': True,
            'scalar_and_independent_dual_currents_in_same_Gauss': True,
            'functional_H_A0_derivative_is_negative_Gauss': True,
            'spatial_boundary_flux_retained': True,
            'Gauss_preservation_or_first_class_assumed': False}


def verify_envelope(model, e):
    geometry = model.coframe.geometry(e)
    K, G = geometry['Lorentz_inverse'], geometry['G'][:, :16]
    Q, Z = geometry['velocity_inverse'], geometry['null_frame']
    equal(K, K.T)
    equal(Q, Q.T)
    # Derivatives of the actual quadratic H with respect to the complete
    # current j. The identities hold separately at every Pi, q, lambda slot.
    p = s.Matrix(s.symbols('aux_p0:16', real=True))
    q = s.Matrix(s.symbols('aux_q0:24', real=True))
    lam = s.Matrix(s.symbols('aux_lambda0:10', real=True))
    shifted = p+G.T*K*q
    H = s.expand((shifted.T*Q*shifted)[0]/2+(q.T*K*q)[0]/2+(lam.T*Z.T*shifted)[0])
    velocity = Q*shifted+Z*lam
    Omega = -K*(G*velocity+q)
    equal(s.Matrix([s.diff(H, x) for x in q]), -Omega)
    # Removing the source primary multiplier loses a real matter-current
    # contribution whenever GZ is nonzero.
    lost = clean(K*G*Z)
    assert lost.todok()
    return {'all24_current_envelope_derivatives': True,
            'arbitrary16_canonical_momenta_and10_multipliers': True,
            'original_full_Lorentz_connection_recovered_in_matter_equations': True,
            'omitting_primary_multiplier_negative_control_nonzero': True}


def main():
    started = time.monotonic()
    model = SourceCommonHamiltonian()
    source_readback = verify_matter_source(model)
    print('PASS original full252 chart0 generator and all70/48 matter source ports', flush=True)
    frames = [s.Matrix([[2, 1, 0, 0], [0, 2, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]]),
              s.Matrix([[-2, 1, 0, 0], [0, 2, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]])]
    consumers = []
    for index, e in enumerate(frames):
        fields = example_fields(e)
        consumers.append(verify_common_density(model, fields, index == 0))
        print('PASS common original density Legendre identity, orientation', s.sign(e.det()), flush=True)
    fields = example_fields(frames[0])
    envelope = verify_envelope(model, frames[0])
    print('PASS full24 Lorentz current envelope with all primary multipliers', flush=True)
    euler = verify_matter_euler_and_chain(model, fields)
    print('PASS original full252 primal/dual Euler and all16 fixed-p coframe chain corrections', flush=True)
    gauss = verify_common_gauss(model, fields)
    print('PASS common native12 Gauss with original full70 and independent-dual matter currents', flush=True)
    bad_frames = [s.Matrix([[1, 1, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]),
                  s.Matrix([[1, 0, 0, 0], [1, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])]
    for e in bad_frames:
        try:
            model.chart(e)
        except AssertionError as error:
            assert 'characteristic' in str(error)
        else:
            raise AssertionError('incompatible common temporal chart accepted')
    inputs = [HERE/name for name in (
        'source_common_hamiltonian.py', 'source_coframe_legendre.py', 'source_coframe_legendre.json',
        'independent_source_coframe_legendre.json', 'source_lorentz_contact.py', 'source_lorentz_contact.json',
        'source_scalar_legendre.py', 'source_scalar_legendre.json', 'independent_source_scalar_legendre.json',
        'source_gauge_legendre.py', 'source_gauge_legendre.json', 'real_scalar_car_source.json')]
    inputs += [BASE/name for name in ('exact_readout.py', 'matter-vertices/receipt.json',
                                     'full-phase/receipt.json', 'full-quantum/receipt.json')]
    inputs += [ROOT/'Lean/SaturationMonoid/PhysicsCore'/name for name in (
        'LowEnergy/FullQuantum/Source.lean', 'StageNineDiracDualFormNativeMotherAction.lean')]
    result = {'root': ROOT_ID, 'source_sha256': model.scalar.exchange.vertices['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in inputs},
        'scope': 'ORIGINAL_UNTRUNCATED_NATIVE12_FULL70_FULL252_COMMON_LOCAL_CONSTRAINED_HAMILTONIAN',
        'actual_API': 'SourceCommonHamiltonian.{lagrangian,momenta,hamiltonian,boson_velocities,matter_canonical_flow,matter_euler,gauss}',
        'chart': 'det(e)!=0, original g^00!=0 and independently original gauge g_00!=0; chart0 scalar coordinates',
        'canonical_pairing': 'Pi_e dot(e)+Pi_phi dot(phi)+sum_i Pi_Ai dot(Ai)+Re(i p dot(psi)); p=-i chi E(e)',
        'Hamiltonian': 'H_coframe(e,Pi_e,psi,chi=i p E^-1,lambda)+H_scalar70+H_gauge_native12+Re(p h_without_Lorentz psi)',
        'source_matter_consumer': source_readback, 'direct_whole_density_consumers': consumers,
        'auxiliary_current_envelope': envelope, 'actual_matter_Euler': euler, 'common_Gauss': gauss,
        'generic_composition_argument': [
            'The exact original scalar/gauge densities contain e but no coframe velocities.',
            'The exact Lorentz current contains full psi and independent chi but no matter velocities.',
            'Each original block velocity derivative is therefore its already generated momentum; the original real matter temporal coefficient is E.',
            'Adding the source block Legendre identities yields the common local Hamiltonian for arbitrary fields in the common chart, with no extra cross-sector momentum.',
            'Differentiating this identity at fixed canonical variables gives all original bosonic Euler equations; the coframe fixed-p derivative differs by the explicitly retained independent-dual Euler multiple.',
            'The derivative of the constrained coframe Hamiltonian in j is minus Omega* including the primary multipliers, so the original full matter primal/dual equations return automatically.'],
        'fixed_p_coframe_Euler': 'EL_e[p]=EL_e[chi]-Re(chi (d_e E) E^-1 R_chi); no additional Pi_e term since psi is unchanged',
        'boundary': 'original BF theta minus reduced theta is delta F0 pulled back through Omega* and chi(e,p); gauge spatial flux Pi_Ai A0 retained',
        'bosonic_primary_constraints': {'coframe': 10, 'gauge_temporal': 12},
        'different_characteristic_charts_rejected': True,
        'full_constraint_consistency_closed': False,
        'operator_ordering_or_quantum_domain_selected': False,
        'four_block_quantum_spectrum_or_decay_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_common_hamiltonian.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')


if __name__ == '__main__':
    main()
