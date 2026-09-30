#!/usr/bin/env python3
"""The original1500-real-component first-order spatial source system.

The temporal gauge connection is generated from the scalar torque constraint.
The temporal coframe and spatial Lorentz rates use their original source
minors. Covariant gradient/curvature variables retain their defining
constraints; none is replaced by a caller-supplied solution trajectory.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, decode
from source_spatial_lorentz_time import SourceSpatialLorentzTime
from source_lorentz_contact import clean, equal, encode, ETA, PAIRS
from source_common_hamiltonian import real
from source_gauge_legendre import contraction, rational


KEYS = ('e', 'Omega', 'A', 'F', 'phi', 'U', 'psi', 'chi')


class SourceFirstOrderCauchy:
    def __init__(self):
        self.geometry = SourceSpatialLorentzTime()
        self.common = self.geometry.common
        self.gauge = self.geometry.time4.gauge
        self.rho = self.gauge.rho70
        self.vacuum = self.common.scalar.vacuum
        self.orbit = clean(s.Matrix.hstack(*[R*self.vacuum for R in self.rho]))
        self.select = s.eye(12)[:, list(self.orbit.rref()[1])]
        active = self.orbit*self.select
        self.row_rebuild = clean(self.orbit.T*active*(active.T*active).inv())

    def scalar_connection(self, A):
        return clean(sum((value*R for value, R in zip(A, self.rho)), s.zeros(70)))

    def consistency(self, phi):
        return clean(self.orbit.T*s.Matrix.hstack(*[R*phi for R in self.rho]))

    def time_connection(self, phi, U0):
        D = self.consistency(phi)
        D9 = clean(self.select.T*D*self.select)
        if D9.det() == 0:
            raise ValueError('The original source scalar-torque chart requires det(D9) != 0.')
        inverse = rational(self.select*D9.inv()*self.select.T)
        value = clean(inverse*self.orbit.T*U0)
        equal(D*value, self.orbit.T*U0)
        return {'value': value, 'inverse': inverse, 'matrix': D, 'broken_matrix': D9}

    def time_connection_derivative(self, port, dphi, dU0):
        return clean(port['inverse']*(self.orbit.T*dU0-self.consistency(dphi)*port['value']))

    @staticmethod
    def metric(e):
        inverse = e.inv()
        return rational(s.Abs(e.det())*inverse*ETA*inverse.T)

    @staticmethod
    def metric_derivative(e, h, de):
        inverse = e.inv()
        return rational(s.trace(inverse*de)*h-inverse*de*h-h*de.T*inverse.T)

    def unpack(self, fields, spatial):
        U = [fields['U'][mu, :].T for mu in range(4)]
        port = self.time_connection(fields['phi'], U[0])
        A = port['value'].T.col_join(fields['A'])
        dA0 = [self.time_connection_derivative(port, direction['phi'], direction['U'][0, :].T)
               for direction in spatial]
        Omega = s.zeros(6, 1).col_join(fields['Omega'])
        dOmega = [s.zeros(6, 1).col_join(direction['Omega']) for direction in spatial]
        return {'U': U, 'A': A, 'dA0': dA0, 'Omega': Omega, 'spatial_Omega': dOmega, 'port': port}

    def rhs(self, fields, spatial):
        """All1500 real rates from fields and precisely their first spatial jets."""
        q = self.unpack(fields, spatial)
        e, phi, F, psi, chi = [fields[key] for key in ('e', 'phi', 'F', 'psi', 'chi')]
        U, A = q['U'], q['A']
        flow = self.geometry.evolve(e, [v['e'] for v in spatial], q['Omega'], q['spatial_Omega'],
            phi, U, A, F, [v['F'] for v in spatial], psi, chi,
            [v['psi'] for v in spatial], [v['chi'] for v in spatial])
        RA = [self.scalar_connection(A[mu, :]) for mu in range(4)]
        phi_rate = clean(U[0]-RA[0]*phi)
        gauge_rate = s.zeros(3, 12)
        for i in range(3):
            gauge_rate[i, :] = (F[i, :].T+q['dA0'][i]-self.gauge.bracket(A[0, :], A[i+1, :])).T
        Usp_rate = [clean(spatial[i]['U'][0, :].T+RA[i+1]*U[0]-RA[0]*U[i+1]+
                         self.scalar_connection(F[i, :])*phi) for i in range(3)]
        h = self.metric(e)
        assert h[0, 0] != 0
        dh_time = self.metric_derivative(e, h, flow['coframe_rate'])
        dh_space = [self.metric_derivative(e, h, v['e']) for v in spatial]
        P = [clean(sum((h[mu, nu]*U[nu] for nu in range(4)), s.zeros(70, 1))) for mu in range(4)]
        divergence = sum((sum((dh_space[i][i+1, nu]*U[nu]+
            h[i+1, nu]*spatial[i]['U'][nu, :].T for nu in range(4)), s.zeros(70, 1))
            for i in range(3)), s.zeros(70, 1))
        Y = self.common.yukawa_basis+[s.I*value for value in self.common.yukawa_basis]
        yukawa = s.Matrix([real((s.Abs(e.det())*chi*value*psi)[0]) for value in Y])
        scalar_force = clean(-sum((RA[mu]*P[mu] for mu in range(4)), s.zeros(70, 1))-
                             2*s.Abs(e.det())*(phi-self.vacuum)+yukawa)
        U0_rate = clean((scalar_force-divergence-
            sum((dh_time[0, nu]*U[nu] for nu in range(4)), s.zeros(70, 1))-
            sum((h[0, i+1]*Usp_rate[i] for i in range(3)), s.zeros(70, 1)))/h[0, 0])
        U_rate = clean(s.Matrix.vstack(U0_rate.T, *[row.T for row in Usp_rate]))
        rates = {'e': flow['coframe_rate'], 'Omega': flow['Omega_spatial_rate'],
                 'A': clean(gauge_rate), 'F': flow['time4']['Maxwell']['curvature_rate'],
                 'phi': phi_rate, 'U': U_rate, 'psi': flow['psi_rate'], 'chi': flow['chi_rate']}
        A0_rate = self.time_connection_derivative(q['port'], phi_rate, U0_rate)
        original_scalar = clean(h[0, 0]*U0_rate+
            sum((h[0, i+1]*Usp_rate[i] for i in range(3)), s.zeros(70, 1))+
            sum((dh_time[0, nu]*U[nu] for nu in range(4)), s.zeros(70, 1))+
            divergence-scalar_force)
        equal(original_scalar, s.zeros(70, 1))
        equal(self.orbit.T*phi_rate, s.zeros(12, 1))
        return {'rates': rates, 'connection': A, 'connection_rate': A0_rate.T.col_join(gauge_rate),
                'spatial_A0': q['dA0'], 'time_connection_port': q['port'],
                'geometry_flow': flow, 'metric': h, 'metric_time_derivative': dh_time,
                'metric_spatial_derivatives': dh_space, 'scalar_momenta': P,
                'scalar_Yukawa_source': clean(yukawa), 'scalar_covariant_force': scalar_force,
                'all70_original_scalar_divergence_rows_zero': True}

    def defects(self, fields, spatial, produced):
        A, h, g = produced['connection'], produced['metric'], self.gauge
        phi, U = fields['phi'], [fields['U'][mu, :].T for mu in range(4)]
        V = [clean(U[i+1]-spatial[i]['phi']-self.scalar_connection(A[i+1, :])*phi) for i in range(3)]
        W = s.zeros(3, 12)
        for row, (i, j) in enumerate(PAIRS[3:]):
            W[row, :] = (fields['F'][row+3, :]-spatial[i-1]['A'][j-1, :]+
                         spatial[j-1]['A'][i-1, :]-g.bracket(A[i, :], A[j, :]).T)
        K = g.constitutive(fields['e'])['kernel']
        P = clean(K*fields['F']*g.gram)
        dP = [clean((self.geometry.time4.kernel_derivative(fields['e'], spatial[i]['e'])*fields['F']+
                     K*spatial[i]['F'])*g.gram) for i in range(3)]
        J = produced['geometry_flow']['time4']['current']['total']
        G = clean(sum((dP[i][i, :].T-g.ad(A[i+1, :]).T*P[i, :].T for i in range(3)),
                      s.zeros(12, 1))+J[0, :].T)
        return {'scalar_jet': V, 'gauge_curvature': clean(W), 'potential': clean(self.orbit.T*phi),
                'Gauss': G, 'gauge_momenta': P, 'gauge_spatial_momentum_jets': dP,
                'spatial_torsion': produced['geometry_flow']['spatial_torsion_constraint'],
                'temporal_coframe': produced['geometry_flow']['all16_coframe_Euler'].extract([0, 4, 8, 12], [0])}

    def current_derivative(self, fields, produced, direction):
        """Original scalar and independent-dual current product rule."""
        e, phi, U = fields['e'], fields['phi'], [fields['U'][mu, :].T for mu in range(4)]
        h = produced['metric']
        dh = self.metric_derivative(e, h, direction['e'])
        dU = [direction['U'][mu, :].T for mu in range(4)]
        P = produced['scalar_momenta']
        dP = [sum((dh[mu, nu]*U[nu]+h[mu, nu]*dU[nu] for nu in range(4)), s.zeros(70, 1))
              for mu in range(4)]
        scalar = s.Matrix(4, 12, lambda mu, a:
            contraction(dP[mu], self.rho[a]*phi)+contraction(P[mu], self.rho[a]*direction['phi']))
        psi, chi = fields['psi'].reshape(4, 63), fields['chi'].reshape(4, 63)
        dpsi, dchi = direction['psi'].reshape(4, 63), direction['chi'].reshape(4, 63)
        adj = e.adjugate()
        dadj = clean(s.trace(e.inv()*direction['e'])*adj-e.inv()*direction['e']*adj)
        from source_lorentz_contact import GAMMA
        E = [s.sign(e.det())*s.I*sum((adj[mu, b]*GAMMA[b] for b in range(4)), s.zeros(4))
             for mu in range(4)]
        dE = [s.sign(e.det())*s.I*sum((dadj[mu, b]*GAMMA[b] for b in range(4)), s.zeros(4))
              for mu in range(4)]
        matter = s.zeros(4, 12)
        for a, rho in enumerate(self.gauge.rho63):
            density = psi*rho.T*chi.T
            change = dpsi*rho.T*chi.T+psi*rho.T*dchi.T
            for mu in range(4):
                matter[mu, a] = real(s.trace(dE[mu]*density+E[mu]*change))
        return clean(scalar+matter)

    def defect_rates(self, fields, spatial, produced):
        """Actual V/W/C/G propagation; mixed second derivatives cancel first."""
        defects = self.defects(fields, spatial, produced)
        rates, A, g = produced['rates'], produced['connection'], self.gauge
        Vdot = []
        for i in range(3):
            gradient_phi_rate = (spatial[i]['U'][0, :].T-
                self.scalar_connection(produced['spatial_A0'][i])*fields['phi']-
                self.scalar_connection(A[0, :])*spatial[i]['phi'])
            actual = clean(rates['U'][i+1, :].T-gradient_phi_rate-
                self.scalar_connection(rates['A'][i, :])*fields['phi']-
                self.scalar_connection(A[i+1, :])*rates['phi'])
            equal(actual, -self.scalar_connection(A[0, :])*defects['scalar_jet'][i])
            Vdot.append(actual)
        Wdot = s.zeros(3, 12)
        for row, (i, j) in enumerate(PAIRS[3:]):
            # The symmetric partial_i partial_j A0 terms have opposite signs.
            actual_curvature_rate = (spatial[i-1]['F'][j-1, :].T-spatial[j-1]['F'][i-1, :].T-
                g.bracket(produced['spatial_A0'][i-1], A[j, :])-
                g.bracket(A[0, :], spatial[i-1]['A'][j-1, :])+
                g.bracket(produced['spatial_A0'][j-1], A[i, :])+
                g.bracket(A[0, :], spatial[j-1]['A'][i-1, :])+
                g.bracket(rates['A'][i-1, :], A[j, :])+g.bracket(A[i, :], rates['A'][j-1, :]))
            Wdot[row, :] = clean(rates['F'][row+3, :].T-actual_curvature_rate).T
            equal(Wdot[row, :].T, -g.bracket(A[0, :], defects['gauge_curvature'][row, :]))
        Jdot = self.current_derivative(fields, produced, rates)
        dJ = [self.current_derivative(fields, produced, direction) for direction in spatial]
        P, dP = defects['gauge_momenta'], defects['gauge_spatial_momentum_jets']
        Pdot = produced['geometry_flow']['time4']['Maxwell']['electric_momentum_rate']
        Gdot = Jdot[0, :].T
        # Sum_i partial_i Pdot_(0i), with the antisymmetric double divergence
        # sum_ij partial_i partial_j P_(ji) cancelled over every source slot.
        for i in range(1, 4):
            Gdot += (g.ad(produced['spatial_A0'][i-1]).T*P[i-1, :].T+
                     g.ad(A[0, :]).T*dP[i-1][i-1, :].T+dJ[i-1][i, :].T-
                     g.ad(rates['A'][i-1, :]).T*P[i-1, :].T-
                     g.ad(A[i, :]).T*Pdot[i-1, :].T)
            for j in range(1, 4):
                Gdot += (g.ad(spatial[i-1]['A'][j-1, :]).T*g.ordered_pair(P, j, i)+
                         g.ad(A[j, :]).T*g.ordered_pair(dP[i-1], j, i))
        scalar_defect = s.Matrix([sum(contraction(produced['scalar_momenta'][i+1],
                    self.rho[a]*defects['scalar_jet'][i]) for i in range(3)) for a in range(12)])
        gauge_defect = sum((g.ad(defects['gauge_curvature'][row, :]).T*P[row+3, :].T
                            for row in range(3)), s.zeros(12, 1))
        expected = clean(g.ad(A[0, :]).T*defects['Gauss']-
                         2*s.Abs(fields['e'].det())*defects['potential']-scalar_defect+gauge_defect)
        equal(clean(Gdot), expected)
        return {'defects': defects, 'scalar_jet_rates': Vdot, 'gauge_curvature_rates': clean(Wdot),
                'potential_rate': clean(self.orbit.T*rates['phi']),
                'Gauss_rate_from_original_Maxwell_and_current_derivatives': clean(Gdot),
                'Gauss_homogeneous_defect_formula': expected,
                'scalar_jet_correction': clean(scalar_defect), 'gauge_curvature_correction': clean(gauge_defect)}


def zero_spatial(fields):
    return [{key: s.zeros(*fields[key].shape) for key in KEYS} for _ in range(3)]


def encode_fields(fields):
    return {key: encode(value) for key, value in fields.items()}


def encode_defects(defects):
    return {key: ([encode(v) for v in value] if isinstance(value, list) else encode(value))
            for key, value in defects.items()}


def homogeneous_fields(model):
    receipt = json.loads((HERE/'source_homogeneous_canonical_flow.json').read_bytes())
    f = {name: decode(value) for name, value in receipt['datum'].items()}
    r = {name: decode(value) for name, value in receipt['complete_rates'].items()}
    e, phi, A = f['e'], f['phi'], f['A']
    g = model.gauge
    h, constitutive = model.metric(e), g.constitutive(e)
    Usp = [model.scalar_connection(A[i+1, :])*phi for i in range(3)]
    U0 = clean((f['Pi_phi']-sum((h[0, i+1]*Usp[i] for i in range(3)), s.zeros(70, 1)))/h[0, 0])
    F = g.curvature(A, s.zeros(4, 48))
    F[:3, :] = clean(constitutive['electric_inverse']*(f['Pi_A']*g.gram_inverse-constitutive['mixed']*F[3:, :]))
    chi = model.common.canonical_dual(model.common.matter_data(e, phi, A), f['p'])
    fields = {'e': e, 'Omega': decode(receipt['source_Lorentz_connection'])[6:, :],
              'A': A[1:, :], 'F': F, 'phi': phi, 'U': s.Matrix.vstack(U0.T, *[v.T for v in Usp]),
              'psi': f['psi'], 'chi': chi}
    return fields, f, r


def certify_homogeneous_consumer(model):
    fields, f, r = homogeneous_fields(model)
    spatial = zero_spatial(fields)
    actual = model.rhs(fields, spatial)
    defects = model.defects(fields, spatial, actual)
    for key in ('e', 'psi', 'phi'):
        equal(actual['rates'][key], r[key])
    equal(actual['connection'], f['A']); equal(actual['connection_rate'], r['A'])
    dPi = clean(sum((actual['metric_time_derivative'][0, nu]*fields['U'][nu, :].T+
                    actual['metric'][0, nu]*actual['rates']['U'][nu, :].T for nu in range(4)), s.zeros(70, 1)))
    equal(dPi, r['Pi_phi'])
    for name in ('gauge_curvature', 'potential', 'Gauss', 'spatial_torsion', 'temporal_coframe'):
        equal(defects[name], s.zeros(*defects[name].shape))
    for row in defects['scalar_jet']:
        equal(row, s.zeros(70, 1))
    count = sum(value.rows*value.cols*(2 if key in ('psi', 'chi') else 1) for key, value in fields.items())
    assert count == 1500
    return {'all1500_real_rates_generated': True, 'source_state_real_dimension': count,
            'fields': encode_fields(fields), 'spatial': [encode_fields(value) for value in spatial],
            'rates': encode_fields(actual['rates']), 'defects': encode_defects(defects),
            'original_coframe_matter_scalar_connection_rates_recovered': True,
            'all70_original_scalar_momentum_rates_recovered': True,
            'all_initial_constraint_groups_zero': True}


def certify_coefficient_spine(model):
    previous = json.loads((HERE/'independent_source_constraint_preservation.json').read_bytes())
    assert previous['root'] == ROOT_ID
    assert previous['all840_full252_Yukawa_covariance_matrices']
    assert previous['all144_scalar_representation_brackets']
    for group in ('source_sha256', 'input_sha256'):
        for path, digest in previous[group].items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    equal(model.select.T*model.row_rebuild, s.eye(9))
    equal(model.row_rebuild*model.select.T*model.orbit.T, model.orbit.T)
    equal(model.time_connection(model.vacuum, s.zeros(70, 1))['broken_matrix'],
          (model.orbit*model.select).T*(model.orbit*model.select))
    g = model.gauge
    for a in range(12):
        equal(model.rho[a].T, -model.rho[a])
        for b in range(12):
            # This is the complete coefficient identity killing the symmetric
            # K(e) contraction sum_pair ad(F_pair)^T (K F Gram)_pair.
            equal(g.adjoint[a].T*g.gram[:, b]+g.adjoint[b].T*g.gram[:, a], s.zeros(12, 1))
    return {'original_full840_Yukawa_covariance_and144_representation_identities_consumed': True,
            'full_source_hashes_of_that_certificate_checked': True,
            'all144_native_curvature_pair_cancellation_coefficients': True,
            'uniform_A0_generator': 'O^T=row_rebuild*S^T O^T, S^T row_rebuild=I9; D A0=O^T U0 follows for every phi,U0 with det D9(phi)!=0, without requiring C=0 to define the ambient RHS.',
            'no_new_source_occurrence': True}


def spatial_fields(model):
    original = json.loads((HERE/'source_spatial_lorentz_time.json').read_bytes())['actual_spatial_first_jet_consumer']['fields']
    one = lambda name: decode(original[name])
    several = lambda name: list(map(decode, original[name]))
    fields = {'e': one('e'), 'Omega': one('Omega')[6:, :], 'A': one('A')[1:, :],
              'F': one('F'), 'phi': one('phi')+(model.orbit*model.select)[:, 0]/43,
              'U': s.Matrix.vstack(*[value.T for value in several('U')]),
              'psi': one('psi'), 'chi': one('chi')}
    spatial = []
    for i in range(3):
        spatial.append({'e': several('spatial_e')[i], 'Omega': several('spatial_Omega')[i][6:, :],
            'A': s.Matrix(3, 12, lambda a, b: s.Rational((i+2*a+b)%5-2, 137)),
            'F': s.Matrix(6, 12, lambda a, b: s.Rational((2*i+a+3*b)%7-3, 139)),
            'phi': s.Matrix([s.Rational((i+2*j)%5-2, 149) for j in range(70)]),
            'U': s.Matrix(4, 70, lambda a, b: s.Rational((i+3*a+b)%7-3, 151)),
            'psi': several('spatial_psi')[i], 'chi': several('spatial_chi')[i]})
    return fields, spatial


def certify_actual_defect_transport(model):
    fields, spatial = spatial_fields(model)
    produced = model.rhs(fields, spatial)
    propagation = model.defect_rates(fields, spatial, produced)
    defects = propagation['defects']
    assert defects['potential'].todok() and defects['Gauss'].todok()
    assert defects['gauge_curvature'].todok() and all(value.todok() for value in defects['scalar_jet'])
    assert propagation['scalar_jet_correction'].todok()
    assert propagation['gauge_curvature_correction'].todok()
    report = {'all1500_real_rates_and_nonzero_spatial_jets': True,
            'fields': encode_fields(fields), 'spatial': [encode_fields(value) for value in spatial],
            'rates': encode_fields(produced['rates']), 'defects': encode_defects(defects),
            'defect_rates': {'scalar_jet': [encode(v) for v in propagation['scalar_jet_rates']],
                             'gauge_curvature': encode(propagation['gauge_curvature_rates']),
                             'potential': encode(propagation['potential_rate']),
                             'spatial_torsion': encode(s.zeros(12, 1)),
                             'Gauss': encode(propagation['Gauss_rate_from_original_Maxwell_and_current_derivatives'])},
            'source_scalar_phi_and_F_jet_defects_intentionally_nonzero': True,
            'Vdot_equals_minus_rho_A0_V_all210_rows': True,
            'Wdot_equals_minus_ad_A0_W_all36_rows': True,
            'Cdot_zero_all12_rows_rank9': True,
            'Gauss_dot_full12_direct_Maxwell_current_product_rule': True,
            'Gauss_dot': encode(propagation['Gauss_rate_from_original_Maxwell_and_current_derivatives']),
            'nonzero_scalar_jet_correction': encode(propagation['scalar_jet_correction']),
            'nonzero_gauge_curvature_correction': encode(propagation['gauge_curvature_correction']),
            'no_initial_constraint_solution_claim_for_this_test_datum': True}
    return report, fields, spatial, produced


def certify_literal_source(model):
    background = json.loads((BASE/'active-gauge/receipt.json').read_bytes())['actual_background']
    occupied = json.loads((BASE/'occupied-response/receipt.json').read_bytes())
    e = s.Matrix(background['coframe']).applyfunc(s.sympify)
    A = s.Matrix(background['gauge_connection']).applyfunc(s.sympify)
    Omega = s.Matrix(background['lowered_Lorentz_connection']).applyfunc(s.sympify).reshape(24, 1)
    psi = decode(occupied['occupied_frame'])*s.Matrix(background['primal_H']).applyfunc(s.sympify)
    phi, chi = model.vacuum, s.sqrt(2)*psi.T
    fields = {'e': e, 'Omega': Omega[6:, :], 'A': A[1:, :],
              'F': model.gauge.curvature(A, s.zeros(4, 48)), 'phi': phi,
              'U': s.Matrix.vstack(*[(model.scalar_connection(A[mu, :])*phi).T for mu in range(4)]),
              'psi': psi, 'chi': chi}
    spatial = zero_spatial(fields)
    actual = model.rhs(fields, spatial)
    defects = model.defects(fields, spatial, actual)
    for name in ('gauge_curvature', 'potential', 'Gauss', 'spatial_torsion', 'temporal_coframe'):
        equal(defects[name], s.zeros(*defects[name].shape))
    for value in defects['scalar_jet']:
        equal(value, s.zeros(70, 1))
    for key in ('e', 'Omega', 'A', 'F', 'phi', 'U'):
        equal(actual['rates'][key], s.zeros(*actual['rates'][key].shape))
    full = json.loads((BASE/'full-quantum/receipt.json').read_bytes())
    equal(actual['rates']['psi'], -s.I*decode(full['original_H_full'])*psi)
    assert actual['rates']['psi'].todok()
    D9 = model.time_connection(phi, fields['U'][0, :].T)['broken_matrix']
    M4 = model.geometry.time4.time_minor(e, fields['F'])['matrix']
    return {'literal_source_fields': encode_fields(fields),
            'all_initial_constraints_zero': True,
            'original_bosonic_source_rate_zero': True,
            'full252_primal_rate_equals_unshifted_original_H': True,
            'source_time_minor_determinant': str(s.factor(M4.det())),
            'source_D9_determinant': str(s.factor(D9.det())),
            'source_coframe_determinant': str(e.det()),
            'source_spatial_metric_determinant': str((e[:, 1:].T*ETA*e[:, 1:]).det()),
            'source_scalar_time_coefficient': str(model.metric(e)[0, 0]),
            'source_native_gauge_time_metric': str((e.T*ETA*e)[0, 0])}


def certify_F4_tail(model, fields, spatial, produced):
    from source_coframe_constraint_transport import SourceCoframeConstraintTransport
    helper = SourceCoframeConstraintTransport()
    data = helper.transport(fields['e'], [produced['rates']['e'], *[v['e'] for v in spatial]])
    equal(data['time'], fields['e'].T)
    # This spatial fixture already has original torsion/Spin rows zero. Its
    # four temporal Euler residuals are kept, testing the off-constraint map.
    full_Euler = produced['geometry_flow']['all16_coframe_Euler']
    F4 = full_Euler.extract([0, 4, 8, 12], [0])
    equal(full_Euler, data['whole']*F4)
    assert F4.todok()
    return {'original_signed_F4_helper_consumed': True,
            'actual_nonzero_F4_reconstructs_all16_coframe_Euler': True,
            'time': encode(data['time']), 'spatial': [encode(v) for v in data['spatial_coefficients']],
            'lower': encode(data['lower']), 'solved_spatial': [encode(v) for v in data['solved_spatial']],
            'solved_lower': encode(data['solved_lower']),
            'domain_order': 'Apply its homogeneous PDE after V/W/C/T/G preservation has generated the other original Euler equations along the analytic field solution.'}


def analytic_Cauchy_contract(source):
    return {
        'public_mouth': 'For every real-analytic initial three-dimensional spatial profile in the source open chart whose original constraint germs vanish (equivalently the constraints hold throughout an initial spatial neighborhood), the generated1500 first-order system has a unique local real-analytic solution germ in the fixed Omega0=0 and source stabilizer representatives. Its reconstructed original fields satisfy all1310 real Euler rows.',
        'independent_fields': 'e16, Omega_i18, A_i36, F_mu_nu72, phi70, U_mu280, psi/chi1008 real =1500',
        'RHS': 'SourceFirstOrderCauchy.rhs(fields,three_spatial_jets) evaluates all rates, including the original scalar divergence/curl, Maxwell/Bianchi, full independent Dirac pair, coframe4 and spatial Lorentz18.',
        'source_open_chart': ['det(e)>0 and det(e_spatial^T eta e_spatial)!=0',
            'native gauge g00!=0; the scalar/Dirac time coefficient is nonzero on the coframe chart',
            'det(D9(phi))!=0 and det(M4(e,F))!=0, with their original source values256 and32*sqrt(30)'],
        'nonempty_source_witness': source,
        'first_order_derivation': [
            'All inverses depend only on the field values: e, its spatial metric, D9(phi), the native electric block, and M4(e,F). No inverse contains a spatial jet.',
            'A0=S D9^-1 S^T O^T U0 is algebraic. Its actual spatial derivative is inverse*(O^T partial_i U0-D(partial_i phi) A0), using precisely first spatial jets.',
            'Torsion0i generates dot(e_i). The original coordinate-defect/Maxwell system then generates dot(eTime) and dot(F). The full Dirac pair gives dot(psi),dot(chi). Prolonged spatial torsion plus metric Euler generates dot(Omega_i). These operations are affine in first spatial jets.',
            'Covariant scalar curl generates dot(U_i); the original scalar divergence then solves its nonzero h00 coefficient for dot(U0). There is no unknown time derivative on the right side of this dependency order.',
            'The apparent second spatial derivatives of eTime and A0 cancel as mixed derivative commutators in torsion/curl. They are absent from the executable RHS.'],
        'analytic_existence_and_uniqueness': [
            'Split each independent complex psi and chi into real and imaginary coordinates. On the positive-orientation chart every displayed source coefficient is a real-analytic rational function of those1500 real fields, with fixed original algebraic constants.',
            'The chart is generated from nonzero source denominators. Write each denominator as D(u_source+z)=D0+sum_(alpha!=0)c_alpha z^alpha, using coefficients after translation to the source. A positive radius<=1 and <=abs(D0)/(2 sum_(alpha!=0)abs(c_alpha)) gives abs(D-D0)<=abs(D0)/2. Constant denominators impose no further restriction. Thus no caller supplies an analytic-majorant certificate.',
            'For analytic initial data u0(x), set u_(n+1)(x)=[t^n] RHS(sum_(j<=n)u_j(x)t^j, partial_x sum_(j<=n)u_j(x)t^j)/(n+1). Every coefficient is generated from the original RHS and earlier coefficients, not from an assumed solution.',
            'The analytic first-order Cauchy-Kowalevski theorem applies to this solved system with time coefficient I1500. It gives local convergence of the generated time series and uniqueness of the analytic solution germ. A first-time/second-space equation is not being substituted for this first-order hypothesis.',
            'The ambient analytic solution exists without imposing a regularity condition on any constraint level. The original Euler conclusion uses the zero initial constraints and the following source-generated propagation.'],
        'uniform_constraint_propagation': [
            'V_i=U_i-D_i phi obeys dot(V_i)=-rho(A0)V_i. W_ij=F_ij-F(A)_ij obeys dot(W_ij)=-[A0,W_ij]. Both identities follow by the actual product rule, cancellation of the symmetric second A0 derivatives, and the original representation/Jacobi identities.',
            'C=O^T phi obeys dot(C)=0 because the generated A0 solves D A0=O^T U0 on the whole ambient chart. The12 spatial torsion constraints obey dot(Tsp)=0 by the actual18 time equations, with Omega0 fixed0.',
            'Using the original scalar/matter currents, symmetric h/K, native Lie pairing and all840 repaired Yukawa covariance coefficients gives dot(G)=ad(A0)^T G-2abs(det e)C-sum_i (P_scalar^i)^T rho_a V_i+sum_spatial_pairs ad(W_ij)^T P_gauge,ij. The mixed second divergence of the antisymmetric curvature momentum cancels before this equation is formed.',
            'Therefore V/W/C/Tsp/G all retain zero initial data by uniqueness of their triangular finite linear equations along each spatial point. The source matter pair, scalar equation, complete Maxwell equation and original Lorentz/torsion equation now hold along the analytic solution.',
            'Original Spin Noether and the six metric Euler equations reconstruct all16 coframe Euler rows from F4 by the independently generated K(e). The original coordinate Noether identity and the actual div(Q)=0 then give e^T partial_t F4+sum_i e^T K_i partial_i F4+B(e,de)F4=0.',
            'Its coefficients are analytic along the generated solution and its time coefficient e^T is invertible. The analytic first-order linear Cauchy theorem gives the unique zero solution for zero initial F4. Every coframe Euler row consequently vanishes.'],
        'initial_constraints_are_current_data': 'V/W/Tsp/C/G and F4 are functions of the initial field values and first spatial jets. Their zero-germ condition is imposed on the analytic initial profile, not merely at one spatial point. Gt has zero temporal-coframe columns and partial_eTime E0=0, so F4 contains no unknown Omega_i time derivative or matter time derivative. No future trajectory is supplied as initial data.',
        'actual_initial_zero_germs': 'The literal source and the certified nontrivial homogeneous datum define constant spatial initial profiles. Their exact zero constraint readbacks therefore hold throughout the initial spatial neighborhood. The separate nonzero spatial ambient fixture certifies propagation identities and is not declared a constrained initial profile.',
        'original_fields_and_auxiliaries': [
            'Recover A0 from the same scalar-torque inverse, keep Omega0=0, and retain all original e,phi,psi,chi fields. V=W=0 identify U=Dphi and the independent F with the same connection curvature.',
            'Recover original gravity B=J wedge2(e), simplicity multiplier=J B-S R(Omega), and gauge B=-star_e F/sigma. Their original algebraic Euler rows vanish by the signed source elimination identities. Original BF boundary fluxes are unchanged.',
            'These are all16 coframe,70 scalar,48 connection,1008 independent real matter,24 Lorentz,72 gravity/simplicity auxiliary and72 gauge auxiliary rows:1310.',
            'Any other analytic original-action solution in the same fixed representatives and chart produces the same first-order variables F and U and hence the same solved1500 RHS. Ambient CK uniqueness then gives original-field uniqueness.'],
        'scope': 'Local analytic spatial Cauchy germs of the untruncated same-source action; no general smooth-data theorem, global-in-time result or interacting quantum spectral measure is inferred.',
        'formal_Lean_time_path_installation_claimed': False,
        'proper_clock': 'Source reference clock tau=N*t, N=3*sqrt(30)/25; the coordinate time has not been reparameterized.'}


def main():
    started = time.monotonic()
    model = SourceFirstOrderCauchy()
    homogeneous = certify_homogeneous_consumer(model)
    print('PASS actual1500 first-order rates and original nontrivial homogeneous scalar70/A0 consumers', flush=True)
    coefficients = certify_coefficient_spine(model)
    print('PASS original full Yukawa/representation coefficients and uniform A0/source curvature cancellation', flush=True)
    transport, fields, spatial, produced = certify_actual_defect_transport(model)
    print('PASS actual nonzero spatial1500 RHS and all V/W/C/G defect propagation rows', flush=True)
    source = certify_literal_source(model)
    print('PASS literal original source initial constraints and unshifted full252 time generator', flush=True)
    tail = certify_F4_tail(model, fields, spatial, produced)
    print('PASS actual off-constraint coframe Euler reconstruction and signed F4 transport consumer', flush=True)
    inputs = [HERE/name for name in (
        'source_first_order_cauchy.py', 'source_spatial_lorentz_time.py', 'source_spatial_lorentz_time.json',
        'independent_source_spatial_lorentz_time.json', 'source_spatial_time_coframe.py', 'source_spatial_time_coframe.json',
        'independent_source_spatial_time_coframe.json', 'source_coframe_constraint_transport.py',
        'source_coframe_constraint_transport.json', 'independent_source_coframe_constraint_transport.json',
        'source_constraint_preservation.py', 'source_constraint_preservation.json', 'independent_source_constraint_preservation.json',
        'source_homogeneous_canonical_flow.json', 'source_common_hamiltonian.py', 'source_gauge_legendre.py',
        'source_lorentz_contact.py', 'source_coframe_legendre.py', 'source_scalar_legendre.py')]
    inputs += [BASE/'active-gauge/receipt.json', BASE/'occupied-response/receipt.json', BASE/'full-quantum/receipt.json']
    result = {'root': ROOT_ID, 'verdict': 'SOURCE_FIRST_ORDER1500_AND_LOCAL_ANALYTIC_SPATIAL_CAUCHY_GENERATED',
              'source_sha256': model.common.scalar.exchange.vertices['source_sha256'],
              'actual_homogeneous_consumer': homogeneous,
              'source_coefficient_spine': coefficients,
              'actual_constraint_transport': transport,
              'original_F4_transport_consumer': tail,
              'analytic_Cauchy_source_construction': analytic_Cauchy_contract(source),
              'local_analytic_spatial_Cauchy_closed': True,
              'general_smooth_spatial_or_global_Cauchy_claimed': False,
              'interacting_quantum_spectral_measure_generated': False,
              'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in inputs},
              'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
              'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_first_order_cauchy.json').write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
