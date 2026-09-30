#!/usr/bin/env python3
"""Actual joint temporal update from the complete homogeneous canonical flow.

The tangent is generated in every original field coordinate. It need not stay
in the explicit initial-data family. All source constraint rates, including
the four temporal coframe equations, consume that same tangent.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID
from source_coframe_initial_constraints import SourceCoframeInitialConstraints
from source_common_hamiltonian import real
from source_lorentz_contact import clean, equal, encode, GAMMA
from source_scalar_legendre import dot
from source_lorentz_contact import PAIRS, PAIR_SIGN, J, WEDGE, wedge_matrix


def contraction(A, B):
    return s.expand(sum(a*b for a, b in zip(A, B)))


class SourceJointTemporalRates:
    def __init__(self):
        self.initial = SourceCoframeInitialConstraints()
        self.common = self.initial.common
        self.constraints = self.initial.constraints
        self.gauge = self.common.gauge
        self.electric_coefficient = s.simplify(self.gauge.sigma*contraction(
            self.initial.A[1:, :], self.initial.A[1:, :]*self.gauge.gram)/6)
        assert self.electric_coefficient == s.Rational(9, 100)

    def initial_fields(self, u, alpha, beta, radial, gauge_radial):
        a = s.factor(self.initial.clock_coefficient(u, alpha, beta, radial))
        assert a.is_positive is True
        c = self.initial.c+self.electric_coefficient*gauge_radial**2
        n2 = s.cancel(3*c/a)
        fields = self.initial.fields(s.sqrt(n2), s.zeros(3, 1), u, alpha, beta, radial)
        return {**fields, 'gauge_momentum': clean(gauge_radial*self.initial.A[1:, :]*self.gauge.gram),
                'gauge_radial': gauge_radial, 'clock_squared': n2, 'clock_coefficient': a,
                'gauge_energy_coefficient': c}

    def gravity_force(self, e, psi, chi, Omega):
        model = self.common.coframe
        density = clean(psi.reshape(4, 63)*chi.reshape(4, 63).T)
        force = s.zeros(16, 1)
        for a in range(16):
            dadj = model.at(model.dadj[a], e)
            dV = [clean(s.sign(e.det())*sum((s.I*dadj[mu, b]*GAMMA[b]
                        for b in range(4)), s.zeros(4))*S)
                  for mu in range(4) for S in model.lorentz.spin]
            dj = s.Matrix([real(s.trace(V*density)) for V in dV])
            dH = model.at(model.dH[a], e)
            force[a] = s.expand(-3*e.adjugate()[a % 4, a//4]+
                (Omega.T*dH*Omega)[0]/2+(Omega.T*dj)[0])
        return clean(force)

    def canonical_rates(self, fields):
        e, phi, psi, p, Pi = [fields[name] for name in ('e', 'phi', 'psi', 'p', 'Pi_phi')]
        A, Pi_A = self.initial.A, fields['gauge_momentum']
        common = self.common
        velocities = common.boson_velocities(e, s.zeros(16, 1), s.zeros(48, 1), phi, Pi,
            [s.zeros(70, 1)]*3, A, Pi_A, s.zeros(3, 48), psi, p, s.zeros(10, 1))
        equal(velocities['coframe'], s.zeros(16, 1))
        data = common.matter_data(e, phi, A)
        chi = common.canonical_dual(data, p)
        Omega = common.coframe.lorentz.eliminate(e, s.zeros(64, 1), psi, chi)['connection']
        matter = common.matter_canonical_flow(e, s.zeros(64, 1), phi, A, psi, p,
            [s.zeros(252, 1)]*3, [s.zeros(1, 252)]*3, Omega)
        psi_dot, p_dot = matter['primal_velocity'], matter['canonical_dual_velocity']
        chi_dot = clean(s.I*p_dot*data['inverse_E'])
        scalar = self.constraints.original_scalar_rates(e, s.zeros(16, 1), [s.zeros(16, 1)]*3,
            phi, Pi, [s.zeros(70, 1)]*3, [s.zeros(70, 1)]*3,
            [[s.zeros(70, 1)]*3 for _ in range(3)], A, s.zeros(3, 48), Pi_A, psi, chi)
        dphi = [velocities['scalar'], *[s.zeros(70, 1)]*3]
        dA = s.zeros(4, 48)
        dA[0, 12:] = velocities['gauge_spatial'].reshape(1, 36)
        curvature = self.gauge.curvature(A, dA)
        field_P = self.gauge.curvature_momentum(e, curvature)
        equal(field_P[:3, :], Pi_A)
        scalar_current, _ = self.gauge.scalar_current(e, phi, dphi, A)
        matter_current = self.gauge.matter_current(e, psi, chi)
        Pi_A_dot = s.zeros(3, 12)
        for i in range(3):
            Pi_A_dot[i, :] = sum((self.gauge.ad(A[mu, :]).T*
                self.gauge.ordered_pair(field_P, mu, i+1) for mu in range(4)), s.zeros(12, 1)).T
        Pi_A_dot += scalar_current[1:, :]+matter_current[1:, :]
        remaining = self.initial.full.remaining_stress(e, phi, dphi, A, dA, psi,
                            [psi_dot, *[s.zeros(252, 1)]*3], chi)
        Pi_e_dot = clean(self.gravity_force(e, psi, chi, Omega)+sum(remaining.values(), s.zeros(16, 1)))
        equal(Pi_e_dot.extract([0, 4, 8, 12], [0]), s.zeros(4, 1))
        return {'coframe_spatial_rate': velocities['coframe'], 'coframe_momentum_rate': Pi_e_dot,
                'scalar_rate': velocities['scalar'], 'scalar_momentum_rate': scalar['scalar_momentum_rate'],
                'gauge_spatial_rate': velocities['gauge_spatial'], 'gauge_momentum_rate': clean(Pi_A_dot),
                'primal_rate': psi_dot, 'canonical_dual_rate': p_dot, 'dual_rate_at_fixed_spatial_coframe': chi_dot,
                'scalar_rate_data': scalar, 'connection': Omega, 'actual_scalar_current': scalar_current,
                'actual_matter_current': matter_current}

    def hamiltonian_tangent(self, fields, rates, n, shift):
        """D_z H for the complete generated tangent, holding only e[:,0] fixed."""
        e = s.diag(n, 1, 1, 1)
        e[1:, 0] = shift
        common, A = self.common, self.initial.A
        phi, Pi, psi, p = [fields[key] for key in ('phi', 'Pi_phi', 'psi', 'p')]
        dphi, dPi, dpsi, dp = [rates[key] for key in ('scalar_rate', 'scalar_momentum_rate', 'primal_rate', 'canonical_dual_rate')]
        dA = s.zeros(4, 12)
        dA[1:, :] = rates['gauge_spatial_rate']
        data = common.matter_data(e, phi, A)
        chi, dchi = common.canonical_dual(data, p), common.canonical_dual(data, dp)
        ports = common.coframe.lorentz.raw_matter_ports(e)
        M = clean(psi.reshape(4, 63)*chi.reshape(4, 63).T)
        dM = clean(dpsi.reshape(4, 63)*chi.reshape(4, 63).T+psi.reshape(4, 63)*dchi.reshape(4, 63).T)
        j = s.Matrix([real(s.trace(V*M)) for V in ports['V']])
        dj = s.Matrix([real(s.trace(V*dM)) for V in ports['V']])
        # The original source Pi_e and the full matter-induced shift both
        # vanish throughout this initial family, so dH/dPi_e=0 for every n,b.
        # Pi_e_dot is still generated above; its coefficient here is zero.
        state = common.coframe.currents(e, s.zeros(48, 1), psi, chi)
        equal(state['momentum_shift'], s.zeros(16, 1))
        dH_coframe = contraction(dj, state['Lorentz_inverse']*j)
        h, volume = common.scalar.metric_density(e)
        RA = [sum((A[mu, a]*common.scalar.rho[a] for a in range(12)), s.zeros(70)) for mu in range(4)]
        dRA = [sum((dA[mu, a]*common.scalar.rho[a] for a in range(12)), s.zeros(70)) for mu in range(4)]
        U = [RA[i+1]*phi for i in range(3)]
        dU = [RA[i+1]*dphi+dRA[i+1]*phi for i in range(3)]
        b = sum((h[0, i+1]*U[i] for i in range(3)), s.zeros(70, 1))
        db = sum((h[0, i+1]*dU[i] for i in range(3)), s.zeros(70, 1))
        dH_scalar = (dot(Pi-b, dPi-db)/h[0, 0]-dot(dPi, RA[0]*phi)-dot(Pi, RA[0]*dphi+dRA[0]*phi)
            -sum(h[i+1, k+1]*dot(U[i], dU[k]) for i in range(3) for k in range(3))
            +2*volume*dot(phi-common.scalar.vacuum, dphi))
        gd = self.gauge.constitutive(e)
        B, _ = self.gauge.spatial_data(A, s.zeros(3, 48))
        dB = s.Matrix.vstack(*[(self.gauge.bracket(dA[mu, :], A[nu, :])+
                               self.gauge.bracket(A[mu, :], dA[nu, :])).T
                              for mu, nu in ((2, 3), (3, 1), (1, 2))])
        X = fields['gauge_momentum']*self.gauge.gram_inverse-gd['mixed']*B
        dX = rates['gauge_momentum_rate']*self.gauge.gram_inverse-gd['mixed']*dB
        dH_gauge = (contraction(dX, gd['electric_inverse']*X*self.gauge.gram)-
                    contraction(dB, gd['magnetic']*B*self.gauge.gram))
        dY = sum(((dphi[j]+s.I*dphi[j+35])*Y for j, Y in enumerate(common.yukawa_basis)), s.zeros(252))
        dK = volume*dY+sum((data['principal'][mu]*sum(
            (dA[mu, a]*common.rho[a] for a in range(12)), s.zeros(252)) for mu in range(4)), s.zeros(252))
        K = data['lower_without_Lorentz']
        dH_matter = -real((dchi*K*psi+chi*K*dpsi+chi*dK*psi)[0])
        components = {key: s.factor(value) for key, value in (
            ('coframe', dH_coframe), ('scalar', dH_scalar), ('gauge', dH_gauge), ('remaining_matter', dH_matter))}
        return components, s.factor(sum(components.values()))

    def lower_left(self, e, phi, Pi_phi, connection):
        data = self.constraints.scalar_kinematics(e, phi, Pi_phi, [s.zeros(70, 1)]*3, connection)
        U = [data['covariant_time'], *data['spatial_covariant']]
        orbit = self.constraints.orbit*self.constraints.select
        return clean(s.Matrix.hstack(*[-orbit.T*sum((e.inv()[mu, a]*U[mu]
                    for mu in range(4)), s.zeros(70, 1)) for a in range(4)]))

    def joint_update(self, fields):
        rates = self.canonical_rates(fields)
        n = s.Symbol('temporal_n', positive=True)
        shift = s.Matrix(s.symbols('temporal_shift1:4', real=True))
        components, tangent = self.hamiltonian_tangent(fields, rates, n, shift)
        at_point = {n: fields['e'][0, 0], **dict.fromkeys(shift, 0)}
        assert s.simplify(tangent.subs(at_point)) == 0
        forcing = s.Matrix([-s.diff(tangent, x).subs(at_point).simplify() for x in [n, *shift]])
        c = fields['gauge_energy_coefficient']
        J = s.diag(-6*c/n**3, *[-4*c/n**3]*3).subs(at_point)
        time_coframe_rate = clean(-J.inv()*forcing)
        equal(J*time_coframe_rate+forcing, s.zeros(4, 1))
        whole_coframe_rate = rates['coframe_spatial_rate'].copy()
        for a in range(4):
            whole_coframe_rate[4*a] = time_coframe_rate[a]
        scalar = self.constraints.original_scalar_rates(fields['e'], whole_coframe_rate,
            [s.zeros(16, 1)]*3, fields['phi'], fields['Pi_phi'], [s.zeros(70, 1)]*3,
            [s.zeros(70, 1)]*3, [[s.zeros(70, 1)]*3 for _ in range(3)], self.initial.A,
            s.zeros(3, 48), fields['gauge_momentum'], fields['psi'], fields['chi'])
        A0_rate = self.constraints.solve_time_connection_derivative(fields['phi'], rates['scalar_rate'],
            scalar['time_connection_rhs_rate'], self.initial.A[0, :].T)['time_connection_rate']
        D = self.constraints.consistency_matrix(fields['phi'])
        equal(D*A0_rate+self.constraints.consistency_matrix(rates['scalar_rate'])*self.initial.A[0, :].T-
              scalar['time_connection_rhs_rate'], s.zeros(12, 1))
        B = self.lower_left(fields['e'], fields['phi'], fields['Pi_phi'], self.initial.A)
        S = self.constraints.select
        right = S.T*(rates['scalar_rate_data']['time_connection_rhs_rate']-
                     self.constraints.consistency_matrix(rates['scalar_rate'])*self.initial.A[0, :].T)
        equal(B*time_coframe_rate+S.T*D*A0_rate, right)
        return {**rates, 'Hamiltonian_tangent_components': components, 'Hamiltonian_tangent': tangent,
                'constraint_forcing': forcing, 'temporal_Jacobian': J,
                'time_coframe_rate': time_coframe_rate, 'whole_coframe_rate': whole_coframe_rate,
                'time_connection_rate': clean(A0_rate), 'lower_left': B,
                'whole_scalar_rate_data': scalar}

    def prolonged_jet(self, fields, update):
        """Generate accelerations from the same inverse Legendre maps and rates."""
        common, model = self.common, self.common.coframe
        e, phi, psi, p = [fields[key] for key in ('e', 'phi', 'psi', 'p')]
        chi = fields['chi']
        erate = update['whole_coframe_rate']
        geometry = model.geometry(e)
        ports = model.lorentz.raw_matter_ports(e)
        M = clean(psi.reshape(4, 63)*chi.reshape(4, 63).T)
        dM = clean(update['primal_rate'].reshape(4, 63)*chi.reshape(4, 63).T+
                   psi.reshape(4, 63)*update['dual_rate_at_fixed_spatial_coframe'].reshape(4, 63).T)
        dadj = model.at(sum((erate[a]*model.dadj[a] for a in range(16)), s.zeros(4)), e)
        dV = [clean(s.sign(e.det())*sum((s.I*dadj[mu, b]*GAMMA[b]
                     for b in range(4)), s.zeros(4))*S)
              for mu in range(4) for S in model.lorentz.spin]
        j = s.Matrix([real(s.trace(V*M)) for V in ports['V']])
        dj = s.Matrix([real(s.trace(dV[a]*M+V*dM)) for a, V in enumerate(ports['V'])])
        dH = model.at(sum((erate[a]*model.dH[a] for a in range(16)), s.zeros(24)), e)
        dGt = model.at(sum((erate[a]*model.dG[a][:, :16] for a in range(16)), s.zeros(24, 16)), e)
        K, Gt = geometry['Lorentz_inverse'], geometry['G'][:, :16]
        dK = clean(-K*dH*K)
        shift_rate = clean(-dGt.T*K*j-Gt.T*dK*j-Gt.T*K*dj)
        equal(geometry['null_frame'].T*(update['coframe_momentum_rate']-shift_rate), s.zeros(10, 1))
        acceleration = clean(geometry['velocity_inverse']*(update['coframe_momentum_rate']-shift_rate))
        de = erate.col_join(s.zeros(48, 1))
        dde = s.zeros(4, 64)
        dde[0, :16] = acceleration.T
        A = self.initial.A
        A_rate = s.zeros(4, 12)
        A_rate[0, :] = update['time_connection_rate'].T
        A_rate[1:, :] = update['gauge_spatial_rate']
        gd = self.gauge.constitutive(e)
        derivative_det = contraction(self.gauge.at(self.gauge.ddet, e), erate)
        derivative_kernel = clean(self.gauge.at(sum((erate[a]*self.gauge.dkernel[a]
            for a in range(16)), s.zeros(6)), e)/e.det()-gd['kernel']*derivative_det/e.det())
        mag, _ = self.gauge.spatial_data(A, s.zeros(3, 48))
        mag_rate = s.Matrix.vstack(*[(self.gauge.bracket(A_rate[mu, :], A[nu, :])+
                       self.gauge.bracket(A[mu, :], A_rate[nu, :])).T for mu, nu in ((2, 3), (3, 1), (1, 2))])
        X = fields['gauge_momentum']*self.gauge.gram_inverse-gd['mixed']*mag
        dX = update['gauge_momentum_rate']*self.gauge.gram_inverse-derivative_kernel[:3, 3:]*mag-gd['mixed']*mag_rate
        gauge_acceleration = clean(-gd['electric_inverse']*derivative_kernel[:3, :3]*gd['electric_inverse']*X+
            gd['electric_inverse']*dX+s.Matrix.vstack(*[(self.gauge.bracket(A_rate[i+1, :], A[0, :])+
                self.gauge.bracket(A[i+1, :], A_rate[0, :])).T for i in range(3)]))
        dA = s.zeros(4, 48)
        dA[0, :] = A_rate.reshape(1, 48)
        ddA = [s.zeros(4, 48) for _ in range(4)]
        ddA[0][0, 12:] = gauge_acceleration.reshape(1, 36)
        scalar_data = self.constraints.scalar_kinematics(e, phi, fields['Pi_phi'], [s.zeros(70, 1)]*3, A)
        h, U0, U = [scalar_data[key] for key in ('metric', 'covariant_time', 'spatial_covariant')]
        dh = self.constraints.metric_derivative(e, erate.reshape(4, 4))
        dRA = [sum((A_rate[mu, a]*self.constraints.rho[a] for a in range(12)), s.zeros(70)) for mu in range(4)]
        db = sum((dh[0, i+1]*U[i]+h[0, i+1]*(dRA[i+1]*phi+
                    scalar_data['R_A'][i+1]*update['scalar_rate']) for i in range(3)), s.zeros(70, 1))
        scalar_acceleration = clean((update['scalar_momentum_rate']-db-dh[0, 0]*U0)/h[0, 0]-
            dRA[0]*phi-scalar_data['R_A'][0]*update['scalar_rate'])
        equal(self.constraints.orbit.T*scalar_acceleration, s.zeros(12, 1))
        return {'de': de, 'dde': dde, 'dA': dA, 'ddA': ddA,
                'coframe_acceleration': acceleration, 'gauge_acceleration': gauge_acceleration,
                'scalar_acceleration': scalar_acceleration, 'coframe_momentum_shift_rate': shift_rate}


def verify_electric_family(model):
    n = s.Symbol('n', positive=True)
    shift = s.Matrix(s.symbols('shift1:4', real=True))
    u, alpha, beta, radial, gamma = s.symbols('u alpha beta radial gamma', real=True)
    fields = model.initial.fields(n, shift, u, alpha, beta, radial)
    momentum = gamma*model.initial.A[1:, :]*model.gauge.gram
    actual = model.common.hamiltonian(fields['e'], s.zeros(16, 1), s.zeros(48, 1),
        fields['phi'], fields['Pi_phi'], [s.zeros(70, 1)]*3, model.initial.A, momentum,
        s.zeros(3, 48), fields['psi'], fields['p'], [s.zeros(252, 1)]*3, s.zeros(10, 1))
    c = model.initial.c+model.electric_coefficient*gamma**2
    a = model.initial.clock_coefficient(u, alpha, beta, radial)
    radius = dot(shift, shift)
    expected = n*a+c*(3*n**2-radius)/(n*(n**2-radius))
    assert s.factor(actual['value']-expected) == 0
    equal(actual['coframe_primary'], s.zeros(10, 1))
    Gauss = model.common.gauss(fields['e'], fields['phi'], fields['Pi_phi'], model.initial.A,
        momentum, [s.zeros(3, 12)]*3, fields['psi'], fields['p'])
    equal(Gauss['total'], s.zeros(12, 1))
    return {'canonical_gauge_momentum': 'gamma*A_i*G_native', 'electric_coefficient': str(model.electric_coefficient),
            'full_gauge_coefficient': str(c), 'source_clock_coefficient': str(a),
            'complete_common_Hamiltonian': str(expected), 'positive_time_column': 'shift=0, n^2=3c/a on a>0',
            'original_source': 'u=alpha=beta=radial=gamma=0 returns SpinPair.actual and N^2=54/125',
            'whole_original_H_value_and_all_primary_Gauss_checked': True}


def verify_constraints_and_original_Euler(model, fields, update, jet):
    common, A = model.common, model.initial.A
    e, phi, Pi, psi, chi, p = [fields[key] for key in ('e', 'phi', 'Pi_phi', 'psi', 'chi', 'p')]
    dpsi = [update['primal_rate'], *[s.zeros(252, 1)]*3]
    dchi = [update['dual_rate_at_fixed_spatial_coframe'], *[s.zeros(1, 252)]*3]
    dphi = [update['scalar_rate'], *[s.zeros(70, 1)]*3]
    coframe = model.initial.full.euler(e, jet['de'], jet['dde'], phi, dphi, A,
        jet['dA'], psi, dpsi, chi, dchi)
    equal(coframe['Euler'], s.zeros(16, 1))
    matter = common.matter_euler(e, jet['de'], phi, A, psi, chi, dpsi, dchi, coframe['connection'])
    equal(matter['primal'], s.zeros(252, 1))
    equal(matter['dual'], s.zeros(1, 252))
    scalar_current, scalar_momenta = model.gauge.scalar_current(e, phi, dphi, A)
    matter_current = model.gauge.matter_current(e, psi, chi)
    gauge = model.gauge.euler(e, jet['de'].reshape(4, 16), A, jet['dA'], jet['ddA'], scalar_current, matter_current)
    equal(gauge['Euler'], s.zeros(4, 12))
    h, volume = common.scalar.metric_density(e)
    dh = model.constraints.metric_derivative(e, update['whole_coframe_rate'].reshape(4, 4))
    RA = [sum((A[mu, a]*model.constraints.rho[a] for a in range(12)), s.zeros(70)) for mu in range(4)]
    A_rate = jet['dA'][0, :].reshape(4, 12)
    dRA = [sum((A_rate[mu, a]*model.constraints.rho[a] for a in range(12)), s.zeros(70)) for mu in range(4)]
    U = [dphi[mu]+RA[mu]*phi for mu in range(4)]
    dU = [jet['scalar_acceleration']+dRA[0]*phi+RA[0]*dphi[0]]
    dU += [dRA[i+1]*phi+RA[i+1]*dphi[0] for i in range(3)]
    raw_Pi_dot = clean(sum((dh[0, mu]*U[mu]+h[0, mu]*dU[mu] for mu in range(4)), s.zeros(70, 1)))
    force = -sum((RA[mu]*scalar_momenta[mu] for mu in range(4)), s.zeros(70, 1))-2*volume*(phi-common.scalar.vacuum)
    Y_source = s.Matrix([real((volume*chi*((s.I if a >= 35 else 1)*common.yukawa_basis[a % 35])*psi)[0]) for a in range(70)])
    equal(raw_Pi_dot, update['scalar_momentum_rate'])
    equal(force+Y_source-raw_Pi_dot, s.zeros(70, 1))
    G_rate = s.zeros(12, 1)
    for i in range(3):
        G_rate -= model.gauge.ad(update['gauge_spatial_rate'][i, :]).T*fields['gauge_momentum'][i, :].T
        G_rate -= model.gauge.ad(A[i+1, :]).T*update['gauge_momentum_rate'][i, :].T
    for a in range(12):
        G_rate[a] += dot(update['scalar_momentum_rate'], model.constraints.rho[a]*phi)+dot(Pi, model.constraints.rho[a]*dphi[0])
        G_rate[a] += real((s.I*(update['canonical_dual_rate']*common.rho[a]*psi+
                                p*common.rho[a]*update['primal_rate']))[0])
    equal(G_rate, s.zeros(12, 1))
    equal(model.constraints.orbit.T*dphi[0], s.zeros(12, 1))
    equal(model.constraints.orbit.T*jet['scalar_acceleration'], s.zeros(12, 1))
    # Reconstruct the original auxiliary fields at this very same second jet.
    lorentz = common.coframe.lorentz
    Omega, dOmega = coframe['connection'], coframe['connection_derivative']
    R = lorentz.curvature_quadratic(Omega)
    for col, (mu, nu) in enumerate(PAIRS):
        for a in range(6):
            R[a, col] += dOmega[mu, 6*nu+a]-dOmega[nu, 6*mu+a]
    B_gravity, multiplier = lorentz.simplicity(e, clean(R))
    metric = s.diag(*PAIR_SIGN)
    equal((R-metric*J*B_gravity+metric*multiplier)*WEDGE, s.zeros(6))
    equal(metric*(B_gravity-J*wedge_matrix(e))*WEDGE, s.zeros(6))
    original_j = lorentz.matter_current(e, psi, chi)
    equal(lorentz.hessian(e)*Omega+lorentz.geometry_maps(e)[0]*jet['de']+original_j, s.zeros(24, 1))
    B_gauge = model.gauge.auxiliary(e, gauge['curvature'])
    equal(gauge['curvature']-model.gauge.sigma*model.gauge.constitutive(e)['Hodge']*B_gauge, s.zeros(6, 12))
    return {'original_coframe_Euler_rows': 16, 'original_scalar_Euler_rows': 70,
            'original_gauge_Euler_rows': 48, 'original_primal_and_independent_dual_complex_rows': [252, 252],
            'original_auxiliary_real_rows': 168, 'whole_original_real_field_Euler_rows': 1310,
            'all_original_Euler_rows_zero_at_generated_second_jet': True,
            'all10_coframe_primary_rates_zero': True, 'all12_Gauss_rates_zero': True,
            'scalar_constraint_first_and_second_rates_zero': True,
            'all4_temporal_coframe_constraint_rates_zero': True,
            'all12_time_connection_consistency_rows_zero': True,
            'gravity_B': encode(B_gravity), 'simplicity_multiplier': encode(multiplier),
            'gauge_B': encode(B_gauge), 'original_BF_boundary_flux': encode(coframe['boundary_flux']),
            'temporal_coframe_and_A0_second_derivatives': 'zero representatives only for reading original second-order equations, which do not consume these entries; their next constraint-preserving rates are not claimed'}


def verify_lower_left_control(model):
    e, phi, A = model.initial.e0, model.initial.vacuum, model.initial.A
    orbit = model.constraints.orbit*model.constraints.select
    Pi = orbit[:, 0]
    state = model.constraints.solve_time_connection(e, phi, Pi, [s.zeros(70, 1)]*3, A)
    live_A = A.copy()
    live_A[0, :] = state['time_connection'].T
    B = model.lower_left(e, phi, Pi, live_A)
    equal(B[:, 0], (orbit.T*orbit)[:, 0])
    equal(B[:, 1:], s.zeros(9, 3))
    assert B.todok()
    equal(model.constraints.potential_constraint(phi), s.zeros(12, 1))
    data = model.constraints.scalar_kinematics(e, phi, Pi, [s.zeros(70, 1)]*3, live_A)
    equal(model.constraints.potential_constraint(data['velocity']), s.zeros(12, 1))
    # The raw kinetic momentum differentiated in the four actual temporal
    # directions supplies the very same generally nonzero lower-left block.
    U = [data['covariant_time'], *data['spatial_covariant']]
    raw = s.zeros(9, 4)
    for a in range(4):
        delta = s.zeros(4); delta[a, 0] = 1
        dh = model.constraints.metric_derivative(e, delta)
        raw[:, a] = orbit.T*sum((dh[0, mu]*U[mu] for mu in range(4)), s.zeros(70, 1))/data['metric'][0, 0]
    equal(raw, B)
    return {'C_and_Cdot_zero': True, 'nonzero_lower_left': encode(B),
            'checked_against_raw_metric_derivative': True, 'general_block_diagonal_not_assumed': True}


def main():
    started = time.monotonic()
    model = SourceJointTemporalRates()
    family = verify_electric_family(model)
    print('PASS source electric momentum family and complete canonical clock branch', flush=True)
    fields = model.initial_fields(s.Rational(1, 4), s.Integer(1), s.Integer(1), s.Rational(1, 3), s.Rational(1, 5))
    update = model.joint_update(fields)
    assert update['time_coframe_rate'][0] == s.Rational(103923, 244235)
    assert update['time_connection_rate'][2] == -s.Rational(283824, 1221175)
    assert update['constraint_forcing'].todok() and update['gauge_spatial_rate'].todok()
    print('PASS full canonical flow generates nonzero coframe rate and actual joint13 preserving update', flush=True)
    jet = model.prolonged_jet(fields, update)
    original = verify_constraints_and_original_Euler(model, fields, update, jet)
    print('PASS all1310 original real Euler rows and actual primary/Gauss/temporal/scalar constraint rates', flush=True)
    control = verify_lower_left_control(model)
    print('PASS nonzero source lower-left block control from the original metric derivative', flush=True)
    paths = [HERE/name for name in ('source_joint_temporal_rates.py','source_coframe_initial_constraints.py',
        'source_coframe_initial_constraints.json','independent_source_coframe_initial_constraints.json',
        'source_coframe_constraints.py','source_coframe_constraints.json','independent_source_coframe_constraints.json',
        'source_common_hamiltonian.py','source_common_hamiltonian.json','source_constraint_preservation.py',
        'source_constraint_preservation.json','source_lorentz_contact.py','source_gauge_legendre.py','source_scalar_legendre.py')]
    result = {'root': ROOT_ID, 'source_sha256': model.common.scalar.exchange.vertices['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'scope': 'ACTUAL_COMPLETE_HOMOGENEOUS_CANONICAL_FLOW_JOINT13_TEMPORAL_UPDATE_AND_ORIGINAL1310_SECOND_JET',
        'source_family': family, 'actual_parameters': {'u':'1/4','alpha':'1','beta':'1','radial':'1/3','gauge_radial':'1/5'},
        'generated_clock_squared': str(fields['clock_squared']),
        'all_canonical_rates': {key: encode(value) for key, value in update.items() if isinstance(value, s.MatrixBase)},
        'actual_Hamiltonian_state_tangent_components': {key: str(value) for key, value in update['Hamiltonian_tangent_components'].items()},
        'actual_Hamiltonian_state_tangent': str(update['Hamiltonian_tangent']),
        'tangent_derivative_rule': 'compute every canonical rate once at the actual initial state, freeze that complete tangent, then differentiate D_z H(n,shift)[z_dot] in the temporal coframe column; never differentiate only the few initial-family parameters or recompute the flow at each n,shift',
        'joint_block': '[[J4,0],[B9x4,D9]] with upper rhs=-f4 and lower rhs from the original scalar Euler; B=-O_b^T sum_mu inv_e[mu,a]U_mu',
        'actual_time_coframe_rate': encode(update['time_coframe_rate']),
        'actual_time_gauge_connection_rate': encode(update['time_connection_rate']),
        'retained_source_accelerations': {key: encode(jet[key]) for key in ('coframe_acceleration','gauge_acceleration','scalar_acceleration')},
        'original_whole_Euler_and_constraint_consumers': original, 'lower_left_control': control,
        'actual_API': 'SourceJointTemporalRates.{initial_fields,canonical_rates,hamiltonian_tangent,lower_left,joint_update,prolonged_jet}',
        'spatial_scope': 'homogeneous source field and canonical jets; all spatial derivatives of these fields and their generated rates are zero, while non-Abelian curvatures and gauge covariant spatial derivatives remain',
        'all_time_Cauchy_or_general_inhomogeneous_evolution_claimed': False,
        'quantum_spectral_measure_or_lifetime_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_joint_temporal_rates.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')


if __name__ == '__main__':
    main()
