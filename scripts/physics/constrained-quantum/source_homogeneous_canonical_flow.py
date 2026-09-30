#!/usr/bin/env python3
"""The complete homogeneous canonical vector field of the original action.

The spatial coframe, every scalar/gauge coordinate, and the independent252
matter pair remain live variables. Temporal coframe and broken connection
rates consume their actual constraint Jacobians. Derivatives below are exact
matrix differentials of the common Hamiltonian, not derivatives of a chosen
initial-data family.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, decode
from source_coframe_constraints import SourceCoframeConstraints
from source_constraint_preservation import SourceConstraintPreservation
from source_coframe_legendre import pack, symmetric, rational
from source_lorentz_contact import clean, equal, encode, GAMMA, ETA, PAIRS, PAIR_SIGN, J, WEDGE, wedge_matrix
from source_common_hamiltonian import real
from source_scalar_legendre import dot

TIME = (0, 4, 8, 12)
SPATIAL = tuple(j for j in range(16) if j not in TIME)
KEYS = ('e', 'Pi_e', 'phi', 'Pi_phi', 'A', 'Pi_A', 'psi', 'p')


def contract(x, y):
    return s.expand(sum(a*b for a, b in zip(x, y)))


def zero_tangent(fields):
    return {name: s.zeros(*fields[name].shape) for name in KEYS}


class SourceHomogeneousCanonicalFlow:
    def __init__(self):
        self.full = SourceCoframeConstraints()
        self.common = self.full.common
        self.constraints = SourceConstraintPreservation()
        self.coframe, self.gauge = self.common.coframe, self.common.gauge
        self.spin = [s.kronecker_product(S, s.eye(63)) for S in self.coframe.lorentz.spin]
        source_e = s.Matrix(self.common.scalar.exchange.active['actual_background']['coframe']).applyfunc(s.sympify)
        source_e[:, 0] = s.zeros(4, 1)
        Z = s.Matrix.hstack(*[(T*source_e).reshape(16, 1) for T in self.coframe.lorentz.basis])
        self.primary_pivots = list(Z.T[:, SPATIAL].rref()[1])
        self.primary_free = [j for j in range(12) if j not in self.primary_pivots]
        P = self.constraints.projector
        self.scalar_frame = P[:, list(P.rref()[1])]
        self.scalar_reader = clean((self.scalar_frame.T*self.scalar_frame).inv()*self.scalar_frame.T)

    def coordinates(self, f):
        """Independent real1229 chart (complex matter pairs are kept paired)."""
        return {'spatial_e': f['e'][:, 1:],
                'free_Pi_e': f['Pi_e'].extract([SPATIAL[j] for j in self.primary_free], [0]),
                'scalar': clean(self.scalar_reader*(f['phi']-self.constraints.vacuum)),
                'Pi_phi': f['Pi_phi'], 'spatial_A': f['A'][1:, :], 'Pi_A': f['Pi_A'],
                'psi': f['psi'], 'p': f['p']}

    def lift_coordinates(self, z, time_column):
        """Actual source section; time_column is evaluated on the F4 branch."""
        e = s.Matrix.hstack(time_column, z['spatial_e'])
        phi = clean(self.constraints.vacuum+self.scalar_frame*z['scalar'])
        Pi_e = self.momentum_section(e, z['psi'], z['p'], z['free_Pi_e'])['momentum']
        A = s.zeros(4, 12); A[1:, :] = z['spatial_A']
        A[0, :] = self.constraints.solve_time_connection(e, phi, z['Pi_phi'],
            [s.zeros(70, 1)]*3, A)['time_connection'].T
        return {'e': e, 'Pi_e': Pi_e, 'phi': phi, 'Pi_phi': z['Pi_phi'], 'A': A,
                'Pi_A': z['Pi_A'], 'psi': z['psi'], 'p': z['p']}

    def project_rates(self, r):
        return {'spatial_e': r['e'][:, 1:],
                'free_Pi_e': r['Pi_e'].extract([SPATIAL[j] for j in self.primary_free], [0]),
                'scalar': clean(self.scalar_reader*r['phi']), 'Pi_phi': r['Pi_phi'],
                'spatial_A': r['A'][1:, :], 'Pi_A': r['Pi_A'], 'psi': r['psi'], 'p': r['p']}

    def reduced_vector_field(self, z, time_column):
        """The analytic ambient chart RHS, evaluated at its actual F4 root.

        Gauss=0 is an invariant initial level, not required to define this
        ambient RHS. The public update additionally enforces that level.
        """
        f = self.lift_coordinates(z, time_column)
        equal(self.temporal_chart(f)['constraints'], s.zeros(4, 1))
        return self.project_rates(self.canonical_rates(f)['rates'])

    def momentum_section(self, e, psi, p, free_momenta):
        """Analytic source chart solving all10 primary rows, including spin."""
        spatial = e.copy(); spatial[:, 0] = s.zeros(4, 1)
        Z = s.Matrix.hstack(*[(T*spatial).reshape(16, 1) for T in self.coframe.lorentz.basis])
        matrix = Z.T[:, SPATIAL]
        minor = matrix[:, self.primary_pivots]
        assert minor.det() != 0
        spin = s.Matrix([real((s.I*p*S*psi)[0]) for S in self.spin])
        dependent = clean(minor.inv()*(-spin-matrix[:, self.primary_free]*free_momenta))
        momentum = s.zeros(16, 1)
        for j, value in zip(self.primary_pivots, dependent):
            momentum[SPATIAL[j]] = value
        for j, value in zip(self.primary_free, free_momenta):
            momentum[SPATIAL[j]] = value
        return {'momentum': momentum, 'minor': minor,
                'dependent_coordinates': [SPATIAL[j] for j in self.primary_pivots],
                'free_coordinates': [SPATIAL[j] for j in self.primary_free]}

    def H(self, f):
        return self.common.hamiltonian(f['e'], f['Pi_e'], s.zeros(48, 1), f['phi'], f['Pi_phi'],
            [s.zeros(70, 1)]*3, f['A'], f['Pi_A'], s.zeros(3, 48), f['psi'], f['p'],
            [s.zeros(252, 1)]*3, s.zeros(10, 1))

    def primary(self, f):
        e = f['e'].copy(); e[:, 0] = s.zeros(4, 1)
        Z = s.Matrix.hstack(*[(T*e).reshape(16, 1) for T in self.coframe.lorentz.basis])
        charge = s.Matrix([real((s.I*f['p']*S*f['psi'])[0]) for S in self.spin])
        return clean(f['Pi_e'].extract(TIME, [0]).col_join(Z.T*f['Pi_e']+charge))

    def primary_rate(self, f, r):
        e, de = f['e'].copy(), r['e'].copy()
        e[:, 0] = s.zeros(4, 1); de[:, 0] = s.zeros(4, 1)
        Z = s.Matrix.hstack(*[(T*e).reshape(16, 1) for T in self.coframe.lorentz.basis])
        dZ = s.Matrix.hstack(*[(T*de).reshape(16, 1) for T in self.coframe.lorentz.basis])
        charge = s.Matrix([real((s.I*(r['p']*S*f['psi']+f['p']*S*r['psi']))[0]) for S in self.spin])
        return clean(r['Pi_e'].extract(TIME, [0]).col_join(dZ.T*f['Pi_e']+Z.T*r['Pi_e']+charge))

    def gauss(self, f):
        return self.common.gauss(f['e'], f['phi'], f['Pi_phi'], f['A'], f['Pi_A'],
                                [s.zeros(3, 12)]*3, f['psi'], f['p'])['total']

    def gauss_rate(self, f, r):
        pure = -sum((self.gauge.ad(r['A'][i+1, :]).T*f['Pi_A'][i, :].T+
                     self.gauge.ad(f['A'][i+1, :]).T*r['Pi_A'][i, :].T for i in range(3)), s.zeros(12, 1))
        scalar = s.Matrix([dot(r['Pi_phi'], R*f['phi'])+dot(f['Pi_phi'], R*r['phi']) for R in self.common.scalar.rho])
        matter = s.Matrix([real((s.I*(r['p']*R*f['psi']+f['p']*R*r['psi']))[0]) for R in self.common.rho])
        return clean(pure+scalar+matter)

    def scalar_rates(self, f, coframe_rate):
        data = self.common.matter_data(f['e'], f['phi'], f['A'])
        chi = self.common.canonical_dual(data, f['p'])
        return self.constraints.original_scalar_rates(f['e'], coframe_rate.reshape(16, 1),
            [s.zeros(16, 1)]*3, f['phi'], f['Pi_phi'], [s.zeros(70, 1)]*3,
            [s.zeros(70, 1)]*3, [[s.zeros(70, 1)]*3 for _ in range(3)],
            f['A'], s.zeros(3, 48), f['Pi_A'], f['psi'], chi)

    def gravity_force(self, e, de, psi, chi, Omega):
        model = self.coframe
        density = clean(psi.reshape(4, 63)*chi.reshape(4, 63).T)
        force = s.zeros(16, 1)
        for a in range(16):
            dadj = model.at(model.dadj[a], e)
            dV = [clean(s.sign(e.det())*sum((s.I*dadj[mu, b]*GAMMA[b]
                        for b in range(4)), s.zeros(4))*S)
                  for mu in range(4) for S in model.lorentz.spin]
            dj = s.Matrix([real(s.trace(V*density)) for V in dV])
            force[a] = s.expand(-3*e.adjugate()[a % 4, a//4]+
                (Omega.T*model.at(model.dH[a], e)*Omega)[0]/2+
                (Omega.T*model.at(model.dG[a], e)*de)[0]+(Omega.T*dj)[0])
        return clean(force)

    def canonical_rates(self, f):
        """All original Hamilton equations; temporal multipliers are still0."""
        e, Pi_e, phi, Pi, A, Pi_A, psi, p = [f[k] for k in KEYS]
        velocities = self.common.boson_velocities(e, Pi_e, s.zeros(48, 1), phi, Pi,
            [s.zeros(70, 1)]*3, A, Pi_A, s.zeros(3, 48), psi, p, s.zeros(10, 1))
        de = velocities['coframe'].col_join(s.zeros(48, 1))
        data = self.common.matter_data(e, phi, A)
        chi = self.common.canonical_dual(data, p)
        Omega = self.coframe.lorentz.eliminate(e, de, psi, chi)['connection']
        matter = self.common.matter_canonical_flow(e, de, phi, A, psi, p,
            [s.zeros(252, 1)]*3, [s.zeros(1, 252)]*3, Omega)
        psi_dot, p_dot = matter['primal_velocity'], matter['canonical_dual_velocity']
        scalar = self.scalar_rates(f, velocities['coframe'])
        dphi = [velocities['scalar'], *[s.zeros(70, 1)]*3]
        dA = s.zeros(4, 48); dA[0, 12:] = velocities['gauge_spatial'].reshape(1, 36)
        F = self.gauge.curvature(A, dA)
        P = self.gauge.curvature_momentum(e, F)
        equal(P[:3, :], Pi_A)
        js, _ = self.gauge.scalar_current(e, phi, dphi, A)
        jm = self.gauge.matter_current(e, psi, chi)
        Pi_A_dot = s.Matrix.vstack(*[sum((self.gauge.ad(A[mu, :]).T*
            self.gauge.ordered_pair(P, mu, i+1) for mu in range(4)), s.zeros(12, 1)).T for i in range(3)])
        Pi_A_dot += js[1:, :]+jm[1:, :]
        remaining = self.full.remaining_stress(e, phi, dphi, A, dA, psi,
                            [psi_dot, *[s.zeros(252, 1)]*3], chi)
        Pi_e_dot = clean(self.gravity_force(e, de, psi, chi, Omega)+sum(remaining.values(), s.zeros(16, 1)))
        A_dot = s.zeros(4, 12); A_dot[1:, :] = velocities['gauge_spatial']
        rates = {'e': velocities['coframe'].reshape(4, 4), 'Pi_e': Pi_e_dot,
                 'phi': velocities['scalar'], 'Pi_phi': scalar['scalar_momentum_rate'],
                 'A': clean(A_dot), 'Pi_A': clean(Pi_A_dot), 'psi': psi_dot, 'p': p_dot}
        return {'rates': rates, 'Omega': Omega, 'chi': chi, 'scalar_data': scalar,
                'curvature': F, 'curvature_momentum': P, 'scalar_current': js, 'matter_current': jm}

    def differential(self, f, r):
        """Exact full-coordinate differential of the common Hamiltonian.

        Matrix inverses use dX^-1=-X^-1(dX)X^-1.  Q=R B^-1 R^T is
        differentiated off the primary surface as well; no tangent direction
        or nonzero coframe velocity is silently discarded.
        """
        e, Pi_e, phi, Pi, A, Pi_A, psi, p = [f[k] for k in KEYS]
        de, dPi_e, dphi, dPi, dA, dPi_A, dpsi, dp = [r[k] for k in KEYS]
        model = self.coframe
        inverse, det = e.inv(), s.factor(e.det())
        ddet = s.cancel(det*s.trace(inverse*de)); orientation = s.sign(det)
        volume, dvolume = s.Abs(det), orientation*ddet
        dadj = model.at(sum((de[a]*model.dadj[a] for a in range(16)), s.zeros(4)), e)
        ports = model.lorentz.raw_matter_ports(e)
        data = self.common.matter_data(e, phi, A)
        dC = [clean(s.kronecker_product(orientation*sum((s.I*dadj[mu, a]*GAMMA[a]
                      for a in range(4)), s.zeros(4)), s.eye(63))) for mu in range(4)]
        dEinv = clean(-data['inverse_E']*dC[0]*data['inverse_E'])
        chi = self.common.canonical_dual(data, p)
        dchi = clean(s.I*dp*data['inverse_E']+s.I*p*dEinv)
        density = clean(psi.reshape(4, 63)*chi.reshape(4, 63).T)
        ddensity = clean(dpsi.reshape(4, 63)*chi.reshape(4, 63).T+psi.reshape(4, 63)*dchi.reshape(4, 63).T)
        dV = [clean(orientation*sum((s.I*dadj[mu, a]*GAMMA[a] for a in range(4)), s.zeros(4))*S)
              for mu in range(4) for S in model.lorentz.spin]
        j = s.Matrix([real(s.trace(V*density)) for V in ports['V']])
        dj = s.Matrix([real(s.trace(V*ddensity+dW*density)) for V, dW in zip(ports['V'], dV)])
        geo = model.geometry(e)
        Hinv, Gt, Q, R, Binv = [geo[k] for k in ('Lorentz_inverse', 'G', 'velocity_inverse', 'R', 'quotient_inverse')]
        Gt = Gt[:, :16]
        dH = model.at(sum((de[a]*model.dH[a] for a in range(16)), s.zeros(24)), e)
        dGt = model.at(sum((de[a]*model.dG[a][:, :16] for a in range(16)), s.zeros(24, 16)), e)
        dHinv = clean(-Hinv*dH*Hinv)
        dinverse = clean(-inverse*de*inverse)
        dRcolumns = []
        for a in range(6):
            delta = s.zeros(4); delta[:, 1:] = ETA*dinverse[1:, :].T*symmetric(s.eye(6)[:, a])/2
            dRcolumns.append(delta.reshape(16, 1))
        dR = s.Matrix.hstack(*dRcolumns)
        dh_spatial = clean(de[:, 1:].T*ETA*e[:, 1:]+e[:, 1:].T*ETA*de[:, 1:])
        dh6 = pack(dh_spatial)
        dBnum = sum((dh6[a]*model.metric_hessian.diff(model.h_variables[a]) for a in range(6)), s.zeros(6))
        dB = clean(dBnum/(4*det)-geo['B']*ddet/det)
        dBinv = clean(-Binv*dB*Binv)
        dQ = clean(dR*Binv*R.T+R*dBinv*R.T+R*Binv*dR.T)
        shift = clean(-Gt.T*Hinv*j)
        dshift = clean(-dGt.T*Hinv*j-Gt.T*dHinv*j-Gt.T*Hinv*dj)
        x, dx = Pi_e-shift, dPi_e-dshift
        hcf = contract(dx, Q*x)+contract(x, dQ*x)/2+3*ddet+contract(dj, Hinv*j)+contract(j, dHinv*j)/2
        h, _ = self.common.scalar.metric_density(e)
        dh = self.constraints.metric_derivative(e, de)
        RA = [sum((A[mu, a]*self.common.scalar.rho[a] for a in range(12)), s.zeros(70)) for mu in range(4)]
        dRA = [sum((dA[mu, a]*self.common.scalar.rho[a] for a in range(12)), s.zeros(70)) for mu in range(4)]
        U = [RA[i+1]*phi for i in range(3)]
        dU = [dRA[i+1]*phi+RA[i+1]*dphi for i in range(3)]
        b = sum((h[0, i+1]*U[i] for i in range(3)), s.zeros(70, 1))
        db = sum((dh[0, i+1]*U[i]+h[0, i+1]*dU[i] for i in range(3)), s.zeros(70, 1))
        z, dz = Pi-b, dPi-db
        hs = dot(z, dz)/h[0, 0]-dot(z, z)*dh[0, 0]/(2*h[0, 0]**2)
        hs -= dot(dPi, RA[0]*phi)+dot(Pi, dRA[0]*phi+RA[0]*dphi)
        hs -= sum(dh[i+1, k+1]*dot(U[i], U[k])/2+h[i+1, k+1]*dot(U[i], dU[k]) for i in range(3) for k in range(3))
        hs += dvolume*dot(phi-self.common.scalar.vacuum, phi-self.common.scalar.vacuum)+2*volume*dot(phi-self.common.scalar.vacuum, dphi)
        gd = self.gauge.constitutive(e)
        dkernel_num = self.gauge.at(sum((de[a]*self.gauge.dkernel[a] for a in range(16)), s.zeros(6)), e)
        dkernel = clean(dkernel_num/det-gd['kernel']*ddet/det)
        dP, dMixed, dMag = dkernel[:3, :3], dkernel[:3, 3:], dkernel[3:, 3:]
        B, _ = self.gauge.spatial_data(A, s.zeros(3, 48))
        dB = s.Matrix.vstack(*[(self.gauge.bracket(dA[mu, :], A[nu, :])+self.gauge.bracket(A[mu, :], dA[nu, :])).T
                              for mu, nu in ((2, 3), (3, 1), (1, 2))])
        X = Pi_A*self.gauge.gram_inverse-gd['mixed']*B
        dX = dPi_A*self.gauge.gram_inverse-dMixed*B-gd['mixed']*dB
        Pinv = gd['electric_inverse']; dPinv = clean(-Pinv*dP*Pinv)
        hg = contract(dX, Pinv*X*self.gauge.gram)+contract(X, dPinv*X*self.gauge.gram)/2
        hg -= contract(dB, gd['magnetic']*B*self.gauge.gram)+contract(B, dMag*B*self.gauge.gram)/2
        for i in range(3):
            hg += dot(dPi_A[i, :].T, self.gauge.bracket(A[i+1, :], A[0, :]))
            hg += dot(Pi_A[i, :].T, self.gauge.bracket(dA[i+1, :], A[0, :])+self.gauge.bracket(A[i+1, :], dA[0, :]))
        dY = sum(((dphi[j]+s.I*dphi[j+35])*Y for j, Y in enumerate(self.common.yukawa_basis)), s.zeros(252))
        dK = dvolume*data['Y']+volume*dY
        for mu in range(4):
            rho = sum((A[mu, a]*self.common.rho[a] for a in range(12)), s.zeros(252))
            drho = sum((dA[mu, a]*self.common.rho[a] for a in range(12)), s.zeros(252))
            dK += dC[mu]*rho+data['principal'][mu]*drho
        K = data['lower_without_Lorentz']
        hm = -real((dchi*K*psi+chi*dK*psi+chi*K*dpsi)[0])
        components = {name: s.factor(value) for name, value in (
            ('coframe_Lorentz_matter', hcf), ('scalar', hs), ('gauge', hg), ('matter_without_Lorentz', hm))}
        dvelocity_e = clean(dQ*x+Q*dx)
        dvelocity_phi = clean(dz/h[0, 0]-z*dh[0, 0]/h[0, 0]**2-dRA[0]*phi-RA[0]*dphi)
        dvelocity_A = clean(dPinv*X+Pinv*dX+s.Matrix.vstack(*[(
            self.gauge.bracket(dA[i+1, :], A[0, :])+
            self.gauge.bracket(A[i+1, :], dA[0, :])).T for i in range(3)]))
        return {'value': s.factor(sum(components.values())), 'components': components,
                'velocity_derivatives': {'coframe': dvelocity_e, 'scalar': dvelocity_phi, 'gauge': dvelocity_A},
                'dual_derivative': dchi, 'coframe_shift_derivative': dshift}

    def temporal_chart(self, f):
        """Original four fixed-canonical equations, with all other fields live."""
        n = s.Symbol('time_coframe0', positive=True)
        variables = [n, *s.symbols('time_coframe1:4', real=True)]
        varying = dict(f); varying['e'] = f['e'].copy(); varying['e'][:, 0] = s.Matrix(variables)
        H = self.H(varying)
        rows = s.Matrix([-s.diff(H['value'], x) for x in variables])
        at = dict(zip(variables, f['e'][:, 0]))
        J = clean(rows.jacobian(variables).subs(at))
        return {'fields': varying, 'variables': variables, 'at': at, 'Hamiltonian': H,
                'constraints': clean(rows.subs(at)), 'Jacobian': J}

    def time_column_Newton_step(self, f, guess):
        """Exact iteration of the original F4; its local limit is the IFT branch.

        A finite iterate is an approximation unless its returned residual is0.
        The initial iterate is the actual source time column in the source
        neighborhood, not an independently chosen clock or constraint value.
        """
        current = dict(f); current['e'] = f['e'].copy(); current['e'][:, 0] = guess
        data = self.temporal_chart(current)
        assert data['Jacobian'].det() != 0
        return {'next': clean(guess-data['Jacobian'].inv()*data['constraints']),
                'residual': data['constraints'], 'Jacobian': data['Jacobian']}

    def update(self, f):
        """Complete source-generated point RHS on the nondegenerate branch."""
        equal(self.primary(f), s.zeros(10, 1))
        equal(self.gauss(f), s.zeros(12, 1))
        equal(self.constraints.potential_constraint(f['phi']), s.zeros(12, 1))
        A0 = self.constraints.solve_time_connection(f['e'], f['phi'], f['Pi_phi'],
            [s.zeros(70, 1)]*3, f['A'])['time_connection']
        equal(f['A'][0, :].T, A0)
        current = self.canonical_rates(f); r = current['rates']
        chart = self.temporal_chart(f)
        equal(chart['constraints'], s.zeros(4, 1))
        equal(r['Pi_e'].extract(TIME, [0]), chart['constraints'])
        assert chart['Jacobian'].det() != 0
        tangent = self.differential(chart['fields'], r)
        force = clean(s.Matrix([-s.diff(tangent['value'], x).subs(chart['at']) for x in chart['variables']]))
        etime = clean(-chart['Jacobian'].inv()*force)
        r = dict(r); r['e'] = r['e'].copy(); r['e'][:, 0] = etime
        scalar = self.scalar_rates(f, r['e'])
        A0rate = self.constraints.solve_time_connection_derivative(f['phi'], r['phi'],
            scalar['time_connection_rhs_rate'], A0)['time_connection_rate']
        r['A'] = r['A'].copy(); r['A'][0, :] = A0rate.T
        equal(self.primary_rate(f, r), s.zeros(10, 1))
        equal(self.gauss_rate(f, r), self.constraints.gauss_rate(f['e'], f['phi'], A0, self.gauss(f)))
        equal(self.constraints.potential_constraint(r['phi']), s.zeros(12, 1))
        equal(chart['Jacobian']*etime+force, s.zeros(4, 1))
        D = self.constraints.consistency_matrix(f['phi'])
        equal(D*A0rate+self.constraints.consistency_matrix(r['phi'])*A0-scalar['time_connection_rhs_rate'], s.zeros(12, 1))
        return {**current, 'rates': r, 'temporal_Jacobian': chart['Jacobian'], 'temporal_forcing': force,
                'time_coframe_rate': etime, 'time_connection_rate': A0rate,
                'Hamiltonian_tangent': tangent, 'scalar_data': scalar}

    def prolonged_jet(self, f, update):
        """Differentiate every inverse Legendre map along the actual full RHS."""
        r = update['rates']
        derivative = self.differential(f, r)
        assert s.simplify(derivative['value']) == 0
        de = r['e'].reshape(16, 1).col_join(s.zeros(48, 1))
        dde = s.zeros(4, 64)
        dde[0, :16] = derivative['velocity_derivatives']['coframe'].T
        dA = s.zeros(4, 48); dA[0, :] = r['A'].reshape(1, 48)
        ddA = [s.zeros(4, 48) for _ in range(4)]
        ddA[0][0, 12:] = derivative['velocity_derivatives']['gauge'].reshape(1, 36)
        return {'de': de, 'dde': dde, 'dA': dA, 'ddA': ddA,
                'dphi': [r['phi'], *[s.zeros(70, 1)]*3],
                'dpsi': [r['psi'], *[s.zeros(252, 1)]*3],
                'dchi': [derivative['dual_derivative'], *[s.zeros(1, 252)]*3],
                'accelerations': derivative['velocity_derivatives'],
                'coframe_shift_derivative': derivative['coframe_shift_derivative']}

    def original_Euler_consumer(self, f, update, jet):
        e, Pi_e, phi, Pi, A, Pi_A, psi, p = [f[k] for k in KEYS]
        chi, r = update['chi'], update['rates']
        measured = self.common.momenta(e, jet['de'], phi, jet['dphi'], A, jet['dA'], psi, chi)
        for name, expected in [('coframe', Pi_e), ('scalar', Pi), ('gauge', Pi_A), ('matter', p)]:
            equal(measured[name], expected)
        gravity = self.full.euler(e, jet['de'], jet['dde'], phi, jet['dphi'], A, jet['dA'],
                                  psi, jet['dpsi'], chi, jet['dchi'])
        equal(gravity['Euler'], s.zeros(16, 1))
        equal(gravity['connection'], update['Omega'])
        matter = self.common.matter_euler(e, jet['de'], phi, A, psi, chi,
            jet['dpsi'], jet['dchi'], gravity['connection'])
        equal(matter['primal'], s.zeros(252, 1)); equal(matter['dual'], s.zeros(1, 252))
        correction = self.common.fixed_p_coframe_correction(e, chi, matter['primal'])
        equal(correction, s.zeros(16, 1))
        js, Pi_mu = self.gauge.scalar_current(e, phi, jet['dphi'], A)
        jm = self.gauge.matter_current(e, psi, chi)
        gauge = self.gauge.euler(e, jet['de'].reshape(4, 16), A, jet['dA'], jet['ddA'], js, jm)
        equal(gauge['Euler'], s.zeros(4, 12))
        h, volume = self.common.scalar.metric_density(e)
        dh = self.constraints.metric_derivative(e, r['e'])
        RA = [sum((A[mu, a]*self.common.scalar.rho[a] for a in range(12)), s.zeros(70)) for mu in range(4)]
        dRA = [sum((r['A'][mu, a]*self.common.scalar.rho[a] for a in range(12)), s.zeros(70)) for mu in range(4)]
        U = [jet['dphi'][mu]+RA[mu]*phi for mu in range(4)]
        dU = [jet['accelerations']['scalar']+dRA[0]*phi+RA[0]*r['phi']]
        dU += [dRA[i+1]*phi+RA[i+1]*r['phi'] for i in range(3)]
        raw_Pi_dot = clean(sum((dh[0, mu]*U[mu]+h[0, mu]*dU[mu] for mu in range(4)), s.zeros(70, 1)))
        force = -sum((RA[mu]*Pi_mu[mu] for mu in range(4)), s.zeros(70, 1))-2*volume*(phi-self.common.scalar.vacuum)
        jY = s.Matrix([real((volume*chi*((s.I if a >= 35 else 1)*self.common.yukawa_basis[a % 35])*psi)[0]) for a in range(70)])
        equal(raw_Pi_dot, r['Pi_phi']); equal(force+jY-raw_Pi_dot, s.zeros(70, 1))
        equal(self.constraints.orbit.T*jet['accelerations']['scalar'], s.zeros(12, 1))
        lorentz = self.coframe.lorentz
        Omega, dOmega = gravity['connection'], gravity['connection_derivative']
        R = lorentz.curvature_quadratic(Omega)
        for col, (mu, nu) in enumerate(PAIRS):
            for a in range(6):
                R[a, col] += dOmega[mu, 6*nu+a]-dOmega[nu, 6*mu+a]
        B, multiplier = lorentz.simplicity(e, clean(R))
        metric = s.diag(*PAIR_SIGN)
        equal((R-metric*J*B+metric*multiplier)*WEDGE, s.zeros(6))
        equal(metric*(B-J*wedge_matrix(e))*WEDGE, s.zeros(6))
        equal(lorentz.hessian(e)*Omega+lorentz.geometry_maps(e)[0]*jet['de']+
              lorentz.matter_current(e, psi, chi), s.zeros(24, 1))
        Bg = self.gauge.auxiliary(e, gauge['curvature'])
        equal(gauge['curvature']-self.gauge.sigma*self.gauge.constitutive(e)['Hodge']*Bg, s.zeros(6, 12))
        return {'all1310_original_real_Euler_rows_zero': True,
                'canonical_momenta_all122_and_complex252_recovered': True,
                'fixed_p_chain_all16_rows_paid_by_actual_matter_flow': True,
                'nonzero_spatial_coframe_acceleration': encode(jet['accelerations']['coframe']),
                'original_BF_four_fluxes': encode(gravity['boundary_flux']),
                'original_auxiliary_fields': {'gravity_B': encode(B), 'simplicity_multiplier': encode(multiplier), 'gauge_B': encode(Bg)}}


def actual_nonlinear_datum(model):
    """A point outside the earlier scalar/matter/radial initial-data family."""
    active = model.common.scalar.exchange.active['actual_background']
    e0 = s.Matrix(active['coframe']).applyfunc(s.sympify)
    A = s.Matrix(active['gauge_connection']).applyfunc(s.sympify)
    occupied = json.loads((BASE/'occupied-response/receipt.json').read_text())
    psi0 = decode(occupied['occupied_frame'])*s.Matrix(active['primal_H']).applyfunc(s.sympify)
    psi, chi0 = psi0.copy(), s.sqrt(2)*psi0.T
    psi[135] += 1; chi0[126] += 1
    q = model.constraints.projector*s.eye(70)[:, 23]
    phi = clean(model.constraints.vacuum+q/4)
    p = clean(-s.I*chi0*model.common.matter_data(e0, phi, A)['E'])
    n = s.Symbol('initial_n', positive=True)
    e = s.diag(n, s.Rational(11, 10), 1, 1)
    # D_h^T q is a genuine metric cotangent, hence annihilates all six
    # Lorentz directions. It generates a nonzero physical metric velocity.
    Pi_e = clean(model.coframe.at(model.coframe.D, e).T*s.Matrix([s.Rational(1, 14)]*3+[0]*3))
    fields = {'e': e, 'Pi_e': Pi_e, 'phi': phi, 'Pi_phi': clean(q/12), 'A': A,
              'Pi_A': clean(A[1:, :]*model.gauge.gram/5), 'psi': psi, 'p': p}
    H = model.H(fields)
    value = s.factor(H['value'])
    numerator = s.Poly(s.cancel(n*value), n)
    assert numerator.degree() == 2 and numerator.coeff_monomial(n) == 0
    a, b = numerator.coeff_monomial(n**2), numerator.coeff_monomial(1)
    assert a.is_positive is True and b.is_positive is True
    clock_squared = s.cancel(b/a)
    fields['e'] = e.subs(n, s.sqrt(clock_squared))
    fields['Pi_e'] = Pi_e.subs(n, s.sqrt(clock_squared))
    equal(model.primary(fields), s.zeros(10, 1))
    equal(model.gauss(fields), s.zeros(12, 1))
    equal(model.constraints.potential_constraint(phi), s.zeros(12, 1))
    return fields, {'lapse_Hamiltonian': str(value), 'lapse_coefficient': str(a),
                    'inverse_lapse_coefficient': str(b), 'clock_squared': str(clock_squared),
                    'components': {k: str(s.factor(v)) for k, v in H['components'].items()},
                    'spatial_coframe_changed': True, 'physical_metric_momentum_nonzero': True}


def direct_H_differential(model, fields):
    """Differentiate the original H on an actual off-primary field curve."""
    base = {k: v.copy() for k, v in fields.items()}
    base['e'] = s.diag(2, 1, 1, 1)
    base['Pi_e'][1] += s.Rational(1, 17)
    direction = zero_tangent(base)
    direction['e'] = base['e'].copy()
    direction['Pi_e'][2] = s.Rational(2, 19)
    direction['phi'][12] = s.Rational(1, 7)
    direction['Pi_phi'][47] = s.Rational(1, 11)
    direction['A'][0, 2] = s.Rational(1, 13)
    direction['A'][2, 7] = s.Rational(1, 23)
    direction['Pi_A'][1, 6] = s.Rational(1, 29)
    direction['psi'][142] = s.I/31
    direction['p'][0, 135] = s.Rational(1, 37)
    assert model.primary(base).todok()
    epsilon = s.Symbol('positive_curve_parameter', positive=True)
    derivative = model.differential(base, direction)
    terms = {}
    for label, group in [('coframe', {'e'}), ('other_canonical_coordinates', set(KEYS)-{'e'})]:
        varying = {k: base[k]+(epsilon*direction[k] if k in group else s.zeros(*base[k].shape)) for k in KEYS}
        direct = model.H(varying)
        terms[label] = {name: s.simplify(s.diff(value, epsilon).subs(epsilon, 0)) for name, value in direct['components'].items()}
        print('direct original H curve', label, flush=True)
    for name, value in derivative['components'].items():
        assert s.simplify(sum(term[name] for term in terms.values())-value) == 0, name
    return {'off_primary_curve': True, 'all8_canonical_field_groups_varied': True,
            'all4_source_H_components_directly_differentiated': True,
            'differential_components': {k: str(v) for k, v in derivative['components'].items()}}


def source_analytic_chart(model, fixture):
    """Construct the finite source chart used by the local analytic ODE."""
    active = model.common.scalar.exchange.active['actual_background']
    e = s.Matrix(active['coframe']).applyfunc(s.sympify)
    A = s.Matrix(active['gauge_connection']).applyfunc(s.sympify)
    occupied = json.loads((BASE/'occupied-response/receipt.json').read_text())
    psi = decode(occupied['occupied_frame'])*s.Matrix(active['primal_H']).applyfunc(s.sympify)
    phi, chi = model.constraints.vacuum, s.sqrt(2)*psi.T
    original = model.common.momenta(e, s.zeros(64, 1), phi, [s.zeros(70, 1)]*4,
        A, s.zeros(4, 48), psi, chi)
    source = {'e': e, 'Pi_e': original['coframe'], 'phi': phi, 'Pi_phi': original['scalar'],
              'A': A, 'Pi_A': original['gauge'], 'psi': psi, 'p': original['matter']}
    chart = model.temporal_chart(source)
    equal(chart['constraints'], s.zeros(4, 1))
    equal(chart['Jacobian'], s.diag(-s.sqrt(30), *[-2*s.sqrt(30)/3]*3))
    assert s.simplify(chart['Jacobian'].det()) == s.Rational(800, 3)
    D9 = model.constraints.select.T*model.constraints.consistency_matrix(phi)*model.constraints.select
    assert D9.det() != 0
    source_primary = model.momentum_section(e, psi, source['p'], s.zeros(6, 1))
    equal(source_primary['momentum'], original['coframe'])
    free_coordinates = source_primary['free_coordinates']
    recovered = model.momentum_section(fixture['e'], fixture['psi'], fixture['p'], fixture['Pi_e'].extract(free_coordinates, [0]))
    equal(recovered['momentum'], fixture['Pi_e'])
    P = model.constraints.projector
    frame, reader = model.scalar_frame, model.scalar_reader
    equal(reader*frame, s.eye(61)); equal(frame*reader, P)
    equal(model.constraints.orbit.T*frame, s.zeros(12, 61))
    equal(P*phi, phi)
    lifted = model.lift_coordinates(model.coordinates(fixture), fixture['e'][:, 0])
    for name in KEYS:
        equal(lifted[name], fixture[name])
    # The original nonlinear algebraic step fixes the actual source exactly.
    step = model.time_column_Newton_step(source, e[:, 0])
    equal(step['next'], e[:, 0]); equal(step['residual'], s.zeros(4, 1))
    return {'source_four_time_Jacobian': encode(chart['Jacobian']),
            'source_four_time_Jacobian_determinant': str(s.factor(chart['Jacobian'].det())),
            'source_nine_connection_matrix': encode(D9),
            'source_nine_connection_determinant': str(s.factor(D9.det())),
            'primary_six_solved_coordinates': source_primary['dependent_coordinates'],
            'primary_six_free_coordinates': free_coordinates,
            'source_primary_minor': encode(source_primary['minor']),
            'scalar61_frame': encode(frame), 'scalar61_reader': encode(reader),
            'actual_source_fixed_by_F4_Newton_step': True,
            'real_chart_coordinate_count_before_Gauss_level': 1229,
            'coordinates': '12 spatial coframe +6 free coframe momenta +61 scalar +70 scalar momenta +36 spatial connection +36 connection momenta +real/imag(252 psi,252 p)',
            'analytic_domain': 'The source-connected local chart has det(e)>0, det(spatial metric)!=0, original gauge g00!=0, det(primary six-minor)!=0, det(D9)!=0, det(J4)!=0. These are open source inequalities; the branch is the local analytic IFT branch through the actual source, not every point of that open set.',
            'field_reconstruction': [
                'Solve the six homogeneous Lorentz primary rows by momentum_section, with Pi_e[:,0]=0; the source minor is invertible. This section includes the complete Re(i p S psi) spin charge and is independent of e[:,0].',
                'Set phi=vacuum+scalar61_frame*q. The original C9 vanishes identically, with no retained scalar direction omitted.',
                'Generate e[:,0]=T(z) from the original F4=-partial_eTime H=0. The source J4 determinant800/3 and real analyticity give a unique local analytic T. The public exact Newton step, seeded with the actual source time column, converges to this branch for nearby inputs; no finite approximation is asserted to solve F4.',
                'Generate A0=Q(D9)^-1 Q^T r from the original scalar velocity and set the three source stabilizer representatives0. All six Lorentz velocity representatives are0. The A0 coefficient of H is -Gauss and Gauss is independent of e, so the F4 solve has no circular A0 dependence.'],
            'constraint_tangency_proof': [
                'The common Legendre identities reconstruct Pi_e=M v+b on the primary chart. The complete canonical Spin moment map is C_full=C_L+Z_time^T Pi_time. Original Spin invariance and the generated full matter equations give dot(C_full)=0. On Pi_time=0 with dot(Pi_time)=F4, this gives dot(C_L)=-Z_time^T F4. Consequently F4=0 and the invertible six-momentum minor force the differentiated primary reconstruction to agree with all six original dependent momentum forces.',
                'The original scalar equation yields dot(C)=r-D A0=0 identically under the generated broken connection. Therefore dot(phi) lies in the same fixed61-dimensional chart.',
                'The original gauge Noether identity yields dot(Gauss)=ad(A0)^T Gauss-2 det(e) C. With C=0, Gauss=0 is an invariant level by uniqueness of this finite linear homogeneous equation. No regular-value premise on the Gauss level is required.',
                'Differentiate the actual analytic branch F4(T(z),z)=0: dot(eTime)=-J4^-1 D_zF4[z_dot]. The complete eight-field Hamiltonian differential supplies this forcing, including nonzero metric velocity and the full fixed-p inverse-E chain.',
                'Differentiate D(phi)A0=r using the original scalar momentum force and the already generated whole coframe rate. The same D9 inverse generates dot(A0); it is exactly the derivative of the algebraic A0 reconstruction.'],
            'local_existence_uniqueness_proof': [
                'Split the independent complex psi and p into real and imaginary parts. On the fixed positive-orientation chart every original matrix entry and every displayed inverse is real analytic; the IFT branch is real analytic as well. The selected components of canonical_rates consequently define an actual analytic vector field in1229 real coordinates.',
                'The finite-dimensional local analytic ODE theorem gives an analytic integral curve through every point of the ambient1229-coordinate chart. Reconstruct the dependent primary momenta, phi, eTime and A0 by the preceding source maps. For initial data satisfying the original Gauss=0 equations, linear Gauss preservation keeps the curve on that level; its lifted derivative then equals every component of update and solves all original Euler equations. Ambient non-Gauss initial data are not claimed to solve the original A0 Euler equations.',
                'Any other homogeneous original-action solution with these fixed Lorentz/stabilizer representatives and the same initial data projects to the same analytic ODE, so local uniqueness holds. Auxiliary fields are the already generated algebraic Lorentz/B/simplicity solutions and retain their original boundary flux.',
                'The existence interval is local and stops at the chart boundary; this is homogeneous evolution of the untruncated original action. Spatially varying PDE well-posedness and interacting quantum spectral measure remain separate consumers.'],
            'local_homogeneous_Cauchy': 'ANALYTIC_EXISTENCE_AND_UNIQUENESS_ON_THE_SOURCE_CONSTRAINT_BRANCH',
            'formal_Lean_time_path_installation_claimed': False}


def main():
    started = time.monotonic()
    model = SourceHomogeneousCanonicalFlow()
    print('general source constructors', round(time.monotonic()-started, 3), flush=True)
    fields, family_readout = actual_nonlinear_datum(model)
    print('outside-family constrained datum', round(time.monotonic()-started, 3), flush=True)
    result = model.update(fields)
    print('complete homogeneous point vector field', round(time.monotonic()-started, 3), flush=True)
    r = result['rates']
    assert r['e'][:, 1:].todok()
    assert r['Pi_e'].todok()
    assert r['phi'].todok() and r['Pi_phi'].todok()
    assert r['A'][1:, :].todok() and r['Pi_A'].todok()
    assert r['psi'].todok() and r['p'].todok()
    assert result['time_coframe_rate'].todok() and result['time_connection_rate'].todok()
    print('all sectors and both temporal updates nonzero', flush=True)
    jet = model.prolonged_jet(fields, result)
    original = model.original_Euler_consumer(fields, result, jet)
    print('all1310 original Euler rows', round(time.monotonic()-started, 3), flush=True)
    direct_derivative = direct_H_differential(model, fields)
    print('actual off-primary full H differential', round(time.monotonic()-started, 3), flush=True)
    analytic_chart = source_analytic_chart(model, fields)
    print('source primary/IFT/connection analytic chart', round(time.monotonic()-started, 3), flush=True)
    omitted_G = clean(s.Matrix([(result['Omega'].T*model.coframe.at(model.coframe.dG[a], fields['e'])*jet['de'])[0]
                                for a in range(16)]))
    assert omitted_G.todok()
    data = model.common.matter_data(fields['e'], fields['phi'], fields['A'])
    omitted_E = clean(jet['dchi'][0]-s.I*r['p']*data['inverse_E'])
    assert omitted_E.todok()
    geo = model.coframe.geometry(fields['e'])
    omitted_dQ = clean(jet['accelerations']['coframe']-geo['velocity_inverse']*(r['Pi_e']-jet['coframe_shift_derivative']))
    assert omitted_dQ.todok()
    body = {'root': ROOT_ID,
            'source_sha256': model.common.scalar.exchange.vertices['source_sha256'],
            'verdict': 'SOURCE_GENERAL_HOMOGENEOUS_CANONICAL_FLOW_AND_LOCAL_ANALYTIC_CAUCHY',
            'datum': {k: encode(v) for k, v in fields.items()},
            'datum_construction': family_readout,
            'complete_rates': {k: encode(v) for k, v in r.items()},
            'source_Lorentz_connection': encode(result['Omega']),
            'temporal_Jacobian': encode(result['temporal_Jacobian']),
            'temporal_Jacobian_determinant': str(s.factor(result['temporal_Jacobian'].det())),
            'temporal_forcing': encode(result['temporal_forcing']),
            'all10_primary_rates_zero': True, 'all12_Gauss_rates_zero': True,
            'all9_potential_constraint_rates_zero': True,
            'all4_temporal_coframe_constraint_rates_zero': True,
            'all9_time_connection_consistency_rates_zero': True,
            'original_Euler_consumer': original,
            'whole_H_differential_consumer': direct_derivative,
            'analytic_Cauchy_source_chart': analytic_chart,
            'nonzero_coframe_velocity_controls': {'omitted_G_derivative_force': encode(omitted_G),
                'omitted_inverse_E_derivative_dual_rate': encode(omitted_E),
                'omitted_quotient_inverse_derivative_acceleration': encode(omitted_dQ)},
            'spatially_inhomogeneous_PDE_Cauchy_claimed': False,
            'interacting_quantum_spectral_measure_generated': False,
            'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
            'elapsed_seconds': round(time.monotonic()-started, 3)}
    bindings = ['source_homogeneous_canonical_flow.py', 'source_common_hamiltonian.py',
        'source_coframe_constraints.py', 'source_constraint_preservation.py', 'source_coframe_legendre.py',
        'source_gauge_legendre.py', 'source_lorentz_contact.py', 'source_scalar_legendre.py',
        'source_temporal_coframe_flux.py', 'source_temporal_coframe_flux.json',
        'independent_source_common_hamiltonian.json', 'independent_source_coframe_constraints.json',
        'independent_source_constraint_preservation.json', 'independent_source_coframe_initial_constraints.json',
        'independent_source_temporal_coframe_flux.json']
    body['input_sha256'] = {str((HERE/name).relative_to(ROOT)): hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                            for name in bindings}
    for name in bindings:
        if name.startswith('independent_'):
            receipt = json.loads((HERE/name).read_text())
            for path, expected in receipt.get('input_sha256', {}).items():
                assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == expected, path
    (HERE/'source_homogeneous_canonical_flow.json').write_text(json.dumps(body, ensure_ascii=False, indent=2)+'\n')
    print(body['verdict'], body['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
