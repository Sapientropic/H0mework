#!/usr/bin/env python3
"""Original18 spatial Lorentz time equations and their source-generated inverse.

Twelve prolonged spatial torsion equations and six metric coframe Euler
equations share the original inverse metric kinetic form. The time derivative
of spatial torsion cancels the second spatial derivatives of the temporal
coframe before the equations are assembled.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, decode
from source_common_hamiltonian import SourceCommonHamiltonian, real
from source_lorentz_contact import clean, equal, encode, PAIRS, ETA, GAMMA, wedge_matrix
from source_coframe_legendre import rational
from source_spatial_time_coframe import SourceSpatialTimeCoframe


SPATIAL_TORSION = [6*a+p for a in range(4) for p in range(3, 6)]


def derivative(matrix, variables, direction):
    return clean(sum((value*matrix.diff(variable) for variable, value in zip(variables, direction)),
                     s.zeros(*matrix.shape)))


class SourceSpatialLorentzTime:
    def __init__(self):
        self.common = SourceCommonHamiltonian()
        self.coframe = self.common.coframe
        self.lorentz = self.coframe.lorentz
        _, self.T, self.curl = self.lorentz.geometry_maps(self.coframe.e)
        _, self.flat_T, _ = self.lorentz.geometry_maps(s.eye(4))
        self.flat_T_inverse = self.flat_T.inv()
        self.C = self.lorentz.curvature_coefficient(self.coframe.e)
        self.dC = [self.C.diff(x) for x in self.coframe.e]
        self.time4 = SourceSpatialTimeCoframe()

    def geometry(self, e):
        data = self.coframe.geometry(e)
        if data['det_h'] == 0:
            raise ValueError('The original six metric velocities require det(h) != 0.')
        T = self.coframe.at(self.T, e)
        XinvT = wedge_matrix(e.inv().T)
        full_inverse = clean(s.kronecker_product(e.T, s.eye(6))*self.flat_T_inverse*
                             s.kronecker_product(s.eye(4), XinvT))
        Tsp = T.extract(SPATIAL_TORSION, range(6, 24))
        right = full_inverse.extract(range(6, 24), SPATIAL_TORSION)
        Gt, R = data['G'][:, :16], data['R']
        kernel = clean((-data['Lorentz_inverse']*Gt*R)[6:, :])
        metric_Euler = clean(-R.T*Gt[6:, :].T)
        inverse = clean(right.row_join(s.zeros(18, 6))+
                        kernel*data['quotient_inverse']*(metric_Euler*right).row_join(-s.eye(6)))
        return {**data, 'torsion': T, 'torsion_inverse': full_inverse,
                'spatial_torsion': Tsp, 'torsion_right_inverse': right,
                'torsion_kernel': kernel, 'metric_Euler_time_rows': metric_Euler,
                'time_matrix': clean(Tsp.col_join(metric_Euler)), 'time_inverse': inverse}

    def solve_principal(self, e, torsion_rhs, metric_Euler_rhs):
        data = self.geometry(e)
        initial = data['torsion_right_inverse']*torsion_rhs
        value = clean(initial-data['torsion_kernel']*data['quotient_inverse']*
                      (metric_Euler_rhs-data['metric_Euler_time_rows']*initial))
        equal(data['time_matrix']*value, torsion_rhs.col_join(metric_Euler_rhs))
        return value

    def current(self, e, psi, chi, de=None, dpsi=None, dchi=None):
        ports = self.lorentz.raw_matter_ports(e)
        density = psi.reshape(4, 63)*chi.reshape(4, 63).T
        j = s.Matrix([real(s.trace(V*density)) for V in ports['V']])
        if de is None:
            return clean(j)
        dadj = self.coframe.at(derivative(self.coframe.adj, self.coframe.e, list(de)), e)
        dV = [s.sign(e.det())*s.I*sum((dadj[mu, b]*GAMMA[b] for b in range(4)), s.zeros(4))*S
              for mu in range(4) for S in self.lorentz.spin]
        ddensity = dpsi.reshape(4, 63)*chi.reshape(4, 63).T+psi.reshape(4, 63)*dchi.reshape(4, 63).T
        return clean(s.Matrix([real(s.trace(change*density+V*ddensity))
                               for V, change in zip(ports['V'], dV)]))

    def torsion_source(self, e, psi, chi, de=None, dpsi=None, dchi=None):
        data = self.geometry(e)
        j = self.current(e, psi, chi)
        HI = data['Lorentz_inverse']
        if de is None:
            return clean(-data['torsion']*HI*j)
        dT = self.coframe.at(derivative(self.T, self.coframe.e, list(de)), e)
        dH = self.coframe.at(derivative(self.coframe.H, self.coframe.e, list(de)), e)
        dj = self.current(e, psi, chi, de, dpsi, dchi)
        return clean(-dT*HI*j+data['torsion']*HI*dH*HI*j-data['torsion']*HI*dj)

    def omega_matrices(self, Omega):
        return [clean(sum((Omega[6*mu+a]*self.lorentz.basis[a] for a in range(6)), s.zeros(4)))
                for mu in range(4)]

    @staticmethod
    def torsion_column(source, mu, nu):
        if (mu, nu) in PAIRS:
            col, sign = PAIRS.index((mu, nu)), 1
        else:
            col, sign = PAIRS.index((nu, mu)), -1
        return s.Matrix([sign*source[6*a+col] for a in range(4)])

    def spatial_coframe_velocity(self, e, spatial_e, Omega, psi, chi):
        O = self.omega_matrices(Omega)
        S = self.torsion_source(e, psi, chi)
        v = s.zeros(4)
        for i in range(1, 4):
            v[:, i] = spatial_e[i-1][:, 0]-O[0]*e[:, i]+O[i]*e[:, 0]+self.torsion_column(S, 0, i)
        return clean(v)

    def matter_flow(self, e, de, phi, A, Omega, psi, chi, spatial_psi, spatial_chi):
        data = self.common.matter_data(e, phi, A)
        lower = clean(data['lower_without_Lorentz']+
                      sum((Omega[a]*V for a, V in enumerate(data['Lorentz_ports'])), s.zeros(252)))
        psi_dot = clean(-data['inverse_E']*(lower*psi+
            sum((data['principal'][i+1]*spatial_psi[i] for i in range(3)), s.zeros(252, 1))))
        divergence = s.zeros(252)
        for mu in range(4):
            dadj = self.coframe.at(derivative(self.coframe.adj, self.coframe.e, list(de[mu])), e)
            dE = s.sign(e.det())*s.I*sum((dadj[mu, b]*GAMMA[b] for b in range(4)), s.zeros(4))
            divergence += s.kronecker_product(dE, s.eye(63))
        chi_dot = clean((chi*lower-sum((spatial_chi[i]*data['principal'][i+1] for i in range(3)),
                                      s.zeros(1, 252))-chi*divergence)*data['inverse_E'])
        original = self.common.matter_euler(e, s.Matrix.vstack(*[d.reshape(16, 1) for d in de]),
            phi, A, psi, chi, [psi_dot, *spatial_psi], [chi_dot, *spatial_chi], Omega)
        equal(original['primal'], s.zeros(252, 1)); equal(original['dual'], s.zeros(1, 252))
        return psi_dot, chi_dot, data

    def coframe_Euler(self, e, phi, U, A, F, Omega, spatial_Omega, psi, chi, dpsi, data):
        """All original16 rows with dot(Omega_i)=0, before solving those rates."""
        curvature = self.lorentz.curvature_quadratic(Omega)
        for p, (mu, nu) in enumerate(PAIRS):
            if mu:
                curvature[:, p] += spatial_Omega[mu-1][6*nu:6*(nu+1), :]
            if nu:
                curvature[:, p] -= spatial_Omega[nu-1][6*mu:6*(mu+1), :]
        gamma_covariant = []
        for mu in range(4):
            spin = sum((Omega[6*mu+a]*self.lorentz.spin[a] for a in range(6)), s.zeros(4))
            gauge = sum((A[mu, a]*self.common.rho[a] for a in range(12)), s.zeros(252))
            gamma_covariant.append(dpsi[mu]+s.kronecker_product(spin, s.eye(63))*psi+gauge*psi)
        density = [v.reshape(4, 63)*chi.reshape(4, 63).T for v in gamma_covariant]
        yukawa = real((chi*data['Y']*psi)[0])
        adj, det = e.adjugate(), e.det()
        inv = e.inv()
        h = s.Abs(det)*inv*ETA*inv.T
        fluctuation = phi-self.common.scalar.vacuum
        g = self.time4.gauge
        force = s.zeros(16, 1)
        for a in range(16):
            delta = s.zeros(4); delta[a] = 1
            ddet = adj[a % 4, a//4]
            dh = s.sign(det)*ddet*inv*ETA*inv.T-inv*delta*h-h*delta.T*inv.T
            value = -3*ddet+sum(x*y for x, y in zip(self.coframe.at(self.dC[a], e), curvature))
            value += sum(dh[mu, nu]*(U[mu].T*U[nu])[0]/2 for mu in range(4) for nu in range(4))
            value -= s.sign(det)*ddet*(fluctuation.T*fluctuation)[0]
            dK = self.time4.kernel_derivative(e, delta)
            value += sum(x*y for x, y in zip(F, dK*F*g.gram))/2
            dadj = self.coframe.at(self.coframe.dadj[a], e)
            value += s.sign(det)*ddet*yukawa
            for mu in range(4):
                dE = s.sign(det)*s.I*sum((dadj[mu, b]*GAMMA[b] for b in range(4)), s.zeros(4))
                value += real(s.trace(dE*density[mu]))
            force[a] = s.expand(value)
        return clean(force), clean(curvature)

    def evolve(self, e, spatial_e, Omega, spatial_Omega, phi, U, A, F, spatial_F,
               psi, chi, spatial_psi, spatial_chi):
        """Actual first-spatial-jet forcing, including the original time4 consumer."""
        # Fix the original Omega0=0 Spin representative. Reconstructing a
        # canonical lambda=0 representative here could differentiate eTime.
        equal(Omega[:6, :], s.zeros(6, 1))
        for direction in spatial_Omega:
            equal(direction[:6, :], s.zeros(6, 1))
        data = self.geometry(e)
        velocity = self.spatial_coframe_velocity(e, spatial_e, Omega, psi, chi)
        time = self.time4.solve_time_rates(e, velocity, spatial_e, A, F, spatial_F, phi, U, psi, chi)
        de = [time['coframe_velocity'], *spatial_e]
        psi_dot, chi_dot, matter = self.matter_flow(e, de, phi, A, Omega, psi, chi, spatial_psi, spatial_chi)
        dpsi, dchi = [psi_dot, *spatial_psi], [chi_dot, *spatial_chi]
        S = self.torsion_source(e, psi, chi)
        dS = [self.torsion_source(e, psi, chi, de[mu], dpsi[mu], dchi[mu]) for mu in range(4)]
        O = self.omega_matrices(Omega)
        dO = [self.omega_matrices(v) for v in spatial_Omega]
        rhs = s.zeros(12, 1)
        for pair, (i, j) in enumerate(PAIRS[3:]):
            # partial_i partial_j eTime cancels with the opposite order.
            curl_v = (-dO[i-1][0]*e[:, j]+dO[j-1][0]*e[:, i]-
                      O[0]*(spatial_e[i-1][:, j]-spatial_e[j-1][:, i])+
                      (dO[i-1][j]-dO[j-1][i])*e[:, 0]+
                      O[j]*spatial_e[i-1][:, 0]-O[i]*spatial_e[j-1][:, 0]+
                      self.torsion_column(dS[i], 0, j)-self.torsion_column(dS[j], 0, i))
            row = (self.torsion_column(dS[0], i, j)-curl_v-
                   O[i]*de[0][:, j]+O[j]*de[0][:, i])
            for a in range(4):
                rhs[3*a+pair] = row[a]
        force, curvature = self.coframe_Euler(e, phi, U, A, F, Omega, spatial_Omega, psi, chi, dpsi, matter)
        metric_rhs = clean(-data['R'].T*force)
        omega_rate = self.solve_principal(e, clean(rhs), metric_rhs)
        complete_force = clean(force-data['G'][6:, :16].T*omega_rate)
        equal(data['R'].T*complete_force, s.zeros(6, 1))
        equal(data['spatial_torsion']*omega_rate, rhs)
        initial_torsion = clean(data['torsion']*Omega+
            self.coframe.at(self.curl, e)*s.Matrix.vstack(*[d.reshape(16, 1) for d in de])-S)
        equal(initial_torsion[[6*a+p for a in range(4) for p in range(3)], :], s.zeros(12, 1))
        return {'Omega_spatial_rate': omega_rate, 'coframe_rate': de[0], 'psi_rate': psi_dot,
                'chi_rate': chi_dot, 'time4': time, 'torsion_rhs': clean(rhs),
                'metric_Euler_rhs': metric_rhs, 'all16_coframe_Euler': complete_force,
                'spatial_torsion_constraint': initial_torsion[SPATIAL_TORSION, :],
                'prolonged_spatial_torsion_zero': True, 'six_original_metric_Euler_zero': True}


def certify_generic_inverse(model):
    c, l = model.coframe, model.lorentz
    e, det, Gt = c.e, c.det, c.G[:, :16]
    X = wedge_matrix(e)
    equal(model.T*s.kronecker_product(e.T, s.eye(6)),
          s.kronecker_product(s.eye(4), X.T)*model.flat_T)
    assert model.flat_T.det() != 0
    equal(model.T[SPATIAL_TORSION, :6], s.zeros(12, 6))
    equal(Gt[:6, :], s.zeros(6, 16))
    equal(model.T*c.K*Gt, det*model.curl[:, :16])
    equal(model.curl[SPATIAL_TORSION, :16], s.zeros(12, 16))
    Bnum = clean(c.metric_hessian.xreplace(dict(zip(c.h_variables,
                  [c.h[i, j] for i, j in ((0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (1, 2))]))))
    equal(-4*Gt.T*c.K*Gt, c.D.T*Bnum*c.D)
    equal(c.D*c.metric_lift_numerator(e), det*s.eye(6))
    # The original curvature coefficient supplies the metric Euler time rows.
    for a in range(16):
        equal(s.Matrix([model.dC[a][b, i] for i in range(3) for b in range(6)]).T,
              -Gt[6:, a].T)
    return {'generic_coframe_variables': 16,
            'original_flat_torsion_determinant': str(model.flat_T.det()),
            'full_torsion_covariance': 'T(e)*(e^T tensor I6)=(I4 tensor wedge2(e)^T)*T(I)',
            'full_torsion_inverse': '(e^T tensor I6)*T(I)^-1*(I4 tensor wedge2(e^-T))',
            'spatial_torsion_surjectivity': 'The12 selected rows have zero Omega0 columns; the full source inverse generates an18x12 right inverse Rtor.',
            'source_kernel': 'U=(-H_Omega^-1 Gt R_h)_spatial; Tsp U=0 follows from the original Cartan identity.',
            'original_metric_Euler_time_rows': 'L=-R_h^T Gt_spatial^T',
            'kinetic_bridge': 'L U=-B6, using Gt[Omega0,:]=0, M=-Gt^T H^-1 Gt=D_h^T B6 D_h, and D_h R_h=I6',
            'explicit_inverse_action': 'u0=Rtor*t; omega_dot=u0-U*B6^-1*(f-L*u0)',
            'uniform_domain': 'det(e)!=0 and det(spatial metric)!=0; the source common chart and time4 chart apply to the joint flow.',
            'second_spatial_temporal_coframe_derivatives_cancel': 'partial_i(dot e_j)-partial_j(dot e_i) contains partial_i partial_j e0-partial_j partial_i e0=0 before assembly; no second spatial jet is supplied to evolve.'}


def certify_actual_inverses(model):
    N = 3*s.sqrt(30)/25
    frames = [s.diag(N, 1, 1, 1), s.Matrix([[2, 1, 0, 0], [0, 2, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]])]
    rows = []
    for e in frames:
        data = model.geometry(e)
        equal(data['time_matrix']*data['time_inverse'], s.eye(18))
        equal(data['time_inverse']*data['time_matrix'], s.eye(18))
        equal(data['spatial_torsion']*data['torsion_kernel'], s.zeros(12, 6))
        equal(data['metric_Euler_time_rows']*data['torsion_kernel'], -data['B'])
        rhs = s.Matrix(s.symbols('rhs0:18', real=True))
        equal(model.solve_principal(e, rhs[:12, :], rhs[12:, :]), data['time_inverse']*rhs)
        rows.append({'coframe': encode(e), 'time_matrix': encode(data['time_matrix']),
                     'time_inverse': encode(data['time_inverse']), 'determinant': str(data['time_matrix'].det()),
                     'all18_independent_forcing_coordinates_checked': True})
    return rows


def certify_original_homogeneous_consumer(model):
    receipt = json.loads((HERE/'source_homogeneous_canonical_flow.json').read_bytes())
    f = {name: decode(value) for name, value in receipt['datum'].items()}
    r = {name: decode(value) for name, value in receipt['complete_rates'].items()}
    e, phi, A, Omega = f['e'], f['phi'], f['A'], decode(receipt['source_Lorentz_connection'])
    data = model.common.matter_data(e, phi, A)
    chi = model.common.canonical_dual(data, f['p'])
    g = model.time4.gauge
    gauge = g.constitutive(e)
    F = g.curvature(A, s.zeros(4, 48))
    F[:3, :] = clean(gauge['electric_inverse']*(f['Pi_A']*g.gram_inverse-gauge['mixed']*F[3:, :]))
    h = s.Abs(e.det())*e.inv()*ETA*e.inv().T
    Usp = [sum((A[i+1, a]*g.rho70[a]*phi for a in range(12)), s.zeros(70, 1)) for i in range(3)]
    U0 = clean((f['Pi_phi']-sum((h[0, i+1]*Usp[i] for i in range(3)), s.zeros(70, 1)))/h[0, 0])
    result = model.evolve(e, [s.zeros(4)]*3, Omega, [s.zeros(24, 1)]*3, phi, [U0, *Usp],
                         A, F, [s.zeros(6, 12)]*3, f['psi'], chi,
                         [s.zeros(252, 1)]*3, [s.zeros(1, 252)]*3)
    equal(result['coframe_rate'], r['e']); equal(result['psi_rate'], r['psi'])
    equal(result['spatial_torsion_constraint'], s.zeros(12, 1))
    equal(result['all16_coframe_Euler'], s.zeros(16, 1))
    dadj = model.coframe.at(derivative(model.coframe.adj, model.coframe.e, list(r['e'])), e)
    dE = s.kronecker_product(s.sign(e.det())*s.I*sum((dadj[0, b]*GAMMA[b] for b in range(4)), s.zeros(4)), s.eye(63))
    canonical_chi_rate = clean(s.I*r['p']*data['inverse_E']-chi*dE*data['inverse_E'])
    equal(result['chi_rate'], canonical_chi_rate)
    acceleration = decode(receipt['original_Euler_consumer']['nonzero_spatial_coframe_acceleration'])
    c = model.coframe
    dH = c.at(derivative(c.H, c.e, list(r['e'])), e)
    dGt = c.at(derivative(c.G[:, :16], c.e, list(r['e'])), e)
    dj = model.current(e, f['psi'], chi, r['e'], r['psi'], canonical_chi_rate)
    expected = clean(-c.geometry(e)['Lorentz_inverse']*(dH*Omega+dGt*r['e'].reshape(16, 1)+
                    c.at(c.G[:, :16], e)*acceleration+dj))
    equal(result['Omega_spatial_rate'], expected[6:, :])
    assert result['Omega_spatial_rate'].todok()
    return {'original_nontrivial_homogeneous_datum': True,
            'all16_original_coframe_rates_recovered': True,
            'full252_primal_and_independent_dual_rates_recovered': True,
            'all18_Lorentz_rates_equal_original_differentiated_auxiliary_solution': True,
            'all16_original_coframe_Euler_zero': True, 'spatial_torsion_and_its12_time_derivatives_zero': True,
            'Omega_spatial_rate': encode(result['Omega_spatial_rate']),
            'time4_rates': encode(result['time4']['time_rates'])}


def certify_spatial_jet_consumer(model):
    receipt = json.loads((HERE/'source_homogeneous_canonical_flow.json').read_bytes())
    f = {name: decode(value) for name, value in receipt['datum'].items()}
    e, phi, A, psi = f['e'], f['phi'], f['A'], f['psi']
    chi = model.common.canonical_dual(model.common.matter_data(e, phi, A), f['p'])
    spatial_e = [s.Matrix(4, 4, lambda a, b: s.Rational((i+2*a+b)%5-2, 101)) for i in range(3)]
    spatial_psi = [s.Matrix([s.Rational((i+3*j)%7-3, 103)+s.I*s.Rational((2*i+j)%5-2, 107)
                            for j in range(252)]) for i in range(3)]
    spatial_chi = [s.Matrix(1, 252, lambda _, j:
        s.Rational((2*i+j)%7-3, 109)+s.I*s.Rational((i+2*j)%5-2, 113)) for i in range(3)]
    seed_velocity = decode(receipt['complete_rates']['e'])
    seed_jet = s.Matrix.vstack(seed_velocity.reshape(16, 1), *[v.reshape(16, 1) for v in spatial_e])
    c, data = model.coframe, model.geometry(e)
    Omega = clean(-data['Lorentz_inverse']*(data['G']*seed_jet+model.current(e, psi, chi)))
    spatial_Omega = []
    for i in range(3):
        dH = c.at(derivative(c.H, c.e, list(spatial_e[i])), e)
        dG = c.at(derivative(c.G, c.e, list(spatial_e[i])), e)
        dj = model.current(e, psi, chi, spatial_e[i], spatial_psi[i], spatial_chi[i])
        spatial_Omega.append(clean(-data['Lorentz_inverse']*(dH*Omega+dG*seed_jet+dj)))
    # Changing only Omega0 fixes the Spin representative; spatial torsion and
    # its spatial prolongations do not involve those six columns.
    Omega[:6, :] = s.zeros(6, 1)
    for value in spatial_Omega:
        value[:6, :] = s.zeros(6, 1)
    g = model.time4.gauge
    F = g.curvature(A, s.zeros(4, 48))
    constitutive = g.constitutive(e)
    F[:3, :] = clean(constitutive['electric_inverse']*(f['Pi_A']*g.gram_inverse-
                                                     constitutive['mixed']*F[3:, :]))
    U = [s.Matrix([s.Rational((i+3*j)%7-3, 127) for j in range(70)]) for i in range(4)]
    result = model.evolve(e, spatial_e, Omega, spatial_Omega, phi, U, A, F,
                         [s.zeros(6, 12)]*3, psi, chi, spatial_psi, spatial_chi)
    equal(result['spatial_torsion_constraint'], s.zeros(12, 1))
    actual_de = s.Matrix.vstack(result['coframe_rate'].reshape(16, 1),
                                *[value.reshape(16, 1) for value in spatial_e])
    equal(c.at(c.H, e)*Omega+data['G']*actual_de+model.current(e, psi, chi), s.zeros(24, 1))
    equal(c.universal_null_frame(e)[:, 4:].T*result['all16_coframe_Euler'], s.zeros(6, 1))
    dS = [model.torsion_source(e, psi, chi, spatial_e[i], spatial_psi[i], spatial_chi[i]) for i in range(3)]
    for i in range(3):
        dT = c.at(derivative(model.T, c.e, list(spatial_e[i])), e)
        equal((dT*Omega+data['torsion']*spatial_Omega[i]-dS[i])[SPATIAL_TORSION, :], s.zeros(12, 1))
    # Differentiate the actual torsion-generated velocity component by
    # component on this affine spatial field jet, independently of the
    # grouped curl expression used by evolve.
    O, dO = model.omega_matrices(Omega), [model.omega_matrices(v) for v in spatial_Omega]
    dv = [s.zeros(4) for _ in range(3)]
    for i in range(3):
        for j in range(1, 4):
            dv[i][:, j] = (-dO[i][0]*e[:, j]-O[0]*spatial_e[i][:, j]+
                          dO[i][j]*e[:, 0]+O[j]*spatial_e[i][:, 0]+
                          model.torsion_column(dS[i], 0, j))
    Sdot = model.torsion_source(e, psi, chi, result['coframe_rate'], result['psi_rate'], result['chi_rate'])
    dOtime = model.omega_matrices(s.zeros(6, 1).col_join(result['Omega_spatial_rate']))
    direct_rows, omitted = [], []
    for a in range(4):
        for i, j in PAIRS[3:]:
            row = (dv[i-1][:, j]-dv[j-1][:, i]+dOtime[i]*e[:, j]-dOtime[j]*e[:, i]+
                   O[i]*result['coframe_rate'][:, j]-O[j]*result['coframe_rate'][:, i]-
                   model.torsion_column(Sdot, i, j))
            direct_rows.append(row[a])
            omitted.append((model.torsion_column(dS[i-1], 0, j)-
                            model.torsion_column(dS[j-1], 0, i))[a])
    equal(s.Matrix(direct_rows), s.zeros(12, 1))
    assert clean(s.Matrix(omitted)).todok()
    assert result['Omega_spatial_rate'].todok()
    return {'all3_nonzero_spatial_coframe_and_Lorentz_jets': True,
            'fields': {'e': encode(e), 'spatial_e': [encode(value) for value in spatial_e],
                       'Omega': encode(Omega), 'spatial_Omega': [encode(value) for value in spatial_Omega],
                       'phi': encode(phi), 'U': [encode(value) for value in U],
                       'A': encode(A), 'F': encode(F), 'spatial_F': [encode(s.zeros(6, 12)) for _ in range(3)],
                       'psi': encode(psi), 'chi': encode(chi),
                       'spatial_psi': [encode(value) for value in spatial_psi],
                       'spatial_chi': [encode(value) for value in spatial_chi]},
            'all252_primal_and_dual_spatial_jet_components_retained': True,
            'original_spatial_torsion_and_all36_spatial_prolongations_zero': True,
            'all24_original_Lorentz_Euler_and6_Spin_Noether_rows_zero': True,
            'all12_time_torsion_derivatives_from_actual_velocity_product_rule_zero': True,
            'omitting_spatial_contorsion_derivatives_negative_control_nonzero': True,
            'Omega_spatial_rate': encode(result['Omega_spatial_rate']),
            'time4_rates': encode(result['time4']['time_rates']),
            'remaining_original_time_coframe_Euler': encode(result['all16_coframe_Euler'].extract([0, 4, 8, 12], [0])),
            'scope': 'Actual nonzero spatial first-jet update on spatial torsion fields; four temporal coframe, gauge Gauss and scalar initial constraints are not asserted for this test datum.'}


def main():
    started = time.monotonic()
    model = SourceSpatialLorentzTime()
    generic = certify_generic_inverse(model)
    print('PASS generic original18 time inverse from12 torsion +6 metric Euler and B6', flush=True)
    exact = certify_actual_inverses(model)
    print('PASS both18 inverse sides, arbitrary18 forcing, source and non-diagonal coframes', flush=True)
    original = certify_original_homogeneous_consumer(model)
    print('PASS actual original full matter/coframe flow and18 Lorentz rates; all16 Euler and12 torsion derivatives', flush=True)
    spatial = certify_spatial_jet_consumer(model)
    print('PASS actual nonzero spatial field jets,36 spatial torsion prolongations,12 time derivatives and contorsion control', flush=True)
    inputs = [HERE/'source_spatial_lorentz_time.py', HERE/'source_spatial_time_coframe.py',
              HERE/'source_spatial_time_coframe.json', HERE/'source_common_hamiltonian.py',
              HERE/'source_coframe_legendre.py', HERE/'source_lorentz_contact.py',
              HERE/'source_homogeneous_canonical_flow.json']
    result = {'root': ROOT_ID, 'verdict': 'SOURCE_SPATIAL_LORENTZ18_TIME_INVERSE_AND_ACTUAL_FIRST_JET_FORCING_GENERATED',
              'generic_original_principal_inverse': generic, 'actual_inverse_consumers': exact,
              'actual_original_flow_consumer': original,
              'actual_spatial_first_jet_consumer': spatial,
              'public_first_order_evolve': 'Original time4, torsion0i coframe velocity, full252 Dirac/dual,12 prolonged spatial torsion and6 metric Euler; source currents and every forcing are evaluated from the same first spatial jets.',
              'Spin_representative': 'Omega0=0 is the actual source value and fixed representative here; the canonical coframe lambda=0 section is not used to reconstruct Omega0 from differentiated eTime.',
              'initial_constraints': 'The spatial torsion, four temporal coframe, gauge Gauss and scalar slice constraints remain initial constraints of the joint PDE; evolve does not assert them for arbitrary supplied jets.',
              'proper_clock': 'tau=N*t, N=3*sqrt(30)/25, unchanged',
              'general_spatial_Cauchy_closed': False,
              'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
              'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs},
              'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_spatial_lorentz_time.json').write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
