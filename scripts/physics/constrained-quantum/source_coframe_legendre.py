#!/usr/bin/env python3
"""Nonlinear coframe Legendre map of the original reduced Lorentz sector.

All derivatives of the coframe and all independent-dual currents are retained.
The velocity quotient follows from a source polynomial identity through the
spatial metric, not from the old Jacobi field count.  The original BF boundary
flux is retained as a canonical one-form difference.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, decode
from source_lorentz_contact import SourceLorentzContact, clean, equal, encode, ETA, PAIRS, GAMMA


SYMMETRIC = ((0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (1, 2))


def pack(matrix):
    return s.Matrix([matrix[i, j] for i, j in SYMMETRIC])


def symmetric(values, dual=False):
    matrix = s.zeros(3)
    for value, (i, j) in zip(values, SYMMETRIC):
        matrix[i, j] = matrix[j, i] = value/(2 if dual and i != j else 1)
    return matrix


def rational(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.cancel)


class SourceCoframeLegendre:
    def __init__(self):
        self.lorentz = SourceLorentzContact()
        self.e = s.Matrix(4, 4, s.symbols('e0:16', real=True))
        self.det = s.expand(self.e.det())
        self.H = self.lorentz.hessian(self.e)
        self.K = self.lorentz.inverse_numerator(self.e)
        self.G = self.lorentz.geometry_maps(self.e)[0]
        self.h = self.e[:, 1:].T*ETA*self.e[:, 1:]
        self.D = pack(self.h).jacobian(list(self.e))
        self.h_variables = s.symbols('h0:6', real=True)
        self.h_symbolic = symmetric(self.h_variables)
        self.metric_hessian = s.hessian(self.h_symbolic.det(), self.h_variables)
        pi = s.Matrix(s.symbols('pi0:6', real=True))
        P = symmetric(pi, dual=True)
        inverse_action = s.trace(P*self.h_symbolic)*self.h_symbolic/2-self.h_symbolic*P*self.h_symbolic
        self.metric_inverse_numerator = pack(inverse_action).jacobian(pi)
        self.dH = [self.H.diff(x) for x in self.e]
        self.dG = [self.G.diff(x) for x in self.e]
        self.adj = self.e.adjugate()
        self.dadj = [self.adj.diff(x) for x in self.e]
        self.boundary = self.boundary_coefficients(self.e)

    def at(self, matrix, e):
        return clean(matrix.xreplace(dict(zip(self.e, e))))

    def boundary_coefficients(self, e):
        C = self.lorentz.curvature_coefficient(e)
        beta = s.zeros(4, 24)
        for p, (mu, nu) in enumerate(PAIRS):
            for a in range(6):
                beta[mu, 6*nu+a] += C[a, p]
                beta[nu, 6*mu+a] -= C[a, p]
        return clean(beta)

    def boundary_flux(self, e, connection):
        return clean(self.boundary_coefficients(e)*connection)

    def metric_lift_numerator(self, e):
        """Right inverse of D_h multiplied by det(e), valid also on null slices."""
        columns = []
        for a in range(6):
            S = symmetric(s.eye(6)[:, a])
            field = s.zeros(4)
            field[:, 1:] = ETA*e.adjugate()[1:, :].T*S/2
            columns.append(field.reshape(16, 1))
        return clean(s.Matrix.hstack(*columns))

    def universal_null_frame(self, e):
        result = s.zeros(16, 10)
        for a in range(4):
            result[4*a, a] = 1
        for a, generator in enumerate(self.lorentz.basis):
            result[:, 4+a] = (generator*e).reshape(16, 1)
        return clean(result)

    def geometry(self, e):
        determinant = s.simplify(e.det())
        assert determinant != 0
        h = clean(e[:, 1:].T*ETA*e[:, 1:])
        h_det = s.factor(h.det())
        substitution = dict(zip(self.h_variables, pack(h)))
        B = clean(self.metric_hessian.xreplace(substitution)/(4*determinant))
        D = self.at(self.D, e)
        R = rational(self.metric_lift_numerator(e)/determinant)
        Z = self.universal_null_frame(e)
        G = self.at(self.G, e)
        inverse = rational(self.lorentz.inverse(e))
        M = rational(-G[:, :16].T*inverse*G[:, :16])
        if h_det != 0:
            B_inverse = rational(4*determinant*self.metric_inverse_numerator.xreplace(substitution)/h_det)
            select = s.eye(6)
            metric_null = s.zeros(6, 0)
            chart = 'det(h)!=0'
        else:
            # Source entries determine the exact chart and its extra constraints.
            pivots = B.rref()[1]
            select = s.eye(6)[:, list(pivots)]
            B_inverse = rational((select.T*B*select).inv())
            metric_null = s.Matrix.hstack(*B.nullspace())
            chart = 'det(h)=0; exact source pivot '+str(tuple(pivots))
        velocity_lift = clean(R*select)
        null_frame = clean(Z.row_join(R*metric_null))
        inverse_velocity = rational(velocity_lift*B_inverse*velocity_lift.T)
        return {'det': determinant, 'h': h, 'det_h': h_det, 'D': D, 'R': R,
                'B': B, 'quotient_inverse': B_inverse, 'metric_select': select,
                'velocity_lift': velocity_lift, 'null_frame': null_frame,
                'velocity_inverse': inverse_velocity, 'M': M, 'G': G,
                'Lorentz_inverse': inverse, 'chart': chart}

    def velocity_coordinates(self, e, velocity):
        """A metric velocity plus the exact10 time/Lorentz frame coordinates."""
        data = self.geometry(e)
        metric_velocity = data['D']*velocity
        residual = (velocity-data['R']*metric_velocity).reshape(4, 4)
        F = residual[:, 1:]
        columns = e.T*ETA*F
        skew = s.zeros(4)
        skew[:, 1:] = columns
        for j in range(1, 4):
            skew[j, 0] = -skew[0, j]
        Lorentz = rational(ETA*e.inv().T*skew*e.inv())
        coefficients = s.Matrix([ETA[a, a]*Lorentz[a, b] for a, b in PAIRS])
        time_column = residual[:, 0]-Lorentz*e[:, 0]
        return clean(metric_velocity), clean(time_column.col_join(coefficients))

    def currents(self, e, spatial, primal, dual):
        assert spatial.shape == (48, 1)
        data = self.geometry(e)
        matter = self.lorentz.matter_current(e, primal, dual)
        q = clean(data['G'][:, 16:]*spatial+matter)
        shift = clean(-data['G'][:, :16].T*data['Lorentz_inverse']*q)
        constant = s.expand(-3*data['det']-(q.T*data['Lorentz_inverse']*q)[0]/2)
        return {**data, 'matter_current': matter, 'q': q, 'momentum_shift': shift,
                'constant_action': constant}

    def lagrangian(self, e, velocity, spatial, primal, dual):
        data = self.currents(e, spatial, primal, dual)
        return s.expand((velocity.T*data['M']*velocity)[0]/2+
                        (data['momentum_shift'].T*velocity)[0]+data['constant_action'])

    def momentum(self, e, velocity, spatial, primal, dual):
        data = self.currents(e, spatial, primal, dual)
        return clean(data['M']*velocity+data['momentum_shift'])

    def constraints(self, e, momentum, spatial, primal, dual):
        data = self.currents(e, spatial, primal, dual)
        return clean(data['null_frame'].T*(momentum-data['momentum_shift']))

    def velocity(self, e, momentum, spatial, primal, dual, multipliers):
        data = self.currents(e, spatial, primal, dual)
        assert multipliers.shape == (data['null_frame'].cols, 1)
        return clean(data['velocity_inverse']*(momentum-data['momentum_shift'])+
                     data['null_frame']*multipliers)

    def hamiltonian(self, e, momentum, spatial, primal, dual, multipliers=None):
        data = self.currents(e, spatial, primal, dual)
        shifted = momentum-data['momentum_shift']
        value = (shifted.T*data['velocity_inverse']*shifted)[0]/2-data['constant_action']
        if multipliers is not None:
            value += (multipliers.T*data['null_frame'].T*shifted)[0]
        return s.expand(value)

    def current_derivative(self, e, de, primal, dual, dprimal=None, ddual=None):
        """Actual derivative of the full252 real current along one spacetime jet."""
        dprimal = s.zeros(252, 1) if dprimal is None else dprimal
        ddual = s.zeros(1, 252) if ddual is None else ddual
        ports = self.lorentz.raw_matter_ports(e)
        derivative_adj = self.at(sum((de[a]*self.dadj[a] for a in range(16)), s.zeros(4)), e)
        derivative_V = [clean(ports['orientation']*sum((derivative_adj[mu, a]*s.I*GAMMA[a]
                           for a in range(4)), s.zeros(4))*spin)
                        for mu in range(4) for spin in self.lorentz.spin]
        values = []
        for V, dV in zip(ports['V'], derivative_V):
            full, dfull = s.kronecker_product(V, s.eye(63)), s.kronecker_product(dV, s.eye(63))
            value = (ddual*full*primal+dual*dfull*primal+dual*full*dprimal)[0]
            values.append(s.expand(s.re(value)))
        return clean(s.Matrix(values))

    def euler(self, e, de, dde, primal, dual, dprimal, ddual):
        """Original gravity+Lorentz-matter Euler on a complete local field jet.

        de: 64=(mu,a,nu); dde[mu,:]=partial_mu(de), with commuting coframe
        second derivatives when this jet comes from a smooth coframe.  Other
        original scalar/gauge/free-Dirac coframe forces are additive consumers.
        """
        assert de.shape == (64, 1) and dde.shape == (4, 64)
        data = self.geometry(e)
        source = self.lorentz.matter_current(e, primal, dual)
        connection = clean(-data['Lorentz_inverse']*(data['G']*de+source))
        dH = [self.at(value, e) for value in self.dH]
        dG = [self.at(value, e) for value in self.dG]
        force = s.zeros(16, 1)
        for a in range(16):
            source_derivative = self.current_derivative(e, s.eye(16)[:, a], primal, dual)
            force[a] = s.expand(-3*self.at(s.Matrix([s.diff(self.det, self.e[a])]), e)[0]+
                (connection.T*dH[a]*connection)[0]/2+
                (connection.T*dG[a]*de)[0]+(connection.T*source_derivative)[0])
        momentum = clean(data['G'].T*connection)
        connection_derivative = s.zeros(4, 24)
        divergence = s.zeros(16, 1)
        for mu in range(4):
            local = de[16*mu:16*(mu+1), 0]
            H_mu = clean(sum((local[a]*dH[a] for a in range(16)), s.zeros(24)))
            G_mu = clean(sum((local[a]*dG[a] for a in range(16)), s.zeros(24, 64)))
            j_mu = self.current_derivative(e, local, primal, dual, dprimal[mu], ddual[mu])
            dOmega = clean(-data['Lorentz_inverse']*(H_mu*connection+G_mu*de+
                                      data['G']*dde[mu, :].T+j_mu))
            connection_derivative[mu, :] = dOmega.T
            divergence += G_mu[:, 16*mu:16*(mu+1)].T*connection+data['G'][:, 16*mu:16*(mu+1)].T*dOmega
        return {'connection': connection, 'connection_derivative': clean(connection_derivative),
                'all_four_coframe_momenta': momentum, 'coframe_force': clean(force),
                'Euler': clean(force-divergence), 'boundary_flux': self.boundary_flux(e, connection)}


def certify_generic(model):
    e, determinant = model.e, model.det
    h_sub = dict(zip(model.h_variables, pack(model.h)))
    B_num = model.metric_hessian.xreplace(h_sub)
    Gt = model.G[:, :16]
    equal(-4*Gt.T*model.K*Gt, model.D.T*B_num*model.D)
    equal(model.D*model.metric_lift_numerator(e), determinant*s.eye(6))
    equal(model.D*model.universal_null_frame(e), s.zeros(6, 10))
    assert s.expand(model.metric_hessian.det()+16*model.h_symbolic.det()**2) == 0
    equal(model.metric_hessian*model.metric_inverse_numerator, model.h_symbolic.det()*s.eye(6))
    equal(model.metric_inverse_numerator*model.metric_hessian, model.h_symbolic.det()*s.eye(6))
    for mu in range(4):
        equal(model.boundary[mu, :].T.jacobian(list(e)), -model.G[:, 16*mu:16*(mu+1)])
    # Every coefficient of the original boundary-divergence and symplectic
    # potential identities is included in the preceding four matrix identities.
    return {'independent_coframe_variables': 16, 'spatial_metric': encode(model.h),
            'metric_velocity_map': encode(model.D), 'metric_lift_numerator': encode(model.metric_lift_numerator(e)),
            'universal10_null_frame': encode(model.universal_null_frame(e)),
            'metric_determinant_Hessian': encode(model.metric_hessian),
            'metric_inverse_numerator': encode(model.metric_inverse_numerator),
            'source_factorization': 'M=-Gt^T H^-1 Gt=D_h^T Hess_h(det h) D_h/(4 det e)',
            'generic_rank_producer': 'det Hess_h(det h)=-16(det h)^2 and D_h has an explicit right inverse on all GL4',
            'temporal_noncharacteristic_identity': 'det h=adj(e)[0,0]^2-sum_{a=1}^3 adj(e)[0,a]^2',
            'right_inverse': 'R: delta E=eta (e^-1[1:,:])^T delta h/2, delta e[:,0]=0',
            'metric_inverse': 'B^-1 pi=(4 det e/det h) pack(1/2 tr(P h)h-hPh), P_diag=pi_diag,P_off=pi_off/2',
            'noncharacteristic_rank': 6, 'noncharacteristic_primary_constraints': 10,
            'universal_null_directions': 'four temporal coframe columns plus all six original Lorentz generators acting on e',
            'null_slice_rank': 4, 'null_slice_primary_constraints': 12,
            'null_rank_reason': 'a real Lorentzian3-plane has radical dimension at most1; det h=0 therefore has rank2 and is congruent to diag(0,a,b) with a,b>0. Hessdet has rank4 on this chart, and congruence transports rank. The exact6x6 pivot consumer retains its two extra null directions',
            'raw_Legendre_domain': 'all real invertible e; noncharacteristic is needed for the closed6dim inverse, not for the raw momentum or null chart',
            'boundary_flux_coefficients': encode(model.boundary),
            'boundary_flux': 'F^mu=beta_mu(e)^T Omega from the original C(e)=J wedge²(e) wedge pairing; no flux set to zero',
            'exact_density_identity': 'L_original_BF+Lorentz_matter=L_after_IBP+sum_mu partial_mu F^mu',
            'original_BF_temporal_momentum': 'p_Omega=beta_0(e)',
            'new_coframe_temporal_momentum': 'Pi_e=Gt(e)^T Omega*',
            'canonical_one_form_identity': 'beta_0(e)^T deltaOmega-(Gt(e)^T Omega)^T deltae=delta F^0, valid also after Omega=Omega* pullback'}


def certify_frames(model):
    N = 3*s.sqrt(30)/25
    frames = [s.diag(N, 1, 1, 1),
              s.Matrix([[2, 1, 0, 0], [0, 1, 1, 0], [0, 0, 1, 1], [0, 0, 0, 1]]),
              s.Matrix([[1, 1, 0, 0], [1, -1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]),
              s.Matrix([[0, 1, 0, 0], [1, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])]
    result = []
    for e in frames:
        data = model.geometry(e)
        D, R, Z, M, Q = [data[key] for key in ('D', 'R', 'null_frame', 'M', 'velocity_inverse')]
        equal(D*R, s.eye(6))
        equal(M, D.T*data['B']*D)
        equal(M*Z, s.zeros(16, Z.cols))
        equal(M*Q*M, M)
        equal(Q*M*Q, Q)
        assert Z.rank()+M.rank() == 16
        # These are whole16 velocity/constraint frames, including all Lorentz
        # directions, rather than hand-selected metric representatives.
        velocity_frame = data['velocity_lift'].row_join(Z)
        assert velocity_frame.rank() == 16
        for a in range(16):
            v = s.eye(16)[:, a]
            metric, null = model.velocity_coordinates(e, v)
            equal(R*metric+model.universal_null_frame(e)*null, v)
        result.append({'coframe': encode(e), 'det': str(data['det']), 'det_h': str(data['det_h']),
                       'rank': M.rank(), 'nullity': Z.cols, 'chart': data['chart'],
                       'whole_kinetic_Hessian': encode(M), 'momentum_constraints_frame': encode(Z),
                       'velocity_quotient_lift': encode(data['velocity_lift']),
                       'velocity_quotient_inverse': encode(data['quotient_inverse'])})
    # The complete null chart with two free transverse metric parameters.
    a, b = s.symbols('a b', nonzero=True, real=True)
    null_h = s.diag(0, a, b)
    C = model.metric_hessian.xreplace(dict(zip(model.h_variables, pack(null_h))))
    assert C.rank() == 4 and len(C.nullspace()) == 2
    return result


def certify_matter_and_energy(model):
    active = json.loads((BASE/'active-gauge/receipt.json').read_text())
    occupied = json.loads((BASE/'occupied-response/receipt.json').read_text())
    e = s.Matrix(active['actual_background']['coframe']).applyfunc(s.sympify)
    frame = decode(occupied['occupied_frame'])
    original = frame*s.Matrix(active['actual_background']['primal_H']).applyfunc(s.sympify)
    raw_dual = s.sqrt(2)*original.T
    primal, dual = s.zeros(252, 1), s.zeros(1, 252)
    for spin, value in enumerate((1, s.I, 2, 3*s.I)):
        primal[63*spin] = value
    for spin, value in enumerate((1, 2*s.I, -1, s.I)):
        dual[63*spin] = value
    spatial = s.Matrix([s.Rational((a*7)%11-5, 13) for a in range(48)])
    data = model.currents(e, spatial, primal, dual)
    matter_shift = clean(-data['G'][:, :16].T*data['Lorentz_inverse']*data['matter_current'])
    assert matter_shift != s.zeros(16, 1)
    velocity = s.Matrix(s.symbols('v0:16', real=True))
    momentum = model.momentum(e, velocity, spatial, primal, dual)
    lagrangian = model.lagrangian(e, velocity, spatial, primal, dual)
    equal(s.Matrix([s.diff(lagrangian, v) for v in velocity]), momentum)
    equal(model.constraints(e, momentum, spatial, primal, dual), s.zeros(10, 1))
    assert s.expand(model.hamiltonian(e, momentum, spatial, primal, dual)-
                    (momentum.T*velocity)[0]+lagrangian) == 0
    p = s.Matrix(s.symbols('p0:16', real=True))
    multipliers = s.Matrix(s.symbols('lambda0:10', real=True))
    total = model.hamiltonian(e, p, spatial, primal, dual, multipliers)
    equal(s.Matrix([s.diff(total, value) for value in p]),
          model.velocity(e, p, spatial, primal, dual, multipliers))
    # The fixed-momentum energy retains the matter-dependent shift. Removing
    # it is a real error even if one keeps the isolated j*H^-1*j term.
    wrong = (p.T*data['velocity_inverse']*p)[0]/2-data['constant_action']
    assert s.expand(total-(multipliers.T*data['null_frame'].T*(p-data['momentum_shift']))[0]-wrong) != 0
    original_data = model.currents(e, s.zeros(48, 1), original, raw_dual)
    return {'source_coframe': encode(e), 'test_primal': encode(primal), 'test_dual': encode(dual),
            'test_spatial_jet': encode(spatial), 'full252_matter_current': encode(data['matter_current']),
            'matter_induced_momentum_shift': encode(matter_shift),
            'complete_momentum_shift': encode(data['momentum_shift']),
            'original_background_momentum_shift': encode(original_data['momentum_shift']),
            'actual_all16_momentum_derivatives': 'equal generated M*v+b',
            'actual_all10_primary_constraints': '0 for every symbolic16 velocity',
            'actual_Legendre_energy_identity': 'H(Pi(v))=Pi(v).v-L(v), all16 independent velocities',
            'actual_total_Hamiltonian_velocity_derivative': 'partial_Pi H_total=Q(Pi-b)+Z lambda',
            'omitting_matter_momentum_shift_negative_control': True,
            'potential_and_shift_formula': 'q=G_spatial spatial+j; b=-Gt^T H^-1 q; L0=-3det e-1/2 q^T H^-1 q',
            'primary_constraints': 'Z(e)^T(Pi-b)=0; exact source frame Z has10 columns off the null slice and12 on it',
            'Hamiltonian_on_constraint_surface': 'H_c=1/2(Pi-b)^T Q(e)(Pi-b)+3det e+1/2 q^T H^-1 q',
            'full_velocity_fiber': 'v=Q(e)(Pi-b)+Z(e)lambda',
            'isolated_action_contact_relabelled_as_whole_Hamiltonian': False}


def certify_Euler(model, matter_test):
    e = decode(matter_test['source_coframe'])
    primal, dual = decode(matter_test['test_primal']), decode(matter_test['test_dual'])
    de = s.Matrix([s.Rational((a*5)%9-4, 17) for a in range(64)])
    # A complete symmetric second jet, not a constant-coframe test.
    dde = s.zeros(4, 64)
    for mu in range(4):
        for rho in range(4):
            for a in range(16):
                dde[mu, 16*rho+a] = s.Rational((mu+rho+3*a)%7-3, 19)
    dp = [s.Rational(mu+1, 5)*primal for mu in range(4)]
    dc = [s.Rational(2*mu-1, 7)*dual for mu in range(4)]
    result = model.euler(e, de, dde, primal, dual, dp, dc)
    data = model.geometry(e)
    connection = result['connection']
    equal(result['all_four_coframe_momenta'][:16, 0],
          model.momentum(e, de[:16, 0], de[16:, 0], primal, dual))
    # Differentiate the original algebraic Lorentz equation in each spacetime
    # direction. All24 rows must return the generated connection derivative.
    for mu in range(4):
        local = de[16*mu:16*(mu+1), 0]
        dH = model.at(sum((local[a]*model.dH[a] for a in range(16)), s.zeros(24)), e)
        dG = model.at(sum((local[a]*model.dG[a] for a in range(16)), s.zeros(24, 64)), e)
        dj = model.current_derivative(e, local, primal, dual, dp[mu], dc[mu])
        equal(model.at(model.H, e)*result['connection_derivative'][mu, :].T+
              dH*connection+dG*de+data['G']*dde[mu, :].T+dj, s.zeros(24, 1))
    # Direct rational differentiation of the actual reduced density checks
    # all16 e-partials independently of the envelope formula used by euler().
    u = s.Symbol('u', real=True)
    raw_force = []
    for a in range(16):
        direction = s.zeros(4); direction[a] = 1
        curve = e+u*direction
        determinant = s.expand(curve.det())
        # This curve stays in the source positive orientation near u=0.
        G = model.at(model.G, curve)
        K = model.at(model.K, curve)
        adj = curve.adjugate()
        current = []
        for mu in range(4):
            for spin in model.lorentz.spin:
                V = sum((adj[mu, b]*s.I*GAMMA[b] for b in range(4)), s.zeros(4))*spin
                current.append(s.expand(s.re((dual*s.kronecker_product(V, s.eye(63))*primal)[0])))
        source = G*de+s.Matrix(current)
        density = -3*determinant-(source.T*K*source)[0]/(2*determinant)
        raw_force.append(s.cancel(s.diff(density, u).subs(u, 0)))
    equal(s.Matrix(raw_force), result['coframe_force'])
    assert result['Euler'] != s.zeros(16, 1)
    # Canonical symplectic potentials differ by the original temporal flux.
    v_e = s.Matrix(s.symbols('deltae0:16', real=True))
    v_omega = s.Matrix(s.symbols('deltaomega0:24', real=True))
    beta = model.boundary_coefficients(e)[0, :].T
    flux_derivative = (beta.T*v_omega)[0]+(connection.T*
        model.at(model.boundary[0, :].T.jacobian(list(model.e)), e)*v_e)[0]
    old_theta = (beta.T*v_omega)[0]
    new_theta = (result['all_four_coframe_momenta'][:16, 0].T*v_e)[0]
    assert s.expand(old_theta-new_theta-flux_derivative) == 0
    return {'full_first_coframe_jet': encode(de), 'full_symmetric_second_coframe_jet': encode(dde),
            'original_reduced_connection': encode(connection),
            'all_four_connection_derivatives': encode(result['connection_derivative']),
            'all64_coframe_momenta': encode(result['all_four_coframe_momenta']),
            'all16_original_coframe_force': encode(result['coframe_force']),
            'all16_nontrivial_Euler_readback': encode(result['Euler']),
            'all_four_original_boundary_fluxes': encode(result['boundary_flux']),
            'direct_actual_density_derivatives_all16': 'equal envelope force',
            'differentiated_original_Lorentz_equations_all96': '0',
            'canonical_temporal_one_form_difference': 'exact delta F0 for independent16 deltae and24 deltaOmega',
            'Euler_formula': 'force_a=-3 d_a det+1/2 Omega*^T(d_a H)Omega*+Omega*^T(d_a G)de+Omega*^T(d_a j); Euler=force-sum_mu partial_mu(G_mu^T Omega*)',
            'constrained_Hamilton_equivalence': 'on Pi=Mv+b and v=Q(Pi-b)+Zlambda, differentiate H_c(Pi(v,x),x)=Pi(v,x).v-L(v,x) and Z^T(Pi-b)=0: partial_x(H_c+lambda.constraint)=-partial_x L; together with partial_Pi H_total=v this reproduces the original Euler equation',
            'scope': 'original gravity BF/simplicity plus its full independent-dual Lorentz-current contribution; other original gauge/scalar/free-Dirac coframe forces add separately'}


def main():
    began = time.monotonic()
    receipt = json.loads((HERE/'source_lorentz_contact.json').read_text())
    audit = json.loads((HERE/'independent_source_lorentz_contact.json').read_text())
    assert receipt['root'] == ROOT_ID
    assert audit['verdict'] == 'CERTIFIED_UNTRUNCATED_SOURCE_LORENTZ_ELIMINATION_AND_FULL_REAL_MATTER_CONTACT_COEFFICIENTS'
    for record in (receipt, audit):
        for name, digest in record['input_sha256'].items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    model = SourceCoframeLegendre()
    generic = certify_generic(model)
    print('PASS original generic16 coframe kinetic factorization,metric inverse and complete boundary flux', flush=True)
    frames = certify_frames(model)
    print('PASS source/non-diagonal/both orientation/null charts:rank6/10 constraints or rank4/12 constraints', flush=True)
    matter = certify_matter_and_energy(model)
    print('PASS actual independent-dual momentum shift,all16 Legendre derivatives and total Hamiltonian', flush=True)
    euler = certify_Euler(model, matter)
    print('PASS complete source coframe/matter jets:all16 Euler forces,96 differentiated Lorentz rows and canonical boundary', flush=True)
    paths = [HERE/name for name in ('source_coframe_legendre.py','source_lorentz_contact.py',
              'source_lorentz_contact.json','independent_source_lorentz_contact.json')]
    bindings = dict(receipt['input_sha256'])
    bindings.update({str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths})
    output = {'root': ROOT_ID, 'source_sha256': receipt['source_sha256'], 'input_sha256': bindings,
              'scope': 'ORIGINAL_NONLINEAR_COFRAME_LEGENDRE_PRIMARY_CONSTRAINTS_VELOCITY_QUOTIENT_AND_EULER_WITH_BF_BOUNDARY',
              'generic_source_geometry': generic, 'exact_frame_consumers': frames,
              'full_matter_momentum_and_energy': matter, 'original_Euler_and_boundary_consumer': euler,
              'public_API': 'SourceCoframeLegendre.{geometry,currents,momentum,constraints,velocity,hamiltonian,euler,boundary_flux}',
              'old_Jacobi121_used_as_nonlinear_producer': False,
              'source_matter_momentum_shift_discarded': False,
              'original_temporal_boundary_contact_discarded': False,
              'new_source_occurrence': False,
              'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'source_coframe_legendre.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS original nonlinear coframe Legendre/Euler producer', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
