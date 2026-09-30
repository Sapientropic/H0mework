#!/usr/bin/env python3
"""Original P286 BF elimination, live-coframe gauge Legendre map and Gauss.

The original Hodge is X(e)^-1 J X(e), literally as defined in the source.
Consequently its electric block depends on g_00, not g^00.  The native12 Lie
pairing, full nonlinear curvature and original scalar/matter currents are
kept.  No inverse-metric Maxwell density is substituted for the source.
"""
from __future__ import annotations

import hashlib
import json
import sys
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, decode
from source_lorentz_contact import clean, equal, encode, ETA, PAIRS, J, WEDGE, GAMMA, wedge_matrix

sys.path.insert(0, str(BASE))
import exact_readout as source


def rational(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.cancel)


def contraction(A, B):
    return s.expand(sum(a*b for a, b in zip(A, B)))


def realify(matrix):
    a, b = matrix.applyfunc(s.re), matrix.applyfunc(s.im)
    return clean(a.row_join(-b).col_join(b.row_join(a)))


class SourceGaugeLegendre:
    def __init__(self):
        _, self.vacuum, degrees, self.source_hashes = source.parse_source(ROOT)
        raw = source.generators([(0, 1, 2), (3, 4)])
        self.labels = [label for label, _, _ in raw]
        self.fundamental = [s.Matrix(matrix)*(s.I if imaginary else 1) for _, imaginary, matrix in raw]
        self.gram = s.Matrix(12, 12, lambda a, b: self.native_pair(self.fundamental[a], self.fundamental[b]))
        self.gram_inverse = self.gram.inv()
        self.brackets = {}
        self.adjoint = []
        for a, A in enumerate(self.fundamental):
            ad = s.zeros(12)
            for b, B in enumerate(self.fundamental):
                commutator = A*B-B*A
                coefficients = self.gram_inverse*s.Matrix([self.native_pair(C, commutator)
                                                           for C in self.fundamental])
                equal(sum((coefficients[c]*self.fundamental[c] for c in range(12)), s.zeros(7)), commutator)
                ad[:, b] = coefficients
                for c, value in enumerate(coefficients):
                    if value:
                        self.brackets[a, b, c] = value
            self.adjoint.append(clean(ad))
        self.rho63 = [clean(s.diag(*[s.Matrix(source.exterior_action(matrix, degree))
                         *(s.I if imaginary else 1) for degree in degrees]))
                      for _, imaginary, matrix in raw]
        self.rho70 = [realify(s.Matrix(source.exterior_action(matrix, 4))*(s.I if imaginary else 1))
                      for _, imaginary, matrix in raw]
        self.sigma = s.Rational(1, 2)
        self.e = s.Matrix(4, 4, s.symbols('e0:16', real=True))
        self.det = s.expand(self.e.det())
        self.X = wedge_matrix(self.e)
        self.metric = self.e.T*ETA*self.e
        self.kernel_numerator = clean(-self.X.T*s.diag(-1, -1, -1, 1, 1, 1)*self.X/self.sigma)
        self.dkernel = [self.kernel_numerator.diff(x) for x in self.e]
        self.ddet = s.Matrix([s.diff(self.det, x) for x in self.e])

    @staticmethod
    def native_pair(A, B):
        # The last factor is the original U(1) scalar pairing. The mother7
        # trace counts its two opposite entries and would incorrectly give2.
        return s.expand(s.re(-s.trace(A[:3, :3]*B[:3, :3])-
                             s.trace(A[3:5, 3:5]*B[3:5, 3:5])-A[5, 5]*B[5, 5]))

    def at(self, matrix, e):
        return clean(matrix.xreplace(dict(zip(self.e, e))))

    def bracket(self, A, B):
        A, B = list(A), list(B)
        result = s.zeros(12, 1)
        for (a, b, c), value in self.brackets.items():
            result[c] += value*A[a]*B[b]
        return clean(result)

    def ad(self, A):
        return clean(sum((value*matrix for value, matrix in zip(A, self.adjoint)), s.zeros(12)))

    def constitutive(self, e):
        determinant = s.factor(e.det())
        assert determinant != 0
        kernel = rational(self.at(self.kernel_numerator, e)/determinant)
        hodge = clean(-self.sigma*WEDGE*kernel)
        electric, mixed, magnetic = kernel[:3, :3], kernel[:3, 3:], kernel[3:, 3:]
        metric = clean(e.T*ETA*e)
        if metric[0, 0] != 0:
            electric_inverse = rational(-self.sigma*determinant/metric[0, 0]*metric.inv()[1:, 1:])
            null = s.zeros(3, 0)
            chart = 'g_00!=0'
        else:
            pivots = electric.rref()[1]
            select = s.eye(3)[:, list(pivots)]
            electric_inverse = rational(select*(select.T*electric*select).inv()*select.T)
            null = s.Matrix.hstack(*electric.nullspace())
            chart = 'g_00=0; source electric rank1 quotient'
        return {'det': determinant, 'metric': metric, 'Hodge': hodge, 'kernel': kernel,
                'electric': electric, 'mixed': mixed, 'magnetic': magnetic,
                'electric_inverse': electric_inverse, 'electric_null': null, 'chart': chart}

    def auxiliary(self, e, curvature):
        return clean(-self.constitutive(e)['Hodge']*curvature/self.sigma)

    def original_BF_density(self, e, curvature, auxiliary):
        hodge = self.constitutive(e)['Hodge']
        return contraction(auxiliary, WEDGE*curvature*self.gram)-self.sigma/2*contraction(auxiliary, WEDGE*hodge*auxiliary*self.gram)

    def curvature(self, connection, derivative):
        """derivative[mu,12*nu+a]=partial_mu A_nu^a, all48 connection fields."""
        assert connection.shape == (4, 12) and derivative.shape == (4, 48)
        return clean(s.Matrix.vstack(*[(derivative[mu, 12*nu:12*(nu+1)]-
            derivative[nu, 12*mu:12*(mu+1)]+self.bracket(connection[mu, :], connection[nu, :]).T)
            for mu, nu in PAIRS]))

    def lagrangian(self, e, connection, derivative):
        F = self.curvature(connection, derivative)
        return contraction(F, self.constitutive(e)['kernel']*F*self.gram)/2

    def curvature_momentum(self, e, curvature):
        return clean(self.constitutive(e)['kernel']*curvature*self.gram)

    def momentum(self, e, connection, derivative):
        return self.curvature_momentum(e, self.curvature(connection, derivative))[:3, :]

    def spatial_data(self, connection, spatial_derivative):
        assert spatial_derivative.shape == (3, 48)
        derivative = s.zeros(4, 48)
        derivative[1:, :] = spatial_derivative
        F = self.curvature(connection, derivative)
        return clean(F[3:, :]), clean(-F[:3, :])

    def velocity(self, e, connection, spatial_derivative, momentum, null_velocity=None):
        data = self.constitutive(e)
        magnetic, D_A0 = self.spatial_data(connection, spatial_derivative)
        shifted = momentum*self.gram_inverse-data['mixed']*magnetic
        value = data['electric_inverse']*shifted+D_A0
        if null_velocity is not None:
            assert null_velocity.shape == (data['electric_null'].cols, 12)
            value += data['electric_null']*null_velocity
        return clean(value)

    def constraints(self, e, connection, spatial_derivative, momentum):
        data = self.constitutive(e)
        magnetic, _ = self.spatial_data(connection, spatial_derivative)
        return clean(data['electric_null'].T*(momentum*self.gram_inverse-data['mixed']*magnetic))

    def hamiltonian(self, e, connection, spatial_derivative, momentum):
        data = self.constitutive(e)
        magnetic, D_A0 = self.spatial_data(connection, spatial_derivative)
        shifted = momentum*self.gram_inverse-data['mixed']*magnetic
        return s.expand(contraction(shifted, data['electric_inverse']*shifted*self.gram)/2-
            contraction(magnetic, data['magnetic']*magnetic*self.gram)/2+contraction(momentum, D_A0))

    def gauss(self, connection, momentum, spatial_momentum_derivative):
        """Covector divergence in the original nonorthonormal Lie coordinates."""
        return clean(sum((spatial_momentum_derivative[i][i, :].T-
            self.ad(connection[i+1, :]).T*momentum[i, :].T
            for i in range(3)), s.zeros(12, 1)))

    @staticmethod
    def ordered_pair(field, mu, nu):
        if mu == nu:
            return s.zeros(12, 1)
        if (mu, nu) in PAIRS:
            return field[PAIRS.index((mu, nu)), :].T
        return -field[PAIRS.index((nu, mu)), :].T

    def scalar_current(self, e, phi, derivative, connection):
        volume = s.Abs(e.det())
        density_metric = clean(volume*e.inv()*ETA*e.inv().T)
        U = [derivative[mu]+sum((connection[mu, a]*self.rho70[a]*phi for a in range(12)), s.zeros(70, 1))
             for mu in range(4)]
        momenta = [sum((density_metric[mu, nu]*U[nu] for nu in range(4)), s.zeros(70, 1)) for mu in range(4)]
        current = s.Matrix(4, 12, lambda mu, a: contraction(momenta[mu], self.rho70[a]*phi))
        return clean(current), list(map(clean, momenta))

    def matter_vertices(self, e):
        adj, orientation = e.adjugate(), s.sign(e.det())
        spin = [orientation*sum((adj[mu, a]*s.I*GAMMA[a] for a in range(4)), s.zeros(4)) for mu in range(4)]
        return [[clean(s.kronecker_product(spin[mu], rho)) for rho in self.rho63] for mu in range(4)]

    def matter_current(self, e, primal, dual):
        vertices = self.matter_vertices(e)
        return s.Matrix(4, 12, lambda mu, a: s.expand(s.re((dual*vertices[mu][a]*primal)[0])))

    def euler(self, e, de, connection, derivative, second_derivative, scalar_current=None, matter_current=None):
        """Exact connection Euler on a full field jet, with original currents."""
        data = self.constitutive(e)
        F = self.curvature(connection, derivative)
        P = self.curvature_momentum(e, F)
        dP = []
        for mu in range(4):
            dA = derivative[mu, :].reshape(4, 12)
            dF = s.Matrix.vstack(*[(second_derivative[mu][rho, 12*nu:12*(nu+1)]-
                 second_derivative[mu][nu, 12*rho:12*(rho+1)]+
                 self.bracket(dA[rho, :], connection[nu, :]).T+
                 self.bracket(connection[rho, :], dA[nu, :]).T) for rho, nu in PAIRS])
            dk_num = self.at(sum((de[mu, a]*self.dkernel[a] for a in range(16)), s.zeros(6)), e)
            ddet = contraction(self.at(self.ddet, e), de[mu, :].T)
            dK = rational(dk_num/data['det']-data['kernel']*ddet/data['det'])
            dP.append(clean((dK*F+data['kernel']*dF)*self.gram))
        result = s.zeros(4, 12)
        for nu in range(4):
            value = sum((-self.ordered_pair(dP[mu], mu, nu)+
                         self.ad(connection[mu, :]).T*self.ordered_pair(P, mu, nu)
                         for mu in range(4)), s.zeros(12, 1))
            result[nu, :] = value.T
        if scalar_current is not None:
            result += scalar_current
        if matter_current is not None:
            result += matter_current
        return {'curvature': F, 'curvature_momentum': P, 'momentum_derivatives': dP,
                'Euler': clean(result), 'Gauss': clean(result[0, :].T),
                'Hamiltonian_spatial_boundary_flux': clean(P[:3, :]*connection[0, :].T)}


def certify_geometry(model):
    equal(model.X.T*WEDGE*model.X, model.det*WEDGE)
    equal(-model.sigma*model.kernel_numerator, wedge_matrix(model.metric))
    numerator_star = clean(-model.sigma*WEDGE*model.kernel_numerator)
    equal(numerator_star*numerator_star, -model.det**2*s.eye(6))
    equal(model.kernel_numerator, model.kernel_numerator.T)
    g = s.zeros(4)
    parameters = s.symbols('g0:10', real=True)
    for (i, j), value in zip(((i, j) for i in range(4) for j in range(i, 4)), parameters):
        g[i, j] = g[j, i] = value
    S = g[0, 0]*g[1:, 1:]-g[1:, 0]*g[0, 1:]
    assert s.expand(S.det()-g[0, 0]**2*g.det()) == 0
    equal(S*g.adjugate()[1:, 1:], g[0, 0]*g.det()*s.eye(3))
    return {'Hodge_definition': 'X(e)^-1 J X(e), X=coframeWedge(e)',
            'generic16_Hodge_square': '-I6 after exact denominator clearing',
            'reduced_kernel': '-W Hodge/sigma=-wedge²(e^T eta e)/(sigma det e)',
            'electric_block': '-(g_00 g_ij-g_0i g_0j)/(sigma det e)',
            'electric_determinant': 'g_00^2/(sigma^3 det e)',
            'electric_inverse': '-sigma det e/g_00 times (g^-1)_spatial',
            'noncharacteristic_gauge_guard': 'g_00!=0; distinct from the scalar/Dirac covector-time guard g^00!=0',
            'null_electric_rank': 1, 'null_additional_primary_constraints': 24,
            'all_A0_primary_momenta': '12 identically zero',
            'gravity_orientation_retained': 'signed det(e), not abs(det(e))',
            'kinetic_kernel_numerator': encode(model.kernel_numerator)}


def certify_Lie(model):
    assert model.labels[-1] == 'Y' and model.gram[11, 11] == 1
    assert s.re(-s.trace(model.fundamental[11]**2)) == 2
    assert any(model.gram[i, j] != 0 for i in range(12) for j in range(12) if i != j)
    assert model.gram.det() != 0
    for a, A in enumerate(model.adjoint):
        equal(A.T*model.gram+model.gram*A, s.zeros(12))
        for b, B in enumerate(model.adjoint):
            equal(A*B-B*A, sum((A[c, b]*model.adjoint[c] for c in range(12)), s.zeros(12)))
    return {'native_generator_labels': model.labels, 'native_Lie_Gram': encode(model.gram),
            'native_Lie_Gram_inverse': encode(model.gram_inverse),
            'all_original_brackets': [[a, b, c, str(v)] for (a, b, c), v in sorted(model.brackets.items())],
            'all144_original_matrix_commutators_reconstructed': True,
            'all12_native_pairing_invariance_and144_Jacobi_maps': True,
            'hypercharge_native_pairing': 1, 'hypercharge_mother_trace_negative_control': 2,
            'independent_mother48_gauge_added': False}


def certify_variation_and_Legendre(model):
    N = 3*s.sqrt(30)/25
    frames = [s.diag(N, 1, 1, 1), s.diag(-N, 1, 1, 1),
              s.Matrix([[2, 1, 0, 0], [0, 2, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]]),
              s.Matrix([[1, 1, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]),
              s.Matrix([[1, 0, 0, 0], [1, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])]
    frame_results = []
    for e in frames:
        data = model.constitutive(e)
        equal(wedge_matrix(e)*data['Hodge'], J*wedge_matrix(e))
        equal(data['electric']*data['electric_inverse']*data['electric'], data['electric'])
        equal(data['electric']*data['electric_null'], s.zeros(3, data['electric_null'].cols))
        frame_results.append({'coframe': encode(e), 'det': str(data['det']),
            'g00': str(data['metric'][0, 0]), 'g_inverse00': str(data['metric'].inv()[0, 0]),
            'electric_rank': data['electric'].rank(), 'chart': data['chart'],
            'electric': encode(data['electric']), 'mixed': encode(data['mixed']),
            'magnetic': encode(data['magnetic']), 'extra_constraint_frame': encode(data['electric_null'])})
    equal(model.constitutive(frames[0])['electric'], N/model.sigma*s.eye(3))
    equal(model.constitutive(frames[0])['magnetic'], -1/(N*model.sigma)*s.eye(3))
    assert frame_results[3]['g_inverse00'] == '0' and frame_results[3]['electric_rank'] == 3
    assert frame_results[4]['g00'] == '0' and frame_results[4]['electric_rank'] == 1

    # Whole native12 density, with every electric/magnetic and auxiliary
    # coordinate independent, proves exact constitutive elimination.
    e = frames[2]
    F = s.Matrix(6, 12, s.symbols('F0:72', real=True))
    B = s.Matrix(6, 12, s.symbols('B0:72', real=True))
    BF = model.original_BF_density(e, F, B)
    eliminated = model.auxiliary(e, F)
    equations = s.Matrix(6, 12, [s.diff(BF, b) for b in B])
    equal(equations, WEDGE*(F-model.sigma*model.constitutive(e)['Hodge']*B)*model.gram)
    substitution = dict(zip(B, eliminated))
    equal(equations.xreplace(substitution), s.zeros(6, 12))
    reduced = contraction(F, model.constitutive(e)['kernel']*F*model.gram)/2
    assert s.expand(BF.xreplace(substitution)-reduced) == 0

    A = s.Matrix(4, 12, s.symbols('A0:48', real=True))
    P = s.Matrix(6, 12, s.symbols('P0:72', real=True))
    F0 = model.curvature(A, s.zeros(4, 48))
    algebraic = contraction(P, F0)
    for nu in range(4):
        expected = sum((model.ad(A[mu, :]).T*model.ordered_pair(P, mu, nu)
                        for mu in range(4)), s.zeros(12, 1))
        equal(s.Matrix([s.diff(algebraic, A[nu, a]) for a in range(12)]), expected)

    actual_A = s.Matrix(4, 12, lambda i, j: s.Rational((i*11+j*3)%13-6, 17))
    spatial = s.Matrix(3, 48, lambda i, j: s.Rational((i*7+j*2)%11-5, 19))
    velocity = s.Matrix(3, 12, s.symbols('velocity0:36', real=True))
    derivative = s.zeros(4, 48); derivative[1:, :] = spatial; derivative[0, 12:] = velocity.reshape(1, 36)
    pi = model.momentum(e, actual_A, derivative)
    L = model.lagrangian(e, actual_A, derivative)
    equal(s.Matrix(3, 12, [s.diff(L, v) for v in velocity]), pi)
    equal(model.velocity(e, actual_A, spatial, pi), velocity)
    assert s.expand(model.hamiltonian(e, actual_A, spatial, pi)-contraction(pi, velocity)+L) == 0
    null_e = frames[-1]
    null_pi = model.momentum(null_e, actual_A, derivative)
    equal(model.constraints(null_e, actual_A, spatial, null_pi), s.zeros(2, 12))
    null_L = model.lagrangian(null_e, actual_A, derivative)
    assert s.expand(model.hamiltonian(null_e, actual_A, spatial, null_pi)-contraction(null_pi, velocity)+null_L) == 0
    return {'exact_frames': frame_results, 'all72_original_auxiliary_Euler_coordinates': '0 after B=-starF/sigma',
            'all72_untruncated_reduced_density_coefficients': 'match original BF after elimination',
            'all48_connection_algebraic_variations': 'ad(A_mu)^T P^{mu,nu} from original full brackets',
            'all36_independent_velocity_momenta_and_inverse': 'exact',
            'nonnull_and_null_constrained_Legendre_energy': 'Pi.dotA-L=H_local on the respective constraint surface',
            'velocity': 'dotA_i=P_electric^-1(Pi G_native^-1-Q_mixed Bmag)_i+D_i A0, plus the source null frame on g00=0',
            'Hamiltonian': '1/2 <Pi G^-1-QB,P_electric^-1(Pi G^-1-QB)>_G-1/2 <B,R_magnetic B>_G+sum_i Pi_i^T D_i A0'}


def certify_Euler_currents_Gauss(model):
    active = json.loads((BASE/'active-gauge/receipt.json').read_text())
    occupied = json.loads((BASE/'occupied-response/receipt.json').read_text())
    vertices = json.loads((BASE/'matter-vertices/receipt.json').read_text())
    e0 = s.Matrix(active['actual_background']['coframe']).applyfunc(s.sympify)
    A0 = s.Matrix(active['actual_background']['gauge_connection']).applyfunc(s.sympify)
    psi = decode(occupied['occupied_frame'])*s.Matrix(active['actual_background']['primal_H']).applyfunc(s.sympify)
    chi = s.sqrt(2)*psi.T
    raw_vertices = {(item['group'], tuple(item['coordinate'])): decode(item['operator']) for item in vertices['primitive_vertices']}
    generated = model.matter_vertices(e0)
    for mu in range(4):
        for a in range(12):
            equal(generated[mu][a], raw_vertices['gauge_A', (mu, a)])
    # Recover the actual scalar vacuum using the original exterior basis.
    import itertools
    words = list(itertools.combinations(range(7), 4))
    phi0 = s.Matrix([model.vacuum.get(word, 0) for word in words]+[0]*35)
    scalar0, _ = model.scalar_current(e0, phi0, [s.zeros(70, 1)]*4, A0)
    matter0 = model.matter_current(e0, psi, chi)
    original = model.euler(e0, s.zeros(4, 16), A0, s.zeros(4, 48),
                           [s.zeros(4, 48)]*4, scalar0, matter0)
    equal(scalar0, s.zeros(4, 12))
    equal(original['Euler'], s.zeros(4, 12))

    # Nonconstant full source jets make derivative terms and every Lie sector
    # observable. They do not replace the generic density/variation identities.
    e = s.Matrix([[2, 1, 0, 0], [0, 2, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    A = s.Matrix(4, 12, lambda i, j: s.Rational((i*11+j*3)%13-6, 17))
    dA = s.Matrix(4, 48, lambda i, j: s.Rational((i*7+j*2)%11-5, 19))
    ddA = [s.Matrix(4, 48, lambda rho, j: s.Rational(((mu+rho)*5+j)%7-3, 23)) for mu in range(4)]
    de = s.Matrix(4, 16, lambda i, j: s.Rational((i*3+j)%9-4, 29))
    phi = s.Matrix([s.Rational(i+1, 71) for i in range(70)])
    dphi = [s.Matrix([s.Rational((i+1)*(mu+1), 73) for i in range(70)]) for mu in range(4)]
    scalar, scalar_momenta = model.scalar_current(e, phi, dphi, A)
    matter = model.matter_current(e, psi, chi)
    result = model.euler(e, de, A, dA, ddA, scalar, matter)
    gauge = model.euler(e, de, A, dA, ddA)
    Pi = result['curvature_momentum'][:3, :]
    spatial_dPi = [result['momentum_derivatives'][i+1][:3, :] for i in range(3)]
    Gauss = model.gauss(A, Pi, spatial_dPi)
    equal(gauge['Gauss'], Gauss)
    equal(result['Gauss'], Gauss+scalar[0, :].T+matter[0, :].T)
    # Original Re Dirac normalization, at the whole48 source current family.
    E4 = s.sign(e.det())*sum((e.adjugate()[0, a]*s.I*GAMMA[a] for a in range(4)), s.zeros(4))
    E = s.kronecker_product(E4, s.eye(63))
    canonical_p = -s.I*chi*E
    for a in range(12):
        time_W = -s.I*s.kronecker_product(s.eye(4), model.rho63[a])
        assert s.expand(s.re((canonical_p*time_W*psi)[0])+matter[0, a]) == 0
        assert s.expand(contraction(scalar_momenta[0], model.rho70[a]*phi)-scalar[0, a]) == 0
    # Original boundary and Gauss identity on independent A0, Pi and their
    # independent first jets; the native covector transpose is retained.
    a0 = s.Matrix(s.symbols('a0:12', real=True))
    pi = s.Matrix(3, 12, s.symbols('pi0:36', real=True))
    dpi = [s.Matrix(3, 12, s.symbols('dpi'+str(i)+'_0:36', real=True)) for i in range(3)]
    da0 = s.Matrix(3, 12, s.symbols('da0_0:36', real=True))
    value = sum(contraction(pi[i, :].T, da0[i, :].T+model.bracket(A[i+1, :], a0)) for i in range(3))
    divergence = sum(contraction(dpi[i][i, :].T, a0)+contraction(pi[i, :], da0[i, :]) for i in range(3))
    assert s.expand(value+(a0.T*model.gauss(A, pi, dpi))[0]-divergence) == 0
    assert result['Euler'] != s.zeros(4, 12)
    return {'actual_source_curvature': encode(original['curvature']),
            'actual_source_auxiliary': encode(model.auxiliary(e0, original['curvature'])),
            'actual_source_scalar_current': encode(scalar0), 'actual_source_matter_current': encode(matter0),
            'actual_source_all48_connection_Euler': '0',
            'all48_full252_current_vertices': 'equal original source primitive vertices',
            'full70_scalar_and_full252_matter_Gauss': 'generated from original covariant derivatives and Re independent-dual action',
            'full_test_Euler': encode(result['Euler']), 'full_test_Gauss': encode(result['Gauss']),
            'test_boundary_flux': encode(result['Hamiltonian_spatial_boundary_flux']),
            'field_Gauss': 'sum_i(partial_i Pi_i-ad(A_i)^T Pi_i), Pi is a native Lie covector',
            'total_Gauss': 'field_Gauss + Pi_scalar^T rho70 phi + Re chi V0 psi',
            'canonical_Dirac_charge': 'Re p(-i rho252)psi=-Re chi V0 psi, with p=-i chi E; original half/Re branches unchanged',
            'original_connection_Euler': '-sum_mu(partial_mu P^{mu,nu}-ad(A_mu)^T P^{mu,nu})+j_scalar^nu+j_matter^nu',
            'connection_variation_boundary': 'theta^mu=sum_nu P^{mu,nu}.delta A_nu',
            'Hamiltonian_boundary_identity': 'sum_i Pi_i.D_i A0=-A0.field_Gauss+sum_i partial_i(Pi_i.A0)',
            'full_Hamiltonian_A0_coefficient': '-total_Gauss after the source scalar and Dirac Legendre maps',
            'first_class_constraint_propagation_claimed': False}


def main():
    began = time.monotonic()
    model = SourceGaugeLegendre()
    geometry = certify_geometry(model)
    lie = certify_Lie(model)
    print('PASS literal original Hodge on generic16 coframe and complete native12 Lie Gram/brackets', flush=True)
    legendre = certify_variation_and_Legendre(model)
    print('PASS all72 auxiliary/current coefficients,whole36 Legendre and distinct g00/g^00 null controls', flush=True)
    euler = certify_Euler_currents_Gauss(model)
    print('PASS actual source48 Euler,full70/full252 currents,original Gauss and retained boundary flux', flush=True)
    core = ROOT/'Lean/SaturationMonoid/PhysicsCore'
    paths = [core/name for name in ('StageNineGlobalIntegratedAction.lean','StageNineFormNativeMotherAction.lean',
        'StageNineDiracDualFormNativeMotherAction.lean','StageNineFormNativeGaugeWedge.lean',
        'StageNineFormNativeP286GaugeConstitutiveElimination.lean','StageNineP286GaugeConnectionPointwiseEquation.lean',
        'StageNineP286GaugeConnectionMomentumRegularity.lean')]
    paths += [BASE/name for name in ('exact_readout.py','active-gauge/receipt.json','matter-vertices/receipt.json',
               'occupied-response/receipt.json')]
    paths += [HERE/name for name in ('source_gauge_legendre.py','source_lorentz_contact.py')]
    bindings = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}
    output = {'root': ROOT_ID, 'source_sha256': model.source_hashes, 'input_sha256': bindings,
        'scope': 'ORIGINAL_UNTRUNCATED_NATIVE12_GAUGE_BF_ELIMINATION_LEGENDRE_EULER_AND_FULL_SOURCE_GAUSS',
        'source_coupling_sigma': '1/2 for all three source-generated coupling blocks',
        'source_geometry': geometry, 'native_Lie_algebra': lie,
        'original_auxiliary_and_Legendre': legendre, 'original_Euler_currents_Gauss_boundary': euler,
        'public_API': 'SourceGaugeLegendre.{constitutive,auxiliary,curvature,lagrangian,momentum,velocity,constraints,hamiltonian,gauss,scalar_current,matter_current,euler}',
        'inverse_metric_Maxwell_density_substituted': False, 'new_source_occurrence': False,
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'source_gauge_legendre.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS original gauge Legendre/Euler/Gauss producer', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
