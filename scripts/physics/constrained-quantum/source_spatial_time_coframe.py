#!/usr/bin/env python3
"""Original coordinate defect generates the four temporal-coframe rates.

The native gauge Hodge is retained. Its coordinate defect is differentiated
after solving the original Maxwell electric equations, including the live
coframe dependence of the constitutive map. All other original density terms
have the coordinate-density transformation used in the Noether identity.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, decode
from source_gauge_legendre import SourceGaugeLegendre, contraction, rational
from source_lorentz_contact import (
    SourceLorentzContact, clean, equal, encode, PAIRS, ETA, WEDGE, GAMMA, wedge_matrix,
)


def exterior_generator(M):
    return s.Matrix(6, 6, lambda i, j:
        M[PAIRS[i][0], PAIRS[j][0]]*int(PAIRS[i][1] == PAIRS[j][1])+
        int(PAIRS[i][0] == PAIRS[j][0])*M[PAIRS[i][1], PAIRS[j][1]]-
        M[PAIRS[i][0], PAIRS[j][1]]*int(PAIRS[i][1] == PAIRS[j][0])-
        int(PAIRS[i][0] == PAIRS[j][1])*M[PAIRS[i][1], PAIRS[j][0]])


def coordinate_matrix(mu, nu):
    M = s.zeros(4)
    M[nu, mu] = 1
    return M


class SourceSpatialTimeCoframe:
    def __init__(self):
        self.gauge = SourceGaugeLegendre()
        self.coordinate_generators = [exterior_generator(coordinate_matrix(mu, nu))
                                      for mu in range(4) for nu in range(4)]

    def defect_kernel(self, K, mu, nu):
        T = self.coordinate_generators[4*mu+nu]
        S = T+T.T
        return clean(S*K+K*S-2*int(mu == nu)*K)

    def defect(self, e, F):
        # Q is a density readout; it needs the original kernel, not an electric
        # inverse along a symbolic coframe curve.
        determinant = e.det()
        assert determinant != 0
        K = rational(self.gauge.at(self.gauge.kernel_numerator, e)/determinant)
        return clean(s.Matrix(4, 4, lambda mu, nu:
            contraction(F, self.defect_kernel(K, mu, nu)*F*self.gauge.gram)/2))

    def kernel_derivative(self, e, direction):
        direction = s.Matrix(list(direction))
        g = self.gauge
        K = g.constitutive(e)['kernel']
        numerator = g.at(sum((direction[a]*g.dkernel[a] for a in range(16)), s.zeros(6)), e)
        ddet = contraction(g.at(g.ddet, e), direction)
        return rational((numerator-K*ddet)/e.det())

    def defect_derivative(self, e, F, de, dF):
        K = self.gauge.constitutive(e)['kernel']
        dK = self.kernel_derivative(e, de)
        return clean(s.Matrix(4, 4, lambda mu, nu:
            contraction(F, self.defect_kernel(dK, mu, nu)*F*self.gauge.gram)/2+
            contraction(dF, self.defect_kernel(K, mu, nu)*F*self.gauge.gram)))

    def source_currents(self, e, phi, U, psi, chi):
        """Actual scalar70 and independent-dual252 currents, not free sources."""
        g = self.gauge
        h = s.Abs(e.det())*e.inv()*ETA*e.inv().T
        scalar_momenta = [sum((h[mu, nu]*U[nu] for nu in range(4)), s.zeros(70, 1))
                          for mu in range(4)]
        scalar = s.Matrix(4, 12, lambda mu, a:
            contraction(scalar_momenta[mu], g.rho70[a]*phi))
        # Exact tensor contraction preserves the original 63 internal entries.
        Psi, Chi = psi.reshape(4, 63), chi.reshape(4, 63)
        adj = e.adjugate()
        principal = [s.sign(e.det())*s.I*sum((adj[mu, b]*GAMMA[b] for b in range(4)), s.zeros(4))
                     for mu in range(4)]
        densities = [Psi*rho.T*Chi.T for rho in g.rho63]
        matter = s.Matrix(4, 12, lambda mu, a: s.expand(s.re(s.trace(principal[mu]*densities[a]))))
        return {'scalar': clean(scalar), 'matter': clean(matter), 'total': clean(scalar+matter)}

    def maxwell_rates(self, e, de_time, spatial_e, A, F, spatial_F, current):
        """Original Maxwell plus Bianchi; de_time includes the four live rates."""
        g = self.gauge
        data = g.constitutive(e)
        assert data['metric'][0, 0] != 0
        K, inverse = data['kernel'], data['electric_inverse']
        P = clean(K*F*g.gram)
        dP = [clean((self.kernel_derivative(e, spatial_e[i])*F+K*spatial_F[i])*g.gram)
              for i in range(3)]
        electric_momentum_rate = s.zeros(3, 12)
        for i in range(1, 4):
            row = g.ad(A[0, :]).T*P[i-1, :].T+current[i, :].T
            for j in range(1, 4):
                row += (-g.ordered_pair(dP[j-1], j, i)+
                        g.ad(A[j, :]).T*g.ordered_pair(P, j, i))
            electric_momentum_rate[i-1, :] = row.T
        magnetic_rate = s.zeros(3, 12)
        for row, (i, j) in enumerate(PAIRS[3:]):
            magnetic_rate[row, :] = (spatial_F[i-1][j-1, :].T-
                spatial_F[j-1][i-1, :].T+
                g.bracket(A[i, :], F[j-1, :])-
                g.bracket(A[j, :], F[i-1, :])-
                g.bracket(A[0, :], F[row+3, :])).T
        dK = self.kernel_derivative(e, de_time)
        electric_rate = clean(inverse*(electric_momentum_rate*g.gram_inverse-
                              (dK*F)[:3, :]-data['mixed']*magnetic_rate))
        rate = clean(electric_rate.col_join(magnetic_rate))
        actual_momentum_rate = clean((dK*F+K*rate)*g.gram)
        equal(actual_momentum_rate[:3, :], electric_momentum_rate)
        return {'curvature_rate': rate, 'curvature_momentum_rate': actual_momentum_rate,
                'electric_momentum_rate': clean(electric_momentum_rate)}

    def time_minor(self, e, F):
        """Coefficient after Maxwell elimination, not the fixed-F derivative."""
        data = self.gauge.constitutive(e)
        inverse = data['electric_inverse']
        columns, fixed, responses = [], [], []
        for a in range(4):
            de = s.zeros(4); de[a, 0] = 1
            dK = self.kernel_derivative(e, de)
            dF = s.zeros(6, 12)
            dF[:3, :] = clean(-inverse*(dK*F)[:3, :])
            fixed.append(self.defect_derivative(e, F, de, s.zeros(6, 12))[0, :].T)
            columns.append(self.defect_derivative(e, F, de, dF)[0, :].T)
            responses.append(dF)
            equal((dK*F+data['kernel']*dF)[:3, :], s.zeros(3, 12))
        return {'matrix': clean(s.Matrix.hstack(*columns)),
                'fixed_curvature_derivative': clean(s.Matrix.hstack(*fixed)),
                'Maxwell_curvature_responses': responses}

    def solve_time_rates(self, e, spatial_velocity, spatial_e, A, F, spatial_F,
                         phi, U, psi, chi):
        """First-spatial-jet etime producer on det(time_minor) != 0."""
        assert spatial_velocity.shape == (4, 4)
        equal(spatial_velocity[:, 0], s.zeros(4, 1))
        current = self.source_currents(e, phi, U, psi, chi)
        base = self.maxwell_rates(e, spatial_velocity, spatial_e, A, F, spatial_F, current['total'])
        residual = self.defect_derivative(e, F, spatial_velocity, base['curvature_rate'])[0, :].T
        for i in range(3):
            residual += self.defect_derivative(e, F, spatial_e[i], spatial_F[i])[i+1, :].T
        minor = self.time_minor(e, F)
        determinant = s.factor(minor['matrix'].det())
        if determinant == 0:
            raise ValueError('This temporal-coframe chart requires the generated Maxwell time minor.')
        u = clean(minor['matrix'].inv()*(-residual))
        whole_velocity = spatial_velocity.copy(); whole_velocity[:, 0] = u
        actual = self.maxwell_rates(e, whole_velocity, spatial_e, A, F, spatial_F, current['total'])
        divergence = self.defect_derivative(e, F, whole_velocity, actual['curvature_rate'])[0, :].T
        for i in range(3):
            divergence += self.defect_derivative(e, F, spatial_e[i], spatial_F[i])[i+1, :].T
        equal(divergence, s.zeros(4, 1))
        return {'time_rates': u, 'coframe_velocity': clean(whole_velocity),
                'Maxwell': actual, 'current': current, 'forcing': clean(residual),
                'time_matrix': minor['matrix'], 'time_determinant': determinant,
                'coordinate_defect_divergence': clean(divergence)}


def certify_density_covariance(model):
    g = model.gauge
    e, X, det = g.e, g.X, g.det
    adj = e.adjugate()
    hnum = clean(adj*ETA*adj.T)
    count = 0
    for mu in range(4):
        for nu in range(4):
            M = coordinate_matrix(mu, nu)
            T = exterior_generator(M)
            de = e*M
            dX = clean(sum((de[a]*X.diff(e[a]) for a in range(16)), s.zeros(6)))
            equal(dX, X*T)
            equal(T*WEDGE+WEDGE*T.T, s.trace(M)*WEDGE)
            equal(T.T*WEDGE+WEDGE*T, s.trace(M)*WEDGE)
            ddet = contraction(g.ddet, s.Matrix(list(de)))
            assert s.expand(ddet-s.trace(M)*det) == 0
            dadj = clean(sum((de[a]*adj.diff(e[a]) for a in range(16)), s.zeros(4)))
            equal(dadj, s.trace(M)*adj-M*adj)
            dhnum = clean(dadj*ETA*adj.T+adj*ETA*dadj.T)
            equal(dhnum, 2*s.trace(M)*hnum-M*hnum-hnum*M.T)
            dKnum = clean(sum((de[a]*g.dkernel[a] for a in range(16)), s.zeros(6)))
            equal(dKnum, T.T*g.kernel_numerator+g.kernel_numerator*T)
            # Native Lg plus the ordinary covariant two-form variation.
            raw_defect = dKnum+T*g.kernel_numerator+g.kernel_numerator*T.T-2*s.trace(M)*g.kernel_numerator
            equal(raw_defect, model.defect_kernel(g.kernel_numerator, mu, nu))
            count += 1
    return {'all16_independent_coordinate_gradient_generators': count,
            'live_coframe_variables': 16,
            'original_gravity_BF_simplicity_density': 'Every row two-form transforms by right multiplication with wedge2(M); T W+W T^T=tr(M)W gives weight1 for all original B, multiplier and curvature terms. B=J wedge2(e) respects the same transformation.',
            'gravity_potential': 'delta(-3 det e)=tr(M)*(-3 det e), with the oriented determinant retained',
            'original_scalar70_density': 'delta(h)=tr(M)h-Mh-hM^T and delta(U)=M^T U cancel to density weight1; the original scalar potential uses the same volume weight',
            'original_full252_independent_dual_density': 'delta(adj(e))=tr(M)adj(e)-M adj(e) cancels every covector derivative and connection term; Yukawa is a coordinate scalar times |det e|, for independent chi and both real branches',
            'source_gauge_only_defect': 'Q^mu_nu=1/2 <F,[(T+T^T)K+K(T+T^T)-2 delta_mu_nu K]F>, T=wedge2_generator(E_nu_mu)',
            'full_auxiliary_gauge_BF_envelope': 'The already generated auxiliary Euler WF-sigma W star B=0 removes the difference between transforming B and differentiating B(e,F); hence this is the original BF defect on its exact auxiliary graph.',
            'local_coordinate_second_derivatives': 'The antisymmetric curvature/torsion derivatives cancel A_rho*(partial_mu partial_nu xi^rho-partial_nu partial_mu xi^rho) identically; no second coordinate jet remains.',
            'original_boundary_flux': 'The identity is derived before gravity BF integration by parts; the certified original four BF boundary fluxes are retained when returning to the common Hamiltonian.'}


def source_state(model):
    active = json.loads((BASE/'active-gauge/receipt.json').read_bytes())['actual_background']
    e = s.Matrix(active['coframe']).applyfunc(s.sympify)
    A = s.Matrix(active['gauge_connection']).applyfunc(s.sympify)
    return e, A, model.gauge.curvature(A, s.zeros(4, 48))


def certify_source_minor(model):
    e, A, F = source_state(model)
    Q = model.defect(e, F)
    minor = model.time_minor(e, F)
    expected = s.diag(-s.Rational(18, 5), *[-2*s.sqrt(30)/3]*3)
    equal(minor['matrix'], expected)
    assert s.simplify(expected.det()) == 32*s.sqrt(30)
    assert clean(minor['matrix']-minor['fixed_curvature_derivative']).todok()
    previous = json.loads((HERE/'source_homogeneous_canonical_flow.json').read_bytes())
    J4 = decode(previous['analytic_Cauchy_source_chart']['source_four_time_Jacobian'])
    equal(minor['matrix'], e.T*J4)
    return {'source_coframe': encode(e), 'source_connection': encode(A), 'source_curvature': encode(F),
            'source_coordinate_defect': encode(Q), 'Maxwell_eliminated_time_matrix': encode(expected),
            'time_determinant': str(s.simplify(expected.det())),
            'fixed_F_derivative': encode(minor['fixed_curvature_derivative']),
            'all4_Maxwell_curvature_responses': [encode(v) for v in minor['Maxwell_curvature_responses']],
            'omitting_Maxwell_response_negative_control_nonzero': True,
            'original_homogeneous_J4_consumer': 'M4=e^T J4 exactly at the original source',
            'generated_local_chart': 'det(M4(e,F))!=0 contains an open neighborhood of the same source by real analyticity; the electric guard g00!=0 is retained'}


def certify_homogeneous_consumer(model):
    receipt = json.loads((HERE/'source_homogeneous_canonical_flow.json').read_bytes())
    fields = {name: decode(value) for name, value in receipt['datum'].items()}
    rates = {name: decode(value) for name, value in receipt['complete_rates'].items()}
    e, A, phi = fields['e'], fields['A'], fields['phi']
    g = model.gauge
    data = g.constitutive(e)
    F = g.curvature(A, s.zeros(4, 48))
    F[:3, :] = clean(data['electric_inverse']*(fields['Pi_A']*g.gram_inverse-data['mixed']*F[3:, :]))
    h = s.Abs(e.det())*e.inv()*ETA*e.inv().T
    Usp = [sum((A[i+1, a]*g.rho70[a]*phi for a in range(12)), s.zeros(70, 1)) for i in range(3)]
    U0 = clean((fields['Pi_phi']-sum((h[0, i+1]*Usp[i] for i in range(3)), s.zeros(70, 1)))/h[0, 0])
    E = SourceLorentzContact().matter_ports(e)['E']
    chi = clean(s.I*fields['p']*s.kronecker_product(E.inv(), s.eye(63)))
    spatial_velocity = rates['e'].copy(); spatial_velocity[:, 0] = s.zeros(4, 1)
    result = model.solve_time_rates(e, spatial_velocity, [s.zeros(4)]*3, A, F,
                                   [s.zeros(6, 12)]*3, phi, [U0, *Usp], fields['psi'], chi)
    equal(result['time_rates'], rates['e'][:, 0])
    equal(result['Maxwell']['electric_momentum_rate'], rates['Pi_A'])
    assert result['time_rates'].todok()
    return {'complete_nontrivial_homogeneous_datum_consumed': True,
            'source_four_generated_rates': encode(result['time_rates']),
            'all4_original_Hamiltonian_time_rates_recovered': True,
            'all36_original_gauge_momentum_rates_recovered': True,
            'actual_scalar_and_full252_independent_dual_currents': True,
            'coordinate_defect_divergence': encode(result['coordinate_defect_divergence'])}


def certify_spatial_jet_consumer(model):
    e, A, F = source_state(model)
    g = model.gauge
    # An actual connection second jet generates the curvature derivatives,
    # so spatial Bianchi is a source identity rather than free assigned rows.
    dA = s.zeros(4, 48)
    ddA = [s.zeros(4, 48) for _ in range(4)]
    for i in range(1, 4):
        for j in range(i, 4):
            row = s.Matrix(1, 48, lambda _, a: s.Rational((i+2*j+3*a)%7-3, 101))
            ddA[i][j, :] = row
            ddA[j][i, :] = row
    spatial_F = [clean(s.Matrix.vstack(*[
        ddA[i][mu, 12*nu:12*(nu+1)]-ddA[i][nu, 12*mu:12*(mu+1)]
        for mu, nu in PAIRS])) for i in range(1, 4)]
    spatial_e = [s.Matrix(4, 4, lambda a, b: s.Rational((i+2*a+b)%7-3, 113)) for i in range(3)]
    velocity = s.Matrix(4, 4, lambda a, b: 0 if b == 0 else s.Rational((3*a+b)%5-2, 127))
    source = json.loads((HERE/'source_homogeneous_canonical_flow.json').read_bytes())['datum']
    phi = decode(source['phi'])
    psi = s.Matrix([s.Rational((3*i+1)%7-3, 211)+s.I*s.Rational((5*i+2)%11-5, 223) for i in range(252)])
    chi = s.Matrix(1, 252, lambda _, i: s.Rational((7*i+1)%13-6, 227)+s.I*s.Rational((2*i+3)%7-3, 229))
    U = [s.Matrix([s.Rational((i+3*j)%7-3, 233) for j in range(70)]) for i in range(4)]
    result = model.solve_time_rates(e, velocity, spatial_e, A, F, spatial_F, phi, U, psi, chi)
    assert result['forcing'].todok() and result['time_rates'].todok()
    # Independent actual density curve verifies dQ and every spatial chain.
    epsilon = s.Symbol('epsilon', real=True)
    for i in range(3):
        de, dF = spatial_e[i], spatial_F[i]
        curved = model.defect(e+epsilon*de, F+epsilon*dF)
        direct = rational(curved.diff(epsilon).subs(epsilon, 0))
        equal(direct, model.defect_derivative(e, F, de, dF))
    return {'all252_primal_and_dual_components_live': True,
            'all70_scalar_components_and_four_covariant_jets_live': True,
            'spatial_curvature_jets_from_symmetric_connection_second_jet': True,
            'all3_spatial_Q_derivatives_checked_by_actual_curves': True,
            'nonzero_forcing': encode(result['forcing']), 'time_rates': encode(result['time_rates']),
            'time_minor': encode(result['time_matrix']),
            'Maxwell_and_coordinate_defect_equations_zero': True,
            'claim': 'Actual first-jet time-rate equation, not a solved spatial initial constraint datum or a complete PDE integral curve.'}


def main():
    started = time.monotonic()
    model = SourceSpatialTimeCoframe()
    covariance = certify_density_covariance(model)
    print('PASS generic16 coframe/all16 coordinate generators: original density covariance and native gauge defect', flush=True)
    minor = certify_source_minor(model)
    print('PASS actual Maxwell-eliminated etime minor det=32*sqrt(30), fixed-F negative control', flush=True)
    homogeneous = certify_homogeneous_consumer(model)
    print('PASS independent coordinate-defect producer recovers original homogeneous etime4 and gauge36 rates', flush=True)
    spatial = certify_spatial_jet_consumer(model)
    print('PASS actual spatial field jets/full252 currents: generated etime4, Maxwell and divQ zero', flush=True)
    inputs = [HERE/'source_spatial_time_coframe.py', HERE/'source_gauge_legendre.py', HERE/'source_lorentz_contact.py',
              HERE/'source_homogeneous_canonical_flow.json', HERE/'source_temporal_coframe_flux.json',
              BASE/'active-gauge/receipt.json']
    result = {'root': ROOT_ID, 'verdict': 'SOURCE_NATIVE_SPATIAL_TEMPORAL_COFRAME_RATE_CHART_GENERATED',
              'source_sha256': model.gauge.source_hashes,
              'density_covariance_and_defect': covariance, 'source_time_minor': minor,
              'original_homogeneous_consumer': homogeneous, 'actual_spatial_jet_consumer': spatial,
              'Noether_identity': 'E_A partial_nu q^A-partial_mu(E_A R^{A,mu}_nu)=-partial_mu Q^mu_nu',
              'temporal_constraint_transport': 'When all other original Euler equations hold: e[a,nu] partial_t F_a=partial_mu Q^mu_nu+F_a(partial_nu e[a,0]-partial_t e[a,nu]). Generated divQ=0 is a homogeneous linear transport of the original temporal constraints.',
              'first_order_dependency': 'etime rates use e,F and their first spatial derivatives, known spatial-coframe velocity, A, original scalar70 covariant jets and full252 independent matter; no second spatial derivative or derivative of an assigned target trajectory is input.',
              'proper_clock': 'tau=N*t, N=3*sqrt(30)/25, unchanged original coordinate time',
              'remaining_PDE_consumer': 'Construct the original18 spatial-Lorentz time equations from12 prolonged spatial torsion equations plus6 independent coframe Euler equations, and close all introduced constraints in the same first-order system.',
              'general_spatial_Cauchy_closed': False,
              'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
              'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs},
              'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_spatial_time_coframe.json').write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
