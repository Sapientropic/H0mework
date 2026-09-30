#!/usr/bin/env python3
"""Independent raw-density coordinate defect and Maxwell time-column chart.

No candidate constructor is imported. Original two-form pullback coefficients
fix the coordinate defect. The full36 electric momentum equations are solved
before extracting the four coframe-rate coefficients.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_joint_temporal_rates import (
    RawSource, HERE, BASE, ROOT, ROOT_ID, PAIRS, SIGMA, W, ETA,
    bindings, clean, decode, encode, equal, eq, zero, dot, ordered, hodge,
    hodge_field_jet, lorentz_exterior)


class RawCoordinateDensity:
    def __init__(self):
        self.raw = RawSource()
        epsilon = s.Symbol('pullback_epsilon', real=True)
        self.M, self.T = [], []
        for mu in range(4):
            for nu in range(4):
                M = s.zeros(4); M[nu, mu] = 1
                self.M.append(M)
                self.T.append(lorentz_exterior(s.eye(4)+epsilon*M).diff(epsilon).subs(epsilon, 0))

    def kernel(self, e): return clean(-W*hodge(e)/SIGMA)

    def kernel_dot(self, e, de):
        _, derivative = hodge_field_jet(e, de, s.eye(6), s.zeros(6))
        return clean(-W*derivative/SIGMA)

    def reduced_pullback_kernel(self, K, index):
        M, T = self.M[index], self.T[index]
        covariant_constitutive = T.T*K+K*T-s.trace(M)*K
        return clean(covariant_constitutive+T*K+K*T.T-s.trace(M)*K)

    def defect(self, e, F):
        K = self.kernel(e)
        # Differentiate the original density along e(I+epsilon M) and
        # Lambda²(I+epsilon M)^T F, then subtract its density weight.
        result = s.zeros(4)
        for index, M in enumerate(self.M):
            dK = self.kernel_dot(e, e*M)
            dF = self.T[index].T*F
            result[index] = dot(F, dK*F*self.raw.Gram)/2+dot(dF, K*F*self.raw.Gram)-s.trace(M)*dot(F, K*F*self.raw.Gram)/2
        return clean(result)

    def defect_dot(self, e, F, de, dF):
        K, dK = self.kernel(e), self.kernel_dot(e, de)
        return clean(s.Matrix(4, 4, lambda mu, nu:
            dot(F, self.reduced_pullback_kernel(dK, 4*mu+nu)*F*self.raw.Gram)/2+
            dot(dF, self.reduced_pullback_kernel(K, 4*mu+nu)*F*self.raw.Gram)))

    def currents(self, e, phi, U, psi, chi):
        h = self.raw.metric(e)
        P = [sum((h[mu, nu]*U[nu] for nu in range(4)), s.zeros(70, 1)) for mu in range(4)]
        scalar = s.Matrix(4, 12, lambda mu, a: dot(P[mu], self.raw.rho70[a]*phi))
        C = self.raw.principals(e)
        matter = s.Matrix(4, 12, lambda mu, a:
            s.re((chi*s.kronecker_product(C[mu], self.raw.rho63[a])*psi)[0]).expand())
        return clean(scalar), clean(matter)

    def dynamic(self, e, de, spatial_e, A, F, spatial_F, current):
        K, Kdot = self.kernel(e), self.kernel_dot(e, de)
        P = clean(K*F*self.raw.Gram)
        spatial_P = [clean((self.kernel_dot(e, spatial_e[i])*F+K*spatial_F[i])*self.raw.Gram) for i in range(3)]
        Bdot = s.zeros(3, 12)
        for row, (i, j) in enumerate(PAIRS[3:]):
            Bdot[row, :] = (spatial_F[i-1][j-1, :].T-spatial_F[j-1][i-1, :].T+
                self.raw.bracket(A[i, :], F[j-1, :])-self.raw.bracket(A[j, :], F[i-1, :])-
                self.raw.bracket(A[0, :], F[row+3, :])).T
        Fdot0 = s.zeros(3, 12).col_join(Bdot)
        Pdot0 = clean((Kdot*F+K*Fdot0)*self.raw.Gram)
        target = s.zeros(3, 12)
        for nu in range(1, 4):
            value = current[nu, :].T
            for mu in range(4):
                value += self.raw.ad(A[mu, :]).T*ordered(P, mu, nu)
                if mu: value -= ordered(spatial_P[mu-1], mu, nu)
            target[nu-1, :] = value.T
        full_velocity_matrix = s.kronecker_product(K[:3, :3], self.raw.Gram)
        electric, free = full_velocity_matrix.gauss_jordan_solve((target-Pdot0[:3, :]).reshape(36, 1))
        assert free.rows == 0
        Fdot = clean(electric.reshape(3, 12).col_join(Bdot))
        Pdot = clean((Kdot*F+K*Fdot)*self.raw.Gram)
        eq(Pdot[:3, :], target)
        # All36 actual dynamical Maxwell equations, not an imposed Gauss row.
        for nu in range(1, 4):
            row = -ordered(Pdot, 0, nu)+current[nu, :].T
            for mu in range(4):
                row += self.raw.ad(A[mu, :]).T*ordered(P, mu, nu)
                if mu: row -= ordered(spatial_P[mu-1], mu, nu)
            eq(row, s.zeros(12, 1))
        return Fdot, Pdot, target

    def solve(self, e, velocity, spatial_e, A, F, spatial_F, phi, U, psi, chi):
        scalar, matter = self.currents(e, phi, U, psi, chi)
        unknown = s.Matrix(s.symbols('etime0:4', real=True))
        de = velocity.copy(); de[:, 0] = unknown
        Fdot, Pdot, target = self.dynamic(e, de, spatial_e, A, F, spatial_F, scalar+matter)
        divergence = self.defect_dot(e, F, de, Fdot)[0, :].T
        for i in range(3): divergence += self.defect_dot(e, F, spatial_e[i], spatial_F[i])[i+1, :].T
        M, rhs = s.linear_eq_to_matrix(list(divergence), list(unknown))
        M, rhs = clean(M), clean(rhs)
        rates, free = M.gauss_jordan_solve(rhs)
        assert free.rows == 0
        substitution = dict(zip(unknown, rates))
        eq(divergence.subs(substitution), s.zeros(4, 1))
        return {'rates': clean(rates), 'matrix': M, 'forcing': -rhs,
            'Fdot': clean(Fdot.subs(substitution)), 'Pdot': clean(Pdot.subs(substitution)),
            'electric_momentum_rate': target, 'scalar_current': scalar, 'matter_current': matter}


def generic_covariance(model):
    e = model.raw.eg; determinant = s.expand(e.det()); adj = e.adjugate()
    X = lorentz_exterior(e)
    metric = e.T*ETA*e
    Knum = clean(-lorentz_exterior(metric)/SIGMA)
    hnum = clean(adj*ETA*adj.T)
    for index, M in enumerate(model.M):
        T = model.T[index]; de = e*M; trace = s.trace(M)
        ddet = s.expand(sum(de[k]*s.diff(determinant, e[k]) for k in range(16)))
        zero(ddet-trace*determinant)
        dX = clean(sum((de[k]*X.diff(e[k]) for k in range(16)), s.zeros(6)))
        equal(dX, X*T)
        # Original BF pairings before auxiliary elimination and integration
        # by parts. The same identity covers every internal field component.
        equal(T*W+W*T.T, trace*W)
        equal(T.T*W+W*T, trace*W)
        dadj = clean(sum((de[k]*adj.diff(e[k]) for k in range(16)), s.zeros(4)))
        # The covariant first derivative/connection slot transforms by M^T;
        # this coefficient equation covers all4 Clifford matrices x63 matter.
        equal(dadj+M*adj-trace*adj, s.zeros(4))
        dhnum = clean(dadj*ETA*adj.T+adj*ETA*dadj.T)
        equal(dhnum+M*hnum+hnum*M.T-2*trace*hnum, s.zeros(4))
        dKnum = clean(sum((de[k]*Knum.diff(e[k]) for k in range(16)), s.zeros(6)))
        pullback_defect_num = clean(dKnum+T*Knum+Knum*T.T-2*trace*Knum)
        equal(pullback_defect_num, model.reduced_pullback_kernel(Knum, index))
    return {'generic_coframe_variables': 16, 'coordinate_gradient_generators': 16,
        'original_BF_simplicity_and_volume_density_weights': True,
        'full70_scalar_and252_independent_dual_density_weights': True,
        'native_gauge_defect_from_actual_covariant_twoform_pullback': True,
        'gauge_auxiliary_envelope': 'Original auxiliary Euler=0 makes the derivative of the eliminated B(e,F) identical to the raw BF derivative; no defect is discarded.',
        'Noether_identity': 'E_A partial_nu q^A - partial_mu(E_A R^{A,mu}_nu) = -partial_mu Q^mu_nu',
        'on_remaining_Euler': 'e[a,nu] partial_t F_a = partial_mu Q^mu_nu + F_a(partial_nu e[a,0]-partial_t e[a,nu])',
        'Q_itself_required_to_vanish': False,
        'boundary': 'original BF density identity precedes integration by parts; the previously generated original flux remains in the common Hamiltonian'}


def source_minor(model, candidate):
    raw = model.raw; active = raw.active['actual_background']
    e = s.Matrix(active['coframe']).applyfunc(s.sympify); A = raw.A
    F = raw.curvature(A); Q = model.defect(e, F)
    assert Q.todok()
    K = model.kernel(e); matrix = []; fixed = []; responses = []
    full = s.kronecker_product(K[:3, :3], raw.Gram)
    for a in range(4):
        de = s.zeros(4); de[a, 0] = 1
        dK = model.kernel_dot(e, de)
        electric, free = full.gauss_jordan_solve((-(dK*F*raw.Gram)[:3, :]).reshape(36, 1))
        assert free.rows == 0
        dF = clean(electric.reshape(3, 12).col_join(s.zeros(3, 12)))
        eq((dK*F+K*dF)[:3, :], s.zeros(3, 12))
        responses.append(dF)
        matrix.append(model.defect_dot(e, F, de, dF)[0, :].T)
        fixed.append(model.defect_dot(e, F, de, s.zeros(6, 12))[0, :].T)
    M, Mfixed = clean(s.Matrix.hstack(*matrix)), clean(s.Matrix.hstack(*fixed))
    expected = s.diag(-s.Rational(18, 5), *[-2*s.sqrt(30)/3]*3)
    eq(M, expected); zero(M.det()-32*s.sqrt(30))
    assert (M-Mfixed).todok()
    saved = candidate['source_time_minor']
    for key, value in [('source_coframe', e), ('source_connection', A), ('source_curvature', F),
        ('source_coordinate_defect', Q), ('Maxwell_eliminated_time_matrix', M), ('fixed_F_derivative', Mfixed)]: eq(value, decode(saved[key]))
    for value, record in zip(responses, saved['all4_Maxwell_curvature_responses']): eq(value, decode(record))
    previous = json.loads((HERE/'source_homogeneous_canonical_flow.json').read_text())
    J4 = decode(previous['analytic_Cauchy_source_chart']['source_four_time_Jacobian'])
    eq(M, e.T*J4)
    return e, A, F, M, Q, previous


def main():
    began = time.monotonic(); path = HERE/'source_spatial_time_coframe.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    model = RawCoordinateDensity(); raw = model.raw
    assert candidate['root'] == ROOT_ID and candidate['source_sha256'] == raw.hashes
    covariance = generic_covariance(model)
    print('PASS original generic densities and ordinary coordinate pullback defect for all16 e/all16 coordinate gradients', flush=True)
    e0, A0, F0, M0, Q0, previous = source_minor(model, candidate)
    count += bindings(previous)+bindings(raw.active)+bindings(raw.occupied)
    print('PASS raw36 Maxwell elimination before time4 coefficient: source det32sqrt30 and fixed-F defect', flush=True)

    f = {k: decode(v) for k, v in previous['datum'].items()}
    rates = {k: decode(v) for k, v in previous['complete_rates'].items()}
    e, A, phi = f['e'], f['A'], f['phi']
    K = model.kernel(e); F = raw.curvature(A)
    electric, free = s.kronecker_product(K[:3, :3], raw.Gram).gauss_jordan_solve((f['Pi_A']-(K[:3, 3:]*F[3:, :]*raw.Gram)).reshape(36, 1))
    assert free.rows == 0; F[:3, :] = electric.reshape(3, 12)
    h = raw.metric(e)
    U = [s.zeros(70, 1)]+[raw.action(A[i, :], raw.rho70)*phi for i in range(1, 4)]
    U[0] = clean((f['Pi_phi']-sum((h[0, i]*U[i] for i in range(1, 4)), s.zeros(70, 1)))/h[0, 0])
    E = s.kronecker_product(raw.principals(e)[0], s.eye(63))
    chi = clean(s.I*f['p']*E.inv())
    velocity = rates['e'].copy(); velocity[:, 0] = s.zeros(4, 1)
    homogeneous = model.solve(e, velocity, [s.zeros(4)]*3, A, F, [s.zeros(6, 12)]*3, phi, U, f['psi'], chi)
    eq(homogeneous['rates'], rates['e'][:, 0]); eq(homogeneous['electric_momentum_rate'], rates['Pi_A'])
    eq(homogeneous['rates'], decode(candidate['original_homogeneous_consumer']['source_four_generated_rates']))
    print('PASS full nontrivial homogeneous datum: independently recovered original four coframe and36 gauge momentum rates', flush=True)

    # Rebuild actual symmetric connection second jets; do not assign F jets
    # independently of the original connection or its spatial Bianchi law.
    ddA = [s.zeros(4, 48) for _ in range(4)]
    for i in range(1, 4):
        for j in range(i, 4):
            value = s.Matrix(1, 48, lambda _, a: s.Rational((i+2*j+3*a)%7-3, 101))
            ddA[i][j, :] = value; ddA[j][i, :] = value
    spatial_F = [clean(s.Matrix.vstack(*(ddA[i][mu, 12*nu:12*(nu+1)]-ddA[i][nu, 12*mu:12*(mu+1)] for mu, nu in PAIRS))) for i in range(1, 4)]
    bianchi = s.zeros(12, 1)
    for i, j, ell in ((1, 2, 3), (2, 3, 1), (3, 1, 2)):
        bianchi += ordered(spatial_F[i-1], j, ell)+raw.bracket(A0[i, :], ordered(F0, j, ell))
    eq(bianchi, s.zeros(12, 1))
    spatial_e = [s.Matrix(4, 4, lambda a, b: s.Rational((i+2*a+b)%7-3, 113)) for i in range(3)]
    velocity = s.Matrix(4, 4, lambda a, b: 0 if b == 0 else s.Rational((3*a+b)%5-2, 127))
    psi = s.Matrix([s.Rational((3*i+1)%7-3, 211)+s.I*s.Rational((5*i+2)%11-5, 223) for i in range(252)])
    chi = s.Matrix(1, 252, lambda _, i: s.Rational((7*i+1)%13-6, 227)+s.I*s.Rational((2*i+3)%7-3, 229))
    covariant = [s.Matrix([s.Rational((i+3*j)%7-3, 233) for j in range(70)]) for i in range(4)]
    spatial = model.solve(e0, velocity, spatial_e, A0, F0, spatial_F, phi, covariant, psi, chi)
    saved = candidate['actual_spatial_jet_consumer']
    for key, value in [('nonzero_forcing', spatial['forcing']), ('time_rates', spatial['rates']), ('time_minor', spatial['matrix'])]: eq(value, decode(saved[key]))
    assert spatial['forcing'].todok() and spatial['rates'].todok()
    # The gauge Gauss row is an initial constraint, not one of the36 solved
    # electric evolution rows. Record its actual residual on this jet.
    K0 = model.kernel(e0); P0 = clean(K0*F0*raw.Gram)
    spatial_P = [clean((model.kernel_dot(e0, spatial_e[i])*F0+K0*spatial_F[i])*raw.Gram) for i in range(3)]
    Gauss = spatial['scalar_current'][0, :].T+spatial['matter_current'][0, :].T
    for i in range(1, 4): Gauss += -ordered(spatial_P[i-1], i, 0)+raw.ad(A0[i, :]).T*ordered(P0, i, 0)
    Gauss = clean(Gauss); assert Gauss.todok()
    print('PASS original spatial connection jets/Bianchi and all252 dual/primal currents; generated first-jet time rates and divQ zero', flush=True)
    paths = [Path(__file__), path, HERE/'source_spatial_time_coframe.py', HERE/'source_gauge_legendre.py',
        HERE/'source_homogeneous_canonical_flow.json', HERE/'source_temporal_coframe_flux.json',
        HERE/'independent_source_joint_temporal_rates.py', HERE/'independent_source_gauge_legendre.py',
        BASE/'active-gauge/receipt.json', BASE/'occupied-response/receipt.json']
    result = {'verdict': 'CERTIFIED_ORIGINAL_COORDINATE_DEFECT_AND_MAXWELL_GENERATED_TIME_COFRAME_CHART',
        'root': ROOT_ID, 'source_sha256': raw.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks': count, 'candidate_constructor_imported': False,
        'density_covariance_and_defect': covariance,
        'source_time_minor': {'matrix': encode(M0), 'determinant': '32*sqrt(30)',
            'original36_electric_equations_solved_first': True,
            'source_Q_nonzero_retained': True, 'fixed_F_derivative_rejected': True,
            'equals_original_e_transpose_J4': True},
        'nontrivial_homogeneous_consumer': {'original_time4_rates_recovered': True,
            'original_gauge36_rates_recovered': True, 'source_scalar70_and_independent_dual252_currents': True},
        'actual_spatial_jet_consumer': {'all252_components_live': True, 'all70_covariant_scalar_jets_live': True,
            'spatial_F_from_symmetric_connection_second_jets': True, 'spatial_Bianchi12': True,
            'dynamic_Maxwell36': True, 'coordinate_defect_divergence4': True,
            'time_rates': encode(spatial['rates']), 'Gauss12_residual_nonzero_retained': encode(Gauss),
            'spatial_initial_constraint_datum_or_PDE_integral_curve_claimed': False},
        'dependency': 'e,F and first spatial derivatives; known spatial coframe velocity, original scalar covariant first jets, gauge connection and independent matter fields',
        'source_local_chart': 'electric g00!=0 and det(M4)!=0; the exact source lies in this open chart',
        'general_spatial_Cauchy_or_quantum_measure_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_spatial_time_coframe.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS independent original time-coframe spatial chart', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
