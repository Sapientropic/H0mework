#!/usr/bin/env python3
"""Source Gauss preservation and its generated scalar/time-connection chain.

The original fixed vacuum is not transformed by an active field variation.
Its exact potential torque generates nine further constraints.  Their time
derivative determines the broken part of A0, and the next derivative consumes
the original scalar/gauge flows.  Rank changes retain their own consistency
rows; no unconstrained gauge freedom or physical mode count is inferred.
"""
from __future__ import annotations

from collections import Counter
import hashlib
import itertools
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, decode
from source_gauge_legendre import SourceGaugeLegendre, source, contraction, rational
from source_lorentz_contact import clean, equal, encode, ETA


class SourceConstraintPreservation:
    def __init__(self):
        self.gauge = SourceGaugeLegendre()
        self.rho = self.gauge.rho70
        words = list(itertools.combinations(range(7), 4))
        self.vacuum = s.Matrix([self.gauge.vacuum.get(word, 0) for word in words]+[0]*35)
        self.orbit = clean(s.Matrix.hstack(*[R*self.vacuum for R in self.rho]))
        self.broken_columns = list(self.orbit.rref()[1])
        self.select = s.eye(12)[:, self.broken_columns]
        self.stabilizer = clean(s.Matrix.hstack(*self.orbit.nullspace()))
        self.active = self.orbit*self.select
        self.gram = clean(self.active.T*self.active)
        self.projector = clean(s.eye(70)-self.active*self.gram.inv()*self.active.T)
        self.yukawa = []
        for word in words:
            _, _, wedge, _ = source.yukawa(Counter({word: 1}))
            internal = s.zeros(63)
            internal[:7, 7:28] = s.Matrix(wedge)
            self.yukawa.append(clean(s.kronecker_product(s.diag(0, 0, 1, 1), internal)))
        self.yukawa += [s.I*matrix for matrix in self.yukawa.copy()]

    def potential_constraint(self, phi):
        return clean(self.orbit.T*phi)

    def torque(self, e, phi):
        return clean(-2*s.Abs(e.det())*self.potential_constraint(phi))

    def gauss_rate(self, e, phi, time_connection, gauss):
        """After the spatial gauge, scalar and both matter Euler equations."""
        return clean(self.gauge.ad(time_connection).T*gauss+self.torque(e, phi))

    def consistency_matrix(self, phi):
        return clean(self.orbit.T*s.Matrix.hstack(*[R*phi for R in self.rho]))

    @staticmethod
    def metric_density(e):
        volume = s.Abs(e.det())
        assert volume != 0
        return rational(volume*e.inv()*ETA*e.inv().T), volume

    def metric_derivative(self, e, direction):
        h, _ = self.metric_density(e)
        inverse = e.inv()
        return rational(s.trace(inverse*direction)*h-inverse*direction*h-
                        h*direction.T*inverse.T)

    def scalar_kinematics(self, e, phi, momentum, spatial_phi, connection):
        h, volume = self.metric_density(e)
        assert h[0, 0] != 0
        R_A = [clean(sum((connection[mu, a]*self.rho[a] for a in range(12)), s.zeros(70))) for mu in range(4)]
        U = [clean(spatial_phi[i]+R_A[i+1]*phi) for i in range(3)]
        shift = clean(sum((h[0, i+1]*U[i] for i in range(3)), s.zeros(70, 1)))
        covariant_time = clean((momentum-shift)/h[0, 0])
        return {'metric': h, 'volume': volume, 'R_A': R_A, 'spatial_covariant': U,
                'shift': shift, 'covariant_time': covariant_time,
                'velocity': clean(covariant_time-R_A[0]*phi),
                'rhs': clean(self.orbit.T*covariant_time)}

    def linear_consistency(self, phi, rhs):
        """Exact rank chart on C=0, retaining every new left-null condition."""
        equal(self.potential_constraint(phi), s.zeros(12, 1))
        D = self.consistency_matrix(phi)
        broken = clean(self.select.T*D*self.select)
        if broken.det() != 0:
            inverse = rational(self.select*broken.inv()*self.select.T)
            kernel = self.stabilizer
            compatibility = clean(self.stabilizer.T*rhs)
            rank = 9
        else:
            # On the potential-constraint surface D is symmetric. Its exact
            # column pivots then choose a nonsingular principal block.
            equal(D, D.T)
            pivots = D.rref()[1]
            Q = s.eye(12)[:, list(pivots)]
            inverse = rational(Q*(Q.T*D*Q).inv()*Q.T) if pivots else s.zeros(12)
            kernel = s.Matrix.hstack(*D.nullspace())
            compatibility = clean(kernel.T*rhs)
            rank = len(pivots)
        return {'matrix': D, 'broken_matrix': broken, 'inverse_on_image': inverse,
                'kernel': clean(kernel), 'rank': rank,
                'new_consistency_rows': compatibility}

    def solve_time_connection(self, e, phi, momentum, spatial_phi, connection, parameters=None):
        C = self.potential_constraint(phi)
        equal(C, s.zeros(12, 1))
        data = self.scalar_kinematics(e, phi, momentum, spatial_phi, connection)
        solve = self.linear_consistency(phi, data['rhs'])
        equal(solve['new_consistency_rows'], s.zeros(solve['kernel'].cols, 1))
        if parameters is None:
            parameters = s.zeros(solve['kernel'].cols, 1)
        assert parameters.shape == (solve['kernel'].cols, 1)
        A0 = clean(solve['inverse_on_image']*data['rhs']+solve['kernel']*parameters)
        return {**data, **solve, 'time_connection': A0}

    def solve_time_connection_derivative(self, phi, phi_rate, rhs_rate, time_connection, parameters=None):
        equal(self.potential_constraint(phi), s.zeros(12, 1))
        equal(self.potential_constraint(phi_rate), s.zeros(12, 1))
        rhs = clean(rhs_rate-self.consistency_matrix(phi_rate)*time_connection)
        solve = self.linear_consistency(phi, rhs)
        equal(solve['new_consistency_rows'], s.zeros(solve['kernel'].cols, 1))
        if parameters is None:
            parameters = s.zeros(solve['kernel'].cols, 1)
        return {**solve, 'time_connection_rate': clean(solve['inverse_on_image']*rhs+solve['kernel']*parameters),
                'differentiated_rhs': rhs}

    def original_scalar_rates(self, e, coframe_rate, spatial_e, phi, momentum,
            spatial_phi, spatial_momentum, second_phi, connection, spatial_connection,
            gauge_momentum, primal, dual):
        """Original scalar Euler and its contribution to the A0 consistency jet.

        All inputs are current field/canonical spatial jets. The coframe rate
        is the current coframe Hamiltonian output, not a proposed constraint
        derivative. The gauge rate is generated here by its original inverse.
        """
        data = self.scalar_kinematics(e, phi, momentum, spatial_phi, connection)
        h, U, U0, RA = [data[key] for key in ('metric', 'spatial_covariant', 'covariant_time', 'R_A')]
        phi_rate = data['velocity']
        dh_space = [self.metric_derivative(e, spatial_e[i].reshape(4, 4)) for i in range(3)]
        spatial_U_derivative, U0_derivative, phi_rate_spatial = [], [], []
        for i in range(3):
            dU = []
            for j in range(3):
                dR = sum((spatial_connection[i, 12*(j+1)+a]*self.rho[a] for a in range(12)), s.zeros(70))
                dU.append(clean(second_phi[i][j]+dR*phi+RA[j+1]*spatial_phi[i]))
            db = sum((dh_space[i][0, j+1]*U[j]+h[0, j+1]*dU[j] for j in range(3)), s.zeros(70, 1))
            dU0 = clean((spatial_momentum[i]-db-U0*dh_space[i][0, 0])/h[0, 0])
            dR0 = sum((spatial_connection[i, a]*self.rho[a] for a in range(12)), s.zeros(70))
            spatial_U_derivative.append(dU)
            U0_derivative.append(dU0)
            phi_rate_spatial.append(clean(dU0-dR0*phi-RA[0]*spatial_phi[i]))
        spatial_pi = [clean(h[i+1, 0]*U0+sum((h[i+1, j+1]*U[j] for j in range(3)), s.zeros(70, 1)))
                      for i in range(3)]
        divergence = s.zeros(70, 1)
        for i in range(3):
            divergence += dh_space[i][i+1, 0]*U0+h[i+1, 0]*U0_derivative[i]
            divergence += sum((dh_space[i][i+1, j+1]*U[j]+h[i+1, j+1]*spatial_U_derivative[i][j]
                               for j in range(3)), s.zeros(70, 1))
            divergence += RA[i+1]*spatial_pi[i]
        yukawa_source = s.Matrix([s.expand(data['volume']*s.re((dual*Y*primal)[0])) for Y in self.yukawa])
        momentum_rate = clean(-RA[0]*momentum-divergence-2*data['volume']*(phi-self.vacuum)+yukawa_source)
        gauge_rate = self.gauge.velocity(e, connection, spatial_connection, gauge_momentum)
        h_rate = self.metric_derivative(e, coframe_rate.reshape(4, 4))
        shift_rate = s.zeros(70, 1)
        for i in range(3):
            R_rate = sum((gauge_rate[i, a]*self.rho[a] for a in range(12)), s.zeros(70))
            U_rate = phi_rate_spatial[i]+R_rate*phi+RA[i+1]*phi_rate
            shift_rate += h_rate[0, i+1]*U[i]+h[0, i+1]*U_rate
        rhs_rate = clean(self.orbit.T*(momentum_rate-shift_rate-U0*h_rate[0, 0])/h[0, 0])
        return {'scalar_velocity': phi_rate, 'scalar_momentum_rate': momentum_rate,
                'gauge_velocity': gauge_rate, 'time_connection_rhs_rate': rhs_rate,
                'Yukawa_scalar_source': yukawa_source, 'spatial_scalar_momenta': spatial_pi,
                'spatial_scalar_momentum_divergence': clean(divergence)}


def certify_source_torque(model):
    phi = s.Matrix(s.symbols('phi0:70', real=True))
    C = model.potential_constraint(phi)
    volume = s.Symbol('volume', positive=True)
    potential = contraction(phi-model.vacuum, phi-model.vacuum)
    gradient = s.Matrix([s.diff(-volume*potential, x) for x in phi])
    D = model.consistency_matrix(phi)
    for a, R in enumerate(model.rho):
        equal(R.T, -R)
        assert s.expand(contraction(gradient, R*phi)+2*volume*C[a]) == 0
        for b in range(12):
            torque = sum(model.gauge.brackets.get((a, b, c), 0)*C[c] for c in range(12))
            assert s.expand(D[a, b]-D[b, a]-torque) == 0
    equal(model.stabilizer.T*D, s.zeros(3, 12))
    equal(model.orbit*model.stabilizer, s.zeros(70, 3))
    equal(model.projector*model.projector, model.projector)
    equal(model.orbit.T*model.projector, s.zeros(12, 70))
    assert model.orbit.rank() == 9 and model.projector.rank() == 61
    assert model.select.row_join(model.stabilizer).det() != 0
    scalar = json.loads((BASE/'scalar-exchange/receipt.json').read_text())
    equal(model.projector, decode(scalar['peripheral_projector']))
    active = json.loads((BASE/'active-gauge/receipt.json').read_text())
    assert model.broken_columns == active['Ward_constraint_elimination']['broken_parameter_columns']
    N = s.sympify(active['source_lapse'])
    inverse = s.Matrix(active['Ward_constraint_elimination']['scalar_constraint_inverse']).applyfunc(s.sympify)
    equal((-2*N*model.gram)*inverse, s.eye(9))
    # The actual all-field potential torque specializes to the old scalar9
    # Ward row; the old Jacobi output did not define the new constraint.
    torque_matrix = -2*N*model.active.T*model.orbit
    original = s.SparseMatrix(9, 12, {(i, j): s.sympify(v)
        for i, j, powers, v in active['H_p_times_T_p']})
    equal(torque_matrix, original)
    return {'vacuum': encode(model.vacuum), 'orbit': encode(model.orbit),
            'potential_constraint_matrix': encode(model.orbit.T),
            'fixed_source_stabilizer': encode(model.stabilizer),
            'broken_parameter_columns': model.broken_columns,
            'source_broken_Gram': encode(model.gram), 'scalar_constraint_projector': encode(model.projector),
            'rank': 9, 'stabilizer_dimension': 3,
            'original_potential': '||phi-v||^2 in source chart0',
            'active_fixed_source_variation': 'delta phi=R_a phi, delta v=0; delta L=-2abs(det e)*(R_a v)^T phi',
            'source_chart_responsibility': 'scalarFrameRelativeCoordinates_zeroChart is the identity; passive generated chart transport also transports the frame and does not cancel this fixed-source active torque',
            'consistency_matrix': 'D_ab(phi)=(R_a v)^T R_b phi',
            'antisymmetric_part': 'D_ab-D_ba=sum_c f_ab^c C_c; D is symmetric on C=0',
            'same_original_scalar61': 'I-O_b(O_b^T O_b)^-1 O_b^T equals the existing full peripheral_projector exactly',
            'same_original_Ward9': 'linearized torque and its actual9x9 inverse equal the old source Ward scalar-constraint rows',
            'stabilizer_dimension_is_physical_mode_count': False}


def certify_repaired_Noether_coefficients(model):
    # Raw repaired exterior Yukawa blocks: all70 directions and all12 original
    # generators. Gauge action is block diagonal in the actual [6,2,4] order.
    Ysmall = [Y.extract(list(range(126, 133)), list(range(133, 154))) for Y in model.yukawa]
    checked = 0
    for a, rho in enumerate(model.gauge.rho63):
        R = model.rho[a]
        for b, Y in enumerate(Ysmall):
            variation = sum((R[c, b]*Ysmall[c] for c in range(70) if R[c, b]), s.zeros(7, 21))
            equal(variation, rho[:7, :7]*Y-Y*rho[7:28, 7:28])
            checked += 1
        equal(model.gauge.adjoint[a].T*model.gauge.gram+model.gauge.gram*model.gauge.adjoint[a], s.zeros(12))
        for b in range(12):
            equal(R*model.rho[b]-model.rho[b]*R,
                  sum((model.gauge.brackets.get((a, b, c), 0)*model.rho[c] for c in range(12)), s.zeros(70)))
    assert checked == 840
    # Full source matter directions must not disappear from a mistaken block
    # extraction before invoking the covariance identity.
    assert sum(len(clean(Y).todok()) for Y in Ysmall) > 0
    return {'all840_repaired_Yukawa_Lie_covariance_coefficients': 'Y(R_a phi)=[rho_a,Y(phi)]',
            'all144_scalar_representation_brackets': 'exact source brackets',
            'kinetic_cancellation': 'scalar rho70 is skew and density metric symmetric; Dirac principal/Lorentz spin commute with the internal rho63; local parameter derivatives cancel with delta A=-D epsilon',
            'native_gauge_cancellation': 'ad^T G_native+G_native ad=0; symmetric coframe constitutive kernel cancels the curvature-pair contraction in the covariant divergence of its Euler rows',
            'Lorentz_reduced_contact_cancellation': 'every raw Lorentz vertex is spin4 tensor I63, hence its full independent-dual current and the eliminated geom/cross/contact action are invariant under the same active internal variation',
            'off_shell_local_Noether_identity': 'sum_mu D_mu^* E_A^mu + E_phi^T R_a phi + Re(E_psi rho_a psi-chi rho_a E_chi)=-2abs(det e) C_a',
            'repaired_matter_cancellation': 'the Yukawa term in the scalar Euler contraction cancels the opposite commutator term in the two independent matter Euler rows; no adjoint graph imposed',
            'Gauss_evolution': 'dot(G)-ad(A0)^T G=-2abs(det e) C when the scalar, both matter and spatial connection Euler rows hold',
            'active_source_vacuum_replaced_or_transformed': False,
            'complete12_local_gauge_invariance_assumed': False}


def certify_consistency_consumers(model):
    active = json.loads((BASE/'active-gauge/receipt.json').read_text())
    e = s.Matrix(active['actual_background']['coframe']).applyfunc(s.sympify)
    A = s.Matrix(active['actual_background']['gauge_connection']).applyfunc(s.sympify)
    Pi = s.Matrix([s.Rational((i*3)%11-5, 37) for i in range(70)])
    spatial = [model.projector*s.Matrix([s.Rational((i+2*j)%7-3, 43) for i in range(70)]) for j in range(3)]
    transverse = model.projector*s.Matrix([s.Rational((i*2)%9-4, 101) for i in range(70)])
    phi = clean(model.vacuum+transverse)
    free = s.Matrix(s.symbols('residual0:3', real=True))
    solved = model.solve_time_connection(e, phi, Pi, spatial, A, free)
    shifted_A = A.copy(); shifted_A[0, :] = solved['time_connection'].T
    flow = model.scalar_kinematics(e, phi, Pi, spatial, shifted_A)
    equal(model.potential_constraint(flow['velocity']), s.zeros(12, 1))
    equal(solved['matrix']*solved['time_connection'], solved['rhs'])
    equal(solved['matrix'], solved['matrix'].T)
    equal(solved['matrix']*model.stabilizer, s.zeros(12, 3))
    source_matrix = model.consistency_matrix(model.vacuum)
    equal(source_matrix, model.orbit.T*model.orbit)
    assert source_matrix.rank() == 9

    # A rank-changing field is a different exact consistency chart. It does
    # not inherit the inverse at the source and cannot silently discard rhs.
    zero_phi = s.zeros(70, 1)
    zero_rhs = model.scalar_kinematics(e, zero_phi, Pi, [s.zeros(70, 1)]*3, A)['rhs']
    dropped = model.linear_consistency(zero_phi, zero_rhs)
    assert dropped['rank'] == 0 and dropped['new_consistency_rows'] != s.zeros(12, 1)
    return {'live_phi': encode(phi), 'live_scalar_momentum': encode(Pi),
            'live_spatial_scalar_jet': [encode(x) for x in spatial],
            'live_consistency_matrix': encode(solved['matrix']),
            'live_broken_matrix_determinant': str(s.factor(solved['broken_matrix'].det())),
            'generated_time_connection': encode(solved['time_connection']),
            'source_consistency_matrix': encode(source_matrix),
            'generated_time_connection_equation': 'D(phi) A0=O^T(Pi_phi-b)/h00, b=sum_i h0i D_i phi',
            'actual_potential_constraint_rate_after_solve': '0 for all3 independent residual stabilizer parameters',
            'rank_drop_field': 'phi=0 lies on C=0 but D=0; all12 rhs rows are retained as further consistency conditions',
            'rank_drop_retained_rhs': encode(dropped['new_consistency_rows']),
            'constraint_chain': ['Pi_A0=0', 'Gauss=0', 'C=O^T phi=0 (rank9)',
                                 'D(phi) A0=r', 'D(phi) dotA0=dotr-dotD A0'],
            'nine_A0_components_are_generated': True,
            'remaining_three_parameters_declared_first_class': False}


def certify_actual_next_rate(model, consumer):
    active = json.loads((BASE/'active-gauge/receipt.json').read_text())
    occupied = json.loads((BASE/'occupied-response/receipt.json').read_text())
    e = s.Matrix(active['actual_background']['coframe']).applyfunc(s.sympify)
    A = s.Matrix(active['actual_background']['gauge_connection']).applyfunc(s.sympify)
    phi, Pi = decode(consumer['live_phi']), decode(consumer['live_scalar_momentum'])
    spatial_phi = [decode(value) for value in consumer['live_spatial_scalar_jet']]
    solved = model.solve_time_connection(e, phi, Pi, spatial_phi, A)
    A[0, :] = solved['time_connection'].T
    spatial_Pi = [s.Matrix([s.Rational((i+3*j)%13-6, 47) for i in range(70)]) for j in range(3)]
    second_phi = [[model.projector*s.Matrix([s.Rational((i+j+k)%5-2, 53) for i in range(70)])
                   for k in range(3)] for j in range(3)]
    spatial_A = s.Matrix(3, 48, lambda i, j: s.Rational((2*i+j)%7-3, 59))
    spatial_e = [s.zeros(16, 1)]*3
    # The spatial derivatives of the generated A0 equation are solved by the
    # same source matrix. This retains actual compatible field jets.
    h = solved['metric']
    for i in range(3):
        rhs_i = model.orbit.T*spatial_Pi[i]/h[0, 0]
        rhs_i -= model.consistency_matrix(spatial_phi[i])*solved['time_connection']
        spatial_A[i, :12] = clean(solved['inverse_on_image']*rhs_i).T
    original_psi = decode(occupied['occupied_frame'])*s.Matrix(active['actual_background']['primal_H']).applyfunc(s.sympify)
    original_chi = s.sqrt(2)*original_psi.T
    Pi_A = s.Matrix(3, 12, lambda i, j: s.Rational((i+j*3)%11-5, 61))
    baseline = model.original_scalar_rates(e, s.zeros(16, 1), spatial_e, phi, Pi,
                spatial_phi, spatial_Pi, second_phi, A, spatial_A, Pi_A, original_psi, original_chi)
    equal(baseline['Yukawa_scalar_source'], s.zeros(70, 1))
    # The old prepared H12 input kills every active-orbit Yukawa vertex.
    # Perturb the original full252 fields in their existing Lambda2/Lambda6
    # coordinates so the same action supplies a nonzero broken-direction load.
    psi, chi = original_psi.copy(), original_chi.copy()
    psi[135] += 1
    chi[126] += 1
    rates = model.original_scalar_rates(e, s.zeros(16, 1), spatial_e, phi, Pi,
                spatial_phi, spatial_Pi, second_phi, A, spatial_A, Pi_A, psi, chi)
    assert rates['Yukawa_scalar_source'] != s.zeros(70, 1)
    active_yukawa = clean(model.orbit.T*rates['Yukawa_scalar_source'])
    assert active_yukawa != s.zeros(12, 1)
    equal(model.potential_constraint(rates['scalar_velocity']), s.zeros(12, 1))
    update = model.solve_time_connection_derivative(phi, rates['scalar_velocity'],
                  rates['time_connection_rhs_rate'], solved['time_connection'])
    residual = (solved['matrix']*update['time_connection_rate']+
                model.consistency_matrix(rates['scalar_velocity'])*solved['time_connection']-
                rates['time_connection_rhs_rate'])
    equal(residual, s.zeros(12, 1))
    assert update['time_connection_rate'] != s.zeros(12, 1)
    reference_update = model.solve_time_connection_derivative(phi, baseline['scalar_velocity'],
                  baseline['time_connection_rhs_rate'], solved['time_connection'])
    forcing_rhs = clean(rates['time_connection_rhs_rate']-baseline['time_connection_rhs_rate'])
    forcing_A0 = clean(update['time_connection_rate']-reference_update['time_connection_rate'])
    equal(forcing_rhs, active_yukawa/h[0, 0])
    equal(solved['matrix']*forcing_A0, forcing_rhs)
    assert forcing_rhs != s.zeros(12, 1) and forcing_A0 != s.zeros(12, 1)
    # Choose the current spatial momentum jet to solve the original Gauss
    # equation itself. This is an explicit local canonical jet, not a claim
    # that all remaining coframe constraints or a global trajectory are paid.
    scalar_charge = s.Matrix([contraction(Pi, R*phi) for R in model.rho])
    matter_charge = model.gauge.matter_current(e, psi, chi)[0, :].T
    divergence = sum((model.gauge.ad(A[i+1, :]).T*Pi_A[i, :].T for i in range(3)), s.zeros(12, 1))
    divergence -= scalar_charge+matter_charge
    spatial_Pi_A = [s.zeros(3, 12) for _ in range(3)]
    spatial_Pi_A[0][0, :] = divergence.T
    total_gauss = model.gauge.gauss(A, Pi_A, spatial_Pi_A)+scalar_charge+matter_charge
    equal(total_gauss, s.zeros(12, 1))
    equal(model.gauss_rate(e, phi, A[0, :].T, total_gauss), s.zeros(12, 1))
    return {'live_full252_primal': encode(psi), 'live_independent_full252_dual': encode(chi),
            'original_prepared_Yukawa_source': encode(baseline['Yukawa_scalar_source']),
            'source_generated_scalar_velocity': encode(rates['scalar_velocity']),
            'source_generated_scalar_momentum_rate': encode(rates['scalar_momentum_rate']),
            'source_generated_gauge_velocity': encode(rates['gauge_velocity']),
            'actual_full_Yukawa_scalar_source': encode(rates['Yukawa_scalar_source']),
            'actual_broken_orbit_Yukawa_source': encode(active_yukawa),
            'nonzero_Yukawa_induced_rhs_rate_change': encode(forcing_rhs),
            'nonzero_Yukawa_induced_A0_rate_change': encode(forcing_A0),
            'generated_consistency_rhs_rate': encode(rates['time_connection_rhs_rate']),
            'generated_time_connection_rate': encode(update['time_connection_rate']),
            'all12_differentiated_time_connection_equations': '0',
            'compatible_spatial_gauge_momentum_jet': [encode(value) for value in spatial_Pi_A],
            'original_total_Gauss_and_generated_rate': 'both exactly0 on this explicit local canonical jet',
            'local_consistency_scope': 'the generated Gauss,C,dotC and A0 consistency rows hold at this local field jet; full coframe secondary constraints and an integrated common trajectory are separate consumers',
            'source_of_rhs_rate': 'original full70 scalar Euler with live metric/spatial coefficient derivatives, all70 repaired Yukawa terms, original gauge velocity, and the supplied current coframe Hamiltonian velocity',
            'independent_postulated_Gauss_derivative_used': False}


def main():
    began = time.monotonic()
    model = SourceConstraintPreservation()
    torque = certify_source_torque(model)
    print('PASS original fixed-source rank9 torque,live consistency tensor and identical P61/Ward9 consumers', flush=True)
    noether = certify_repaired_Noether_coefficients(model)
    print('PASS all840 repaired Yukawa coefficients and full source Noether Gauss-preservation mechanism', flush=True)
    consumer = certify_consistency_consumers(model)
    print('PASS actual live A0 solve,all3 source stabilizer parameters and rank-drop consistency rows', flush=True)
    next_rate = certify_actual_next_rate(model, consumer)
    print('PASS original scalar/gauge Euler generated dotr and exact next time-connection update', flush=True)
    core = ROOT/'Lean/SaturationMonoid/PhysicsCore'
    paths = [core/name for name in ('StageNineDynamicBreakingVacuum.lean','StageNineGlobalIntegratedAction.lean',
        'StageNineDiracDualFormNativeMotherAction.lean','StageNineP286GaugeConnectionVariationDensity.lean',
        'StageNineP286FrozenSourceScalarTorque.lean')]
    paths += [BASE/name for name in ('exact_readout.py','active-gauge/compute.py','active-gauge/receipt.json',
              'scalar-exchange/receipt.json','occupied-response/receipt.json')]
    paths += [HERE/name for name in ('source_constraint_preservation.py','source_gauge_legendre.py',
              'source_gauge_legendre.json','source_scalar_legendre.py','source_scalar_legendre.json',
              'source_coframe_legendre.py','source_coframe_legendre.json')]
    bindings = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}
    result = {'root': ROOT_ID, 'source_sha256': model.gauge.source_hashes, 'input_sha256': bindings,
        'scope': 'ORIGINAL_FIXED_SOURCE_GAUSS_PRESERVATION_SCALAR_CONSTRAINT_AND_TIME_CONNECTION_CONSISTENCY_PRODUCER',
        'source_potential_torque': torque, 'repaired_local_Noether_consumer': noether,
        'actual_time_connection_consumer': consumer, 'actual_next_consistency_update': next_rate,
        'public_API': 'SourceConstraintPreservation.{potential_constraint,torque,gauss_rate,consistency_matrix,linear_consistency,solve_time_connection,original_scalar_rates,solve_time_connection_derivative}',
        'coframe10_primary_preservation_responsibility': 'use the same common Hamiltonian to differentiate Z_e^T(Pi_e-b_e); include live Z_e, original BF temporal boundary and fixed-p matter chain before classifying or solving the resulting coframe constraints',
        'all_joint_constraints_classified_or_global_Cauchy_claimed': False,
        'new_source_occurrence_or_gauge_invariance_premise': False,
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'source_constraint_preservation.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS original source Gauss/constraint consistency producer', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
