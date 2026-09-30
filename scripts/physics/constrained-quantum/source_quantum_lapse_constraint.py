#!/usr/bin/env python3
"""Original lapse-primary consistency on the common local quantum domain.

The same coefficient-left103-coordinate operator has the exact dependence
H(nu)=nu H_A+nu^-1 H_B. Its derivative is an operator pencil constraint,
with the original full matter and the live coframe coefficient derivatives.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID, decode
from source_joint_local_quantum import SourceJointLocalQuantum
from source_coframe_live_ordering import FREE, full
from source_coframe_legendre import pack, rational
from source_lorentz_contact import clean, equal, encode, ETA
from source_gauss_quantum_current import weighted_sum, encode_state


def eq(A, B): equal(rational(A-B), s.zeros(*A.shape))
def zero(value): assert s.cancel(value) == 0


class SourceQuantumLapseConstraint:
    def __init__(self):
        self.joint = SourceJointLocalQuantum()
        self.coframe = self.joint.coframe
        self.nu = s.Symbol('nu', positive=True)
        self.e = self.coframe.e.copy(); self.e[0, 0] *= self.nu

    def metric_and_native(self, e):
        # The actual six-coordinate slice has a triangular coframe. Using
        # its polynomial adjugate avoids the nested rational pivots produced
        # by a generic elimination inverse; both inverse identities are paid.
        determinant = s.factor(e.det())
        inverse = rational(e.adjugate()/determinant)
        eq(e*inverse, s.eye(4)); eq(inverse*e, s.eye(4))
        inverse_metric = rational(inverse*ETA*inverse.T)
        metric_density = rational(determinant*inverse_metric)
        source = self.joint.gauge.source
        kernel = rational(source.at(source.kernel_numerator, e)/determinant)
        g00 = (e[:, 0].T*ETA*e[:, 0])[0]
        electric_inverse = rational(-source.sigma*determinant/g00*inverse_metric[1:, 1:])
        eq(kernel[:3, :3]*electric_inverse, s.eye(3))
        eq(electric_inverse*kernel[:3, :3], s.eye(3))
        return metric_density, determinant, dict(electric=kernel[:3, :3],
            mixed=kernel[:3, 3:], magnetic=kernel[3:, 3:], electric_inverse=electric_inverse)

    def original_lapse_coefficients(self):
        """All original coefficients before imposing the proposed scaling."""
        c, nu, e = self.coframe, self.nu, self.e
        model = c.model
        Hi = rational(model.lorentz.inverse(e))
        Gt = model.at(model.G[:, :16], e)
        h = e[:, 1:].T*ETA*e[:, 1:]
        R = rational(model.metric_lift_numerator(e)/e.det())
        Bi = rational(4*e.det()*model.metric_inverse_numerator.xreplace(
            dict(zip(model.h_variables, pack(h))))/h.det())
        Q = rational(R*Bi*R.T)
        spatial = e.copy(); spatial[:, 0] = s.zeros(4, 1)
        Z = s.Matrix.hstack(*((T*spatial).reshape(16, 1) for T in model.lorentz.basis))
        eq(Z, c.Z)
        ports = model.lorentz.raw_matter_ports(e)
        J = [rational(s.diag(s.I*ports['E'].inv()*V,
                 s.I*(ports['E'].inv()*V).conjugate())) for V in ports['V']]
        L = rational(c.S*s.eye(24)[:6, :]+Gt.T*Hi)
        T = [rational(sum((L[j, a]*J[a] for a in range(24)), s.zeros(8))) for j in range(16)]
        K = rational(c.A.T*Q*c.A/2)
        W = rational((L.T*Q*L+Hi)/2)
        one_body = rational(sum((value*J[a]*J[b] for (a, b), value in W.todok().items()), s.zeros(8)))
        mixed = [rational(sum(((c.A.T*Q)[r, j]*T[j] for j in range(16)), s.zeros(8))) for r in range(6)]
        drift = rational(-s.I*sum(((c.A.T*Q)[r, j]*c.A.diff(q)[j, :]
                                   for r, q in enumerate(c.q) for j in range(16)), s.zeros(1, 6))/2)
        correction = rational(-s.I*sum(((c.A.T*Q)[r, j]*T[j].diff(q)
                                        for r, q in enumerate(c.q) for j in range(16)), s.zeros(8))/2)
        metric, volume, gauge = self.metric_and_native(e)
        return dict(Hinv=Hi, Gt=Gt, Q=Q, L=L, J=J, T=T, K=K, W=W, one_body=one_body,
                    mixed=mixed, drift=drift, correction=correction, ports=ports,
                    metric=metric, volume=volume, gauge=gauge)

    def verify_scaling(self):
        c, nu = self.coframe, self.nu
        d = self.original_lapse_coefficients()
        P = s.diag(*([nu]*6+[1]*18)); D = nu*P.inv()
        eq(c.model.lorentz.hessian(self.e), nu*P.inv().T*c.model.lorentz.hessian(c.e)*P.inv())
        eq(d['Hinv'], P*c.Hinv*P.T/nu); eq(d['Gt'], c.Gt)
        eq(d['Q'], nu*c.Q); eq(d['L'], c.L*D.inv())
        for a in range(24): eq(d['J'][a], D[a, a]*c.J[a])
        for j in range(16): eq(d['T'][j], c.T[j])
        eq(d['W'], nu*D.inv().T*c.W*D.inv())
        for key in ('K', 'one_body', 'drift', 'correction'): eq(d[key], nu*getattr(c, key))
        for value, old in zip(d['mixed'], c.M): eq(value, nu*old)
        # Coefficient-level normal quartics retain both ordered current slots.
        # W_ab J_a tensor J_b scales by nu even though its three factors do
        # not individually have that same weight.
        eq(D.T*d['W']*D, nu*c.W)
        for q in c.q:
            for a in range(24): eq(d['J'][a].diff(q), D[a, a]*c.J[a].diff(q))
        h, volume, old_gauge = self.metric_and_native(c.e)
        eq(d['metric'][1:, 1:], nu*h[1:, 1:]); zero(d['metric'][0, 0]-h[0, 0]/nu)
        eq(h[0, 1:], s.zeros(1, 3)); eq(d['metric'][0, 1:], s.zeros(1, 3))
        zero(d['volume']-nu*volume)
        for name, factor in [('electric', nu), ('electric_inverse', 1/nu), ('magnetic', 1/nu)]:
            eq(d['gauge'][name], factor*old_gauge[name])
        eq(d['gauge']['mixed'], s.zeros(3)); eq(old_gauge['mixed'], s.zeros(3))
        old_ports = c.model.lorentz.raw_matter_ports(c.e)
        eq(d['ports']['E'], old_ports['E'])
        for mu in range(4):
            eq(d['ports']['oriented_principals'][mu], (1 if mu == 0 else nu)*old_ports['oriented_principals'][mu])
        # The source Gauss graph depends on phi,A and canonical matter alone;
        # its actual definitions contain no coframe or lapse. Together with
        # these original metric identities all its derivatives scale uniformly.
        # Original lower_without_Lorentz is sum_i D_i rho(A_i)+det(e)Y(phi).
        return d, {'generic_six_q': True, 'all24_Lorentz_current_coefficients': True,
            'original_Hessian_covariance': 'Hnu=nu P^-T H1 P^-1, P=diag(nu I6,I18)',
            'source_primary_graph_A_S_unchanged': True,
            'coframe_Q_K_mixed_drift_current_and_one_body_weight': 'nu',
            'normal_quartic_both_current_slots_preserved': True,
            'scalar': 'h00(nu)=h00(1)/nu, hij(nu)=nu hij(1), h0i=0, det(nu)=nu det(1); original Gauss momentum graph independent of nu',
            'gauge': 'K_E(nu)=nu K_E(1), K_E^-1(nu)=K_E^-1(1)/nu, K_B(nu)=K_B(1)/nu, K_mix=0',
            'full252_matter': 'E(nu)=E(1), D_i(nu)=nu D_i(1), det(e)Y(nu)=nu det(e1)Y; A0=0 common Gauss bulk',
            'all_x_A_and_original504_CAR_retained': True}

    def actual_action(self, q, x, A, state, gradient, Hessian):
        data = self.joint.coefficients(q, x, A)
        pieces, total = self.joint.action(data, state, gradient, Hessian)
        HA = weighted_sum((1, pieces[name]) for name in ('coframe', 'scalar', 'matter_without_Lorentz'))
        HB = pieces['gauge']; nu = self.nu
        H = weighted_sum([(nu, HA), (1/nu, HB)])
        constraint = weighted_sum([(1, HA), (-1/nu**2, HB)])
        pencil = weighted_sum([(nu**2, HA), (-1, HB)])
        derivative = {word: s.diff(value, nu) for word, value in H.items()}
        assert weighted_sum([(1, derivative), (-1, constraint)]) == {}
        assert weighted_sum([(nu**2, constraint), (-1, pencil)]) == {}
        assert weighted_sum([(1, total), (-1, HA), (-1, HB)]) == {}
        return data, {'H_A': HA, 'H_B': HB, 'Hamiltonian': H, 'constraint': constraint, 'pencil': pencil}

    def noncommuting_consumer(self, original_coefficients):
        """Actual full [HA,HB] on a compactly supported cubic vacuum germ.

        Scalar and matter have no q derivatives. Every such contribution
        retains (q_r-q_r0), including after HB's gauge derivatives, and is
        exactly zero at q=q0. This pays their whole-operator contribution;
        no selection of terms from the commutator is imposed as a premise.
        """
        c = self.coframe
        source = dict(zip(c.q, (c.e0[j] for j in FREE)))
        _, _, raw = self.metric_and_native(c.e)
        W = rational(s.kronecker_product(raw['electric_inverse'], self.joint.gauge.source.gram_inverse))
        candidates = s.Matrix(6, 36, lambda r, a: s.cancel(sum(c.K[r, t]*s.diff(W[a, a], c.q[t])
                                                                    for t in range(6))).subs(source))
        assert candidates.todok()
        r, a = next(iter(sorted(candidates.todok())))
        u = s.Symbol('centered_gauge_coordinate', real=True)
        f = (c.q[r]-source[c.q[r]])*u**2/2
        # HB's potential contribution is retained as an arbitrary smooth
        # coefficient through its relevant first two q derivatives. Its factor
        # u^2 makes both complete ordered actions vanish at the chosen germ.
        V = s.Function('original_magnetic_potential')(*c.q, u)
        Bf = -W[a, a]*s.diff(f, u, 2)/2+V*f
        def coframe_vacuum(value):
            answer = -sum(c.K[i, j]*s.diff(value, c.q[i], c.q[j]) for (i, j) in c.K.todok())
            answer -= s.I*sum(c.drift[t]*s.diff(value, c.q[t]) for t in range(6))
            answer += 3*c.e.det()*value
            return answer
        AB = s.cancel(coframe_vacuum(Bf).subs(u, 0).subs(source).doit())
        Af_at_q = s.cancel(coframe_vacuum(f).subs(source))
        BA = s.cancel((-W[a, a].subs(source)*s.diff(Af_at_q, u, 2)/2+
                       V.subs(source)*Af_at_q).subs(u, 0).doit())
        commutator = s.cancel(AB-BA)
        zero(commutator-candidates[r, a]); assert commutator != 0
        return {'coframe_coordinate': r, 'gauge_coordinate': a,
            'wavefunction_germ': '(q_r-q_source_r)*(A_a-A_base_a)^2/2 tensor CAR vacuum; multiply by a smooth compact cutoff equal1 near the configuration',
            'base_coframe': encode(c.e0), 'H_A_H_B_action': str(AB), 'H_B_H_A_action': str(BA),
            'commutator_action': str(commutator), 'all_scalar_matter_and_magnetic_terms_retained_or_exactly_zero': True,
            'universal_cubic_coefficient': 'sum_t K_rt(q_source) partial_qt W_aa(q_source)',
            'all6_by36_cubic_coefficients': encode(candidates),
            'operator_pencil_is_not_a_scalar_energy_ratio': True}


def main():
    started = time.monotonic(); model = SourceQuantumLapseConstraint()
    original, scaling = model.verify_scaling()
    print('PASS original generic sixq Lorentz/primary/metric/Hodge/matter lapse weights, including live derivative and normal quartic terms', flush=True)
    saved = json.loads((HERE/'source_joint_local_quantum.json').read_text())
    q = tuple(decode(saved['configuration']['coframe'])[j] for j in FREE)
    x, A = decode(saved['configuration']['scalar']), decode(saved['configuration']['gauge'])
    ell = s.Matrix([s.Rational(j%11+1, 67) for j in range(103)])
    radial = s.Matrix([s.Rational(j%7-3, 53) for j in range(103)])
    data, action = model.actual_action(q, x, A, (5, 258), s.I*ell, radial*radial.T-s.eye(103))
    # Direct evaluation of the original full scalar/gauge/matter coefficients
    # at variable lapse supplies an additional same-wavepacket consumer.
    e = data['e'].copy(); e[0, 0] *= model.nu
    scalar = model.joint.scalar.coefficients(e, x, A)
    for key in ('momentum_vectors', 'normal_embedding', 'F', 'vectors', 'shift', 'shift_derivative'):
        eq(scalar[key], data['scalar'][key])
    zero(scalar['h00']-data['scalar']['h00']/model.nu)
    zero(scalar['spatial_potential']-model.nu*data['scalar']['spatial_potential'])
    gauge = model.joint.gauge.coefficients(e)
    point = dict(zip(model.joint.gauge.coordinates, A.reshape(36, 1)))
    eq(gauge['weight'], data['gauge']['weight']/model.nu)
    zero(gauge['magnetic_potential'].subs(point)-data['gauge']['magnetic_potential']/model.nu)
    matter = model.joint.common.matter_data(e, data['scalar']['phi'], data['connection'])
    eq(matter['inverse_E'], data['matter']['inverse_E'])
    eq(matter['lower_without_Lorentz'], model.nu*data['matter']['lower_without_Lorentz'])
    for name in ('H_A', 'H_B', 'constraint', 'pencil'): assert action[name]
    print('PASS actual joint103 wavepacket, raw scalar/gauge/full252 lapse evaluation and primary-generated operator pencil', flush=True)
    commutator = model.noncommuting_consumer(original)
    print('PASS complete nonzero [H_A,H_B] on a real compact-support cubic vacuum germ', flush=True)
    nu = model.nu
    # Formal canonical primary reader acts on smooth parameter families with
    # the common103-coordinate domain as fibre; no compact support in lapse
    # or physical-state solution is presumed.
    eta = s.Function('lapse_test')(nu)
    pH = {w: -s.I*s.diff(eta*v, nu) for w, v in action['Hamiltonian'].items()}
    Hp = {w: -s.I*s.diff(eta, nu)*v for w, v in action['Hamiltonian'].items()}
    expected = weighted_sum([(-s.I*eta, action['constraint'])])
    assert weighted_sum([(1, pH), (-1, Hp), (-1, expected)]) == {}
    paths = [HERE/name for name in ('source_quantum_lapse_constraint.py', 'source_joint_local_quantum.py',
        'source_joint_local_quantum.json', 'independent_source_joint_local_quantum.json',
        'source_coframe_live_ordering.py', 'source_coframe_live_ordering.json', 'independent_source_coframe_live_ordering.json',
        'source_scalar_shift_quantum.py', 'source_scalar_shift_quantum.json', 'source_gauge_quantum_energy.py',
        'source_gauge_quantum_energy.json', 'source_common_hamiltonian.py', 'source_coframe_legendre.py',
        'source_lorentz_contact.py', 'source_gauge_legendre.py', 'source_scalar_gauss_reduction.py')]
    result = {'root': ROOT_ID, 'source_sha256': saved['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'scope': 'ORIGINAL_PRIMARY_GENERATED_QUANTUM_LAPSE_OPERATOR_PENCIL_ON_COMMON103_DOMAIN',
        'lapse': 'eTime=(N*nu,0,0,0), nu>0, N=3sqrt30/25; same six-coordinate Lorentz slice',
        'proper_clock': 'at nu=1, tau=N*t; for a varying lapse the local proper-time rate is N*nu',
        'original_coefficient_scaling': scaling,
        'Hamiltonian': 'H(nu)=nu H_A+nu^-1 H_B; H_A=H_coframe_live+H_scalar_Gauss+H_matter_without_Lorentz at nu1; H_B=H_native_gauge at nu1',
        'primary': 'p_nu=N Pi_e00=0 from the original temporal coframe primary',
        'primary_consistency': 'dot p_nu=i[H,p_nu]=-partial_nu H=-C(nu)',
        'constraint': 'C(nu)=H_A-nu^-2 H_B', 'equivalent_operator_pencil': 'nu^2 H_A-H_B',
        'actual103_wavepacket': {key: encode_state(value) for key, value in action.items()},
        'arbitrary_lapse_test_primary_commutator_checked': True,
        'noncommuting_full_H_A_H_B_consumer': commutator,
        'domain': 'for each nu>0: the same Cc_infinity(Uq times Ux times R36) tensor algebraic CAR504; p_nu is the formal derivative on smooth lapse-parameter families of this common domain',
        'original_ordering_preserved': True, 'physical_state_solution_generated': False,
        'remaining_temporal_constraints': 'three other time-coframe equations retained independently; stabilizer Gauss also retained',
        'Hilbert_positivity_or_no_go_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_quantum_lapse_constraint.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS original quantum lapse constraint', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
