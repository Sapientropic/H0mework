#!/usr/bin/env python3
"""Exact volume/shape representation of the original coframe quantum form.

The radius below is sqrt(det spatial coframe), a configuration coordinate;
it is not a spatial distance or a composite-particle separation. The five
shape momenta have explicit global unitary flows, with the original CAR
connection and all normal products retained.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_joint_form_hamiltonian import read_bound
from source_coframe_live_ordering import SourceCoframeLiveOrdering, full, verify_jet_action
from source_coframe_legendre import rational
from source_lorentz_contact import equal, encode
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state
from source_quantum_gauss_section import exterior_word


def simp(A):
    return A.applyfunc(s.simplify) if isinstance(A, s.MatrixBase) else s.simplify(A)


class SourceCoframeVolumeShape:
    def __init__(self):
        self.source = SourceCoframeLiveOrdering(); c = self.source
        self.q = s.Matrix(c.q); q = self.q
        self.v = q[0]*q[2]*q[5]; v = self.v
        self.number = s.Symbol('particle_number', integer=True, nonnegative=True)
        r = s.sqrt(v); g = s.Matrix([s.diff(v, x)/v for x in q])
        self.inverse_coordinates = s.Matrix([r, s.log(q[0])-s.log(v)/3,
            s.log(q[2])-s.log(v)/3, q[1]/v**s.Rational(1, 3),
            q[3]/v**s.Rational(1, 3), q[4]/v**s.Rational(1, 3)])
        self.J = self.inverse_coordinates.jacobian(q)
        self.coordinate_Hessians = [s.hessian(x, q) for x in self.inverse_coordinates]
        self.r = s.Symbol('volume_radius', positive=True)
        self.theta = s.Matrix(s.symbols('shape_u shape_w shape_a shape_b shape_c', real=True))
        u, w, a, b, z = self.theta; self.coordinates = s.Matrix([self.r, *self.theta])
        self.forward = self.r**s.Rational(2, 3)*s.Matrix([s.exp(u), a, s.exp(w), b, z, s.exp(-u-w)])
        self.substitution = dict(zip(q, self.forward))
        forward_J = self.forward.jacobian(self.coordinates)
        self.jacobian = simp(forward_J.det())
        assert self.jacobian == 2*self.r**3
        equal(simp(self.J.subs(self.substitution)*forward_J), s.eye(6))
        equal(simp(forward_J*self.J.subs(self.substitution)), s.eye(6))
        metric = simp(self.J*c.K*self.J.T)
        assert simp(metric[0, 0]-3*c.N/16) == 0
        equal(metric[0, 1:], s.zeros(1, 5))
        t = rational(c.K*g)
        D = rational(s.I*c.drift.T)+self.number*t
        drift = simp(s.Matrix([-sum(c.K[i, j]*H[i, j] for i in range(6) for j in range(6))-
            (self.J[row, :]*D)[0] for row, H in enumerate(self.coordinate_Hessians)]))
        assert simp(drift[0]+3*c.N*(2*self.number+7)/(16*r)) == 0
        self.shape_metric = self.shape(simp(metric[1:, 1:]*v/c.N))
        self.shape_divergence = s.Matrix([sum(s.diff(self.shape_metric[i, j], self.theta[i])
            for i in range(5)) for j in range(5)])
        equal(simp(self.shape(drift[1:, :]*v/c.N)+self.shape_divergence), s.zeros(5, 1))
        Mh = [rational(M+s.I*t[j]*s.eye(8)) for j, M in enumerate(c.M)]
        equal(simp(sum((self.J[0, j]*Mh[j] for j in range(6)), s.zeros(8))), s.zeros(8))
        self.mixed = [self.shape(simp(v/c.N*sum((self.J[i, j]*Mh[j] for j in range(6)), s.zeros(8))))
                      for i in range(1, 6)]
        equal(simp(sum((M.diff(self.theta[i]) for i, M in enumerate(self.mixed)), s.zeros(8))), s.zeros(8))
        self.V = s.Matrix([[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, a, s.exp(u), 0, 0],
            [-b, -b, 0, s.exp(u), a], [-z, -z, 0, 0, s.exp(w)]])
        self.G = s.diag(s.Matrix([[s.Rational(1, 3), -s.Rational(1, 6)],
                                 [-s.Rational(1, 6), s.Rational(1, 3)]]), s.eye(3))
        equal(simp(self.V*self.G*self.V.T+self.shape_metric), s.zeros(5))
        assert self.G.eigenvals() == {s.Rational(1, 6): 1, s.Rational(1, 2): 1, s.S.One: 3}
        coefficients = self.G.inv()*self.V.inv()
        self.B = [simp(-sum((coefficients[j, i]*self.mixed[i]/2 for i in range(5)), s.zeros(8)))
                  for j in range(5)]
        assert all(not M.free_symbols for M in self.B)
        self.divergences = s.Matrix([sum(s.diff(self.V[i, j], self.theta[i]) for i in range(5)) for j in range(5)])
        equal(self.divergences, s.Matrix([-2, -1, 0, 0, 0]))
        for j, B in enumerate(self.B):
            equal(B.H, B)
            equal(B*B, s.zeros(8) if j < 2 else s.eye(8)/16)
        equal(sum((self.divergences[i]*self.G[i, j]*self.B[j] for i in range(5) for j in range(5)), s.zeros(8)), s.zeros(8))
        assert (self.divergences.T*self.G*self.divergences)[0]/4 == s.Rational(1, 4)
        flat = s.Matrix.hstack(*(J.reshape(64, 1) for J in c.J))
        self.normal_tensor = self.shape(rational(flat*c.W*flat.T)*v/c.N)
        self.onebody = self.shape(rational(c.one_body+c.correction)*v/c.N)
        assert not self.normal_tensor.free_symbols and not self.onebody.free_symbols
        equal(self.onebody, -9*s.eye(8)/4)
        # Turn the two original current slots into the actual two-spin
        # operator, retaining their order before estimating its finite norm.
        self.pair_tensor = s.Matrix(64, 64, lambda ij, kl:
            self.normal_tensor[8*(ij//8)+(kl//8), 8*(ij % 8)+(kl % 8)])
        equal(self.pair_tensor.H, self.pair_tensor)
        self.pair_bound = max(sum(abs(self.pair_tensor[i, j]) for j in range(64)) for i in range(64))
        self.radial_potential = 3*(2*self.number+7)*(2*self.number+5)/64

    def shape(self, A):
        result = simp(A.subs(self.substitution))
        assert self.r not in result.free_symbols
        return result

    def flow(self, j, time):
        u, w, a, b, c = self.theta
        return (s.Matrix([u+time, w, a, b*s.exp(-time), c*s.exp(-time)]),
            s.Matrix([u, w+time, a*s.exp(time), b*s.exp(-time), c*s.exp(-time)]),
            s.Matrix([u, w, a+time*s.exp(u), b, c]),
            s.Matrix([u, w, a, b+time*s.exp(u), c]),
            s.Matrix([u, w, a, b+time*a, c+time*s.exp(w)]))[j]

    def complete_flows(self):
        t, s0 = s.symbols('flow_time flow_time_second', real=True)
        brackets = []
        for i in range(5):
            for j in range(i+1, 5):
                bracket = self.V[:, j].jacobian(self.theta)*self.V[:, i]-self.V[:, i].jacobian(self.theta)*self.V[:, j]
                coefficient = simp(self.V.inv()*bracket)
                assert not coefficient.free_symbols
                if coefficient.todok(): brackets.append({'left': i, 'right': j, 'coefficients': encode(coefficient)})
        records = []
        word = (144, 396)
        for j in range(5):
            flow = self.flow(j, t)
            equal(simp(flow.diff(t)-self.V[:, j].subs(dict(zip(self.theta, flow)), simultaneous=True)), s.zeros(5, 1))
            equal(simp(flow.subs(t, 0)-self.theta), s.zeros(5, 1))
            equal(simp(self.flow(j, s0).subs(dict(zip(self.theta, flow)), simultaneous=True)-self.flow(j, t+s0)), s.zeros(5, 1))
            determinant = simp(flow.jacobian(self.theta).det())
            assert simp(determinant-s.exp(self.divergences[j]*t)) == 0
            U = s.eye(8) if j < 2 else s.cos(t/4)*s.eye(8)+4*s.I*s.sin(t/4)*self.B[j]
            equal(simp(U.H*U), s.eye(8)); equal(simp(U.diff(t)-s.I*self.B[j]*U), s.zeros(8))
            image = exterior_word(full(U), word)
            norm = sum(s.conjugate(c)*c for c in image.values())
            assert simp(s.expand(norm.rewrite(s.exp))) == 1
            records.append({'index': j, 'global_flow': encode(flow), 'Jacobian': str(determinant),
                'unitary_density_factor': str(s.exp(self.divergences[j]*t/2)), 'spin_unitary': encode(U),
                'actual_N2_image': encode_state(image)})
        return {'brackets': brackets, 'five_global_flows': records,
            'source_Hilbert_action': 'U_j(t)f(theta)=exp(div(V_j)t/2) Gamma(exp(i t B_j tensor I63)) f(Phi_j(t,theta)).',
            'unitarity': 'The displayed positive Jacobian cancels the squared density factor under change of variables on all R5. The original finite CAR exterior functor preserves the unitary spin factor, for every occupation sector.',
            'common_domain': 'Each explicit global diffeomorphism and constant spin rotation preserves smooth compact support. Dominated convergence on this dense test space gives strong continuity of these five unitary groups.',
            'generators': 'P_j+dGamma(B_j), P_j=-i(V_j+div(V_j)/2). These are the original angular covariant momenta; their flows are not asserted to commute.'}

    def actual_consumer(self, word):
        c = self.source; m = len(word)
        q = (s.Rational(7, 3), s.Rational(2, 11), s.Rational(9, 4),
             -s.Rational(2, 13), s.Rational(2, 17), s.Rational(32, 21))
        point = dict(zip(self.q, q)); r = 2*s.sqrt(2)
        assert simp(self.v.subs(point)-8) == 0
        shape_point = dict(zip(self.theta, (s.log(s.Rational(7, 6)), s.log(s.Rational(9, 8)),
            s.Rational(1, 11), -s.Rational(1, 13), s.Rational(1, 17))))
        gradient = s.Matrix([s.Rational(i-2, 19)+s.I*s.Rational(i+1, 17) for i in range(6)])
        direction = s.Matrix([s.Rational(i % 3-1, 23) for i in range(6)])
        Hessian = direction*direction.T-s.eye(6)
        alpha = s.Rational(2*m+7, 2)
        ell = s.zeros(6, 1); ell[0] = alpha/r
        logH = s.zeros(6); logH[0, 0] = -alpha/r**2
        inner_g = gradient-ell
        inner_H = Hessian-ell*gradient.T-gradient*ell.T+ell*ell.T-logH
        J = simp(self.J.subs(point)); coordinate_H = [simp(H.subs(point)) for H in self.coordinate_Hessians]
        qg = simp(J.T*inner_g)
        qH = simp(J.T*inner_H*J+sum((inner_g[i]*H for i, H in enumerate(coordinate_H)), s.zeros(6)))
        data = c.coefficients(q)
        raw = verify_jet_action(data, word, 1, qg, qH)
        actual = {tuple(w): s.sympify(value) for w, value in raw['raw_nested_square']}
        constant = verify_jet_action(data, word, 1, s.zeros(6, 1), s.zeros(6))
        terms = [(1, {tuple(w): s.sympify(value) for w, value in constant['raw_nested_square']})]
        metric = simp(self.shape_metric.subs(shape_point))
        div = simp(self.shape_divergence.subs(shape_point))
        scalar = -3*c.N*Hessian[0, 0]/16
        scalar += c.N/r**2*(self.radial_potential.subs(self.number, m)-
            sum(metric[i, j]*Hessian[i+1, j+1] for i in range(5) for j in range(5))-
            (div.T*gradient[1:, :])[0])
        terms.append((scalar, {word: 1}))
        for i, M in enumerate(self.mixed):
            terms.append((-s.I*c.N/r**2*gradient[i+1], apply_superposition(full(simp(M.subs(shape_point))), {word: 1})))
        separated = weighted_sum(terms)
        assert weighted_sum([(1, actual), (-1, separated)]) == {}
        missing = weighted_sum([(1, separated), (-c.N/r**2*self.radial_potential.subs(self.number, m), {word: 1})])
        assert weighted_sum([(1, missing), (-1, actual)])
        return {'q': list(map(str, q)), 'volume_radius': str(r), 'input_CAR': list(word),
            'configuration_gradient6': encode(gradient), 'configuration_Hessian6': encode(Hessian),
            'original_q_gradient6': encode(qg), 'original_q_Hessian6': encode(qH),
            'original_nested_square_image': encode_state(actual), 'volume_shape_image': encode_state(separated),
            'nonzero_omitted_radial_half_density_term': str(c.N/r**2*self.radial_potential.subs(self.number, m))}


def main():
    started = time.monotonic()
    deps = ('source_temporal_coframe_pairing', 'independent_source_temporal_coframe_pairing',
            'source_coframe_weyl_symbol', 'independent_source_coframe_weyl_symbol')
    for name in deps: read_bound(name)
    model = SourceCoframeVolumeShape()
    print('PASS exact source volume/shape coordinates, full coframe metric and constant original CAR connection', flush=True)
    flows = model.complete_flows()
    consumers = [model.actual_consumer(word) for word in ((144,), (144, 396))]
    print('PASS five complete source unitary flows and actual fullCAR radial half-density readback', flush=True)
    files = [HERE/(name+'.json') for name in deps]+[HERE/name for name in (
        'source_coframe_volume_shape.py', 'source_coframe_live_ordering.py', 'source_coframe_legendre.py',
        'source_temporal_coframe_pairing.py', 'source_quantum_gauss_section.py', 'source_gauss_quantum_current.py')]
    N = model.number
    finite_bound = s.expand(model.pair_bound*N*(N-1)+9*N/4+3*N**2/16+model.radial_potential-s.Rational(1, 4))
    result = {'root': ROOT_ID, 'scope': 'SOURCE_COFRAME_VOLUME_SHAPE_FORM_AND_EXPLICIT_GLOBAL_COVARIANT_MOMENTUM_FLOWS',
        'source_sha256': model.source.source['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'configuration_coordinate_map': {'forward': encode(model.forward), 'inverse': encode(model.inverse_coordinates),
            'positive_Jacobian': str(model.jacobian), 'source_point': 'r=1, theta=(0,0,0,0,0)',
            'physical_meaning': 'r=sqrt(det spatial coframe), not spatial radius or hadron separation.'},
        'source_pairing': 'dq6*v^(m+2)=2*r^(2m+7) dr dtheta5. The existing scalar/gauge density is independent of these six coframe variables.',
        'half_density': 'U_m=sqrt(2)*r^(m+7/2); the sqrt(2) is the actual coordinate Jacobian, not a leg normalization.',
        'shape_principal': encode(model.shape_metric), 'source_vector_fields': encode(model.V),
        'constant_positive_Gram': encode(model.G), 'constant_spin8_connection': [encode(B) for B in model.B],
        'original_normal_current_tensor': encode(model.normal_tensor), 'original_onebody': encode(model.onebody),
        'nonformal_covariant_momentum_flows': flows,
        'exact_operator': 'U_m Hcoframe(n,b) U_m^-1=n*(-3/16*partial_r^2+(-Q_m+C_m)/r^2+3*r^2). The original coframe family is independent of b.',
        'angular_positive_form': 'Q_m is the sum with the displayed positive Gram of ||(P_j+dGamma(B_j))f||^2 on the actual compact smooth shape/CAR core; all five generators have the displayed global unitary flows.',
        'finite_Fock_constant': 'C_m=original normal-current tensor+dGamma(-9/4 I)+sum_j dGamma(B_j)^2+(3(2m+7)(2m+5)/64-1/4) I.',
        'generated_bounds': {'original_two_spin_operator_row_bound': str(model.pair_bound),
            'constant_Cm_norm_bound': str(finite_bound), 'original_spin_B_squared': 'B0=B1=0, B2^2=B3^2=B4^2=I8/16'},
        'actual_fullCAR_consumers': consumers,
        'direct_consumer': 'The genuine coframe operator domain and the grade-zero clock/resolvent construction: the inverse-volume coefficient is exposed exactly, without a bounded-momentum or static-CAR replacement.',
        'full_Hamiltonian_extension_time_root_spectrum_or_lifetime_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_coframe_volume_shape.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source coframe volume/shape operator', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
