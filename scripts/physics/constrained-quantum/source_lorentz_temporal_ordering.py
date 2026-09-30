#!/usr/bin/env python3
"""Original Lorentz covariance and the complete four-time coframe ordering gap.

The spatial source slice is fixed; its original four time coordinates remain
symbols. Both orderings are evaluated independently before the finite-CAR
normal tensor is simplified. The positive pairing is the existing source U.
"""
from __future__ import annotations
import copy
import hashlib
import json
import time
from types import SimpleNamespace
import sympy as s
from dynamic import HERE, ROOT, ROOT_ID
from source_lorentz_quantum_section import SourceLorentzQuantumSection, SPATIAL
from source_quantum_stabilizer import SourceQuantumStabilizer
from source_quantum_ordered_temporal import SourceTemporalQuantumFamily
from source_coframe_constraints import generic_Lorentz_invariance
from source_coframe_live_ordering import full, verify_jet_action
from source_coframe_legendre import rational
from source_lorentz_contact import clean, equal, encode
from source_gauss_quantum_current import weighted_sum, encode_state
from source_joint_ccr_car_ports import simplified, same
from source_joint_form_hamiltonian import read_bound


class SourceLorentzTemporalOrdering:
    def __init__(self):
        self.source = SourceLorentzQuantumSection()
        self.family = SourceTemporalQuantumFamily(SourceQuantumStabilizer())
        self.y = self.family.y
        self.ambient = copy.copy(self.source)
        self.ambient.e = self.source.e.copy()
        self.ambient.e[:, 0] = s.Matrix(self.y)
        substitutions = dict(zip(self.family.joint.coframe.q, self.source.q))
        def at(value):
            if isinstance(value, list): return [at(v) for v in value]
            if isinstance(value, s.MatrixBase): return rational(value.subs(substitutions))
            return s.cancel(value.subs(substitutions))
        self.ambient.data = {k: at(v) for k, v in self.family.cf.items()}
        self.ambient._ambient_coefficients()
        self._normal_coefficients()

    def _normal_coefficients(self):
        m = self.ambient
        z, alpha = m.z*m.Is.T, m.alpha*m.Is.T
        a2 = [m.Is*H*m.Is.T for H in m.second[:6]]
        z2 = [m.Is*H*m.Is.T for H in m.second[6:]]
        equal(rational(z*m.Q*z.T/2), m.data['K'])
        self.drift = rational(s.Matrix([-sum(v*z2[r][i, j] for (i, j), v in m.Q.todok().items())/2
            + s.I*m.data['drift'][r] for r in range(6)]))
        for r in range(6):
            difference = -sum(((alpha[a, :]*m.Q*z[r, :].T)[0]*m.R8[a] for a in range(6)), s.zeros(8))
            difference -= s.I*sum((z[r, i]*m.T[i] for i in range(16)), s.zeros(8))
            equal(rational(difference+s.I*m.data['M'][r]), s.zeros(8))
        one = m.D-sum((sum(v*a2[a][i, j] for (i, j), v in m.Q.todok().items())*m.R8[a]
            for a in range(6)), s.zeros(8))/2-m.data['correction']
        tensor = s.zeros(64)
        def pair(weight, A, B):
            nonlocal one, tensor
            one += weight*A*B
            tensor += weight*A.reshape(64, 1)*B.reshape(1, 64)
        for a in range(6):
            for b in range(6): pair(-(alpha[a, :]*m.Q*alpha[b, :].T)[0]/2, m.R8[a], m.R8[b])
        for i in SPATIAL:
            for a in range(6): pair(-s.I*alpha[a, i], m.T[i], m.R8[a])
        for a in range(24):
            for b in range(24):
                if weight := m.W[a, b]-m.data['W'][a, b]: pair(weight, m.J[a], m.J[b])
        self.one, self.tensor = rational(one), rational(tensor)
        equal(rational(self.tensor+self.tensor.T), s.zeros(64))
        n, *b = self.y; b2 = sum(v*v for v in b)
        self.number_coefficient = -3*b2/(8*n)
        equal(self.one, self.number_coefficient*s.eye(8))
        expected = s.Matrix([-n/2-b2/(4*n), 0, -b2/(4*n), 0, 0, n/2-b2/(4*n)])
        equal(self.drift, expected)
        # U_m=v^(1+m/2), with the original rho3 factor independent of q.
        number = s.Symbol('source_Number', integer=True, nonnegative=True)
        ell = s.Matrix([(number+2)/2 if j in (0, 2, 5) else 0 for j in range(6)])
        self.current_identity = s.cancel(self.number_coefficient*number-(self.drift.T*ell)[0])
        assert s.cancel(self.current_identity-3*b2/(4*n)) == 0

    def difference(self, value, gradient, *, current_pairing=False):
        """Actual source-produced first-order operator; no supplied correction."""
        out = {}
        for word in set(value)|set(gradient):
            constant = self.current_identity if current_pairing else len(word)*self.number_coefficient
            out[word] = (self.drift.T*gradient.get(word, s.zeros(6, 1)))[0]+constant*value.get(word, 0)
        return simplified(out)

    def primitive_covariance(self):
        """Original16 tensors, before choosing a CAR word or orbit extension."""
        prior = generic_Lorentz_invariance(SimpleNamespace(common=self.family.joint.common))
        m, e = self.source.native, self.source.native.e
        R = m.metric_lift_numerator(e)
        rows = []
        for h, (T, S) in enumerate(zip(m.lorentz.basis, m.lorentz.spin)):
            D = s.kronecker_product(T, s.eye(4))
            ad = s.Matrix(6, 6, lambda i, j: m.lorentz.structure.get((i, h, j), 0))
            U = s.kronecker_product(s.eye(4), ad)
            Z = (T*e).reshape(16, 1)
            def derivative(M):
                return clean(sum((Z[i]*M.diff(e[i]) for i in range(16)), s.zeros(*M.shape)))
            equal(derivative(m.H)+U.T*m.H+m.H*U, s.zeros(24))
            equal(derivative(m.G[:, :16])+U.T*m.G[:, :16]+m.G[:, :16]*D, s.zeros(24, 16))
            equal(derivative(R)-D*R, s.zeros(16, 6))
            for a in range(6):
                equal(S*m.lorentz.spin[a]-m.lorentz.spin[a]*S,
                    sum((ad[c, a]*m.lorentz.spin[c] for c in range(6)), s.zeros(4)))
            # The original inverse E and every ordered current slot at all y.
            e0 = self.ambient.e
            d = (T*e0).reshape(16, 1)
            adj_d = clean(sum((d[i]*m.at(m.dadj[i], e0) for i in range(16)), s.zeros(4)))
            from source_lorentz_contact import GAMMA
            ports = m.lorentz.raw_matter_ports(e0); Ei = ports['E'].inv()
            dP = [clean(sum((s.I*adj_d[mu, b]*GAMMA[b] for b in range(4)), s.zeros(4))) for mu in range(4)]
            for mu in range(4):
                for a in range(6):
                    V = ports['V'][6*mu+a]
                    J = s.I*Ei*V
                    dJ = s.I*(-Ei*dP[0]*Ei*V+Ei*dP[mu]*m.lorentz.spin[a])
                    expected = S*J-J*S-sum((ad[c, a]*s.I*Ei*ports['V'][6*mu+c]
                        for c in range(6)), s.zeros(4))
                    equal(rational(dJ-expected), s.zeros(4))
            rows.append({'generator': h, 'original_H24_G24x16_metricLift16x6': True,
                'all24_original_current_slots_at_all4time': True})
        return {'source_generic_Lorentz_consumer': prior, 'coefficient_rows': rows,
            'ordered_covariance': 'For constant Lambda, Pi transforms by Lambda^-T with the same spin CAR similarity; Q, G, Hinv and every J transform by the checked source tensors. Both ordered Pshift factors and their differentiated coefficients therefore transform together. The fixed linear chain rule has no unretained ordering term.'}


def main():
    began = time.monotonic()
    bound = read_bound('source_lorentz_quantum_section')
    read_bound('source_quantum_ordered_temporal'); read_bound('source_coframe_constraints')
    model = SourceLorentzTemporalOrdering()
    covariance = model.primitive_covariance()
    reports = []
    aliases = {str(y): y for y in model.y}
    for word in ((16, 268), (5, 144, 396)):
        value = {word: s.S.One}
        gradient = {word: s.Matrix([s.I*s.Rational(j-2, 17) for j in range(6)])}
        u = s.Matrix([s.Rational(j % 3-1, 19) for j in range(6)])
        Hessian = {word: u*u.T-s.eye(6)}
        jet = model.source.extend_jet(value, gradient, Hessian)
        ambient = model.ambient.ambient_action(jet)
        result = verify_jet_action(model.ambient.data, word, 1, gradient[word], Hessian[word])
        reduced = {tuple(w): s.sympify(c, locals=aliases) for w, c in result['raw_nested_square']}
        actual = simplified(weighted_sum(((1, ambient), (-1, reduced))))
        expected = model.difference(value, gradient)
        same(actual, expected)
        assert actual
        ell = s.Matrix([s.Rational(len(word)+2, 2) if j in (0, 2, 5) else 0 for j in range(6)])
        same(model.difference(value, {word: gradient[word]-ell}),
            model.difference(value, gradient, current_pairing=True))
        reports.append({'word': list(word), 'actual_alltime_ambient_minus_reduced': encode_state(actual),
            'current_pairing_difference': encode_state(model.difference(value, gradient, current_pairing=True))})
    paths = ('source_lorentz_temporal_ordering.py', 'source_lorentz_quantum_section.py',
        'source_lorentz_quantum_section.json', 'source_quantum_ordered_temporal.py',
        'source_quantum_ordered_temporal.json', 'source_coframe_legendre.py',
        'source_coframe_constraints.py', 'source_coframe_constraints.json',
        'source_coframe_live_ordering.py')
    out = {'root': ROOT_ID, 'scope': 'ORIGINAL_LORENTZ_TENSORS_AND_ALLTIME_COFRAME_QUANTUM_ORDERING_DIFFERENCE',
        'source_sha256': bound['source_sha256'],
        'input_sha256': {str((HERE/p).relative_to(ROOT)): hashlib.sha256((HERE/p).read_bytes()).hexdigest() for p in paths},
        'spatial_source_q': list(map(str, model.source.q)), 'time_coordinates': list(map(str, model.y)),
        'primitive_covariance': covariance, 'all_finite_CAR_normal_coefficients': {
            'principal_and_all6_current_gradient_differences_zero': True,
            'central_drift6': encode(model.drift), 'spin8_onebody_difference': encode(model.one),
            'ordered_normal_tensor64': encode(model.tensor), 'symmetric_normal_tensor_zero': True,
            'full504_extension': 'Every spin8 matrix is tensored with I63; the vanished symmetric normal tensor covers all finite occupations, including cross-sector pairs.'},
        'current_pairing': {'source_U': 'sqrt(rho3)*v^(1+Number/2)',
            'generated_zeroth_order_difference': str(model.current_identity),
            'Number_cancels_after_actual_source_U_pullback': True},
        'actual_consumers': reports,
        'restriction': 'Only the spatial source q is fixed. All four original time parameters remain symbolic on the regular n chart. Neither ordering is changed, and their difference is not identified as a new physical interaction.',
        'seconds': round(time.monotonic()-began, 3)}
    (HERE/'source_lorentz_temporal_ordering.json').write_text(json.dumps(out, indent=2)+'\n')
    print('PASS original Lorentz tensors and all-time coframe ordering:', out['seconds'], 'seconds', flush=True)

if __name__ == '__main__': main()
