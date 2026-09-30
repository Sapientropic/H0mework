#!/usr/bin/env python3
"""Live coefficients of the original coframe CCR-CAR square.

The six-coordinate Lorentz slice and the coefficient-left ordering are the
ones in source_coframe_quantum_kinetic. Keeping that order with variable
coefficients generates additional first-order and one-body terms. This
constructs a local differential operator; it does not select a Hilbert
completion or an ordering-independent quantization of the classical action.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, ROOT, ROOT_ID, decode
from source_coframe_legendre import SourceCoframeLegendre, pack, rational
from source_lorentz_contact import clean, equal, encode, ETA
from source_gauss_quantum_current import apply_current, normal_pair, weighted_sum, encode_state


FREE = (5, 9, 10, 13, 14, 15)
DEPENDENT = (1, 2, 3, 6, 7, 11)


def req(left, right):
    equal(rational(left-right), s.zeros(*left.shape))


class SourceCoframeLiveOrdering:
    def __init__(self):
        self.model = SourceCoframeLegendre()
        self.source = json.loads((HERE/'source_coframe_quantum_kinetic.json').read_text())
        self.e0 = decode(self.source['source_coframe'])
        self.N = self.e0[0, 0]
        self.q = tuple(s.Symbol('q'+str(j), positive=True) if j in (0, 2, 5)
                       else s.Symbol('q'+str(j), real=True) for j in range(6))
        self.e = self.e0.copy()
        for index, value in zip(FREE, self.q):
            self.e[index] = value
        self.det = s.factor(self.e.det())
        self.Hinv = rational(self.model.lorentz.inverse(self.e))
        self.Gt = self.model.at(self.model.G[:, :16], self.e)
        h = self.e[:, 1:].T*ETA*self.e[:, 1:]
        R = rational(self.model.metric_lift_numerator(self.e)/self.det)
        B_inverse = rational(4*self.det*self.model.metric_inverse_numerator.xreplace(
            dict(zip(self.model.h_variables, pack(h))))/h.det())
        self.Q = rational(R*B_inverse*R.T)
        spatial = self.e.copy(); spatial[:, 0] = s.zeros(4, 1)
        self.Z = s.Matrix.hstack(*[(T*spatial).reshape(16, 1) for T in self.model.lorentz.basis])
        minor = self.Z.T[:, DEPENDENT]
        self.A, self.S = s.zeros(16, 6), s.zeros(16, 6)
        response = rational(-minor.inv()*self.Z.T[:, FREE])
        for a, j in enumerate(FREE):
            self.A[j, a] = 1
        for a, j in enumerate(DEPENDENT):
            self.A[j, :] = response[a, :]
            self.S[j, :] = -minor.inv()[a, :]
        self.A, self.S = rational(self.A), rational(self.S)
        self.L = rational(self.S*s.eye(24)[:6, :]+self.Gt.T*self.Hinv)
        ports = self.model.lorentz.raw_matter_ports(self.e)
        self.E = ports['E']
        native = [rational(self.E.inv()*V) for V in ports['V']]
        self.J = [rational(s.diag(s.I*M, s.I*M.conjugate())) for M in native]
        self.T = [rational(sum((self.L[i, a]*self.J[a] for a in range(24)), s.zeros(8)))
                  for i in range(16)]
        self.K = rational(self.A.T*self.Q*self.A/2)
        self.M = [rational(sum(((self.A.T*self.Q)[r, j]*self.T[j] for j in range(16)), s.zeros(8)))
                  for r in range(6)]
        self.W = rational((self.L.T*self.Q*self.L+self.Hinv)/2)
        self.one_body = rational(sum((v*self.J[a]*self.J[b]
                                      for (a, b), v in self.W.todok().items()), s.zeros(8)))
        self.dA = [rational(self.A.diff(q)) for q in self.q]
        self.dT = [[rational(T.diff(q)) for T in self.T] for q in self.q]
        self.drift = rational(-s.I*sum(((self.A.T*self.Q)[r, j]*self.dA[r][j, :]
                                       for r in range(6) for j in range(16)), s.zeros(1, 6))/2)
        self.correction = rational(-s.I*sum(((self.A.T*self.Q)[r, j]*self.dT[r][j]
                                            for r in range(6) for j in range(16)), s.zeros(8))/2)

    def at(self, matrix, values):
        return rational(matrix.subs(dict(zip(self.q, values))))

    def coefficients(self, values):
        scalar = lambda expression: s.cancel(expression.subs(dict(zip(self.q, values))))
        return {**{name: self.at(getattr(self, name), values)
                   for name in ('A', 'S', 'L', 'Q', 'Hinv', 'K', 'W', 'drift', 'correction', 'one_body')},
                **{name: [self.at(value, values) for value in getattr(self, name)] for name in ('J', 'T', 'M', 'dA')},
                'dT': [[self.at(T, values) for T in row] for row in self.dT],
                'constant': 3*scalar(self.det)}


def full(matrix):
    return clean(s.kronecker_product(matrix, s.eye(63)))


def verify_jet_action(data, state, f0, f1, f2):
    """Actual value on an arbitrary second jet, using the nested source square."""
    J, T, M = [[full(matrix) for matrix in data[key]] for key in ('J', 'T', 'M')]
    dT = [[full(matrix) for matrix in row] for row in data['dT']]
    unit = {state: s.S.One}
    cur = lambda matrix, vector: weighted_sum((v, apply_current(matrix, word)) for word, v in vector.items())
    inner = [weighted_sum([(-s.I*sum(data['A'][j, t]*f1[t] for t in range(6)), unit),
                            (f0, cur(T[j], unit))]) for j in range(16)]
    dinner = [[weighted_sum([
        (-s.I*sum(data['dA'][r][j, t]*f1[t]+data['A'][j, t]*f2[r, t] for t in range(6)), unit),
        (f0, cur(dT[r][j], unit)), (f1[r], cur(T[j], unit))]) for j in range(16)] for r in range(6)]
    raw = [(data['constant']*f0, unit)]
    for (i, j), coefficient in data['Q'].todok().items():
        outer = weighted_sum([(-s.I*data['A'][i, r], dinner[r][j]) for r in range(6)]+[(1, cur(T[i], inner[j]))])
        raw.append((coefficient/2, outer))
    raw += [(coefficient*f0/2, cur(J[a], cur(J[b], unit))) for (a, b), coefficient in data['Hinv'].todok().items()]
    pieces = {
        'kinetic': weighted_sum([(-sum(v*f2[r, t] for (r, t), v in data['K'].todok().items()), unit)]),
        'mixed': weighted_sum((-s.I*f1[r], cur(M[r], unit)) for r in range(6)),
        'drift': weighted_sum([(-s.I*sum(data['drift'][r]*f1[r] for r in range(6)), unit)]),
        'coefficient_current': weighted_sum([(f0, cur(full(data['correction']), unit))]),
        'normal_quartic': weighted_sum((v*f0, normal_pair(J[a], J[b], state)) for (a, b), v in data['W'].todok().items()),
        'one_body': weighted_sum([(f0, cur(full(data['one_body']), unit))]),
        'constant': weighted_sum([(data['constant']*f0, unit)])}
    raw = weighted_sum(raw)
    ordered = weighted_sum((1, value) for value in pieces.values())
    assert weighted_sum([(1, raw), (-1, ordered)]) == {}
    return {'input_CAR': list(state), 'raw_nested_square': encode_state(raw),
            'ordered_terms': {key: encode_state(value) for key, value in pieces.items()}}


def main():
    started = time.monotonic(); model = SourceCoframeLiveOrdering()
    req(model.Z.T*model.A, s.zeros(6)); req(model.Z.T*model.S, -s.eye(6))
    req(model.A.T*s.eye(16)[:, FREE], s.eye(6)); req(model.S.T*s.eye(16)[:, FREE], s.zeros(6))
    req(model.Q, model.Q.T); req(model.Hinv, model.Hinv.T)
    baseline = tuple(model.e0[j] for j in FREE)
    at_source = model.coefficients(baseline)
    old = model.source['ordered_Hamiltonian']
    req(at_source['K'], decode(old['CCR_kinetic_weight']))
    req(at_source['W'], decode(old['whole_current_square_weight']))
    req(at_source['one_body'], decode(old['one_body_spin8_matrix']))
    for a in range(24):
        req(at_source['J'][a], decode(model.source['source_quantum_current_spin8_tensor_identity63'][a]))
    for r in range(6):
        req(at_source['M'][r], decode(old['mixed_spin8_matrices'][r]))
    print('PASS generic live six-coordinate primary graph and original source coefficient restriction', flush=True)
    values = (s.Rational(7, 6), s.Rational(1, 11), s.Rational(9, 8), s.Rational(-1, 13), s.Rational(1, 17), s.Rational(11, 10))
    data = model.coefficients(values)
    # Both all-six-coordinate jets and a constant germ are realized by local
    # compactly supported smooth functions in the same open chart.
    f0 = s.Rational(3, 2)
    f1 = s.Matrix([s.Rational(j+1, 7) for j in range(6)])
    f2 = s.Matrix(6, 6, lambda i, j: s.Rational((i+1)*(j+1), 19)+(1 if i == j else 0))
    records = [verify_jet_action(data, (0, 315), f0, f1, f2),
               verify_jet_action(data, (63, 126, 252), f0, f1, f2),
               verify_jet_action(data, (0,), 1, s.zeros(6, 1), s.zeros(6))]
    assert data['drift'].todok() or data['correction'].todok()
    assert records[0]['ordered_terms']['drift'] or records[0]['ordered_terms']['coefficient_current']
    print('PASS live coframe nested CCR-CAR square with generated coefficient derivatives', flush=True)
    paths = [HERE/name for name in ('source_coframe_live_ordering.py', 'source_coframe_quantum_kinetic.py',
        'source_coframe_quantum_kinetic.json', 'independent_source_coframe_quantum_kinetic.json',
        'source_coframe_legendre.py', 'source_lorentz_contact.py', 'source_gauss_quantum_current.py')]
    result = {'root': ROOT_ID, 'source_sha256': model.source['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'scope': 'LIVE_COFRAME_ORDERED_LOCAL_CCR_CAR_DIFFERENTIAL_OPERATOR',
        'chart': 'eTime fixed at its original source value; Lorentz slice fixes coordinates 1,2,3,6,7,11; q0,q2,q5>0 and q1,q3,q4 real',
        'coframe': encode(model.e), 'free_coordinates': list(FREE),
        'ordering': 'H=1/2 sum_ij Q_ij(q) P_i P_j +1/2 sum_ab Hinv_ab(q) J_a J_b+3 det(e); P_i=sum_r A_ir(q) kappa_r+J(T_i(q)); every displayed coefficient is on the left',
        'original_phase_space': 'kappa=-i partial_q, J(T)=dGamma(T tensor identity63), original real504 CAR; primary pullback remains kappa.dq+Re(i p.dpsi)',
        'ordered_expansion': 'sum_rt K_rt kappa_r kappa_t+sum_r J(M_r) kappa_r+sum_t drift_t kappa_t+J(correction)+sum_ab W_ab normalProduct(J_a,J_b)+J(one_body)+3det(e)',
        'drift_formula': '-i/2 sum_ijr Q_ij A_ir partial_r A_jt',
        'current_correction_formula': '-i/2 sum_ijr Q_ij A_ir partial_r T_j',
        'generic_primary_graph_and_canonical_one_form_checked': True,
        'generic_drift': encode(model.drift), 'generic_current_correction_spin8': encode(model.correction),
        'source_value_drift': encode(at_source['drift']), 'source_value_current_correction_spin8': encode(at_source['correction']),
        'source_value_is_not_coefficient_freezing': True,
        'actual_live_configuration': list(map(str, values)), 'actual_second_jet_consumers': records,
        'domain': 'Cc_infinity of the displayed open six-coordinate chart tensor algebraic CAR(Fin504); all smooth rational coefficients and their finite derivatives preserve compact support, CAR number and this common component domain',
        'coefficient_freezing_omits_nonzero_terms': True,
        'source_order_is_explicit_not_an_ordering_independence_claim': True,
        'quantized_temporal_constraint_solution_or_full_joint_Hilbert_evolution_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_coframe_live_ordering.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS live coframe ordering', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
