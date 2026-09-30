#!/usr/bin/env python3
"""Original BF primary graph and live-coefficient exterior-CAR certification.

The candidate constructor is not imported. Original epsilon Hessians, the
metric quotient inverse and a direct primary linear solve determine the
coefficients. Actual local polynomial differentiation checks their ordered
operator on finite exterior states.
"""
from __future__ import annotations

from collections import defaultdict
import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_lorentz_contact import (
    HERE, BASE, ROOT, ROOT_ID, GENERATORS, original_hessian, geometric_load,
    original_gamma, original_density_ports, real_linear)
from independent_source_coframe_legendre import quotient_right_inverse, quotient_inverse
from independent_source_gauge_legendre import bindings, decode, encode, ETA
from independent_source_gauss_quantum_current import (
    exterior_current, distinct_slot_product, decoded_state)

FREE = (5, 9, 10, 13, 14, 15)
DEPENDENT = (1, 2, 3, 6, 7, 11)
TIME = (0, 4, 8, 12)


def rational(A): return s.SparseMatrix(A).applyfunc(s.cancel)
def eq(A, B): assert not rational(A-B).todok()
def normalize(state): return {k: s.cancel(v) for k, v in state.items() if s.cancel(v) != 0}


def terms(items):
    answer = defaultdict(lambda: s.S.Zero)
    for coefficient, state in items:
        for word, value in state.items(): answer[word] += coefficient*value
    return normalize(answer)


def current(A, state):
    return terms((value, exterior_current(A, word)) for word, value in state.items())


def quartic(A, B, state):
    return terms((value, distinct_slot_product(A, B, word)) for word, value in state.items())


def full(A): return s.kronecker_product(A, s.eye(63))
def state_encode(state): return [[list(k), str(v)] for k, v in sorted(state.items())]


class RawLiveCoefficients:
    def __init__(self):
        active = json.loads((BASE/'active-gauge/receipt.json').read_text())
        self.e0 = s.Matrix(active['actual_background']['coframe']).applyfunc(s.sympify)
        self.N = self.e0[0, 0]
        self.q = tuple(s.Symbol('q'+str(j), positive=True) if j in (0, 2, 5)
                       else s.Symbol('q'+str(j), real=True) for j in range(6))
        self.e = self.e0.copy()
        for index, value in zip(FREE, self.q): self.e[index] = value
        # The covariant epsilon-Hessian inverse follows from H(e)T^T H(I)^-1 T
        # = det(e) I; checking the original H here pays its actual use.
        H = original_hessian(self.e)
        pullback = s.kronecker_product(self.e, s.eye(6))
        self.Hinv = rational(pullback.T*original_hessian(s.eye(4)).inv()*pullback/self.e.det())
        eq(H*self.Hinv, s.eye(24)); eq(self.Hinv*H, s.eye(24))
        raw_e = s.Matrix(4, 4, s.symbols('raw_e0:16', real=True))
        G = geometric_load(raw_e).xreplace(dict(zip(raw_e, self.e)))
        self.Gt = rational(G[:, :16])
        h = rational(self.e[:, 1:].T*ETA*self.e[:, 1:])
        R = quotient_right_inverse(self.e)
        self.Q = rational(R*quotient_inverse(self.e, h)*R.T)
        spatial = self.e.copy(); spatial[:, 0] = s.zeros(4, 1)
        self.Z = s.Matrix.hstack(*((T*spatial).reshape(16, 1) for T in GENERATORS))
        solution, parameters = self.Z.T[:, DEPENDENT].gauss_jordan_solve(
            (-self.Z.T[:, FREE]).row_join(-s.eye(6)))
        assert parameters.rows == 0
        self.A, self.S = s.zeros(16, 6), s.zeros(16, 6)
        for a, i in enumerate(FREE): self.A[i, a] = 1
        for a, i in enumerate(DEPENDENT):
            self.A[i, :] = solution[a, :6]; self.S[i, :] = solution[a, 6:]
        self.A, self.S = rational(self.A), rational(self.S)
        self.L = rational(self.S*s.eye(24)[:6, :]+self.Gt.T*self.Hinv)
        M = rational(-self.Gt.T*self.Hinv*self.Gt)
        eq(M*self.Q*self.A, self.A); eq(M*self.Q*self.L, self.L)
        eq(self.Z.T*self.A, s.zeros(6)); eq(self.Z.T*self.S, -s.eye(6))
        eq(self.A.T*s.eye(16)[:, FREE], s.eye(6)); eq(self.S.T*s.eye(16)[:, FREE], s.zeros(6))
        eq(self.A.extract(TIME, range(6)), s.zeros(4, 6)); eq(self.S.extract(TIME, range(6)), s.zeros(4, 6))
        self.E, V = original_density_ports(self.e, original_gamma())
        native = [rational(self.E.inv()*v) for v in V]
        I = s.eye(4)
        U = s.Matrix.vstack(s.Matrix.hstack(I, s.I*I), s.Matrix.hstack(I, -s.I*I))/s.sqrt(2)
        self.J = [rational(U*(s.I*real_linear(v))*U.H) for v in native]
        for v, j in zip(native, self.J): eq(j, s.diag(s.I*v, s.I*v.conjugate()))
        self.T = [rational(sum((self.L[i, a]*self.J[a] for a in range(24)), s.zeros(8))) for i in range(16)]
        self.K = rational(self.A.T*self.Q*self.A/2)
        self.M = [rational(sum(((self.A.T*self.Q)[r, j]*self.T[j] for j in range(16)), s.zeros(8))) for r in range(6)]
        self.W = rational((self.L.T*self.Q*self.L+self.Hinv)/2)
        self.one_body = rational(sum((v*self.J[a]*self.J[b] for (a, b), v in self.W.todok().items()), s.zeros(8)))
        self.dA = [rational(self.A.diff(q)) for q in self.q]
        self.dT = [[rational(T.diff(q)) for T in self.T] for q in self.q]
        self.drift = rational(-s.I*sum(((self.A.T*self.Q)[r, j]*self.dA[r][j, :]
                                       for r in range(6) for j in range(16)), s.zeros(1, 6))/2)
        self.correction = rational(-s.I*sum(((self.A.T*self.Q)[r, j]*self.dT[r][j]
                                            for r in range(6) for j in range(16)), s.zeros(8))/2)

    def at(self, A, values): return rational(A.subs(dict(zip(self.q, values))))

    def coefficients(self, values):
        return {**{key: self.at(getattr(self, key), values)
            for key in ('A', 'S', 'L', 'Q', 'Hinv', 'K', 'W', 'drift', 'correction', 'one_body')},
            **{key: [self.at(A, values) for A in getattr(self, key)] for key in ('J', 'T', 'M', 'dA')},
            'dT': [[self.at(A, values) for A in row] for row in self.dT],
            'constant': s.cancel(3*self.e.det().subs(dict(zip(self.q, values))))}


def polynomial_action(data, word, f0, gradient, Hessian):
    """Apply nested operators by actual differentiation of a local polynomial.

    Only first coefficient jets enter an operator of order two. No derivative
    hits its outside-left Q coefficient. A smooth compact cutoff equal to one
    near the base point realizes every polynomial germ used here.
    """
    z = s.Matrix(s.symbols('local_increment0:6', real=True)); at0 = dict.fromkeys(z, 0)
    f = f0+(gradient.T*z)[0]+(z.T*Hessian*z)[0]/2
    J, T, mixed = [[full(A) for A in data[key]] for key in ('J', 'T', 'M')]
    unit = {word: s.S.One}
    inner = []
    for j in range(16):
        Ajet = data['A'][j, :]+sum((z[r]*data['dA'][r][j, :] for r in range(6)), s.zeros(1, 6))
        Tjet = full(data['T'][j]+sum((z[r]*data['dT'][r][j] for r in range(6)), s.zeros(8)))
        inner.append(terms([(-s.I*sum(Ajet[r]*s.diff(f, z[r]) for r in range(6)), unit),
                            (f, current(Tjet, unit))]))
    raw_terms = [(data['constant']*f0, unit)]
    for (i, j), coefficient in data['Q'].todok().items():
        derived = {w: -s.I*sum(data['A'][i, r]*s.diff(v, z[r]).subs(at0)
                             for r in range(6)) for w, v in inner[j].items()}
        at_origin = normalize({w: v.subs(at0) for w, v in inner[j].items()})
        raw_terms.extend([(coefficient/2, derived), (coefficient/2, current(T[i], at_origin))])
    raw_terms.extend((v*f0/2, current(J[a], current(J[b], unit))) for (a, b), v in data['Hinv'].todok().items())
    pieces = {
        'kinetic': terms([(-sum(v*Hessian[r, t] for (r, t), v in data['K'].todok().items()), unit)]),
        'mixed': terms((-s.I*gradient[r], current(mixed[r], unit)) for r in range(6)),
        'drift': terms([(-s.I*sum(data['drift'][r]*gradient[r] for r in range(6)), unit)]),
        'coefficient_current': terms([(f0, current(full(data['correction']), unit))]),
        'normal_quartic': terms((v*f0, quartic(J[a], J[b], unit)) for (a, b), v in data['W'].todok().items()),
        'one_body': terms([(f0, current(full(data['one_body']), unit))]),
        'constant': terms([(data['constant']*f0, unit)])}
    actual = terms(raw_terms)
    assert terms([(1, actual)]+[(-1, value) for value in pieces.values()]) == {}
    return actual, pieces


def main():
    began = time.monotonic()
    path = HERE/'source_coframe_live_ordering.json'; candidate = json.loads(path.read_text())
    count = bindings(candidate); assert candidate['root'] == ROOT_ID
    raw = RawLiveCoefficients()
    locals_map = {str(q): q for q in raw.q}
    eq(raw.e, decode(candidate['coframe'], locals_map))
    eq(raw.drift, decode(candidate['generic_drift'], locals_map))
    eq(raw.correction, decode(candidate['generic_current_correction_spin8'], locals_map))
    eq(raw.correction, -9*raw.N*s.eye(8)/(8*raw.q[0]*raw.q[2]*raw.q[5]))
    source = tuple(raw.e0[j] for j in FREE); src = raw.coefficients(source)
    eq(src['drift'], decode(candidate['source_value_drift']))
    eq(src['correction'], decode(candidate['source_value_current_correction_spin8']))
    assert src['correction'].todok() and src['drift'].todok()
    old = json.loads((HERE/'source_coframe_quantum_kinetic.json').read_text()); count += bindings(old)
    for key, old_key in [('K', 'CCR_kinetic_weight'), ('W', 'whole_current_square_weight'), ('one_body', 'one_body_spin8_matrix')]:
        eq(src[key], decode(old['ordered_Hamiltonian'][old_key]))
    print('PASS raw generic epsilon Hessian, full primary solve, actual six-coordinate derivatives and nonzero source-value correction', flush=True)
    values = tuple(map(s.sympify, candidate['actual_live_configuration'])); data = raw.coefficients(values)
    f1 = s.Matrix([s.Rational(j+1, 7) for j in range(6)])
    f2 = s.Matrix(6, 6, lambda i, j: s.Rational((i+1)*(j+1), 19)+(1 if i == j else 0))
    checked = []
    for index, record in enumerate(candidate['actual_second_jet_consumers']):
        f0, gradient, Hessian = (s.Rational(3, 2), f1, f2) if index < 2 else (s.S.One, s.zeros(6, 1), s.zeros(6))
        actual, pieces = polynomial_action(data, tuple(record['input_CAR']), f0, gradient, Hessian)
        assert terms([(1, actual), (-1, decoded_state(record['raw_nested_square']))]) == {}
        for name, value in pieces.items():
            assert terms([(1, value), (-1, decoded_state(record['ordered_terms'][name]))]) == {}, name
        missing = terms([(1, pieces['drift']), (1, pieces['coefficient_current'])]); assert missing
        checked.append({'CAR': record['input_CAR'], 'coefficient_freezing_defect': state_encode(missing)})
    print('PASS actual polynomial differentiation and independent exterior-slot CAR on all three live germs; coefficient-freezing control nonzero', flush=True)
    paths = [Path(__file__), path, HERE/'source_coframe_live_ordering.py',
        HERE/'independent_source_lorentz_contact.py', HERE/'independent_source_coframe_legendre.py',
        HERE/'independent_source_gauge_legendre.py', HERE/'independent_source_gauss_quantum_current.py',
        HERE/'source_coframe_quantum_kinetic.json', BASE/'active-gauge/receipt.json']
    result = {'verdict': 'CERTIFIED_LIVE_COFRAME_COEFFICIENT_LEFT_CCR_CAR_OPERATOR', 'root': ROOT_ID,
        'source_sha256': candidate['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks': count, 'candidate_constructor_imported': False,
        'independent_method': 'raw epsilon Hessian and covariance inverse; direct six-primary linear solve; original real-current basis change; literal q differentiation; independent exterior-slot CAR and distinct-slot normal product',
        'generic_primary_and_domain': {'all10_primary': True, 'canonical_one_form': True, 'six_live_variables': True,
            'fixed_original_time_column': True, 'Cc_infinity_open_chart_tensor_algebraic_CAR504_invariant': True},
        'generic_current_correction': '-9*N/(8*q0*q2*q5) identity504',
        'generic_drift': encode(raw.drift), 'source_value_derivatives_are_not_frozen': True,
        'actual_polynomial_germ_consumers': checked,
        'claim': 'Original explicit coefficient-left ordering with variable coefficients generates the certified first-order drift and CAR one-body correction on one common local domain.',
        'scope': 'ordered local differential operator; no unique-ordering or temporal-constraint/Hilbert-evolution conclusion',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_coframe_live_ordering.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent live coframe ordering', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
