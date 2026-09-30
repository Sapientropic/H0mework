#!/usr/bin/env python3
"""Native-matrix audit of the invariant broken complement and quantum Gauss.

No stabilizer producer is imported. Original occupation-bit representations,
native block traces, raw coefficient differentiation and exterior-slot CAR
rebuild the operator on the common103-coordinate compact smooth domain.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_joint_local_quantum import (
    HERE, ROOT, ROOT_ID, RawLiveCoefficients, FREE, representations,
    scalar_coefficients, scalar_action, gauge_coefficients, gauge_action,
    raw_matter, original_inventory, bindings, clean, rational, eq,
    decode, encode, terms, current, polynomial_action, state_encode)
from independent_source_gauss_quantum_current import tensor_apply, decoded_state


def combine(matrices, coefficients):
    return clean(sum((value*matrices[j] for j, value in enumerate(coefficients) if value), s.zeros(*matrices[0].shape)))


class OriginalStabilizer:
    def __init__(self):
        self.inventory = representations()
        self.fund, self.rho, self.matter, self.ad, self.v, self.hashes = self.inventory
        self.Gram = s.Matrix(12, 12, lambda a, b: s.re(-s.trace(self.fund[a][:3, :3]*self.fund[b][:3, :3])-
            s.trace(self.fund[a][3:5, 3:5]*self.fund[b][3:5, 3:5])-self.fund[a][5, 5]*self.fund[b][5, 5]))
        orbit = clean(s.Matrix.hstack(*(T*self.v for T in self.rho)))
        self.select = s.eye(12)[:, list(orbit.rref()[1])]
        self.S = s.Matrix.hstack(*orbit.nullspace())
        self.O = clean(orbit*self.select)
        self.J, free = (self.S.T*self.Gram*self.S).gauss_jordan_solve(self.S.T*self.Gram*self.select)
        assert free.rows == 0
        self.J = clean(self.J); self.B = clean(self.select-self.S*self.J)
        eq(self.S.T*self.Gram*self.B, s.zeros(3, 9)); eq(orbit*self.B, self.O)
        P = clean(s.eye(70)-self.O*(self.O.T*self.O).inv()*self.O.T)
        self.R = P[:, list(P.rref()[1])]; self.Rd = clean(self.R*(self.R.T*self.R).inv())
        self.rhos = [combine(self.rho, self.S[:, h]) for h in range(3)]
        self.rhob = [combine(self.rho, self.B[:, a]) for a in range(9)]
        self.ads = [combine(self.ad, self.S[:, h]) for h in range(3)]
        self.adb = [combine(self.ad, self.B[:, a]) for a in range(9)]
        self.ms = [combine(self.matter, self.S[:, h]) for h in range(3)]
        self.mb = [combine(self.matter, self.B[:, a]) for a in range(9)]
        self.Qs = [clean(s.diag(s.I*T, s.I*T.conjugate())) for T in self.ms]
        self.Qb = [clean(s.diag(s.I*T, s.I*T.conjugate())) for T in self.mb]
        self.Ts = [clean(s.diag(self.Rd.T*T*self.R, ad, ad, ad)) for T, ad in zip(self.rhos, self.ads)]
        self.Tb = [clean(s.diag(self.Rd.T*T*self.R, ad, ad, ad)) for T, ad in zip(self.rhob, self.adb)]
        self.C, self.structure = [], []
        basis = self.B.row_join(self.S)
        for ad in self.ads:
            action, free = basis.gauss_jordan_solve(ad*basis); assert free.rows == 0
            eq(action[:9, 9:], s.zeros(9, 3)); eq(action[9:, :9], s.zeros(3, 9))
            self.C.append(clean(action[:9, :9])); self.structure.append(clean(action[9:, 9:]))

    def universal_covariance(self):
        x = s.Matrix(s.symbols('scalar_coordinate0:61', real=True))
        phi = self.v+self.R*x
        D = clean(self.O.T*s.Matrix.hstack(*(T*phi for T in self.rhob)))
        oldD = clean(self.O.T*s.Matrix.hstack(*(combine(self.rho, self.select[:, a])*phi for a in range(9))))
        eq(D, oldD)
        Ds, Cs = s.MatrixSymbol('original_D', 9, 9), s.MatrixSymbol('induced_C', 9, 9)
        Fs = Ds.T.I
        dDs = -Cs.T*Ds-Ds*Cs
        assert s.expand(dDs.T*Fs+Ds.T*(Cs*Fs+Fs*Cs.T)) == s.ZeroMatrix(9, 9)
        F = s.Matrix(9, 9, s.symbols('inverse_entry0:81'))
        normal = -self.O*F
        reader = self.Rd.row_join(s.zeros(70, 36))
        Y = original_inventory()['scalar']; Y = Y+[s.I*T for T in Y]
        metric = clean(s.diag(self.R.T*self.R, self.Gram, self.Gram, self.Gram))
        for h, (rho, ad, Ts, C) in enumerate(zip(self.rhos, self.ads, self.Ts, self.C)):
            eq(rho+rho.T, s.zeros(70)); eq(rho*self.v, s.zeros(70, 1))
            eq(ad.T*self.Gram+self.Gram*ad, s.zeros(12))
            eq(Ts.T*metric+metric*Ts, s.zeros(97))
            eq(rho*self.O, self.O*C); eq(rho*self.R, self.R*Ts[:61, :61])
            eq(rho*self.Rd, -self.Rd*Ts[:61, :61].T)
            assert s.trace(C) == 0
            dx = Ts[:61, :61]*x
            directional = clean(sum((dx[j]*D.diff(x[j]) for j in range(61)), s.zeros(9)))
            eq(directional, -C.T*D-D*C)
            # The generic inverse equation above and every affine D
            # coefficient give this derivative at every point of det D!=0.
            dF = C*F+F*C.T
            dnormal = -self.O*dF
            eq(dnormal-normal*C.T, rho*normal)
            eq(-reader*Ts.T, rho*reader)
            for a in range(9):
                eq(Ts*self.Tb[a]-self.Tb[a]*Ts, combine(self.Tb, C[:, a]))
                eq(self.Qs[h]*self.Qb[a]-self.Qb[a]*self.Qs[h], s.I*combine(self.Qb, C[:, a]))
            # The two preceding identities give every derivative coefficient
            # of [G_s,Pi_j]=-i rho[j,k] Pi_k, not only a sampled commutator.
            for k in range(3):
                f = self.structure[h][:, k]
                eq(Ts*self.Ts[k]-self.Ts[k]*Ts, combine(self.Ts, f))
                eq(self.Qs[h]*self.Qs[k]-self.Qs[k]*self.Qs[h], s.I*combine(self.Qs, f))
            for a in range(12):
                eq(combine(self.rho, ad[:, a])*phi+self.rho[a]*rho*phi, rho*self.rho[a]*phi)
                eq(self.ms[h]*self.matter[a]-self.matter[a]*self.ms[h], combine(self.matter, ad[:, a]))
                for b in range(12):
                    bracket = self.ad[a][:, b]
                    eq(ad*bracket, combine(self.ad, ad[:, a])[:, b]+self.ad[a]*ad[:, b])
            for a in range(70):
                eq(self.ms[h]*Y[a]-Y[a]*self.ms[h], combine(Y, rho[:, a]))
            eq(self.ms[h], s.kronecker_product(s.eye(4), self.ms[h][:63, :63]))
        self.x_symbols, self.Dsymbol, self.metric = x, D, metric
        return {'all61_affine_D_coefficients_and_inverse_derivative': True,
                'all70_ordered_momentum_coefficients_covariant': True,
                'all9_stabilizer_and27_broken_CCR_CAR_Lie_identities': True,
                'all432_original_bracket_derivations': True, 'all210_full252_Yukawa_identities': True,
                'native_Gram_and_all_scalar_gauge_shift_coefficients_invariant': True,
                'operator_argument': 'The actual70 momenta transform by the original real skew rho. Contracting their ordered squares cancels without permuting operators. All spatial scalar terms and native gauge curvature coefficients transform in invariant pairings. The original full252 Yukawa and spin-only coframe coefficients give the remaining two commutators.',
                'domain_argument': 'D transforms by congruence with trace-zero C, hence det D is invariant. All operators preserve the common compact support and each CAR particle sector; their exact commutators preserve the simultaneous stabilizer kernel under finite powers of H.'}

    def scalar_data(self, e, x, A):
        data = scalar_coefficients(e, x, A, self.inventory)
        eq(data['R'], self.R); eq(data['Rd'], self.Rd); eq(data['O'], self.O)
        y = s.Matrix(s.symbols('local_scalar_gauge0:97', real=True))
        point = dict(zip(y, x.col_join(A.reshape(36, 1))))
        Dsym = self.Dsymbol.xreplace(dict(zip(self.x_symbols, y[:61, :])))
        D = rational(Dsym.subs(point))
        F, free = D.T.gauss_jordan_solve(s.eye(9)); assert free.rows == 0
        F = rational(F); eq(D.T*F, s.eye(9))
        normal = -self.O*F
        Vsym = s.Matrix.vstack(*((T*y).T for T in self.Tb)); V = clean(Vsym.subs(point))
        a = rational(self.Rd.row_join(s.zeros(70, 36))+normal*V)
        drift, dc = s.zeros(1, 97), s.zeros(1, 9)
        for alpha in range(97):
            dD = Dsym.diff(y[alpha])
            dF, free = D.T.gauss_jordan_solve(-dD.T*F); assert free.rows == 0
            dF = rational(dF); eq(dD.T*F+D.T*dF, s.zeros(9))
            dn = -self.O*dF
            da = rational(dn*V+normal*Vsym.diff(y[alpha]))
            drift += a[:, alpha].T*da; dc += a[:, alpha].T*dn
        data.update(a=a, normal=normal, Q=self.Qb, drift=rational(drift), dc=rational(dc), F=F)
        return data

    def rref_control(self, x, expected):
        D = rational(self.Dsymbol.subs(dict(zip(self.x_symbols, x))))
        F, free = D.T.gauss_jordan_solve(s.eye(9)); assert free.rows == 0
        oldbasis = self.select.row_join(self.S)
        records = []
        for h, ad in enumerate(self.ads):
            old_action, free = oldbasis.gauss_jordan_solve(ad*self.select); assert free.rows == 0
            E = clean(old_action[9:, :])
            # The old normal-current defect is (O F E^T)_jk G_s,k.
            # Commuting each G_s,k through the next original momentum
            # produces the reported first-order term; no classical zero is
            # used as an operator replacement.
            commuted = s.zeros(1, 9)
            for k in range(3): commuted += (self.O*F*E[k, :].T).T*self.rhos[k]*self.O*F
            commuted = rational(commuted)
            eq(E, decode(expected[h]['complement_defect']))
            eq(commuted, decode(expected[h]['scalar_square_reordering_coefficient_before_1_over_2h00']))
            records.append(bool(commuted.todok()))
        assert records == [True, True, False]
        return records


def main():
    began = time.monotonic(); path = HERE/'source_quantum_stabilizer.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    paid = ['independent_source_joint_local_quantum.json', 'independent_source_coframe_live_ordering.json',
            'independent_source_scalar_gauss_reduction.json', 'independent_source_gauge_quantum_energy.json']
    for name in paid: count += bindings(json.loads((HERE/name).read_text()))
    m = OriginalStabilizer(); assert m.hashes == candidate['source_sha256']
    algebra = candidate['native_stabilizer']
    for A, key in [(m.S, 'stabilizer_embedding'), (m.Gram, 'native_Gram'), (m.B, 'native_orthogonal_broken_embedding'), (m.J, 'rref_to_orthogonal_correction')]:
        eq(A, decode(algebra[key]))
    eq(m.structure[0][:, 1], s.Matrix([0, 0, -2]))
    eq(m.structure[1][:, 2], s.Matrix([-2, 0, 0]))
    eq(m.structure[2][:, 0], s.Matrix([0, -2, 0]))
    covariance = m.universal_covariance()
    print('PASS raw native Gram orthogonal complement, whole61 D identities and all original ordered-momentum/energy covariance coefficients', flush=True)
    consumer = candidate['actual_consumers']; configuration = consumer['configuration']
    q = tuple(map(s.sympify, configuration['q'])); x, A = decode(configuration['x']), decode(configuration['A'])
    raw_cf = RawLiveCoefficients(); e = raw_cf.at(raw_cf.e, q); cf = raw_cf.coefficients(q)
    for matrix in raw_cf.J+raw_cf.T+raw_cf.M+[raw_cf.correction, raw_cf.one_body]:
        eq(matrix[:4, 4:], s.zeros(4)); eq(matrix[4:, :4], s.zeros(4))
    sc, gauge = m.scalar_data(e, x, A), gauge_coefficients(e, A, m.inventory)
    connection = s.zeros(4, 12); connection[1:, :] = A
    raw = raw_matter(e, sc['phi'], connection)
    matter = clean(-s.I*raw['E_inverse']*raw['lower'])
    matter_Q = clean(s.diag(matter, -matter.conjugate()))
    y = x.col_join(A.reshape(36, 1))
    gradient = s.Matrix.vstack(s.Matrix([s.Rational(j+1, 29) for j in range(6)]), -2*m.metric*y)
    Hessian = gradient*gradient.T-s.diag(s.eye(6), 2*m.metric)
    kernel = consumer['nonzero_simultaneous_Gauss_kernel_state']; state = tuple(kernel['CAR'])
    for h in range(3):
        assert current(m.Qs[h], {state: 1}) == {}
        assert s.cancel(((m.Ts[h]*y).T*gradient[6:, :])[0]) == 0
    coframe, _ = polynomial_action(cf, state, 1, gradient[:6, :], Hessian[:6, :6])
    components = dict(coframe=coframe, scalar=scalar_action(sc, state, gradient[6:, :], Hessian[6:, 6:]),
        gauge=gauge_action(gauge, state, gradient[67:, :], Hessian[67:, 67:]), matter=current(matter_Q, {state: 1}))
    assert all(components.values())
    total = terms((1, value) for value in components.values())
    assert terms([(1, total), (-1, decoded_state(kernel['complete_new_Hamiltonian_image']))]) == {}
    charged = consumer['charged_tensor_polynomial']; word = (charged['boson_coordinate'], tuple(charged['CAR']))
    matrices = [clean(-s.I*T.T) for T in m.Ts]
    images = [tensor_apply(T, Q, {word: s.S.One}) for T, Q in zip(matrices, m.Qs)]
    assert all(images)
    for h in range(3):
        for k in range(3):
            lhs = terms([(1, tensor_apply(matrices[h], m.Qs[h], images[k])), (-1, tensor_apply(matrices[k], m.Qs[k], images[h]))])
            rhs = terms((s.I*value, images[j]) for j, value in enumerate(m.structure[h][:, k]))
            assert terms([(1, lhs), (-1, rhs)]) == {}
    defects = m.rref_control(x, consumer['rref_difference']['actual_nonzero_rref_reordering_coefficients'])
    assert consumer['rref_difference']['old_quantum_square_equivalent_on_constraint_kernel_claimed'] is False
    print('PASS independently differentiated97 coefficients, actual invariant(7,259) wavepacket and four-block image; charged words and old-rref control', flush=True)
    paths = [Path(__file__), path, HERE/'source_quantum_stabilizer.py', HERE/'independent_source_joint_local_quantum.py',
        HERE/'independent_source_coframe_live_ordering.py', HERE/'independent_source_gauss_quantum_current.py',
        HERE/'independent_source_common_hamiltonian.py', HERE/'independent_source_gauge_legendre.py']+[HERE/name for name in paid]
    output = {'verdict': 'CERTIFIED_NATIVE_ORTHOGONAL_STABILIZER_COVARIANCE_AND_COMMON_KERNEL', 'root': ROOT_ID,
        'source_sha256': m.hashes, 'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks': count, 'candidate_constructor_imported': False,
        'independent_method': 'Native block traces and occupation-bit exterior representations; nullspace and Gram linear solve; every affine D coefficient; direct97 coefficient derivatives; raw gauge density and full252 matter; exterior-slot CAR',
        'generic_covariance': covariance,
        'native_stabilizer_embedding': encode(m.S), 'orthogonal_broken_embedding': encode(m.B),
        'actual_invariant_wavepacket': {'CAR': list(state), 'all3_Gauss_actions_zero': True,
            'all4_nonzero_components': {key: state_encode(value) for key, value in components.items()}, 'joint_action': state_encode(total)},
        'charged_all9_CCR_CAR_Lie_words': True, 'old_rref_reordering_nonzero_pattern': defects,
        'same_classical_full_Gauss_surface': 'Pi_orthogonal-Pi_rref=O F J^T G_stabilizer, so original classical energies agree on the full Gauss surface. No equality of the old and new quantum kernels is claimed.',
        'scope': 'Native Gram selects the invariant complement before the original momentum graph is ordered. The resulting common-domain Hamiltonian commutes with all three residual Gauss operators and preserves their nonempty simultaneous kernel under finite powers. Temporal reduction, continuous quantum evolution and spectral measure are separate consumers.',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_quantum_stabilizer.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS independent quantum stabilizer', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
