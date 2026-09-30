#!/usr/bin/env python3
"""Source Lorentz-primary inverse two-jets on the full real504 CAR carrier.

The spatial coframe orbit and original spin representation generate the germ;
no primary solution is supplied. Four temporal coframe coordinates retain
zero momentum for this time-parameterized germ. The ambient coefficient-left
coframe quantization and the existing reduce-first ordering are both read.
Their exact source-point difference is retained without changing either H.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_coframe_live_ordering import (
    SourceCoframeLiveOrdering, FREE, DEPENDENT, full, verify_jet_action)
from source_gauss_quantum_current import (
    apply_superposition, weighted_sum, encode_state)
from source_joint_ccr_car_ports import simplified, same
from source_joint_form_hamiltonian import read_bound
from source_lorentz_contact import clean, equal, encode, GAMMA

TIME = (0, 4, 8, 12)
SPATIAL = tuple(i for i in range(16) if i not in TIME)


class SourceLorentzQuantumSection:
    """The exact source point of the existing six-coordinate coframe slice."""
    def __init__(self):
        self.model = SourceCoframeLiveOrdering()
        self.native = self.model.model
        self.e = self.model.e0
        self.q = tuple(self.e[i] for i in FREE)
        self.data = self.model.coefficients(self.q)
        self.Is = s.eye(16)[:, SPATIAL]
        self.If = s.eye(12)[:, [SPATIAL.index(i) for i in FREE]]
        self.Cp = s.eye(12)[[SPATIAL.index(i) for i in DEPENDENT], :]
        self.L = []
        for T in self.native.lorentz.basis:
            M = s.zeros(16)
            for j in SPATIAL:
                E = s.zeros(4); E[j] = 1
                M[:, j] = (T*E).reshape(16, 1)
            self.L.append(clean(self.Is.T*M*self.Is))
        x = self.Is.T*self.e.reshape(16, 1)
        self.Z = clean(s.Matrix.hstack(*(M*x for M in self.L)))
        self.minor = self.Cp*self.Z
        self.alpha = clean(self.minor.inv()*self.Cp)
        self.z = clean(self.If.T*(s.eye(12)-self.Z*self.alpha))
        self.forward = self.Z.row_join(self.If)
        self.inverse = self.alpha.col_join(self.z)
        equal(self.forward*self.inverse, s.eye(12))
        equal(self.inverse*self.forward, s.eye(12))
        curvature = [s.zeros(12) for _ in range(12)]
        for a in range(6):
            mixed = self.L[a]*self.If*self.z
            for k in range(12):
                curvature[k] += self.alpha[a, :].T*mixed[k, :]+mixed[k, :].T*self.alpha[a, :]
            for b in range(a, 6):
                acceleration = (self.L[a]*self.L[b]+self.L[b]*self.L[a])*x/2
                outer = self.alpha[a, :].T*self.alpha[b, :]
                if b != a:
                    outer += self.alpha[b, :].T*self.alpha[a, :]
                for k in range(12):
                    curvature[k] += acceleration[k]*outer
        self.second = [clean(-sum((self.inverse[i, k]*curvature[k]
            for k in range(12)), s.zeros(12))) for i in range(12)]
        for k in range(12):
            equal(sum((self.forward[k, i]*self.second[i]
                for i in range(12)), s.zeros(12))+curvature[k], s.zeros(12))
        self.R8 = [clean(s.diag(S, S.conjugate())) for S in self.native.lorentz.spin]
        self.R = list(map(full, self.R8))
        self._ambient_coefficients()

    def verify_primary_coefficients(self):
        """All-germ coefficient proof, using the original CAR charge Lie law."""
        n = self.native.lorentz
        for a in range(6):
            for b in range(6):
                coefficients = [n.structure.get((c, a, b), 0) for c in range(6)]
                equal(clean(self.L[a]*self.L[b]-self.L[b]*self.L[a]),
                    sum((v*M for v, M in zip(coefficients, self.L)), s.zeros(12)))
                equal(clean(self.R8[a]*self.R8[b]-self.R8[b]*self.R8[a]),
                    sum((v*M for v, M in zip(coefficients, self.R8)), s.zeros(8)))
            # J_time=i dGamma(diag(S,bar S)) is the original spin primary.
            equal(self.J[a], s.I*self.R8[a])
        equal(self.alpha*self.Z, s.eye(6)); equal(self.z*self.Z, s.zeros(6))
        checked = 0
        for a in range(6):
            for i in range(12):
                for r in range(6):
                    coefficient = (self.L[a][:, i].T*self.z[r, :].T)[0]
                    coefficient += (self.second[6+r][i, :]*self.Z[:, a])[0]
                    assert s.expand(coefficient) == 0
                    checked += 1
                for b in range(6):
                    coefficient = (self.L[a][:, i].T*self.alpha[b, :].T)[0]
                    coefficient += (self.second[b][i, :]*self.Z[:, a])[0]
                    coefficient += sum(self.alpha[c, i]*n.structure.get((b, c, a), 0)/2
                                       for c in range(6))
                    assert s.expand(coefficient) == 0
                    checked += 1
        return checked

    def extend_jet(self, value, gradient, Hessian):
        """Generate a 16-coordinate CAR germ from its actual six-coordinate jet."""
        out = {}
        def add(state, v=0, g=None, H=None):
            for word, coefficient in state.items():
                row = out.setdefault(word, {'value': s.S.Zero,
                    'gradient': s.zeros(12, 1), 'Hessian': s.zeros(12)})
                row['value'] += coefficient*v
                if g is not None: row['gradient'] += coefficient*g
                if H is not None: row['Hessian'] += coefficient*H
        for word in set(value)|set(gradient)|set(Hessian):
            first = gradient.get(word, s.zeros(6, 1))
            second = Hessian.get(word, s.zeros(6))
            dg = self.z.T*first
            ddg = self.z.T*second*self.z+sum((first[j]*self.second[6+j]
                for j in range(6)), s.zeros(12))
            add({word: 1}, value.get(word, 0), dg, ddg)
            for a in range(6):
                add(apply_superposition(self.R[a], {word: 1}),
                    H=self.alpha[a, :].T*dg.T+dg*self.alpha[a, :])
        for a in range(6):
            add(apply_superposition(self.R[a], value),
                g=self.alpha[a, :].T, H=self.second[a])
            for b in range(a, 6):
                ab = apply_superposition(self.R[a], apply_superposition(self.R[b], value))
                if a == b:
                    add(ab, H=self.alpha[a, :].T*self.alpha[b, :])
                else:
                    ba = apply_superposition(self.R[b], apply_superposition(self.R[a], value))
                    sym = weighted_sum(((s.Rational(1, 2), ab), (s.Rational(1, 2), ba)))
                    add(sym, H=self.alpha[a, :].T*self.alpha[b, :]+
                        self.alpha[b, :].T*self.alpha[a, :])
        for row in out.values():
            row['value'] = s.expand(row['value'])
            row['gradient'] = clean(self.Is*row['gradient'])
            row['Hessian'] = clean(self.Is*row['Hessian']*self.Is.T)
        return out

    def verify_primary_jet(self, jet):
        values = {w: r['value'] for w, r in jet.items() if r['value']}
        Z = self.Is*self.Z
        for a in range(6):
            first = {w: -s.I*(Z[:, a].T*r['gradient'])[0] for w, r in jet.items()}
            same(weighted_sum(((1, first), (s.I, apply_superposition(self.R[a], values)))), {})
            for i in range(16):
                dZ = (self.Is*self.L[a]*self.Is.T)[:, i]
                residual = {w: -s.I*((dZ.T*r['gradient'])[0]+
                    (r['Hessian'][i, :]*Z[:, a])[0]) for w, r in jet.items()}
                dg = {w: r['gradient'][i] for w, r in jet.items() if r['gradient'][i]}
                same(weighted_sum(((1, residual),
                    (s.I, apply_superposition(self.R[a], dg)))), {})
        for row in jet.values():
            equal(row['gradient'].extract(TIME, [0]), s.zeros(4, 1))
            equal(row['Hessian'].extract(TIME, range(16)), s.zeros(4, 16))
        return {'original_four_temporal_primary_zero': True,
            'original_six_spin_primary_zero': True, 'all96_spin_primary_derivatives_zero': True}

    def _ambient_coefficients(self):
        source, e = self.native, self.e
        geometry = source.geometry(e)
        self.Q = geometry['velocity_inverse']; Hi = geometry['Lorentz_inverse']
        G = geometry['G'][:, :16]
        ports = source.lorentz.raw_matter_ports(e); Einv = ports['E'].inv()
        self.J = [clean(s.diag(s.I*Einv*V, s.I*(Einv*V).conjugate())) for V in ports['V']]
        B = clean(G.T*Hi)
        C = [clean(sum((B[i, a]*self.J[a] for a in range(24)), s.zeros(8))) for i in range(16)]
        dC = []
        for k in range(16):
            dH = source.at(source.dH[k], e); dG = source.at(source.dG[k][:, :16], e)
            dB = clean(dG.T*Hi-G.T*Hi*dH*Hi)
            dadj = source.at(source.dadj[k], e)
            dE = clean(sum((s.I*dadj[0, b]*GAMMA[b] for b in range(4)), s.zeros(4)))
            dJ = []
            for mu in range(4):
                dp = clean(sum((s.I*dadj[mu, b]*GAMMA[b] for b in range(4)), s.zeros(4)))
                for a, S in enumerate(source.lorentz.spin):
                    M = clean(-Einv*dE*Einv*ports['V'][6*mu+a]+Einv*dp*S)
                    dJ.append(clean(s.diag(s.I*M, s.I*M.conjugate())))
            dC.append([clean(sum((dB[i, a]*self.J[a]+B[i, a]*dJ[a]
                for a in range(24)), s.zeros(8))) for i in range(16)])
        self.W = clean((B.T*self.Q*B+Hi)/2)
        self.D = clean(-s.I*sum((v*dC[i][j]
            for (i, j), v in self.Q.todok().items()), s.zeros(8))/2)
        self.T = [clean(sum((self.Q[i, j]*C[j]
            for j in range(16)), s.zeros(8))) for i in range(16)]

    def ambient_action(self, jet):
        """Original full16 coefficient-left (Pi+G^T Hinv J) squared action."""
        values = {w: r['value'] for w, r in jet.items() if r['value']}
        identity = {w: -sum(v*r['Hessian'][i, j]
            for (i, j), v in self.Q.todok().items())/2+3*self.e.det()*r['value']
            for w, r in jet.items()}
        terms = [(1, identity), (1, apply_superposition(full(self.D), values))]
        for i in SPATIAL:
            dg = {w: r['gradient'][i] for w, r in jet.items() if r['gradient'][i]}
            terms.append((-s.I, apply_superposition(full(self.T[i]), dg)))
        J = list(map(full, self.J))
        terms.extend((v, apply_superposition(J[a], apply_superposition(J[b], values)))
            for (a, b), v in self.W.todok().items())
        return simplified(weighted_sum(terms))

    def complete_ordering_difference(self):
        """Coefficient proof before any occupation or restriction to occupied12."""
        z, alpha = self.z*self.Is.T, self.alpha*self.Is.T
        a2 = [self.Is*H*self.Is.T for H in self.second[:6]]
        z2 = [self.Is*H*self.Is.T for H in self.second[6:]]
        equal(clean(z*self.Q*z.T/2), self.data['K'])
        drift = s.Matrix([s.simplify(-sum(v*z2[r][i, j]
            for (i, j), v in self.Q.todok().items())/2+s.I*self.data['drift'][r]) for r in range(6)])
        for r in range(6):
            matrix = -sum(((alpha[a, :]*self.Q*z[r, :].T)[0]*self.R8[a]
                for a in range(6)), s.zeros(8))
            matrix -= s.I*sum((z[r, i]*self.T[i] for i in range(16)), s.zeros(8))
            equal(clean(matrix+s.I*self.data['M'][r]), s.zeros(8))
        one = self.D-sum((sum(v*a2[a][i, j] for (i, j), v in self.Q.todok().items())*
            self.R8[a] for a in range(6)), s.zeros(8))/2-self.data['correction']
        tensor = s.zeros(64)
        def pair(weight, A, B):
            nonlocal one, tensor
            one += weight*A*B
            tensor += weight*A.reshape(64, 1)*B.reshape(1, 64)
        for a in range(6):
            for b in range(6):
                pair(-(alpha[a, :]*self.Q*alpha[b, :].T)[0]/2, self.R8[a], self.R8[b])
        for i in SPATIAL:
            for a in range(6):
                pair(-s.I*alpha[a, i], self.T[i], self.R8[a])
        for a in range(24):
            for b in range(24):
                if weight := self.W[a, b]-self.data['W'][a, b]:
                    pair(weight, self.J[a], self.J[b])
        equal(clean(one), s.zeros(8)); equal(clean(tensor+tensor.T), s.zeros(64))
        return drift

    def orbit_density_readback(self, drift):
        spatial = self.model.e.copy(); spatial[:, 0] = s.zeros(4, 1)
        generic = s.Matrix.hstack(*((T*spatial).reshape(16, 1)
            for T in self.native.lorentz.basis))
        determinant = s.factor(generic.extract(DEPENDENT, range(6)).det())
        q = self.model.q; v = q[0]*q[2]*q[5]
        density = -determinant
        assert s.factor(density-q[0]*q[2]**2*q[5]**3) == 0
        h = s.Matrix([s.diff(density, x)/density-2*s.diff(v, x)/v for x in q])
        h0 = h.subs(dict(zip(q, self.q)))
        equal(clean(drift+self.data['K']*h0), s.zeros(6, 1))
        return {'source_orbit_Jacobian': str(density), 'old_number_m_density': 'v^(m+2)',
            'source_difference_identity': 'drift=-K grad(log(J/v^2)) at the actual source',
            'ambient_positive_pairing_or_unitary_equivalence_claimed': False}


def main():
    began = time.monotonic()
    bound = read_bound('source_coframe_live_ordering')
    m = SourceLorentzQuantumSection()
    coefficient_checks = m.verify_primary_coefficients()
    drift = m.complete_ordering_difference()
    density = m.orbit_density_readback(drift)
    reports = []
    for word in ((16, 142), (16, 268), (5, 144, 396)):
        value = {word: s.S.One}
        gradient = {word: s.Matrix([s.I*s.Rational(j-2, 17) for j in range(6)])}
        u = s.Matrix([s.Rational(j % 3-1, 19) for j in range(6)])
        Hessian = {word: u*u.T-s.eye(6)}
        jet = m.extend_jet(value, gradient, Hessian)
        constraints = m.verify_primary_jet(jet)
        ambient = m.ambient_action(jet)
        old = verify_jet_action(m.data, word, 1, gradient[word], Hessian[word])
        reduced = {tuple(w): s.sympify(v) for w, v in old['raw_nested_square']}
        difference = simplified(weighted_sum(((1, ambient), (-1, reduced))))
        same(difference, {word: (drift.T*gradient[word])[0]})
        assert difference
        reports.append({'input_CAR': list(word), 'extended_CAR_words': len(jet),
            'source_gradient6': encode(gradient[word]), 'source_Hessian6': encode(Hessian[word]),
            'original_primary_checks': constraints, 'ambient_H_image': encode_state(ambient),
            'existing_H_image': encode_state(reduced), 'actual_difference': encode_state(difference)})
        print('PASS original10 primary, complete derivatives and ambient H:', word, flush=True)
    paths = ['source_lorentz_quantum_section.py', 'source_coframe_live_ordering.py',
        'source_coframe_live_ordering.json', 'source_coframe_legendre.py',
        'source_coframe_quantum_kinetic.py', 'source_lorentz_contact.py',
        'source_coframe_constraints.py', 'source_gauss_quantum_current.py',
        'source_reducing_coframe_metric.py']
    out = {'root': ROOT_ID, 'source_sha256': bound['source_sha256'],
        'input_sha256': {str((HERE/p).relative_to(ROOT)):
            hashlib.sha256((HERE/p).read_bytes()).hexdigest() for p in paths},
        'scope': 'ORIGINAL_SOURCE_LORENTZ_PRIMARY_GERM_AND_AMBIENT_ORDERING_DIFFERENCE',
        'configuration': encode(m.e), 'spatial_source_minor': str(m.minor.det()),
        'inverse_first_jet': encode(m.inverse), 'all_germ_primary_derivative_coefficients': coefficient_checks,
        'source_generation': 'spatial coframe orbit exp(sum alpha T) e_slice(q), represented by Gamma(exp(sum alpha diag(S,bar S))) on full504 CAR; inverse first/second jets come from the original orbit minor.',
        'original_constraint': 'Pi_time=0; Z_spatial^T Pi_spatial + dGamma(i diag(S,bar S) tensor I63)=0',
        'four_time_columns': 'Original y parameters are retained; these input germs have no y derivatives. No temporal secondary Euler value is set to zero.',
        'full_matter_carrier': {'modes': 504, 'internal_identity_factor': 63,
            'occupied12_projection_used': False, 'finite_Fock_number_preserved': True},
        'ambient_order': '1/2 sum Q_ij(e) Pshift_i Pshift_j +1/2 sum Hinv_ab(e) J_a J_b+3det(e), Pshift_i=-i partial_ei+Q((Gt^T Hinv J)_i); inner coefficients are differentiated.',
        'existing_order': 'SourceCoframeLiveOrdering: substitute the original primary momentum section, then retain its coefficient-left nested square. Its value is unchanged.',
        'complete_difference': {'central_drift6': encode(drift), 'principal_difference_zero': True,
            'all6_CAR_linear_coefficients_zero': True, 'one_body_difference_zero': True,
            'full63_normal_pair_symmetric_tensor_zero': True,
            'identity': 'ambient_H(extended_germ)-existing_H(germ)=N/2*(-partial_q0+partial_q5)germ at the actual source, for every finite CAR germ'},
        'orbit_density': density, 'actual_consumers': reports,
        'direct_consumer': 'Combine this Lorentz-primary configuration extension with the existing native Gauss inverse jet before applying the common original differential/CAR ports.',
        'physical_spacetime_Ward9_or_temporal_secondary_solution_claimed': False,
        'seconds': round(time.monotonic()-began, 3)}
    (HERE/'source_lorentz_quantum_section.json').write_text(json.dumps(out, indent=2)+'\n')
    print('PASS source Lorentz section and exact fullCAR ordering difference', out['seconds'], flush=True)


if __name__ == '__main__':
    main()
