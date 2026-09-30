#!/usr/bin/env python3
"""Raw-density lapse scaling and independent nested-operator certification.

The candidate constructor is never imported. The BF epsilon Hessian,
metric velocity quotient, original 4x4-form Hodge and original real Dirac
current independently determine the lapse weights. The commutator is
computed with the unexpanded sixteen primary momenta on a cubic germ.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_coframe_live_ordering import (
    RawLiveCoefficients, HERE, BASE, ROOT, ROOT_ID, FREE, rational, eq,
    terms, current, polynomial_action, full, state_encode)
from independent_source_lorentz_contact import (
    original_hessian, geometric_load, original_density_ports, original_gamma,
    real_linear, GENERATORS)
from independent_source_coframe_legendre import quotient_right_inverse, quotient_inverse
from independent_source_gauge_legendre import bindings, decode, encode, ETA, SIGMA, W, form, components, fixed_star, matrix_coordinates
from independent_source_joint_local_quantum import representations
from independent_source_gauss_quantum_current import decoded_state


def scalar(value): return s.cancel(value)
def zero(value): assert scalar(value) == 0, value


def original_hodge(e):
    # Use the original antisymmetric4x4 definition. Cofactors avoid the large
    # nested denominators produced by generic elimination on this live slice.
    inverse = rational(e.adjugate()/e.det())
    eq(e*inverse, s.eye(4)); eq(inverse*e, s.eye(4))
    return rational(s.Matrix.hstack(*(components(inverse*fixed_star(e*form(s.eye(6)[:, j])*e.T)*inverse.T)
                                     for j in range(6))))


class RawLapse:
    def __init__(self):
        self.raw = RawLiveCoefficients()
        self.nu = s.Symbol('nu', positive=True)
        self.e = self.raw.e.copy(); self.e[0, 0] *= self.nu
        self.inventory = representations()
        self.fundamental = self.inventory[0]
        self.gram = s.Matrix(12, 12, lambda a, b: s.re(
            -s.trace(self.fundamental[a][:3, :3]*self.fundamental[b][:3, :3])
            -s.trace(self.fundamental[a][3:5, 3:5]*self.fundamental[b][3:5, 3:5])
            -self.fundamental[a][5, 5]*self.fundamental[b][5, 5]))
        self.gram_inverse = self.gram.inv()

    def original_scaling(self):
        raw, e, nu = self.raw, self.e, self.nu
        H = original_hessian(e)
        U = s.kronecker_product(e, s.eye(6))
        Hi = rational(U.T*original_hessian(s.eye(4)).inv()*U/e.det())
        eq(H*Hi, s.eye(24)); eq(Hi*H, s.eye(24))
        generic = s.Matrix(4, 4, s.symbols('lapse_original_e0:16', real=True))
        Gt = rational(geometric_load(generic)[:, :16].xreplace(dict(zip(generic, e))))
        eq(Gt, raw.Gt)
        spatial = e.copy(); spatial[:, 0] = s.zeros(4, 1)
        Z = s.Matrix.hstack(*((T*spatial).reshape(16, 1) for T in GENERATORS))
        eq(Z, raw.Z); eq(Z.T*raw.A, s.zeros(6)); eq(Z.T*raw.S, -s.eye(6))
        R = quotient_right_inverse(e)
        h = rational(e[:, 1:].T*ETA*e[:, 1:])
        Q = rational(R*quotient_inverse(e, h)*R.T)
        eq(Q, nu*raw.Q)
        E, V = original_density_ports(e, original_gamma())
        eq(E, raw.E)
        I = s.eye(4)
        transform = s.Matrix.vstack(s.Matrix.hstack(I, s.I*I), s.Matrix.hstack(I, -s.I*I))/s.sqrt(2)
        J = [rational(transform*(s.I*real_linear(E.inv()*vertex))*transform.H) for vertex in V]
        D = s.diag(*([1]*6+[nu]*18))
        for a in range(24): eq(J[a], D[a, a]*raw.J[a])
        L = rational(raw.S*s.eye(24)[:6, :]+Gt.T*Hi)
        eq(L*D, raw.L)
        T = [rational(sum((L[i, a]*J[a] for a in range(24)), s.zeros(8))) for i in range(16)]
        for i in range(16): eq(T[i], raw.T[i])
        eq(D.T*Hi*D, nu*raw.Hinv)
        K = rational(raw.A.T*Q*raw.A/2)
        M = [rational(sum(((raw.A.T*Q)[r, j]*T[j] for j in range(16)), s.zeros(8))) for r in range(6)]
        weight = rational((L.T*Q*L+Hi)/2)
        eq(D.T*weight*D, nu*raw.W)
        one_body = rational(sum((v*J[a]*J[b] for (a, b), v in weight.todok().items()), s.zeros(8)))
        drift = rational(-s.I*sum(((raw.A.T*Q)[r, j]*raw.dA[r][j, :]
                                    for r in range(6) for j in range(16)), s.zeros(1, 6))/2)
        dT = [[rational(value.diff(q)) for value in T] for q in raw.q]
        correction = rational(-s.I*sum(((raw.A.T*Q)[r, j]*dT[r][j]
                                         for r in range(6) for j in range(16)), s.zeros(8))/2)
        for actual, old in [(K, raw.K), (one_body, raw.one_body), (drift, raw.drift), (correction, raw.correction)]:
            eq(actual, nu*old)
        for actual, old in zip(M, raw.M): eq(actual, nu*old)
        # This is the original densitized inverse coframe metric, not the
        # different native gauge Hodge contraction.
        inverse = rational(e.adjugate()/e.det()); old_inverse = rational(raw.e.adjugate()/raw.e.det())
        eq(e*inverse, s.eye(4)); eq(inverse*e, s.eye(4))
        metric = rational(s.Abs(e.det())*inverse*ETA*inverse.T)
        old_metric = rational(s.Abs(raw.e.det())*old_inverse*ETA*old_inverse.T)
        zero(metric[0, 0]*nu-old_metric[0, 0]); eq(metric[1:, 1:], nu*old_metric[1:, 1:])
        eq(metric[0, 1:], s.zeros(1, 3)); zero(e.det()-nu*raw.e.det())
        constitutive = rational(-W*original_hodge(e)/SIGMA)
        old_constitutive = rational(-W*original_hodge(raw.e)/SIGMA)
        eq(constitutive[:3, :3], nu*old_constitutive[:3, :3])
        eq(constitutive[3:, 3:], old_constitutive[3:, 3:]/nu)
        eq(constitutive[:3, 3:], s.zeros(3)); eq(constitutive[3:, :3], s.zeros(3))
        # All full252 kinetic and Yukawa coefficients follow before selecting
        # any matter state: the internal factor is untouched by the coframe.
        gamma = original_gamma()
        for mu in range(4):
            original = rational(s.I*s.Abs(e.det())*sum((inverse[mu, a]*gamma[a] for a in range(4)), s.zeros(4)))
            old = rational(s.I*s.Abs(raw.e.det())*sum((old_inverse[mu, a]*gamma[a] for a in range(4)), s.zeros(4)))
            eq(original, (1 if mu == 0 else nu)*old)
        self.constitutive = old_constitutive
        spatial = raw.e[1:, 1:]
        spatial_inverse = rational(spatial.adjugate()/spatial.det())
        electric_inverse = rational(SIGMA*raw.e[1:, 1:].det()/raw.N*spatial_inverse*spatial_inverse.T)
        eq(old_constitutive[:3, :3]*electric_inverse, s.eye(3))
        eq(electric_inverse*old_constitutive[:3, :3], s.eye(3))
        self.gauge_weight = rational(s.kronecker_product(electric_inverse, self.gram_inverse))
        return {'A': raw.A, 'S': raw.S, 'Q': Q, 'Hinv': Hi, 'L': L, 'K': K, 'W': weight,
                'one_body': one_body, 'drift': drift, 'correction': correction, 'J': J, 'T': T, 'M': M,
                'dA': raw.dA, 'dT': dT, 'constant': 3*e.det()}

    def actual_cubic(self, expected):
        raw = self.raw
        r, a = expected['coframe_coordinate'], expected['gauge_coordinate']
        point = dict(zip(raw.q, [raw.e0[i] for i in FREE]))
        u = s.Symbol('raw_gauge_increment', real=True)
        factor = raw.q[r]-point[raw.q[r]]
        f = factor*u**2/2
        # Compute the genuine native magnetic potential on the same source
        # connection plus this one coordinate; its full contribution is retained.
        original = json.loads((BASE/'active-gauge/receipt.json').read_text())['actual_background']
        gauge = s.Matrix(original['gauge_connection']).applyfunc(s.sympify)[1:, :]
        gauge[a//12, a % 12] += u
        connection = [sum((gauge[i, b]*self.fundamental[b] for b in range(12)), s.zeros(7)) for i in range(3)]
        magnetic = s.Matrix.vstack(*(matrix_coordinates(connection[i]*connection[j]-connection[j]*connection[i]).T
                                      for i, j in ((1, 2), (2, 0), (0, 1))))
        V = scalar(-s.trace(magnetic.T*self.constitutive[3:, 3:]*magnetic*self.gram)/2)
        W_aa = self.gauge_weight[a, a]
        Bf = -W_aa*s.diff(f, u, 2)/2+V*f
        # The original unexpanded primary kinetic operator on the CAR vacuum.
        # No K/drift commutator formula is used for these two ordered actions.
        def original_coframe(value):
            inner = [-s.I*sum(raw.A[j, t]*s.diff(value, raw.q[t]) for t in range(6)) for j in range(16)]
            return scalar(sum(-s.I*coefficient*sum(raw.A[i, t]*s.diff(inner[j], raw.q[t]) for t in range(6))/2
                              for (i, j), coefficient in raw.Q.todok().items())+3*raw.e.det()*value)
        for matrix in raw.J:
            assert current(full(matrix), {(): s.S.One}) == {}
        # Evaluating u=0 commutes with every coframe derivative; this pays the
        # omitted symbolic V expansion without dropping its actual contribution.
        zero(Bf.subs(u, 0)+W_aa*factor/2)
        AB = scalar(original_coframe(Bf.subs(u, 0)).subs(point))
        Af = original_coframe(f)
        BA = scalar((-W_aa*s.diff(Af, u, 2)/2+V*Af).subs(u, 0).subs(point))
        difference = scalar(AB-BA)
        assert difference != 0
        for actual, name in [(AB, 'H_A_H_B_action'), (BA, 'H_B_H_A_action'), (difference, 'commutator_action')]:
            zero(actual-s.sympify(expected[name]))
        # Check the whole reported coefficient tensor only after the actual
        # ordered source operators have generated the nonzero witness.
        tensor = s.Matrix(6, 36, lambda i, j:
            scalar(sum(raw.K[i, t]*self.gauge_weight[j, j].diff(raw.q[t]) for t in range(6))).subs(point))
        eq(tensor, decode(expected['all6_by36_cubic_coefficients']))
        return {'coframe_coordinate': r, 'gauge_coordinate': a,
                'actual_HA_HB': str(AB), 'actual_HB_HA': str(BA), 'actual_commutator': str(difference),
                'raw_native_magnetic_potential_retained': True,
                'original_sixteen_primary_momenta_nested_directly': True,
                'all24_original_CAR_currents_annihilate_vacuum_checked': True,
                'scalar_and_matter_ideal_argument': 'Their actual shared103 component mouths differentiate only x61 and A36, never q6. Thus either composition with the gauge component preserves the ideal (q_r-q_source_r), and vanishes at the chosen q. This includes every variable coefficient and mixed scalar/gauge derivative.',
                'same_common_domain': 'Cubic germ times a compact smooth cutoff equal1 locally, tensor the genuine CAR vacuum',
                'all6_by36_coefficients_independently_equal': True}


def main():
    began = time.monotonic()
    path = HERE/'source_quantum_lapse_constraint.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    paid_paths = ['independent_source_joint_local_quantum.json', 'independent_source_coframe_live_ordering.json',
                  'independent_source_scalar_shift_quantum.json', 'independent_source_gauge_quantum_energy.json']
    for name in paid_paths: count += bindings(json.loads((HERE/name).read_text()))
    raw = RawLapse(); generated = raw.original_scaling()
    assert raw.inventory[-1] == candidate['source_sha256']
    print('PASS raw BF/metric quotient, all24 real currents, live ordering derivatives and original gauge Hodge lapse weights', flush=True)
    joint = json.loads((HERE/'source_joint_local_quantum.json').read_text())
    q = tuple(decode(joint['configuration']['coframe'])[j] for j in FREE)
    at = dict(zip(raw.raw.q, q))
    data = {}
    for key, value in generated.items():
        if key == 'dT': data[key] = [[rational(A.subs(at)) for A in row] for row in value]
        elif isinstance(value, list): data[key] = [rational(A.subs(at)) for A in value]
        elif isinstance(value, s.MatrixBase): data[key] = rational(value.subs(at))
        else: data[key] = scalar(value.subs(at))
    ell = s.Matrix([s.Rational(j%11+1, 67) for j in range(103)])
    radial = s.Matrix([s.Rational(j%7-3, 53) for j in range(103)])
    gradient, Hessian = s.I*ell, radial*radial.T-s.eye(103)
    state = tuple(joint['actual_nonseparable_103_wavepacket']['state'])
    coframe, _ = polynomial_action(data, state, 1, gradient[:6, :], Hessian[:6, :6])
    pieces = {name: decoded_state(value) for name, value in joint['actual_nonseparable_103_wavepacket']['components'].items()}
    assert terms([(1, coframe), (-raw.nu, pieces['coframe'])]) == {}
    HA = terms([(1/raw.nu, coframe), (1, pieces['scalar']), (1, pieces['matter_without_Lorentz'])])
    HB = pieces['gauge']
    H = terms([(raw.nu, HA), (1/raw.nu, HB)])
    C = terms((1, {word: s.diff(value, raw.nu)}) for word, value in H.items())
    pencil = terms([(raw.nu**2, C)])
    actual = dict(H_A=HA, H_B=HB, Hamiltonian=H, constraint=C, pencil=pencil)
    for key, value in actual.items():
        assert terms([(1, value), (-1, {tuple(word): s.sympify(value, locals={'nu': raw.nu})
                                 for word, value in candidate['actual103_wavepacket'][key]})]) == {}, key
    eta = s.Function('independent_lapse_family')(raw.nu)
    commutator = {word: -s.I*s.diff(eta*value, raw.nu)+s.I*s.diff(eta, raw.nu)*value for word, value in H.items()}
    assert terms([(1, commutator), (s.I*eta, C)]) == {}
    assert terms([(1, pencil), (-raw.nu**2, HA), (1, HB)]) == {}
    print('PASS actual mixed-branch CAR polynomial germ, whole103 scaled action and lapse-primary differential reader', flush=True)
    witness = raw.actual_cubic(candidate['noncommuting_full_H_A_H_B_consumer'])
    print('PASS actual raw native gauge potential and nested original primary operators: full nonzero cubic commutator', flush=True)
    paths = [Path(__file__), path, HERE/'source_quantum_lapse_constraint.py',
             HERE/'independent_source_coframe_live_ordering.py', HERE/'independent_source_joint_local_quantum.py',
             HERE/'independent_source_gauge_legendre.py', HERE/'independent_source_lorentz_contact.py',
             HERE/'independent_source_coframe_legendre.py', HERE/'source_joint_local_quantum.json']+[HERE/name for name in paid_paths]
    output = {'root': ROOT_ID, 'verdict': 'CERTIFIED_ORIGINAL_QUANTUM_LAPSE_SCALING_AND_PRIMARY_OPERATOR_PENCIL',
        'source_sha256': candidate['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks': count, 'candidate_constructor_or_action_imported': False,
        'independent_method': 'Original epsilon BF Hessian/inverse and metric velocity quotient; original 4x4 antisymmetric-form Hodge; independent real Dirac current basis; coefficient differentiation; nested16 primary momenta on the actual cubic CCR germ',
        'generic_lapse_and_six_coframe_coefficients_checked': True,
        'all24_current_weights_and_both_normal_quartic_slots_checked': True,
        'live_drift_and_one_body_correction_weights_checked': True,
        'source_matter_principal_full252_and_original_Yukawa_volume_weights_checked': True,
        'scalar_full_Gauss_coefficients': 'The original Gauss momentum graph has no e or nu; h00 rescales inversely, every spatial metric/potential coefficient linearly, and zero shift is kept. All97 coefficient derivatives commute with this independent lapse multiplication.',
        'actual103_wavepacket_action': {key: state_encode(value) for key, value in actual.items()},
        'arbitrary_smooth_lapse_primary_reader': '[p_nu,H]=-i*(HA-nu^-2*HB), p_nu=N*Pi_e00',
        'actual_full_commutator': witness,
        'common_domain': 'Smooth nu>0 families with fibre Cc_infinity(Uq times Ux times R36) tensor finite CAR504; derivatives and compositions preserve the fixed compact support in the103 configuration coordinates',
        'scope': 'Same source parameterized temporal coframe; a generated operator constraint and noncommuting coefficient operators. No physical-state solution, other temporal/stabilizer constraints, Hilbert evolution or composite spectrum is asserted.',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_quantum_lapse_constraint.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS independent quantum lapse constraint', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
