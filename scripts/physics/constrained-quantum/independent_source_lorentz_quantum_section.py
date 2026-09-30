#!/usr/bin/env python3
"""Independent source-point Lorentz section and ordered coframe action audit.

Inverse jets are recovered from the Lorentz Gram matrix by reverse Cholesky,
the future normal, and log(Lambda), rather than the candidate inverse-function
formula. Original shifted momenta are composed with independent bit CAR. The
complete degree-zero/two/four CAR difference is tested on its full coefficient
carrier, including two distinct internal sectors.
"""
from __future__ import annotations

from collections import defaultdict
import hashlib
import itertools
import json
import time

import sympy as s

from dynamic import HERE, ROOT, ROOT_ID, decode
import source_lorentz_quantum_section as candidate
from source_lorentz_contact import ETA, GAMMA, PAIRS
from source_coframe_live_ordering import FREE, DEPENDENT
from independent_source_joint_charge_conservation import (
    OccupationAction, clean, equal_states)

TIME = (0, 4, 8, 12)
SPATIAL = tuple(i for i in range(16) if i not in TIME)


def equal(A, B):
    difference = s.SparseMatrix(A-B).applyfunc(s.cancel)
    assert not difference.todok(), list(difference.todok().items())[:3]


def total(*terms):
    out = defaultdict(int)
    for coefficient, state in terms:
        for word, value in state.items():
            out[word] += coefficient*value
    return clean(out)


def series(expression, variable):
    return s.Poly(s.series(expression, variable, 0, 3).removeO().expand(), variable)


def inverse_curve(E0, direction):
    """Literal local inverse from Gram/normal geometry along E0+t*direction."""
    t = s.Symbol('audit_curve', real=True)
    E = E0+t*direction
    h = E.T*ETA*E
    trunc = lambda value: series(value, t).as_expr()
    q5 = trunc(s.sqrt(h[2, 2]))
    q4 = trunc(h[1, 2]/q5)
    q3 = trunc(h[0, 2]/q5)
    q2 = trunc(s.sqrt(h[1, 1]-q4*q4))
    q1 = trunc((h[0, 1]-q3*q4)/q2)
    q0 = trunc(s.sqrt(h[0, 0]-q1*q1-q3*q3))
    q = (q0, q1, q2, q3, q4, q5)
    triangle = s.Matrix([[q0, 0, 0], [q1, q2, 0], [q3, q4, q5]])
    volume = trunc(q0*q2*q5)
    normal = s.Matrix([(-ETA[a, a])*(-1)**a
        * E.extract([b for b in range(4) if b != a], range(3)).det()/volume
        for a in range(4)]).applyfunc(trunc)
    spatial = (E*triangle.inv()).applyfunc(trunc)
    Lorentz = normal.row_join(spatial)
    first = Lorentz.applyfunc(lambda value: s.expand(value).coeff(t))
    second = Lorentz.applyfunc(lambda value: s.expand(value).coeff(t, 2))
    # log(I+t*A+t^2*B)=t*A+t^2*(B-A^2/2).
    logarithm = t*first+t*t*(second-first*first/2)
    alpha = [trunc(ETA[a, a]*logarithm[a, b]) for a, b in PAIRS]
    values = alpha+list(q)
    first_inverse = s.Matrix([s.expand(value).coeff(t) for value in values])
    second_inverse = s.Matrix([2*s.expand(value).coeff(t, 2) for value in values])
    equal(Lorentz.subs(t, 0), s.eye(4))
    for i, j in itertools.product(range(4), repeat=2):
        assert trunc((Lorentz.T*ETA*Lorentz-ETA)[i, j]) == 0
    equal((Lorentz*s.Matrix.vstack(s.zeros(1, 3), triangle)-E).applyfunc(trunc), s.zeros(4, 3))
    return first_inverse, second_inverse


def independent_inverse(model):
    E = model.e[:, 1:]
    first = s.zeros(12)
    second = [s.zeros(12) for _ in range(12)]
    diagonal = []
    for i in range(12):
        dE = s.zeros(4, 3); dE[i] = 1
        a, b = inverse_curve(E, dE)
        first[:, i] = a
        diagonal.append(b)
        for k in range(12):
            second[k][i, i] = b[k]
    for i in range(12):
        for j in range(i+1, 12):
            dE = s.zeros(4, 3); dE[i] = dE[j] = 1
            a, b = inverse_curve(E, dE)
            equal(a, first[:, i]+first[:, j])
            mixed = (b-diagonal[i]-diagonal[j])/2
            for k in range(12):
                second[k][i, j] = second[k][j, i] = mixed[k]
    equal(first, model.inverse)
    for left, right in zip(second, model.second):
        equal(left, right)
    print('PASS independent Gram/Cholesky/normal/log inverse: all78 curves, 12 first and second jets', flush=True)
    return first, second


class BitAction:
    def __init__(self):
        self.raw = OccupationAction()
        self.saved = {}
        self.retained = {}

    def Q(self, A, state):
        key = id(A)
        self.retained[key] = A
        out = defaultdict(int)
        for word, coefficient in state.items():
            cache = key, word
            if cache not in self.saved:
                self.saved[cache] = self.raw.one_body(A, {word: s.S.One})
            for target, value in self.saved[cache].items():
                out[target] += coefficient*value
        return clean(out)


def lift_matrix(A):
    return s.SparseMatrix(s.kronecker_product(A, s.eye(63)))


def make_extension(model, first, second, action):
    embedding = s.eye(16)[:, SPATIAL]
    first16 = first*embedding.T
    hessians = [embedding*A*embedding.T for A in second]
    spin = [s.diag(S, S.conjugate()) for S in model.native.lorentz.spin]
    B = [lift_matrix(sum((first16[a, i]*spin[a] for a in range(6)), s.zeros(8)))
         for i in range(16)]
    D = {(i, j): lift_matrix(sum((hessians[a][i, j]*spin[a] for a in range(6)), s.zeros(8)))
         for i in range(16) for j in range(i, 16)}
    def extend(values, gradients, Hessians):
        words = set(values) | set(gradients) | set(Hessians)
        g = [{w: (first16[6:, i].T*gradients.get(w, s.zeros(6, 1)))[0]
              for w in words} for i in range(16)]
        full_gradient = [total((1, g[i]), (1, action.Q(B[i], values))) for i in range(16)]
        full_hessian = {}
        for i in range(16):
            for j in range(i, 16):
                scalar = {w: (first16[6:, i].T*Hessians.get(w, s.zeros(6))
                              *first16[6:, j])[0]
                    +sum(gradients.get(w, s.zeros(6, 1))[a]*hessians[6+a][i, j]
                         for a in range(6)) for w in words}
                result = total((1, scalar), (1, action.Q(D[i, j], values)),
                    (1, action.Q(B[i], g[j])), (1, action.Q(B[j], g[i])),
                    (s.Rational(1, 2), action.Q(B[i], action.Q(B[j], values))),
                    (s.Rational(1, 2), action.Q(B[j], action.Q(B[i], values))))
                full_hessian[i, j] = full_hessian[j, i] = result
        out = {w: {'value': values.get(w, 0), 'gradient': s.zeros(16, 1), 'Hessian': s.zeros(16)}
               for w in words | set().union(*(set(a) for a in full_gradient),
                   *(set(a) for a in full_hessian.values()))}
        for w, row in out.items():
            row['gradient'] = s.Matrix([state.get(w, 0) for state in full_gradient])
            row['Hessian'] = s.Matrix(16, 16, lambda i, j: full_hessian[i, j].get(w, 0))
        return out
    return extend


def original_coefficients(model):
    native, e0 = model.native, model.e
    lorentz = native.lorentz
    t = s.Symbol('audit_original_coframe', real=True)
    C0, J0, derivatives = None, None, []
    for k in range(16):
        e = e0.copy(); e[k] += t
        Hi = lorentz.inverse_numerator(e)/e.det()
        G = lorentz.geometry_maps(e)[0][:, :16]
        B = G.T*Hi
        adj = e.adjugate()
        principals = [sum((adj[mu, a]*s.I*GAMMA[a] for a in range(4)), s.zeros(4))
                      for mu in range(4)]
        E = principals[0]
        norm = (E*E)[0, 0]
        equal(E*E, norm*s.eye(4))
        J = []
        for principal in principals:
            for S in lorentz.spin:
                M = (E*principal*S/norm).applyfunc(s.cancel)
                J.append(s.diag(s.I*M, s.I*M.conjugate()))
        C = [sum((B[i, a]*J[a] for a in range(24) if B[i, a]), s.zeros(8))
             for i in range(16)]
        derivatives.append([lift_matrix(A.diff(t).subs(t, 0).applyfunc(s.cancel)) for A in C])
        current_C = [A.subs(t, 0).applyfunc(s.cancel) for A in C]
        current_J = [A.subs(t, 0).applyfunc(s.cancel) for A in J]
        if C0 is None:
            C0, J0 = current_C, current_J
        else:
            for a, b in zip(current_C+current_J, C0+J0):
                equal(a, b)
    for a in range(6):
        equal(J0[a], s.I*s.diag(lorentz.spin[a], lorentz.spin[a].conjugate()))
    print('PASS independent original full16 shifted-current derivatives from inverse numerator and Dirac square', flush=True)
    return list(map(lift_matrix, C0)), list(map(lift_matrix, J0)), derivatives


def make_hamiltonians(model, action, C, J, dC):
    geometry = model.native.geometry(model.e)
    Q, Hi = geometry['velocity_inverse'], geometry['Lorentz_inverse']
    potential = 3*model.e.det()
    def tail(values):
        return total((potential, values), *((v/2, action.Q(J[a], action.Q(J[b], values)))
            for (a, b), v in Hi.todok().items()))
    def ambient(jet):
        value = clean({w: row['value'] for w, row in jet.items()})
        gradients = [clean({w: row['gradient'][i] for w, row in jet.items()}) for i in range(16)]
        inner = [total((-s.I, gradients[j]), (1, action.Q(C[j], value))) for j in range(16)]
        terms = [(1, tail(value))]
        for (i, j), v in Q.todok().items():
            hessian = clean({w: row['Hessian'][i, j] for w, row in jet.items()})
            dinner = total((-s.I, hessian), (1, action.Q(dC[i][j], value)),
                           (1, action.Q(C[j], gradients[i])))
            terms.extend(((-s.I*v/2, dinner), (v/2, action.Q(C[i], inner[j]))))
        return total(*terms)
    data = model.data
    T = list(map(lift_matrix, data['T']))
    dT = [list(map(lift_matrix, row)) for row in data['dT']]
    def old(values, gradients, Hessians):
        A, dA = data['A'], data['dA']
        g = [clean({w: row[r] for w, row in gradients.items()}) for r in range(6)]
        inner = [total(*((-s.I*A[j, r], g[r]) for r in range(6)),
                       (1, action.Q(T[j], values))) for j in range(16)]
        terms = [(1, tail(values))]
        for (i, j), v in Q.todok().items():
            for r in range(6):
                if not A[i, r]:
                    continue
                h = [clean({w: row[r, b] for w, row in Hessians.items()}) for b in range(6)]
                dinner = total(*((-s.I*dA[r][j, b], g[b]) for b in range(6)),
                    *((-s.I*A[j, b], h[b]) for b in range(6)),
                    (1, action.Q(dT[r][j], values)), (1, action.Q(T[j], g[r])))
                terms.append((-s.I*v*A[i, r]/2, dinner))
            terms.append((v/2, action.Q(T[i], inner[j])))
        return total(*terms)
    return ambient, old


def noether_and_density(model):
    native = model.native
    e = native.e
    adj = e.adjugate()
    principals = [sum((adj[mu, b]*s.I*GAMMA[b] for b in range(4)), s.zeros(4))
                  for mu in range(4)]
    for T, S in zip(native.lorentz.basis, native.lorentz.spin):
        variation = (T*e).reshape(16, 1)
        for P in principals:
            differential = sum((variation[k]*P.diff(e[k]) for k in range(16)), s.zeros(4))
            equal(differential-S*P+P*S, s.zeros(4))
    equal(native.G[:, TIME], s.zeros(24, 4))
    # Full12 forward Jacobian, rather than the candidate's dependent6 minor.
    live = model.model.e[:, 1:]
    q = model.model.q
    orbit = [(T*live).reshape(12, 1) for T in native.lorentz.basis]
    section = [live.diff(x).reshape(12, 1) for x in q]
    jacobian = s.factor(s.Matrix.hstack(*orbit, *section).det())
    volume = q[0]*q[2]*q[5]
    density = q[0]*q[2]**2*q[5]**3
    assert s.factor(jacobian*jacobian-density*density) == 0
    source_ratio_gradient = s.Matrix([s.diff(density, x)/density-2*s.diff(volume, x)/volume
                                     for x in q]).subs(dict(zip(q, model.q)))
    drift = s.Matrix([-model.e[0, 0]/2, 0, 0, 0, 0, model.e[0, 0]/2])
    equal(drift, -model.data['K']*source_ratio_gradient)
    return {'original_full16_Dirac_Noether_covariance_identities': 24,
        'original_four_temporal_momentum_columns': True,
        'full12_forward_Jacobian': str(jacobian),
        'positive_orbit_density': str(density),
        'pairing_identity_scope': 'drift=-K grad(log(J/v^2)) at the actual source point only; no full-q adjoint or unitary equivalence is inferred.'}


def main():
    began = time.monotonic()
    target_path = HERE/'source_lorentz_quantum_section.json'
    target = json.loads(target_path.read_text())
    assert target['root'] == ROOT_ID
    assert target['scope'] == 'ORIGINAL_SOURCE_LORENTZ_PRIMARY_GERM_AND_AMBIENT_ORDERING_DIFFERENCE'
    hashes = {name: digest for field in ('source_sha256', 'input_sha256')
              for name, digest in target[field].items()}
    for name, digest in hashes.items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    model = candidate.SourceLorentzQuantumSection()
    first, second = independent_inverse(model)
    noether = noether_and_density(model)
    action = BitAction()
    extend = make_extension(model, first, second, action)
    C, J, dC = original_coefficients(model)
    ambient, old = make_hamiltonians(model, action, C, J, dC)
    expected_drift = s.Matrix([-model.e[0, 0]/2, 0, 0, 0, 0, model.e[0, 0]/2])
    records = []
    def compare(values, gradients, Hessians, label, check_primary=False):
        jet = extend(values, gradients, Hessians)
        if check_primary:
            actual = model.extend_jet(values, gradients, Hessians)
            for word in set(jet) | set(actual):
                left = jet.get(word, {'value': 0, 'gradient': s.zeros(16, 1), 'Hessian': s.zeros(16)})
                right = actual.get(word, {'value': 0, 'gradient': s.zeros(16, 1), 'Hessian': s.zeros(16)})
                assert s.expand(left['value']-right['value']) == 0
                equal(left['gradient'], right['gradient']); equal(left['Hessian'], right['Hessian'])
            model.verify_primary_jet(jet)
        raw = ambient(jet)
        expected = old(values, gradients, Hessians)
        difference = total((1, raw), (-1, expected))
        predicted = clean({w: (expected_drift.T*g)[0] for w, g in gradients.items()})
        equal_states(difference, predicted)
        if check_primary:
            equal_states(raw, model.ambient_action(jet))
        return {'label': label, 'extended_words': len(jet), 'ambient_words': len(raw),
                'difference': [[list(w), str(c)] for w, c in sorted(difference.items())]}
    # Constant germs exhaust the CAR coefficient carrier through degree four.
    constant_words = [()] + [(63*a,) for a in range(8)]
    constant_words += [tuple(sorted((63*a, 63*b+1))) for a in range(8) for b in range(8)]
    constant_words += [(63*a, 63*b) for a in range(8) for b in range(a+1, 8)]
    for word in constant_words:
        compare({word: s.S.One}, {}, {}, 'constant '+str(word))
    print('PASS complete CAR coefficient carrier: vacuum,8 one-body,64 cross-internal and28 same-internal two-body columns', flush=True)
    # Empty and all eight one-particle columns separate central and CAR drift.
    for r in range(6):
        for word in [()] + [(63*a,) for a in range(8)]:
            compare({}, {word: s.eye(6)[:, r]}, {}, 'gradient '+str((r, word)))
    for r in range(6):
        for k in range(r, 6):
            H = s.zeros(6); H[r, k] = H[k, r] = 1
            compare({}, {}, {(): H}, 'Hessian '+str((r, k)))
    print('PASS all6 central/CAR first-order and21 principal coefficients by original nested actions', flush=True)
    for index, word in enumerate(((11, 263), (7, 133, 385), (0, 64, 254, 442))):
        v = {word: 1+s.I*s.Rational(index+1, 7)}
        g = {word: s.Matrix([s.Rational((j+2)*(index+1), 23)+s.I*s.Rational(j%3-1, 29)
                            for j in range(6)])}
        u = s.Matrix([s.Rational(j-index, 31) for j in range(6)])
        H = {word: u*u.T+s.I*s.eye(6)/37}
        row = compare(v, g, H, 'new source germ '+str(index), True)
        assert row['difference']
        records.append(row)
    # The wrong original spin sign and deleting the curvature jet have real defects.
    word = (11, 263)
    jet = extend({word: s.S.One}, {}, {})
    Z = s.eye(16)[:, SPATIAL]*model.Z
    wrong_spin = 0
    for a in range(6):
        derivative = clean({w: (Z[:, a].T*row['gradient'])[0] for w, row in jet.items()})
        charge = action.Q(lift_matrix(s.diag(model.native.lorentz.spin[a],
                       model.native.lorentz.spin[a].conjugate())), {word: s.S.One})
        equal_states(derivative, charge)
        wrong_spin += bool(total((1, derivative), (1, charge)))
    assert wrong_spin
    flat_second = [s.zeros(12) for _ in range(12)]
    flat_extend = make_extension(model, first, flat_second, action)
    g = {(): s.Matrix([s.Rational(i+1, 7) for i in range(6)])}
    flat = flat_extend({}, g, {})
    omitted_curvature = 0
    for a, T in enumerate(model.native.lorentz.basis):
        for i in SPATIAL:
            direction = s.zeros(4); direction[i] = 1
            dZ = (T*direction).reshape(16, 1)
            residual = clean({w: (dZ.T*row['gradient'])[0]
                +(row['Hessian'][i, :]*Z[:, a])[0] for w, row in flat.items()})
            omitted_curvature += bool(residual)
    assert omitted_curvature
    # Reversing the original current composition is observable on a fresh word.
    wrong_order = 0
    for a in range(6):
        for b in range(a+1, 6):
            forward = action.Q(J[a], action.Q(J[b], {word: s.S.One}))
            reverse = action.Q(J[b], action.Q(J[a], {word: s.S.One}))
            wrong_order += bool(total((1, forward), (-1, reverse)))
    assert wrong_order
    owned = ('independent_source_lorentz_quantum_section.py', 'source_lorentz_quantum_section.json',
             'independent_source_joint_charge_conservation.py')
    hashes.update({str((HERE/name).relative_to(ROOT)): hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                   for name in owned})
    for name, digest in hashes.items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    out = {'root': ROOT_ID, 'scope': target['scope'], 'verdict': 'CERTIFIED',
        'verified_input_sha256': hashes,
        'inverse_algorithm': 'Exact2 Taylor jets of reverse Cholesky(Esp^T eta Esp), future normal and matrix log;12 coordinate curves plus66 polarized curves.',
        'inverse_first_jet_entries': 144, 'inverse_second_jet_entries': 1728,
        'Noether_and_density': noether,
        'ambient_algorithm': 'Original inverse numerator/det and Clifford E^2 inversion differentiated in all16 raw coordinates; direct nested shifted momenta with independent bit CAR.',
        'complete_CAR_coefficient_carrier': {'vacuum': 1, 'one_particle_spin_branches': 8,
            'two_distinct_internal_sectors_columns': 64, 'same_internal_exterior2_columns': 28,
            'full_original_modes': 504,
            'coverage': 'A number-preserving polynomial of CAR degree<=4 is determined by its vacuum, one-body matrix and two-body tensor. The64 cross-internal columns span both complete8 spin/real branches and determine the pair-symmetric64x64 tensor for the identity63 factor; the28 same-sector columns also test the exterior signs.'},
        'all_germ_operator_coefficients': {'central_and_CAR_gradient_tests': 54, 'principal_tests': 21},
        'new_source_germs': records,
        'reverse_controls': {'wrong_original_spin_sign_nonzero': wrong_spin,
            'drop_inverse_curvature_primary_derivatives_nonzero': omitted_curvature,
            'reverse_original_current_word_order_nonzero': wrong_order},
        'certified_difference': 'N/2*(-partial_q0+partial_q5) I at the actual source; all finite CAR germs, original order and full504 retained.',
        'scope_limit': 'The operator difference and pairing-density drift readback are source-point identities. The orbit density is generic on the positive slice. No global-q equality, new positive ambient pairing, unitary equivalence, temporal secondary solution or physical Ward9 is claimed.',
        'seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_lorentz_quantum_section.json').write_text(json.dumps(out, indent=2)+'\n')
    print('PASS CERTIFIED independent Lorentz quantum section', out['seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
