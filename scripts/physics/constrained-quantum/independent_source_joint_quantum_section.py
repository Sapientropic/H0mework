#!/usr/bin/env python3
"""Independent reverse-order Spin/native jet and fixed-order H readback.

The audit consumes the signed Lorentz inverse jet, reconstructs native jets
from the independent implicit-slice primitive, and extends Spin before native
instead of native before Spin. The compared old operator is exactly
SourceQuantumGaussSection -> SourceJointLocalQuantum, before half density.
"""
from __future__ import annotations

from collections import defaultdict
import hashlib
import json
import time

import sympy as s

from dynamic import HERE, ROOT, ROOT_ID, decode
from source_joint_quantum_section import SourceJointQuantumSection
from source_joint_local_quantum import SourceJointLocalQuantum
from source_quantum_gauss_section import SourceQuantumGaussSection
from source_joint_current_hilbert_section import SourceJointCurrentHilbertSection
from source_joint_ccr_car_ports import SourceJointCCRCarPorts
from source_joint_current_heisenberg import patch_symbolic_equal
from independent_source_full_gauss_section import RawFullSection
from independent_source_quantum_gauss_section import raw_whole_action
from independent_source_lorentz_quantum_section import (
    BitAction, total, equal, lift_matrix, TIME, SPATIAL)
from independent_source_joint_charge_conservation import clean, equal_states
from source_spatial_active_phase_splice import dm, DOMAIN

SCOPE = 'COMMON122_CONFIGURATION_JET_FROM_ORIGINAL100_GERM_AND_FULL504_CAR'


def read_bound(name):
    path = HERE/(name+'.json')
    data = json.loads(path.read_text())
    assert data['root'] == ROOT_ID
    hashes = {key: value for field in ('source_sha256', 'input_sha256', 'verified_input_sha256')
              for key, value in data.get(field, {}).items()}
    for key, digest in hashes.items():
        assert hashlib.sha256((ROOT/key).read_bytes()).hexdigest() == digest, key
    return data, hashes


def sparse(M):
    return s.SparseMatrix(M).applyfunc(s.cancel)


def extend_general(values, gradients, Hessians, D, second, alpha, alpha2, R, action):
    """Ordinary chain rule and exponential representation, using bit CAR."""
    input_size, output_size = D.shape
    result = {}
    def add(state, value=0, gradient=None, Hessian=None):
        for word, coefficient in state.items():
            row = result.setdefault(word, [s.S.Zero, s.zeros(output_size, 1),
                                            s.SparseMatrix(output_size, output_size, {})])
            row[0] += coefficient*value
            if gradient is not None:
                row[1] += coefficient*gradient
            if Hessian is not None:
                row[2] += coefficient*Hessian
    for word in set(values) | set(gradients) | set(Hessians):
        g = gradients.get(word, s.zeros(input_size, 1))
        h = Hessians.get(word, s.SparseMatrix(input_size, input_size, {}))
        dg = sparse(D.T*g)
        hg = D.T*h*D
        for j, coefficient in enumerate(g):
            if coefficient:
                hg += coefficient*second[j]
        add({word: 1}, values.get(word, 0), dg, sparse(hg))
        for a, M in enumerate(R):
            image = action.Q(M, {word: 1})
            if image:
                add(image, Hessian=alpha[a, :].T*dg.T+dg*alpha[a, :])
    for a, A in enumerate(R):
        add(action.Q(A, values), gradient=alpha[a, :].T, Hessian=alpha2[a])
        for b, B in enumerate(R):
            symmetric = total((s.Rational(1, 2), action.Q(A, action.Q(B, values))),
                              (s.Rational(1, 2), action.Q(B, action.Q(A, values))))
            if symmetric:
                add(symmetric, Hessian=alpha[a, :].T*alpha[b, :])
    return {w: {'value': s.cancel(f), 'gradient': sparse(g), 'Hessian': sparse(h)}
            for w, (f, g, h) in result.items() if f or g.todok() or h.todok()}


def reverse_order_factory(m, raw, chart, action):
    spin = m.spin
    Is = s.eye(16)[:, SPATIAL]
    # Spin acts first on the100 source coordinates, giving16+61+33=110.
    Dspin = s.SparseMatrix(100, 110, {})
    Dspin[:6, :16] = spin.z*Is.T
    Dspin[6:, 16:] = s.eye(94)
    aspin = s.SparseMatrix(6, 110, {})
    aspin[:, :16] = spin.alpha*Is.T
    hspin = []
    for H in spin.second:
        matrix = s.SparseMatrix(110, 110, {})
        matrix[:16, :16] = Is*H*Is.T
        hspin.append(matrix)
    hzspin = hspin[6:]+[s.SparseMatrix(110, 110, {}) for _ in range(94)]
    # Native group then restores the original70 scalars and36 gauge fields.
    equal(chart['alpha'][:, :6], s.zeros(12, 6))
    equal(chart['z'][:6, :], s.eye(112)[:6, :])
    Dnative = s.SparseMatrix(110, 122, {})
    Dnative[:16, :16] = s.eye(16)
    Dnative[16:, 16:] = chart['z'][6:, 6:]
    anative = s.SparseMatrix(12, 122, {})
    anative[:, 16:] = chart['alpha'][:, 6:]
    def restore(H):
        equal(H[:6, :], s.zeros(6, 112))
        equal(H[:, :6], s.zeros(112, 6))
        matrix = s.SparseMatrix(122, 122, {})
        matrix[16:, 16:] = H[6:, 6:]
        return matrix
    hn = [restore(H) for H in chart['Ha']]
    zn = [s.SparseMatrix(122, 122, {}) for _ in range(16)]
    zn += [restore(H) for H in chart['Hz'][6:]]
    Rspin = [lift_matrix(s.diag(S, S.conjugate())) for S in spin.native.lorentz.spin]
    for S in Rspin:
        for R in raw.R:
            equal(S*R, R*S)
    def extend(values, gradients, Hessians):
        first = extend_general(values, gradients, Hessians, Dspin, hzspin,
                               aspin, hspin[:6], Rspin, action)
        return extend_general({w: r['value'] for w, r in first.items()},
            {w: r['gradient'] for w, r in first.items()},
            {w: r['Hessian'] for w, r in first.items()},
            Dnative, zn, anative, hn, raw.R, action)
    return extend, Rspin+raw.R


def trace_packed(second, size, weights):
    vector = s.SparseMatrix(size*size, 1, {(size*i+j, 0): coefficient
        for (i, j), coefficient in weights.items() if coefficient})
    answer = second*dm(vector)
    return s.Matrix([DOMAIN.to_sympy(answer.rep.get(i, {}).get(0, DOMAIN.zero))
                     for i in range(answer.shape[0])])


def original_ordering_coefficients(m, raw, chart):
    """Compose the original70 momentum derivations before using CAR normal order."""
    native = raw.native
    old_geo = raw.old.implicit_jets(raw.old.source)
    old_a = old_geo['a']; old_z = raw.old.free_reader*old_geo['tangent']
    equal(old_a, m.native.alpha); equal(old_z, m.native.z)
    O, Rd = native.O, native.Rd
    phi = native.v
    D = sparse(O.T*s.Matrix.hstack(*(T*phi for T in native.rhob)))
    F, free = D.T.gauss_jordan_solve(s.eye(9)); assert free.rows == 0
    F = sparse(F); OF = sparse(O*F)
    y = raw.old.source[6:, :]
    V = sparse(s.Matrix.vstack(*((T*y).T for T in native.Tb)))
    momentum = sparse(Rd.row_join(s.zeros(70, 36))-OF*V)
    A = s.zeros(103, 70); A[6:, :] = momentum.T
    derivative = s.zeros(103, 1); derivative_normal = s.zeros(9, 1)
    for j in range(70):
        direction = momentum[j, :].T
        dphi = native.R*direction[:61, :]
        dD = O.T*s.Matrix.hstack(*(T*dphi for T in native.rhob))
        dF, parameters = D.T.gauss_jordan_solve(-dD.T*F)
        assert parameters.rows == 0
        dnormal = sparse(O*dF)
        dV = s.Matrix.vstack(*((T*direction).T for T in native.Tb))
        da = sparse(-dnormal*V-OF*dV)
        derivative[6:, :] += da[j, :].T
        derivative_normal += dnormal[j, :].T
    equal(momentum, m.data['scalar']['momentum_vectors'])
    equal(OF, m.data['scalar']['normal_embedding'])
    assert not m.data['scalar']['shift_derivative'].todok()
    # Original coordinate divergence: F depends only on61 scalar variables,
    # their orbit entries vanish at x=0, and all97 linear vector traces vanish.
    equal(V[:, :61], s.zeros(9, 61))
    assert all(s.trace(T) == 0 for T in native.Tb)
    coordinate_divergence = s.zeros(70, 1)
    for k in range(61):
        dD = O.T*s.Matrix.hstack(*(T*native.R[:, k] for T in native.rhob))
        dF, _ = D.T.gauss_jordan_solve(-dD.T*F)
        coordinate_divergence -= O*dF*V[:, k]
    equal(coordinate_divergence, s.zeros(70, 1))
    G = sparse(A*A.T)
    def old_traces(weight):
        angle = s.Matrix([s.trace(H*weight) for H in old_geo['Halpha']])
        remainder = -sum(((T*raw.old.source)*angle[a]
                         for a, T in enumerate(raw.old.T)), s.zeros(103, 1))
        remainder -= 2*sum((T*weight*old_a[a, :].T
                            for a, T in enumerate(raw.old.T)), s.zeros(103, 1))
        for a, T in enumerate(raw.old.T):
            for b, U in enumerate(raw.old.T):
                remainder += ((old_a[a, :]*weight*old_a[b, :].T)[0]
                              *(T*U+U*T)*raw.old.source/2)
        return angle, sparse(raw.old.free_reader*remainder)
    full_trace = trace_packed(chart['second'], 112,
                              {(j, j): 1 for j in range(6, 76)})
    angle_trace, coordinate_trace = old_traces(G)
    old_angle_trace = angle_trace+old_a*derivative
    old_coordinate_trace = coordinate_trace+old_z*derivative
    broken = s.zeros(12, 70); broken[:9, :] = OF.T
    residual = s.zeros(12, 70); residual[9:, :] = old_a*A
    whole = chart['alpha'][:, 6:76]
    equal(whole, broken+residual)
    equal(chart['z'][:, 6:76], old_z*A)
    # Keep all ordered native pairs, then independently use each actual Lie law.
    pair = s.zeros(12)
    for j in range(70):
        u, b, a = whole[:, j], broken[:, j], residual[:, j]
        pair += u*u.T-b*b.T-2*b*a.T-a*a.T
    pair = sparse(pair)
    equal(pair+pair.T, s.zeros(12))
    body_coeff = full_trace[:12, :]-derivative_normal.col_join(old_angle_trace)
    body = sum((body_coeff[a]*raw.R[a] for a in range(12)), s.zeros(504))
    actual_lie = 0
    for a in range(12):
        for b in range(a+1, 12):
            commutator = raw.R[a]*raw.R[b]-raw.R[b]*raw.R[a]
            expected = sum((v*R for v, R in zip(raw.structure[a][:, b], raw.R)), s.zeros(504))
            equal(commutator, expected)
            body += pair[a, b]*commutator
            actual_lie += bool(pair[a, b] and commutator.todok())
    equal(body, s.zeros(504))
    N = m.spin.e[0, 0]
    drift = sparse(N*(full_trace[12:, :]-old_coordinate_trace)/2)
    # Original gauge36 weight is contracted with the two independently generated inverses.
    W = m.data['gauge']['weight']
    gauge_full = trace_packed(chart['second'], 112,
        {(76+i, 76+j): v for (i, j), v in W.todok().items()})
    gauge_old = s.zeros(103); gauge_old[67:, 67:] = W
    ga, gz = old_traces(gauge_old)
    equal(gauge_full[:9, :], s.zeros(9, 1))
    equal(gauge_full[9:12, :], ga); equal(gauge_full[12:, :], gz)
    equal(chart['z'][:, 76:], old_z[:, 67:])
    equal(chart['alpha'][:9, 76:], s.zeros(9, 36))
    equal(chart['alpha'][9:, 76:], old_a[:, 67:])
    drift[0] -= N/2; drift[5] += N/2
    expected = s.zeros(100, 1)
    for index, coefficient in ((0, -s.Rational(1, 2)), (5, s.Rational(1, 2)),
        (7, s.Rational(7, 8)), (9, s.Rational(3, 8)),
        (12, s.Rational(15, 8)), (14, s.Rational(11, 8))):
        expected[index] = coefficient*N
    equal(drift, expected)
    equal(drift, m.complete_ordering_difference())
    print('PASS independent all100 ordering coefficients, complete native12 normal pairs and full504 Lie cancellation', flush=True)
    return drift, {'all70_original_momentum_fields': True,
        'source_scalar_form_divergence70_zero_by_coordinate_trace': True,
        'normal_pair_coefficient_entries': len(pair.todok()),
        'nonzero_ordered_pairs_using_actual_Lie': actual_lie,
        'native_Lie_matrix_checks': 66, 'full504_one_body_remainder_zero': True,
        'gauge36_first_and_second_inverse_contractions_equal': True}


def constraints(m, R, jet, action):
    values = clean({w: row['value'] for w, row in jet.items()})
    defects = []
    for a in range(18):
        value = total((1, {w: (m.orbit[a].T*r['gradient'])[0] for w, r in jet.items()}),
                      (-1, action.Q(R[a], values)))
        derivative = {w: sparse(m.L[a].T*row['gradient']+row['Hessian']*m.orbit[a])
                      for w, row in jet.items()}
        for word, row in jet.items():
            for target, coefficient in action.Q(R[a], {word: 1}).items():
                derivative.setdefault(target, s.zeros(122, 1))
                derivative[target] -= coefficient*row['gradient']
        derivative = {w: sparse(g) for w, g in derivative.items() if sparse(g).todok()}
        defects.append((value, derivative))
    return defects


def compare_jets(left, right):
    empty = {'value': 0, 'gradient': s.zeros(122, 1), 'Hessian': s.zeros(122)}
    for word in set(left) | set(right):
        a, b = left.get(word, empty), right.get(word, empty)
        assert s.cancel(a['value']-b['value']) == 0
        equal(a['gradient'], b['gradient']); equal(a['Hessian'], b['Hessian'])


def scope_and_sectors(m, raw, R):
    target, _ = read_bound('source_full_gauss_section')
    native = raw.native
    D = sparse(native.O.T*s.Matrix.hstack(*(T*native.v for T in native.rhob)))
    assert D.det() != 0 and D.shape == (9, 9)
    currents = s.Matrix(s.symbols('audit_native_G0:12', real=True))
    K = s.Matrix(9, 9, lambda a, b: (raw.structure[a][:, b].T*currents)[0])
    Delta = s.zeros(9).row_join(D).col_join((-D.T).row_join(K))
    saved = decode(target['source_second_class_measure']['Dirac_matrix'])
    equal(Delta, saved.subs({x: currents[int(str(x).removeprefix('actual_G'))]
                            for x in saved.free_symbols}))
    Di = D.inv()
    inverse = (Di.T*K*Di).row_join(-Di.T).col_join(Di.row_join(s.zeros(9)))
    equal(Delta*inverse, s.eye(18)); equal(inverse*Delta, s.eye(18))
    assert K.free_symbols & set(currents[9:])
    charge, _ = read_bound('source_joint_charge_conservation')
    Qs = [s.SparseMatrix(decode(item)) for item in charge['source_real_CAR504_generators'][:12]]
    checks = 0
    for Q in Qs:
        diagonal = list(Q.diagonal())
        for A in R:
            for (i, j), coefficient in s.SparseMatrix(A).todok().items():
                assert s.cancel((diagonal[i]-diagonal[j])*coefficient) == 0
            checks += 1
    print('PASS all12 source charge sectors and original broken9 second-class block with residual currents retained', flush=True)
    return {'source_charge_sector_generator_checks': checks, 'charge_sectors': 12,
        'full_CAR_modes': 504, 'broken9_D_rank': 9, 'broken18_Dirac_rank': 18,
        'unfixed_residual_Gs_retained_in_Dirac_bracket': True,
        'geometric_native12_not_physical_first_class12': True}


def independent_half_density(point, raw, values, gradients, Hessians):
    active = (0, 2, 5, 67+raw.gauge_free.index(1), 67+raw.gauge_free.index(12))
    variables = s.symbols('audit_density0:5', positive=True)
    at = {variable: point[j] for variable, j in zip(variables, active)}
    gs, hs = {}, {}
    for word in set(values) | set(gradients) | set(Hessians):
        powers = [s.Rational(len(word)+2, 2)]*3+[s.S.One, s.Rational(1, 2)]
        product = s.prod((point[j]/variable)**power
            for j, variable, power in zip(active, variables, powers))
        assert product.subs(at) == 1
        first = s.zeros(100, 1); second = s.SparseMatrix(100, 100, {})
        for j, variable in zip(active, variables):
            first[j] = s.diff(product, variable).subs(at)
            for k, other in zip(active, variables):
                second[j, k] = s.diff(product, variable, other).subs(at)
        g = gradients.get(word, s.zeros(100, 1))
        h = Hessians.get(word, s.SparseMatrix(100, 100, {}))
        value = values.get(word, 0)
        gs[word] = sparse(g+first*value)
        hs[word] = sparse(h+first*g.T+g*first.T+second*value)
    return values.copy(), gs, hs


def current_weyl_factory(model, point, action):
    """Independent normal-symbol differential evaluator, including ordering."""
    data = model.coefficients(tuple(point))
    leaf = model.leaf
    coframe = leaf.weyl.native.joint.coframe
    q = leaf.background(tuple(point))[0]
    substitution = dict(zip(coframe.q, q))
    divergence = s.zeros(100, 1)
    divergence[:6, :] = model.at_time(leaf.pairing['divergence'].subs(substitution))
    divergence[6:, :] = model.at_time(data['scalar']['div_principal']+data['gauge']['div_principal'])
    second = sum(s.diff(leaf.pairing['K'][i, j], coframe.q[i], coframe.q[j])
                 for i in range(6) for j in range(6))
    divdiv = model.at_time(second.subs(substitution))
    divdiv += model.at_time(data['scalar']['divdiv_principal']+data['gauge']['divdiv_principal'])
    divlinear = model.at_time(data['scalar']['div_momentum_identity']+data['gauge']['div_momentum_identity'])
    weights = model.at_time(data['scalar']['div_momentum_current']+data['gauge']['div_momentum_current'])
    divcurrent = s.SparseMatrix(sum((c*Q for c, Q in zip(weights, leaf.charges)), s.zeros(504)))
    M = data['linear_current']; zero = data['zero']
    def apply(values, gradients, Hessians):
        scalar = {}
        for word in set(values) | set(gradients) | set(Hessians):
            g = gradients.get(word, s.zeros(100, 1))
            h = Hessians.get(word, s.SparseMatrix(100, 100, {}))
            value = values.get(word, 0)
            coefficient = -sum(c*h[i, j] for (i, j), c in data['principal'].todok().items())
            coefficient -= (divergence.T*g)[0]+divdiv*value/4
            coefficient -= s.I*(data['linear_identity'].T*g)[0]+s.I*divlinear*value/2
            scalar[word] = coefficient+zero.scalar*value
        terms = [(1, scalar), (1, action.Q(zero.one_body, values)),
                 (-s.I/2, action.Q(divcurrent, values))]
        for j in range(100):
            derivative = clean({w: g[j] for w, g in gradients.items()})
            if derivative:
                terms.append((-s.I, action.Q(M[j], derivative)))
        for coefficient, A, B in zero.pairs:
            terms.append((coefficient, action.raw.normal(A, B, values)))
        return total(*terms)
    return apply


def hilbert_consumers(source, raw, reverse, action):
    current = SourceJointCCRCarPorts()
    point = s.Matrix([current.leaf.source_point[i] for i in current.leaf.free])
    equal(point, source.point)
    direct = current_weyl_factory(current, point, action)
    results = []
    inputs = ({(3, 287): s.Rational(2, 3)+s.I/13},
              {(): s.Rational(2, 5), (3, 287): 1+s.I/11, (3, 86, 417): -s.Rational(2, 7)})
    for index, values in enumerate(inputs):
        gradients, Hessians = {}, {}
        for word in values:
            gradients[word] = s.Matrix([s.Rational(j%5-2, 61)+s.I*s.Rational(j%7-3, 67)
                                       for j in range(100)])
            H = s.SparseMatrix(100, 100, {(j, j): -s.Rational(j%3+1, 71) for j in range(100)})
            for a, b in ((0, 7), (2, 67), (5, 77), (12, 88)):
                H[a, b] = H[b, a] = s.I/s.Integer(73)
            Hessians[word] = H
        # A nonzero derivative with zero value checks support and number handling.
        if index:
            gradients[(5,)] = s.eye(100)[:, 0]+s.I*s.eye(100)[:, 80]
            Hessians[(5,)] = s.SparseMatrix(100, 100, {(2, 81): s.S.One, (81, 2): s.S.One})
        expected_native = independent_half_density(point, raw, values, gradients, Hessians)
        actual_native = source.inverse_half_density_jet(values, gradients, Hessians)
        assert expected_native[0] == actual_native[0]
        for word in expected_native[1]:
            equal(expected_native[1][word], actual_native[1][word])
            equal(expected_native[2][word], actual_native[2][word])
        returned = source.action(values, gradients, Hessians)
        other_order = reverse(*expected_native)
        compare_jets(returned['generated122_jet'], other_order)
        source.section.verify_constraints(other_order)
        image = direct(values, gradients, Hessians)
        equal_states(returned['current_H_image'], image)
        _, old_raw = raw.old.extension_jet(raw.old.source, values, gradients, Hessians)
        without_density = total(*((1, part) for part in
            raw_whole_action(raw.old, raw.old.source, old_raw).values()))
        defect = total((1, image), (-1, without_density))
        assert defect
        results.append({'case': index, 'input_particle_numbers': sorted({len(w) for w in values}),
            'all_input_jet_particle_numbers': sorted({len(w) for w in set(values)|set(gradients)|set(Hessians)}),
            'current_H_output_words': len(image), 'full122_jet_words': len(other_order),
            'omitted_half_density_defect_words': len(defect),
            'direct_normal_symbol_Weyl_evaluator_matches': True,
            'different_group_combination_order_matches': True})
        print('PASS direct current Hilbert H, independent product-density and full122 mixed-number germ', index, flush=True)
    return {'scope': 'SOURCE122_CONFIGURATION_RETURN_TO_CURRENT_FORM_HALF_DENSITY_WEYL_H',
        'density_algorithm': 'Differentiate the literal source-normalized product in q0,q2,q5,A1,A12 twice; number exponent is computed separately for every value/gradient/Hessian word.',
        'current_H_algorithm': 'OpW(Kpp+ell.p+p.Q(M)+zero) with divK,divdivK,divell,divM and independent bit-CAR normal products.',
        'source_scalar_adjoint_form_zero_by_all_coordinate_coefficients': True,
        'new_consumers': results,
        'scope_limit': 'Current H is reached only after the original number-dependent half density and the actual source-point form equality. No off-source form equality is inferred.'}


def main():
    began = time.monotonic()
    target, hashes = read_bound('source_joint_quantum_section')
    assert target['scope'] == SCOPE
    signed, old_hashes = read_bound('independent_source_lorentz_quantum_section')
    assert signed['verdict'] == 'CERTIFIED'
    hashes.update(old_hashes)
    hilbert_target, hilbert_hashes = read_bound('source_joint_current_hilbert_section')
    assert hilbert_target['scope'] == 'SOURCE122_CONFIGURATION_RETURN_TO_CURRENT_FORM_HALF_DENSITY_WEYL_H'
    hashes.update(hilbert_hashes)
    patch_symbolic_equal()
    hilbert = SourceJointCurrentHilbertSection()
    m = hilbert.section
    raw = RawFullSection(); chart = raw.chart(raw.z0)
    equal(chart['first'], m.gauge.source.inverse)
    assert (chart['second']-m.gauge.source.inverse_second).is_zero_matrix
    action = BitAction()
    reverse, R = reverse_order_factory(m, raw, chart, action)
    for a, b in zip(R, m.R): equal(a, b)
    drift, coefficients = original_ordering_coefficients(m, raw, chart)
    sectors = scope_and_sectors(m, raw, R)
    assert m.native.Hamiltonian_action.__func__ is SourceQuantumGaussSection.Hamiltonian_action
    assert m.native.native.joint.action.__func__ is SourceJointLocalQuantum.action
    records = []
    for index, word in enumerate(((31, 287), (3, 86, 417))):
        values = {word: s.Rational(index+2, 3)+s.I/7}
        gradient = s.Matrix([s.Rational((j%7)-3, 43)+s.I*s.Rational((j%5)-2, 47)
                            for j in range(100)])
        H = s.SparseMatrix(100, 100, {(j, j): s.Rational((j%3)+1, 53) for j in range(100)})
        for a, b in ((0, 7), (5, 80), (2, 40), (14, 95)):
            H[a, b] = H[b, a] = s.I/s.Integer(59)
        gradients, Hessians = {word: gradient}, {word: H}
        expected = reverse(values, gradients, Hessians)
        actual = m.extend_jet(values, gradients, Hessians)
        compare_jets(actual, expected)
        defects = constraints(m, R, expected, action)
        assert all(not f and not g for f, g in defects)
        for row in expected.values():
            equal(row['gradient'].extract(TIME, [0]), s.zeros(4, 1))
            equal(row['Hessian'].extract(TIME, range(122)), s.zeros(4, 122))
        returned = m.native_action_from_extended_jet(actual)
        _, old = m.existing_native_action(values, gradients, Hessians)
        _, old_raw = raw.old.extension_jet(raw.old.source, values, gradients, Hessians)
        independent_parts = raw_whole_action(raw.old, raw.old.source, old_raw)
        independent_old = total(*((1, part) for part in independent_parts.values()))
        equal_states(old, independent_old)
        equal_states(returned['native'], independent_old)
        correction = clean({w: (drift.T*g)[0] for w, g in gradients.items()})
        assert correction
        equal_states(returned['source_ordering_correction'], correction)
        equal_states(returned['ambient'], total((1, independent_old), (1, correction)))
        for w, row in actual.items():
            equal(m.section_embedding.T*row['gradient'], gradients.get(w, s.zeros(100, 1)))
            equal(m.section_embedding.T*row['Hessian']*m.section_embedding,
                  Hessians.get(w, s.zeros(100)))
        omitted = {}
        for w, row in expected.items():
            h = row['Hessian'].copy()
            h[:16, 16:] = s.zeros(16, 106); h[16:, :16] = s.zeros(106, 16)
            omitted[w] = {**row, 'Hessian': h}
        bad = constraints(m, R, omitted, action)
        assert all(not f for f, _ in bad)
        counts = [sum(len(v.todok()) for v in g.values()) for _, g in bad]
        assert any(counts[:6]) and any(counts[6:])
        mixed = sum(len(row['Hessian'][:16, 16:].todok()) for row in actual.values())
        assert mixed
        records.append({'CAR_word': list(word), 'extended_CAR_words': len(actual),
            'mixed_Hessian_entries_one_orientation': mixed,
            'all18_values_and2196_derivatives_zero': True,
            'four_temporal_primary_and_derivatives_zero': True,
            'same_old_coefficient_left_H_readback': True,
            'source_correction': [[list(w), str(c)] for w, c in correction.items()],
            'omitted_only_cross_Hessian_defects_by_generator': counts})
        print('PASS reverse Spin-first/native-second joint122 germ and independently rebuilt old H', index, flush=True)
    hilbert_results = hilbert_consumers(hilbert, raw, reverse, action)
    owned_inputs = ('independent_source_joint_quantum_section.py', 'source_joint_quantum_section.json',
        'source_joint_current_hilbert_section.json',
        'independent_source_full_gauss_section.py', 'independent_source_quantum_gauss_section.py',
        'independent_source_quantum_stabilizer.py', 'independent_source_lorentz_quantum_section.json')
    hashes.update({str((HERE/name).relative_to(ROOT)): hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                   for name in owned_inputs})
    for name, digest in hashes.items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    out = {'root': ROOT_ID, 'scope': SCOPE, 'verdict': 'CERTIFIED',
        'verified_input_sha256': hashes,
        'independent_combination': 'Spin first:100->110; independent native implicit-slice second:110->122. Both mixed configuration legs and CAR products retained.',
        'all72_original_Spin_native_commutators_zero': True,
        'operator_coefficients': coefficients, 'source_sectors_and_broken_responsibility': sectors,
        'actual_callee': 'SourceQuantumGaussSection.Hamiltonian_action -> SourceQuantumStabilizer.joint -> SourceJointLocalQuantum.action',
        'independent_H_algorithm': 'RawGaussSection implicit residual3 jets -> raw_whole_action, reconstructing original native matrix coefficients and four-energy ordering.',
        'old_H_comparison_uses_later_Weyl_or_half_density': False,
        'current_Hilbert_consumer': hilbert_results,
        'central_drift100': [[j, str(v)] for j, v in enumerate(drift) if v],
        'new_source_germs': records,
        'scope_limit': 'Exact source-point configuration jets, old coefficient-left H readback and the separately paid current half-density/form H splice. Broken9 remain second class; no physical18-first-class quotient, spacetime Ward9, global-q operator equivalence or interacting spectrum is inferred.',
        'seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_joint_quantum_section.json').write_text(json.dumps(out, indent=2)+'\n')
    print('PASS CERTIFIED independent common122 source section', out['seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
