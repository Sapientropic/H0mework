#!/usr/bin/env python3
"""Original generator and differential audit of live temporal/Gauss relations."""
from __future__ import annotations

from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path
import time
import sympy as s

from independent_source_scalar_temporal_form import (
    RawGaussSection, RawLiveCoefficients, HERE, ROOT, ROOT_ID, bindings,
    rational, eq, decode, encode, terms, current, state_encode, decoded_state,
    zero, state_equal, raw_coefficients, reclock_scalar, fixed_correction_atoms,
    magnetic, original_inventory, polynomial_action, json_integer)
from independent_source_yukawa_reducing_carrier import free_add, free_scale, free_multiply, field_number, DOMAIN
from independent_source_gauge_legendre import ETA


def uniform_source(section, raw, candidate):
    native = section.native; q = raw.q
    basis = native.B.row_join(native.S)
    inverse, free = basis.gauss_jordan_solve(s.eye(12)); assert free.rows == 0
    eq(basis*inverse, s.eye(12)); eq(inverse*basis, s.eye(12))
    beta, gamma = inverse[:9, :], inverse[9:, :]
    eq(beta, decode(candidate['native_broken_coordinates']))
    eq(gamma, decode(candidate['native_stabilizer_coordinates']))
    z = s.Matrix(s.symbols('scalar_gauge0:97', real=True)); x, A = z[:61, :], z[61:, :].reshape(3, 12)
    phi = native.v+native.R*x
    D = rational(native.O.T*s.Matrix.hstack(*(T*phi for T in native.rhob)))
    Vb = s.Matrix.vstack(*((T*z).T for T in native.Tb))
    Vs = s.Matrix.vstack(*((T*z).T for T in native.Ts))
    tangential = native.Rd.row_join(s.zeros(70, 36))
    Q = [rational(s.diag(s.I*T, s.I*T.conjugate())) for T in native.matter]
    vectors = []
    for a in range(12):
        U = native.rho[a]*phi
        eq(native.O.T*U, D*beta[:, a])
        scalar_vector = rational(tangential.T*U-Vb.T*beta[:, a])
        gauge_vector = s.zeros(97, 1)
        for k in range(3): gauge_vector[61+12*k:61+12*(k+1), :] = native.ad[a]*A[k, :].T
        eq(scalar_vector, Vs.T*gamma[:, a]-gauge_vector)
        eq(Q[a]-sum((beta[b, a]*native.Qb[b] for b in range(9)), s.zeros(504)),
           sum((gamma[h, a]*native.Qs[h] for h in range(3)), s.zeros(504)))
        derivative = rational(scalar_vector.jacobian(z)); zero(s.trace(derivative))
        eq(derivative, sum((gamma[h, a]*native.Ts[h] for h in range(3)), s.zeros(97))-
           s.diag(s.zeros(61), *[native.ad[a]]*3))
        vectors.append(scalar_vector)
    field_vectors = [rational(sum((A[k, a]*vectors[a] for a in range(12)), s.zeros(97, 1))) for k in range(3)]
    for v in field_vectors: zero(sum(s.diff(v[j], z[j]) for j in range(97)))
    derivative_symbols = s.Matrix(s.symbols('audit_gauge_derivative0:36'))
    B = magnetic(native, A)
    C = s.Matrix(3, 3, lambda i, j: -s.I*sum(B[j, a]*derivative_symbols[12*i+a] for a in range(12)))
    axial = s.Matrix([C[2, 1]-C[1, 2], C[0, 2]-C[2, 0], C[1, 0]-C[0, 1]])
    gauge_cross = []
    for k in range(3):
        adjoint = sum((A[k, a]*native.ad[a] for a in range(12)), s.zeros(12))
        gauge_cross.append(s.I*sum((adjoint*A[j, :].T).dot(derivative_symbols[12*j:12*(j+1), :]) for j in range(3)))
    eq(axial, s.Matrix(gauge_cross))
    L = raw.e[1:, 1:]; Li = L.inv(); G = rational(Li.T*Li)
    symbolic_cross = s.Matrix(3, 3, s.symbols('audit_cross0:9', real=True))
    transformed = L.det()*Li.T*symbolic_cross*Li
    def axial_of(M): return s.Matrix([M[2, 1]-M[1, 2], M[0, 2]-M[2, 0], M[1, 0]-M[0, 1]])
    eq(axial_of(transformed), L*axial_of(symbolic_cross))
    eq(G*(L*L.T), s.eye(3)); eq(G*L, Li.T)
    residual = rational(Li.T*s.Matrix.vstack(*((gamma*A[k, :].T).T for k in range(3))))
    symbols = {str(v): v for v in (*q, *z)}
    eq(L, decode(candidate['generic_L'], symbols)); eq(G, decode(candidate['generic_G'], symbols))
    eq(residual, decode(candidate['residual_Gauss_coefficients'], symbols))
    ys = (s.Symbol('audit_lapse', positive=True), *s.symbols('audit_time_shift0:3', real=True))
    e = raw.e.copy(); e[:, 0] = s.Matrix(ys); metric = rational(e.det()*(e.T*ETA*e).inv())
    weights = rational(s.Matrix([1, *list(metric[0, 1:])])/(2*metric[0, 0]))
    W = rational(weights.jacobian(ys)); eq(weights, W*s.Matrix(ys)); eq(W[1:, 1:], -Li/2)
    gamma4 = original_inventory()['gamma']; ei = e.inv()
    principal = [rational(s.I*e.det()*sum((ei[mu, a]*gamma4[a] for a in range(4)), s.zeros(4))) for mu in range(4)]
    E_inverse, free = principal[0].gauss_jordan_solve(s.eye(4)); assert free.rows == 0
    for k in range(3):
        matter = rational(-s.I*E_inverse*principal[k+1])
        for j in range(3): eq(matter.diff(ys[j+1]), s.I*Li[k, j]*s.eye(4))
    return G, W, Q, {'all12_original_normal_polynomial_identities': True,
        'all12_complete97_vector_and504_current_identities': True,
        'all12_constant_generator_and3_field_dependent_vector_divergences_zero': True,
        'original_magnetic_cross_equals_native_adjoint_vector': True,
        'complete_live_frame_axial_transformation_and_residual_coefficients': True,
        'all9_original_matter_shift_partial_coefficients': True,
        'operator_identity': 'a-G(q)d=R(q,A)Gs with G=(L L^T)^-1. All field coefficients multiply from the left. The full Pi-dagger Ui contact is the divergence of the actual vector; its two differentiated terms sum to zero.'}


def actual_shifts(section, raw, G, W, Q, row):
    q = tuple(map(s.sympify, row['q'])); x, A = decode(row['scalar61']), decode(row['gauge36'])
    point = s.Matrix(q).col_join(x).col_join(A.reshape(36, 1))
    word = tuple(row['input_CAR']); g, H = decode(row['gradient100']), decode(row['Hessian100'])
    _, jets = section.extension_jet(point, {word: 1}, {word: g}, {word: H})
    gauss = section.Gauss_checks(point, jets)
    e = raw.at(raw.e, q); data = raw_coefficients(section.native, e, x, A)
    data = reclock_scalar(section.native, data, e, A)
    L = e[1:, 1:]; Li = L.inv(); B = magnetic(section.native, A)
    old, updated, cross = ([[] for _ in range(3)] for _ in range(3))
    for w, (value, gradient, _) in jets.items():
        derivative = gradient[6:, :]
        C = s.Matrix(3, 3, lambda i, j: -s.I*sum(B[j, a]*derivative[61+12*i+a] for a in range(12)))
        Ct = L.det()*Li.T*C*Li
        for j, scalar in enumerate((Ct[2, 1]-Ct[1, 2], Ct[0, 2]-Ct[2, 0], Ct[1, 0]-Ct[0, 1])):
            cross[j].append((scalar, {w: 1}))
        for k in range(3):
            U = data['U'][k]; dU = s.zeros(70, 97)
            dU[:, :61] = sum((A[k, a]*section.native.rho[a] for a in range(12)), s.zeros(70))*section.native.R
            for a in range(12): dU[:, 61+12*k+a] = section.native.rho[a]*data['phi']
            differential_contact = s.cancel(sum(data['a'][i, a]*dU[i, a] for i in range(70) for a in range(97)))
            adjoint_contact = s.cancel((data['divergence'].T*U)[0])
            zero(differential_contact+adjoint_contact)
            current_matrix = rational(sum(((U.T*data['normal'])[a]*data['Q'][a] for a in range(9)), s.zeros(504))+
                sum((A[k, a]*Q[a] for a in range(12)), s.zeros(504)))
            old_scalar = -s.I*(U.T*data['a']*derivative)[0]-s.I*value*differential_contact/2
            previous = terms([(old_scalar, {w: 1}), (value, current(current_matrix, {w: 1}))])
            new = terms([(1, previous), (-s.I*value*adjoint_contact/2, {w: 1})])
            for j in range(3):
                old[j].append((Li[k, j], previous)); updated[j].append((Li[k, j], new))
    old, updated, cross = [[terms(v) for v in family] for family in (old, updated, cross)]
    _, patches = fixed_correction_atoms(data, raw.at(W, q), jets)
    actual_G = raw.at(G, q); eq(actual_G, decode(row['G_at_point']))
    expected = [terms((actual_G[i, j], cross[j]) for j in range(3)) for i in range(3)]
    for j in range(3):
        state_equal(updated[j], expected[j])
        state_equal(updated[j], terms([(1, old[j]), (1, patches[j+1])]))
        state_equal(updated[j], decoded_state(row['nongauge_shift_atoms'][j]))
        state_equal(cross[j], decoded_state(row['native_cross_atoms'][j]))
        state_equal(patches[j+1], decoded_state(row['old_scalar_ordering_to_form_shift_patch'][j]))
    frozen = [terms([(1, updated[j]), (-1, cross[j])]) for j in range(3)]
    lapse = [terms([(1, updated[j]), (-1/raw.N**2, cross[j])]) for j in range(3)]
    for j in range(3):
        state_equal(frozen[j], decoded_state(row['replace_G_by_source_identity_defects'][j]))
        state_equal(lapse[j], decoded_state(row['replace_G_by_inverse_N_squared_defects'][j]))
    assert all(updated) and all(lapse) and any(patches[j+1] for j in range(3))
    hidden = [list(w) for w, (f, g, h) in jets.items() if f == 0 and (g.todok() or h.todok())]
    assert hidden
    return {'q': list(map(str, q)), 'Gauss': gauss, 'zero_value_nonzero_derivative_words': hidden,
        'nongauge_shift_images': [state_encode(v) for v in updated],
        'native_cross_images': [state_encode(v) for v in cross],
        'old_to_form_patches': [state_encode(v) for v in patches[1:]],
        'source_identity_wrong_at_this_point': bool(any(frozen)), 'inverse_lapse_wrong_in_all3_directions': True}


def actual_commutator(section, raw, G, saved):
    coefficient = G[2, 2]; zero(coefficient-raw.q[5]**-2)
    dG = s.Matrix([s.diff(coefficient, q) for q in raw.q])
    first = rational(-2*raw.K*dG)
    eq(first, decode(saved['all_six_q_first_order_commutator_coefficient'], {str(q): q for q in raw.q}))
    point = decode(saved['same_section_base103']); q = tuple(point[:6, 0])
    eq(s.Matrix(q), section.source[:6, :])
    sub = dict(zip(raw.q, q)); direction = int(saved['derivative_direction'])
    assert direction == next(j for j in range(6) if first[j].subs(sub) != 0)
    g = s.eye(6)[:, direction]; scalar = coefficient.subs(sub); derivative = dG.subs(sub)
    data = raw.coefficients(q)
    left, _ = polynomial_action(data, (), 0, scalar*g, derivative*g.T+g*derivative.T)
    right, _ = polynomial_action(data, (), 0, g, s.zeros(6))
    difference = terms([(1, left), (-scalar, right)])
    state_equal(difference, decoded_state(saved['actual_Hcf_G_minus_G_Hcf']))
    state_equal(difference, {(): raw.N}); assert difference
    g100 = s.zeros(100, 1); g100[direction] = 1
    H100 = s.zeros(100); H100[:6, :6] = derivative*g.T+g*derivative.T
    _, first_jet = section.extension_jet(point, {(): 0}, {(): g100}, {(): s.zeros(100)})
    _, second_jet = section.extension_jet(point, {(): 0}, {(): scalar*g100}, {(): H100})
    gauss = [section.Gauss_checks(point, jets) for jets in (first_jet, second_jet)]
    return {'original_G22': str(coefficient), 'whole_first_order_commutator': encode(first),
        'both_actual_Gauss_two_jets': gauss, 'actual_compact_germ_commutator': state_encode(difference),
        'scope': 'The compact slice vacuum germ vanishes at the base point and has one nonzero coframe derivative. The displayed value is an actual differential-operator commutator, not a free-word inequality.'}


def free_coefficients(saved):
    n = s.Symbol('n', positive=True); b = s.symbols('b0:3', real=True); ys = (n, *b)
    N = 3*s.sqrt(30)/25; origin = dict(zip(ys, (N, 0, 0, 0))); delta = n*n-sum(x*x for x in b)
    pairs = ((0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (1, 2))
    weights = [*ys, *[(n*n-b[i]*b[j])/(2*n*delta) if i == j else -b[i]*b[j]/(n*delta) for i, j in pairs], *[-x/delta for x in b]]
    source = [s.Rational(9, 5), 0, 0, 0]+[s.Rational(324, 625)]*3+[0]*6
    Hs = s.factor(sum(a*c for a, c in zip(source, weights)))
    J = [-s.diff(Hs, y, y).subs(origin) for y in ys]
    letters = [{(a,): DOMAIN.one} for a in range(13)]
    @lru_cache(None)
    def d(part, indices):
        value = Hs if part == -1 else weights[part]
        for a in indices: value = s.diff(value, ys[a])
        return s.simplify(value.subs(origin))
    def factorial(indices): return s.prod(s.factorial(indices.count(a)) for a in range(4))
    def product(indices, vector):
        value = {(): DOMAIN.one}
        for a in indices: value = free_multiply(value, vector[a])
        return value
    u1 = [free_scale(1/J[a], free_add(*(free_scale(d(j, (a,)), letters[j]) for j in range(13)))) for a in range(4)]
    quadratic = list(itertools.combinations_with_replacement(range(4), 2))
    cubic = list(itertools.combinations_with_replacement(range(4), 3))
    u2 = []
    for a in range(4):
        terms0 = [free_scale(-d(-1, tuple(sorted((a, *indices))))/factorial(indices), product(indices, u1)) for indices in quadratic]
        terms0 += [free_scale(-d(j, tuple(sorted((a, r)))), free_multiply(letters[j], u1[r])) for j in range(13) for r in range(4)]
        u2.append(free_scale(-1/J[a], free_add(*terms0)))
    energy = [{(): field_number(Hs.subs(origin))}, free_add(*(free_scale(d(j, ()), letters[j]) for j in range(13)))]
    energy.append(free_add(*[free_scale(d(-1, indices)/factorial(indices), product(indices, u1)) for indices in quadratic],
        *[free_scale(d(j, (r,)), free_multiply(letters[j], u1[r])) for j in range(13) for r in range(4)]))
    third = [free_scale(d(-1, indices)/factorial(indices), product(indices, u1)) for indices in cubic]
    for a, c in quadratic:
        term = free_add(free_multiply(u1[a], u2[c]), free_multiply(u2[a], u1[c]))
        third.append(free_scale(d(-1, (a, c))/factorial((a, c)), term))
    third += [free_scale(d(j, (r,)), free_multiply(letters[j], u2[r])) for j in range(13) for r in range(4)]
    third += [free_scale(d(j, indices)/factorial(indices), free_multiply(letters[j], product(indices, u1))) for j in range(13) for indices in quadratic]
    energy.append(free_add(*third))
    def reversed_difference(poly): return free_add(poly, free_scale(-1, {tuple(reversed(w)): c for w, c in poly.items()}))
    defects = [reversed_difference(p) for p in energy]
    assert [len(p) for p in energy] == saved['energy_word_counts']
    assert [len(p) for p in defects] == saved['free_star_difference_word_counts']
    assert [len(reversed_difference(p)) for p in u2] == saved['time_order2_difference_counts']
    coefficient = DOMAIN.to_sympy(defects[3][(0, 1, 1)])
    zero(coefficient-s.sympify(saved['first_nonzero_free_difference']['coefficient']))
    return {'independent_direct_first_second_and_cubic_Taylor_coefficients': True,
        'free_energy_counts': [len(p) for p in energy], 'free_reversal_difference_counts': [len(p) for p in defects],
        'example_coefficient': str(coefficient),
        'scope': 'This checks the stated free-word readout only. No implication to the actual composed source operators is taken; the live G coefficients have the separately checked nonzero coframe commutator.'}


def main():
    started = time.monotonic(); path = HERE/'source_temporal_gauss_relations.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    names = ('source_scalar_temporal_form', 'independent_source_scalar_temporal_form',
        'source_temporal_coframe_pairing', 'independent_source_temporal_coframe_pairing')
    for name in names:
        record = json.loads((HERE/(name+'.json')).read_text()); count += bindings(record)
        assert record['root'] == ROOT_ID
    section = RawGaussSection(); raw = RawLiveCoefficients()
    assert section.native.hashes == candidate['source_sha256']
    G, W, Q, uniform = uniform_source(section, raw, candidate)
    print('PASS independent full native12/97/504 polynomial Gauss relation and all field divergences', flush=True)
    actual = [actual_shifts(section, raw, G, W, Q, row) for row in candidate['actual_full_Gauss_consumers']]
    assert len(actual) == 2 and not actual[0]['source_identity_wrong_at_this_point'] and actual[1]['source_identity_wrong_at_this_point']
    commutator = actual_commutator(section, raw, G, candidate['coframe_noncommutation'])
    print('PASS two independent full Gauss jets, scalar shift corrections and actual coframe commutator', flush=True)
    words = free_coefficients(candidate['old_ordered_word_readout'])
    paths = [Path(__file__), path, HERE/'source_temporal_gauss_relations.py',
        HERE/'independent_source_scalar_temporal_form.py', HERE/'independent_source_quantum_gauss_section.py',
        HERE/'independent_source_scalar_form_hamiltonian.py', HERE/'independent_source_yukawa_reducing_carrier.py',
        HERE/'independent_source_coframe_live_ordering.py']+[HERE/(name+'.json') for name in names]
    result = {'verdict': 'CERTIFIED_UNIFORM_ORIGINAL_TEMPORAL_GAUSS_RELATIONS_AND_LIVE_COFRAME_COMMUTATOR',
        'root': ROOT_ID, 'source_sha256': section.native.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks': count, 'candidate_constructor_imported': False,
        'independent_method': 'Original native generators and independently solved B/S coordinates; full polynomial97 vectors and504 CAR coefficients; implicit Gauss two-jets; raw shifted momenta; direct coframe differential action; closed first/second/cubic Taylor word formulas.',
        'uniform_operator_relation': uniform, 'generic_G': encode(G),
        'actual_full_Gauss_consumers': actual, 'actual_coframe_noncommutation': commutator,
        'independent_free_word_readout': words,
        'scope': 'a-G(q)d=R(q,A)Gs on the original invertible scalar chart, hence a=G(q)d on the actual residual3 section. The coefficients stay on the left and cannot be moved through coframe derivatives. No actual cubic-star defect, temporal secondary solution, series sum or quantum spectrum is claimed.',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'independent_source_temporal_gauss_relations.json').write_text(json.dumps(result, separators=(',', ':'), default=json_integer)+'\n')
    print('PASS independent source temporal Gauss relations', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
