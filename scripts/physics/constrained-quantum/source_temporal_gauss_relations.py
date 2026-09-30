#!/usr/bin/env python3
"""Original time-shift atoms on the same scalar/Gauss quantum section.

The three nongauge shift atoms are restrictions of the gauge cross atoms
with a live coframe matrix, modulo the actual residual Gauss generators.
The matrix is kept as an operator coefficient; no temporal root is chosen.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_scalar_temporal_form import SourceScalarTemporalForm
from source_scalar_form_hamiltonian import relocate_section
from source_lorentz_contact import clean, equal, encode
from source_coframe_legendre import rational
from source_coframe_live_ordering import verify_jet_action
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state
from source_quantum_ordered_temporal import OrderedTemporalCoefficients, DOMAIN, add, scale
from source_quantum_temporal_symbol import N


def zero(value): assert s.cancel(s.expand(value)) == 0
def equal_state(a, b): assert weighted_sum([(1, a), (-1, b)]) == {}


def bound(name):
    data = json.loads((HERE/(name+'.json')).read_text())
    assert data['root'] == ROOT_ID
    for key in ('source_sha256', 'input_sha256'):
        for path, digest in data[key].items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    return data


def uniform_relations(model):
    native = model.native; graph = native.graph; R, Rd, O = graph.R, graph.dual_R, graph.O
    W = native.B.row_join(native.S); inverse = clean(W.inv())
    beta, gamma = inverse[:9, :], inverse[9:, :]
    equal(W*inverse, s.eye(12)); equal(inverse*W, s.eye(12))
    coordinates = s.Matrix(s.symbols('scalar_gauge0:97', real=True))
    x, A = coordinates[:61, :], coordinates[61:, :].reshape(3, 12)
    phi = native.c.vacuum+R*x
    D = clean(O.T*s.Matrix.hstack(*(T*phi for T in native.rho_b)))
    Vb = s.Matrix.vstack(*((T*coordinates).T for T in native.T_b))
    Vs = s.Matrix.vstack(*((T*coordinates).T for T in native.T_s))
    embedding = Rd.row_join(s.zeros(70, 36))
    Qall = [clean(s.diag(s.I*T, s.I*T.conjugate())) for T in graph.common.rho]
    vectors = []
    for a, rho in enumerate(native.c.rho):
        U = rho*phi
        # This polynomial identity followed by D^-1 gives U^T O D^-T=beta^T
        # at every point of the original det(D)!=0 chart.
        equal(clean(O.T*U), clean(D*beta[:, a]))
        left = clean(embedding.T*U-Vb.T*beta[:, a])
        gauge_vector = s.zeros(97, 1)
        ad = native.gauge.ad(s.eye(12)[:, a])
        for j in range(3): gauge_vector[61+12*j:61+12*(j+1), :] = ad*A[j, :].T
        right = clean(Vs.T*gamma[:, a]-gauge_vector)
        equal(left, right)
        current = clean(Qall[a]-sum((beta[j, a]*native.Q_b[j] for j in range(9)), s.zeros(504)))
        equal(current, clean(sum((gamma[h, a]*native.Q_s[h] for h in range(3)), s.zeros(504))))
        derivative = sum((gamma[h, a]*native.T_s[h] for h in range(3)), s.zeros(97))
        derivative -= s.diag(s.zeros(61), ad, ad, ad)
        equal(right.jacobian(coordinates), derivative)
        zero(s.trace(derivative)); vectors.append(right)
    Ui_vectors, residual, coordinate_cross = [], [], []
    derivatives = s.Matrix(s.symbols('derivative0:36'))
    for k in range(3):
        vector = clean(sum((A[k, a]*vectors[a] for a in range(12)), s.zeros(97, 1)))
        # Differentiating A_k itself is retained. It cancels by the original
        # trace-zero adjoint representation and invariant native complement.
        divergence = sum(s.diff(vector[j], coordinates[j]) for j in range(97))
        zero(divergence)
        Ui_vectors.append(vector); residual.append(clean(gamma*A[k, :].T))
        ad = native.gauge.ad(A[k, :].T)
        cross = s.zeros(1, 36)
        for j in range(3): cross[:, 12*j:12*(j+1)] = s.I*(ad*A[j, :].T).T
        coordinate_cross.append(cross)
    connection = s.zeros(4, 12); connection[1:, :] = A
    B, _ = native.gauge.spatial_data(connection, s.zeros(3, 48))
    C = s.Matrix(3, 3, lambda i, j: -s.I*sum(B[j, a]*derivatives[12*i+a] for a in range(12)))
    axial = s.Matrix([C[2, 1]-C[1, 2], C[0, 2]-C[2, 0], C[1, 0]-C[0, 1]])
    cross = s.Matrix.vstack(*coordinate_cross)
    equal(clean(axial), clean(cross*derivatives))
    L = model.e[1:, 1:]; Li = rational(L.inv()); volume = s.factor(L.det())
    generic_C = s.Matrix(3, 3, s.symbols('electric_magnetic0:9'))
    Ct = volume*Li.T*generic_C*Li
    transformed = s.Matrix([Ct[2, 1]-Ct[1, 2], Ct[0, 2]-Ct[2, 0], Ct[1, 0]-Ct[0, 1]])
    original = s.Matrix([generic_C[2, 1]-generic_C[1, 2], generic_C[0, 2]-generic_C[2, 0], generic_C[1, 0]-generic_C[0, 1]])
    equal(rational(transformed), rational(L*original))
    G = rational(Li.T*Li)
    equal(rational(G*L), Li.T)
    equal(rational(G*(L*L.T)), s.eye(3))
    equal(rational(model.time_coefficients[1:, 1:]), -Li/2)
    ports = native.joint.coframe.model.lorentz.raw_matter_ports(model.e)
    for k in range(3):
        spin = rational(-s.I*ports['E'].inv()*ports['oriented_principals'][k+1])
        for j, b in enumerate(model.y[1:]):
            equal(rational(spin.diff(b)), s.I*Li[k, j]*s.eye(4))
    return {'G': G, 'L': L, 'beta': beta, 'gamma': gamma, 'coordinates': coordinates,
        'residual_coefficients': rational(Li.T*s.Matrix.vstack(*(r.T for r in residual))),
        'report': {'all61_scalar_coefficients_original_normal_identity': True,
            'normal_identity': 'U_a^T O D^-T=beta_a^T, from O^T rho_a(v+Rx)=D beta_a and the actual nonzero D inverse.',
            'all12_full97_derivative_and_full504_current_coefficients_checked': True,
            'all12_generator_vector_divergences_zero': True,
            'all3_field_dependent_Ui_vector_divergences_zero': True,
            'scalar_adjoint_contact': 'For Pi=-i a.partial+n.Q, (Pi^dagger.Ui+Ui.Pi)/2 has contact -i div(a^T Ui)/2. Both partial(Ui) and div(a).Ui are retained and their complete sum vanishes.',
            'complete_current_identity': 'The scalar normal current -beta.Q_b cancels the broken part of dGamma(i rho(A_i)); the remaining current is gamma.Q_s.',
            'gauge_cross_identity': 'd_coordinate,i=i sum_j (ad(A_i)A_j).partial_Aj= axial(-i B_j.partial_Ai)_i.',
            'generic_frame_identity': 'axial(det(L) L^-T C L^-1)=L axial(C).',
            'matter_shift_identity': 'partial_bj(-i E^-1 D_k)=i (L^-1)_kj I4 for every original spatial principal k and all six q/four time parameters.',
            'operator_identity': 'a_i-sum_j G_ij(q)d_j=sum_h R_ih(q,A) G_s,h, G=(L L^T)^-1 and R=L^-T gamma(A). Coefficients stay on the left.',
            'after_actual_Gauss_extension': 'a=G(q)d on every local smooth CAR-valued residual3 section; no temporal secondary equation or value n is imposed.'}}


def shift_images(model, q, x, A, jets):
    data = model.coefficients((N, 0, 0, 0), q, x, A)
    native = model.native; rho = native.c.rho
    L = model.e[1:, 1:].subs(dict(zip(model.q, q))); Li = L.inv()
    Qall = [clean(s.diag(s.I*T, s.I*T.conjugate())) for T in native.graph.common.rho]
    U = [clean(sum((A[k, b]*rho[b]*data['phi'] for b in range(12)), s.zeros(70, 1))) for k in range(3)]
    connection = s.zeros(4, 12); connection[1:, :] = A
    B, _ = native.gauge.spatial_data(connection, s.zeros(3, 48))
    a, old, d = ([{} for _ in range(3)] for _ in range(3))
    for word, item in jets.items():
        f, gradient = item['value'], item['gradient'][6:, :]
        C = s.Matrix(3, 3, lambda i, j: -s.I*sum(B[j, b]*gradient[61+12*i+b] for b in range(12)))
        Ct = L.det()*Li.T*C*Li
        axial = (Ct[2, 1]-Ct[1, 2], Ct[0, 2]-Ct[2, 0], Ct[1, 0]-Ct[0, 1])
        for j in range(3): d[j] = weighted_sum([(1, d[j]), (axial[j], {word: 1})])
        for k in range(3):
            dU = s.zeros(70, 97)
            RA = sum((A[k, b]*rho[b] for b in range(12)), s.zeros(70))
            dU[:, :61] = RA*native.graph.R
            for b in range(12): dU[:, 61+12*k+b] = rho[b]*data['phi']
            vector = data['momentum_vectors']; normal = -data['normal_embedding']
            derivative = sum(vector[i, j]*dU[i, j] for i in range(70) for j in range(97))
            scalar_old = -s.I*(U[k].T*vector*gradient)[0]-s.I*f*derivative/2
            correction = -s.I*f*(data['divergence'].T*U[k])[0]/2
            matrix = clean(sum(((U[k].T*normal)[j]*model.form.scalar.Q[j] for j in range(9)), s.zeros(504))+
                           sum((A[k, b]*Qall[b] for b in range(12)), s.zeros(504)))
            previous = weighted_sum([(scalar_old, {word: 1}), (f, apply_superposition(matrix, {word: 1}))])
            updated = weighted_sum([(1, previous), (correction, {word: 1})])
            for j in range(3):
                old[j] = weighted_sum([(1, old[j]), (Li[k, j], previous)])
                a[j] = weighted_sum([(1, a[j]), (Li[k, j], updated)])
    values = {w: j['value'] for w, j in jets.items() if j['value']}
    gradients = {w: j['gradient'][6:, :] for w, j in jets.items()}
    patch = model.correction_atoms(data, q, values, gradients)
    for j in range(3): equal_state(a[j], weighted_sum([(1, old[j]), (1, patch[j+1])]))
    return data, a, d, old, patch


def coframe_noncommutation(model, G):
    cf = model.native.joint.coframe; q = cf.q
    coefficient = G[2, 2]; zero(coefficient-1/q[5]**2)
    gradient = s.Matrix([s.diff(coefficient, value) for value in q])
    first = rational(-2*cf.K*gradient)
    assert first.todok()
    q0 = tuple(cf.e0[j] for j in (5, 9, 10, 13, 14, 15)); at = dict(zip(q, q0))
    values = rational(first.subs(at)); direction = next(j for j in range(6) if values[j] != 0)
    f1 = s.eye(6)[:, direction]; f2 = s.zeros(6)
    G0 = coefficient.subs(at); dG = gradient.subs(at)
    data = cf.coefficients(q0)
    left = verify_jet_action(data, (), 0, G0*f1, dG*f1.T+f1*dG.T)
    right = verify_jet_action(data, (), 0, f1, f2)
    state = lambda record: {tuple(w): s.sympify(v) for w, v in record['raw_nested_square']}
    difference = weighted_sum([(1, state(left)), (-G0, state(right))])
    equal_state(difference, {(): values[direction]}); assert difference
    point = model.section.b0.copy(); point[:6, :] = s.Matrix(q0)
    relocate_section(model.section, point)
    gradient100 = s.zeros(100, 1); gradient100[direction] = 1
    first_jet = model.section.extend_jet({(): 0}, {(): gradient100}, {(): s.zeros(100)})
    product_H = s.zeros(100); product_H[:6, :6] = dG*f1.T+f1*dG.T
    second_jet = model.section.extend_jet({(): 0}, {(): G0*gradient100}, {(): product_H})
    gauss = [model.section.verify_Gauss_jet(jet) for jet in (first_jet, second_jet)]
    return {'matrix_entry': [2, 2], 'entry_function': str(coefficient),
        'all_six_q_first_order_commutator_coefficient': encode(first),
        'actual_source_test': 'Vacuum times a compact smooth cutoff in the original100-dimensional slice, equal1 near the displayed point, times (q_j-q_source,j); both this germ and G times it are extended through the original residual3 section.',
        'same_section_base103': encode(point), 'both_original_Gauss_two_jets': gauss,
        'derivative_direction': direction, 'actual_Hcf_G_minus_G_Hcf': encode_state(difference),
        'generic_G_must_not_be_moved_through_coframe_derivatives': True}


def free_word_scope():
    ordered = OrderedTemporalCoefficients(); ordered.atoms[0] = {(0,): DOMAIN.one}
    time_series, energies, _ = ordered.generate(3)
    reversal = lambda p: {tuple(reversed(w)): v for w, v in p.items()}
    defects = [add(p, scale(-1, reversal(p))) for p in energies]
    assert all(s.im(DOMAIN.to_sympy(value)) == 0 for p in energies for value in p.values())
    assert [len(p) for p in defects] == [0, 0, 0, 168]
    return {'energy_word_counts': [len(p) for p in energies],
        'free_star_difference_word_counts': [len(p) for p in defects],
        'time_order2_difference_counts': [len(add(row[2], scale(-1, reversal(row[2])))) for row in time_series],
        'first_nonzero_free_difference': {'word': [0, 1, 1], 'coefficient': str(DOMAIN.to_sympy(defects[3][(0, 1, 1)]))},
        'scope': 'The13 symbols are free in this calculation. The generated actual relation has nonconstant q coefficients, so neither free-word inequality nor a constant substitution decides the actual third-order operator. That higher-order consumer is not supplied by this receipt.'}


def main():
    started = time.monotonic(); pairing = bound('source_temporal_coframe_pairing')
    bound('source_scalar_temporal_form')
    assert all(all(value == 0 for value in support.values()) for support in pairing['shift_coefficient_support'])
    model = SourceScalarTemporalForm(); uniform = uniform_relations(model)
    print('PASS all source generator/field-dependent divergence coefficients and uniform live-q time-atom Gauss relation', flush=True)
    section = model.section
    original_A = section.A0.copy()
    x = s.Matrix([s.Rational((3*j+1) % 7-3, 100) for j in range(61)])
    A = original_A.copy(); A[0, 2] += s.Rational(1, 31); A[1, 7] += s.Rational(1, 19)
    qs = [tuple(section.b0[:6, 0]), (s.Rational(7, 6), s.Rational(1, 11), s.Rational(9, 8),
                                   s.Rational(-1, 13), s.Rational(1, 17), s.Rational(11, 10))]
    word = (7, 71); gradient = s.Matrix([s.I*s.Rational(j % 5-2, 47) for j in range(100)])
    u = s.Matrix([s.Rational(j % 3-1, 43) for j in range(100)]); Hessian = u*u.T-s.eye(100)
    cases = []
    for q in qs:
        point = s.Matrix(q).col_join(x).col_join(A.reshape(36, 1)); relocate_section(section, point)
        jets = section.extend_jet({word: 1}, {word: gradient}, {word: Hessian})
        gauss = section.verify_Gauss_jet(jets)
        data, atoms, cross, old, patch = shift_images(model, q, x, A, jets)
        G = rational(uniform['G'].subs(dict(zip(model.q, q))))
        expected = [weighted_sum((G[i, j], cross[j]) for j in range(3)) for i in range(3)]
        for actual, value in zip(atoms, expected): equal_state(actual, value)
        assert all(atoms) and any(patch[j+1] for j in range(3))
        source_constant = [weighted_sum([(1, atoms[j]), (-1, cross[j])]) for j in range(3)]
        wrong_lapse = [weighted_sum([(1, atoms[j]), (-1/N**2, cross[j])]) for j in range(3)]
        assert all(wrong_lapse)
        if q == qs[0]: assert not any(source_constant)
        else: assert any(source_constant)
        cases.append({'q': list(map(str, q)), 'scalar61': encode(x), 'gauge36': encode(A),
            'input_CAR': list(word), 'gradient100': encode(gradient), 'Hessian100': encode(Hessian),
            'whole_Gauss_jet': gauss, 'G_at_point': encode(G),
            'nongauge_shift_atoms': [encode_state(v) for v in atoms],
            'native_cross_atoms': [encode_state(v) for v in cross],
            'same_q_G_times_cross': [encode_state(v) for v in expected],
            'old_scalar_ordering_to_form_shift_patch': [encode_state(v) for v in patch[1:]],
            'replace_G_by_source_identity_defects': [encode_state(v) for v in source_constant],
            'replace_G_by_inverse_N_squared_defects': [encode_state(v) for v in wrong_lapse],
            'zero_value_nonzero_jet_words_retained': any(j['value'] == 0 and (j['gradient'].todok() or j['Hessian'].todok()) for j in jets.values())})
    commutator = coframe_noncommutation(model, uniform['G'])
    print('PASS two actual charged Gauss two-jets, nonzero scalar shift patches and real coframe/G commutator', flush=True)
    words = free_word_scope()
    names = ('source_temporal_gauss_relations.py', 'source_scalar_temporal_form.py', 'source_scalar_temporal_form.json',
        'source_temporal_coframe_pairing.py', 'source_temporal_coframe_pairing.json', 'source_scalar_form_hamiltonian.py',
        'source_quantum_stabilizer.py', 'source_quantum_gauss_section.py', 'source_quantum_ordered_temporal.py',
        'source_gauge_legendre.py', 'source_coframe_live_ordering.py')
    result = {'root': ROOT_ID, 'scope': 'ORIGINAL_TEMPORAL_ATOM_RELATIONS_ON_THE_ACTUAL_GAUSS_SECTION',
        'source_sha256': model.native.graph.common.source_hashes,
        'input_sha256': {str((HERE/name).relative_to(ROOT)): hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in names},
        'uniform_operator_relation': uniform['report'], 'generic_L': encode(uniform['L']),
        'generic_G': encode(uniform['G']), 'native_broken_coordinates': encode(uniform['beta']),
        'native_stabilizer_coordinates': encode(uniform['gamma']),
        'residual_Gauss_coefficients': encode(uniform['residual_coefficients']),
        'complete_coframe_shift_coefficient_support': pairing['shift_coefficient_support'],
        'actual_full_Gauss_consumers': cases, 'coframe_noncommutation': commutator,
        'old_ordered_word_readout': words,
        'direct_consumer': 'The actual temporal reduction must compose these source operators with G(q) and every coframe derivative retained. Nongauge shifts and native crosses are dependent restrictions of the same action, not13 independent operators.',
        'temporal_stationarity_or_summed_series_or_quantum_spectrum_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_temporal_gauss_relations.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source temporal Gauss atom relations', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
