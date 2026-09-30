#!/usr/bin/env python3
"""Raw four-time scalar form, fixed correction atoms and full-family audit."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_joint_form_hamiltonian import (
    RawGaussSection, RawLiveCoefficients, HERE, ROOT, ROOT_ID, bindings,
    rational, eq, decode, encode, terms, current, state_encode, decoded_state,
    zero, state_equal, raw_gauge_coefficients, whole_action)
from independent_source_scalar_form_hamiltonian import raw_coefficients, form_action, general_scalar_action
from independent_source_quantum_ordered_temporal import raw_coframe_family, generic_gauge_Gram_identity
from independent_source_common_hamiltonian import raw_matter, original_inventory
from independent_source_coframe_live_ordering import polynomial_action
from independent_source_gauge_legendre import ETA, matrix_coordinates


def at(value, substitutions):
    if isinstance(value, list): return [at(v, substitutions) for v in value]
    if isinstance(value, s.MatrixBase): return rational(value.subs(substitutions))
    return s.cancel(value.subs(substitutions))


def json_integer(value):
    if isinstance(value, s.Integer): return int(value)
    raise TypeError(f'Unexpected receipt value: {type(value).__name__}')


def reclock_scalar(raw, initial, e, A):
    """Only original metric contractions depend on the four time entries."""
    metric = rational(e.det()*(e.T*ETA*e).inv()); phi = initial['phi']
    U = [sum((A[i, a]*raw.rho[a]*phi for a in range(12)), s.zeros(70, 1)) for i in range(3)]
    b = rational(sum((metric[0, i+1]*U[i] for i in range(3)), s.zeros(70, 1)))
    db = s.zeros(70, 97)
    for i in range(3):
        T = sum((A[i, a]*raw.rho[a] for a in range(12)), s.zeros(70))
        db[:, :61] += metric[0, i+1]*T*raw.R
        for a in range(12): db[:, 61+12*i+a] = metric[0, i+1]*raw.rho[a]*phi
    db = rational(db)
    potential = s.cancel(-sum(metric[i+1, j+1]*(U[i].T*U[j])[0]/2
        for i in range(3) for j in range(3))+e.det()*((phi-raw.v).T*(phi-raw.v))[0])
    div_shift = s.cancel((initial['divergence'].T*b)[0]+sum(initial['a'][i, u]*db[i, u]
                           for i in range(70) for u in range(97)))
    return {**initial, 'metric': metric, 'h00': metric[0, 0], 'b': b, 'db': db,
            'potential': potential, 'div_shift': div_shift, 'U': U}


def nested70(data, jets):
    """Differentiate each original Pi_j using all97 independently solved derivatives."""
    a, n, b = data['a'], data['normal'], data['b']; directional = []
    for j in range(70):
        da = sum((a[j, u]*data['derivatives'][u][0][j, :] for u in range(97)
                  if a[j, u]), s.zeros(1, 97))
        dn = sum((a[j, u]*data['derivatives'][u][1][j, :] for u in range(97)
                  if a[j, u]), s.zeros(1, 9))
        directional.append((rational(da), rational(dn), s.cancel((a[j, :]*data['db'][j, :].T)[0])))
    old, new = [], []
    for word, (f, g103, H103) in jets.items():
        g, H = g103[6:, :], H103[6:, 6:]; unit = {word: 1}
        def charge(coefficients, state):
            return terms((coefficient, current(data['Q'][k], state))
                         for k, coefficient in enumerate(coefficients) if coefficient)
        for j in range(70):
            da, dn, db = directional[j]; ag = (a[j, :]*g)[0]
            first = terms([(-s.I*ag-b[j]*f, unit), (f, charge(n[j, :], unit))])
            differentiated = terms([(-s.I*((da*g)[0]+(a[j, :]*H*a[j, :].T)[0])-db*f-b[j]*ag, unit),
                                    (f, charge(dn, unit)), (ag, charge(n[j, :], unit))])
            square = terms([(-s.I, differentiated), (1, charge(n[j, :], first)), (-b[j], first)])
            old.append((1/(2*data['h00']), square))
            new += [(1/(2*data['h00']), square), (-s.I*data['divergence'][j]/(2*data['h00']), first)]
        for out in (old, new): out.append((f*data['potential'], unit))
    return terms(old), terms(new)


def fixed_correction_atoms(data, W, jets):
    r = data['divergence']; coefficients = []; images = []
    for a in range(4):
        derivative = rational(-W[0, a]*data['a'].T*r)
        charge = rational(-s.I*W[0, a]*data['normal'].T*r)
        multiplication = s.cancel(s.I*sum(W[i+1, a]*(r.T*data['U'][i])[0] for i in range(3)))
        coefficients.append(dict(derivative=derivative, current=charge, multiplication=multiplication))
        result = []
        for word, (f, g, _) in jets.items():
            result.append(((derivative.T*g[6:, :])[0]+multiplication*f, {word: 1}))
            result.extend((f*c, current(data['Q'][j], {word: 1})) for j, c in enumerate(charge) if c)
        images.append(terms(result))
    return coefficients, images


def magnetic(raw, A):
    connection = [sum((A[i, a]*raw.fund[a] for a in range(12)), s.zeros(7)) for i in range(3)]
    return rational(s.Matrix.vstack(*(matrix_coordinates(connection[i]*connection[j]-connection[j]*connection[i]).T
                                     for i, j in ((1, 2), (2, 0), (0, 1)))))


def main():
    started = time.monotonic(); path = HERE/'source_scalar_temporal_form.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    paid = ('independent_source_scalar_form_hamiltonian', 'independent_source_quantum_ordered_temporal',
            'independent_source_quantum_gauss_section', 'independent_source_full_quantum_adjoint',
            'source_quantum_temporal_symbol', 'independent_source_quantum_temporal_symbol')
    records = {}
    for name in paid:
        record = json.loads((HERE/(name+'.json')).read_text()); count += bindings(record)
        assert record['root'] == ROOT_ID
        records[name] = record
    section = RawGaussSection(); raw = RawLiveCoefficients()
    assert section.native.hashes == candidate['source_sha256']
    ys = (s.Symbol('scalar_n', positive=True), *s.symbols('scalar_b1:4', real=True))
    e, cf = raw_coframe_family(raw, ys)
    metric = rational(e.det()*(e.T*ETA*e).inv())
    weights = rational(s.Matrix([1, *list(metric[0, 1:])])/(2*metric[0, 0]))
    W = rational(weights.jacobian(ys)); eq(weights, W*s.Matrix(ys))
    assert not set(ys).intersection(W.free_symbols) and W.det() != 0
    symbols = {str(v): v for v in (*raw.q, *ys)}
    eq(weights, decode(candidate['generic_time_weights'], symbols))
    eq(W, decode(candidate['generic_time_coefficients'], symbols))
    # Affinity is an original coefficient identity. Four evaluation
    # functionals below only read these already-affine nongauge operators.
    scalar_weights = [1/metric[0, 0], *list(-metric[0, 1:]/metric[0, 0]),
        *list(metric[1:, 0]*metric[0, 1:]/metric[0, 0]-metric[1:, 1:]), e.det()]
    collected = scalar_weights+[cf['constant']]
    for key in ('K', 'one_body', 'correction', 'drift'): collected += list(cf[key].todok().values())
    for M in cf['M']: collected += list(M.todok().values())
    tensor = rational(sum((v*s.kronecker_product(cf['J'][a], cf['J'][b])
                           for (a, b), v in cf['W'].todok().items()), s.zeros(64)))
    collected += list(tensor.todok().values())
    for value in collected:
        polynomial = s.Poly(s.cancel(value), *ys)
        assert polynomial.total_degree() <= 1 and polynomial.coeff_monomial((0, 0, 0, 0)) == 0
    gauge_Gram = generic_gauge_Gram_identity(e, ys)
    print('PASS raw all-sixq/four-time scalar correction weights and complete original nongauge affinity', flush=True)

    saved = candidate['actual_consumer']; q = tuple(map(s.sympify, saved['q']))
    time_column = tuple(map(s.sympify, saved['time_column']))
    x, A = decode(saved['x61']), decode(saved['A36'])
    substitutions = {**dict(zip(raw.q, q)), **dict(zip(ys, time_column))}
    actual_e = at(e, substitutions)
    data = raw_coefficients(section.native, actual_e, x, A)
    shifted = reclock_scalar(section.native, data, actual_e, A)
    for key in ('b', 'db', 'potential', 'h00', 'div_shift'):
        if isinstance(data[key], s.MatrixBase): eq(data[key], shifted[key])
        else: zero(data[key]-shifted[key])
    data = shifted
    eq(data['b'], decode(saved['original_shift']))
    assert len(data['db'].todok()) == saved['shift_derivative_nonzero_entries']
    assert all(data['metric'][0, j] != 0 for j in (1, 2, 3))
    assert (data['divergence'].T*data['b'])[0] != 0
    shift_derivative = s.cancel(sum(data['a'][j, u]*data['db'][j, u] for j in range(70) for u in range(97)))
    assert shift_derivative != 0 and data['principal'][:61, 61:].todok()
    point = s.Matrix(q).col_join(x).col_join(A.reshape(36, 1))
    word = tuple(saved['input_CAR']); assert word == (144, 396)
    gradient, Hessian = decode(saved['gradient100']), decode(saved['Hessian100'])
    _, jets = section.extension_jet(point, {word: 1}, {word: gradient}, {word: Hessian})
    gauss = section.Gauss_checks(point, jets)
    old = terms((1, general_scalar_action(data, w, f, g[6:, :], H[6:, 6:])) for w, (f, g, H) in jets.items())
    new = terms((1, form_action(data, w, f, g[6:, :], H[6:, 6:])) for w, (f, g, H) in jets.items())
    coefficients, delta = fixed_correction_atoms(data, at(W, dict(zip(raw.q, q))), jets)
    for c, row in zip(coefficients, candidate['four_atoms']):
        eq(c['derivative'], decode(row['derivative'])); eq(c['current'], decode(row['current']))
        zero(c['multiplication']-s.sympify(row['multiplication']))
    for image, saved_image in zip(delta, saved['four_correction_atom_images']):
        assert image; state_equal(image, decoded_state(saved_image))
        assert all(len(w) == 2 and sum(i % 63 < 7 for i in w) == 0 for w in image)
    correction = terms(zip(time_column, delta))
    state_equal(terms([(1, new), (-1, old)]), correction)
    assert terms([(1, correction), (-time_column[0], delta[0])])
    nested_old, nested_new = nested70(data, jets)
    state_equal(old, nested_old); state_equal(new, nested_new)
    state_equal(old, decoded_state(saved['original_full70_old_square']))
    state_equal(new, decoded_state(saved['original_full70_adjoint_form']))
    print('PASS independent all97 divergence, shifted70 nested actions and four fixed correction atoms', flush=True)

    N = raw.N; inventory = original_inventory()
    source_A = section.source[67:, :].reshape(3, 12)
    source_B = magnetic(section.native, source_A)
    source_S = rational(2*source_B*section.native.Gram*source_B.T)
    assert source_S.is_diagonal() and len(set(source_S.diagonal())) == 1
    source_magnetic = source_S[0, 0]
    # The temporal seed is the original canonical source with its actual
    # matter field, not the zero-particle Fock vacuum. Consume that already
    # generated and independently certified nongauge source germ unchanged.
    epsilon = s.Symbol('source_epsilon', real=True)
    source_nongauge = s.cancel(s.sympify(records['source_quantum_temporal_symbol']['generated_input_germ'][0],
        locals={str(epsilon): epsilon}).subs(epsilon, 0))
    assert source_nongauge == s.Rational(9, 5) and source_magnetic == s.Rational(324, 625)
    def original_parts(clock):
        sub = {**dict(zip(raw.q, q)), **dict(zip(ys, clock))}
        ee = at(e, sub); cc = {k: at(v, sub) for k, v in cf.items()}
        sc = reclock_scalar(section.native, data, ee, A)
        connection = s.zeros(4, 12); connection[1:, :] = A
        matter = raw_matter(ee, sc['phi'], connection)
        onebody = rational(-s.I*matter['E_inverse']*matter['lower'])
        CAR = rational(s.diag(onebody, -onebody.conjugate()))
        components = {'coframe': [], 'scalar': [], 'matter_without_Lorentz': []}
        for w, (f, g, H) in jets.items():
            cf_image, _ = polynomial_action(cc, w, f, g[:6, :], H[:6, :6])
            components['coframe'].append((1, cf_image))
            components['scalar'].append((1, general_scalar_action(sc, w, f, g[6:, :], H[6:, 6:])))
            components['matter_without_Lorentz'].append((1, current(CAR, {w: f})))
        return {k: terms(v) for k, v in components.items()}
    base = original_parts((N, 0, 0, 0)); base_sum = terms((1, v) for v in base.values())
    values = {w: f for w, (f, _, _) in jets.items() if f}
    rawY = sum(((data['phi'][j]+s.I*data['phi'][j+35])*inventory['scalar'][j] for j in range(35)), s.zeros(252))
    Y = rational(s.kronecker_product(inventory['gamma'][0], s.eye(63))*rawY)
    Yatom = current(rational(s.diag(Y, -Y.conjugate())), values)
    old_atoms = [terms([(1/N, base_sum), (-source_nongauge, values), (-1, Yatom)])]
    for a in range(3):
        clock = [N, 0, 0, 0]; clock[a+1] = N/7
        image = terms((1, v) for v in original_parts(clock).values())
        old_atoms.append(terms([(7/N, image), (-7/N, base_sum)]))
    B = magnetic(section.native, A); L = actual_e[1:, 1:]; Li = L.inv()
    gauge_atoms = [[] for _ in range(9)]
    pairs = ((0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (1, 2))
    Gi = section.native.Gram.inv()
    for w, (f, g, H) in jets.items():
        gg, HH = g[67:, :], H[67:, 67:]
        E = s.Matrix(3, 3, lambda i, j: -sum(Gi[a, b]*HH[12*i+a, 12*j+b] for a in range(12) for b in range(12)))
        C = s.Matrix(3, 3, lambda i, j: -s.I*sum(B[j, a]*gg[12*i+a] for a in range(12)))
        M = B*section.native.Gram*B.T*f
        S = rational(L.det()*Li.T*(E/2+2*M)*Li); Ct = rational(L.det()*Li.T*C*Li)
        scalars = [S[i, j]-(source_magnetic*f if i == j else 0) for i, j in pairs]
        scalars += [Ct[2, 1]-Ct[1, 2], Ct[0, 2]-Ct[2, 0], Ct[1, 0]-Ct[0, 1]]
        for a, value in enumerate(scalars): gauge_atoms[a].append((value, {w: 1}))
    old_atoms += [terms(v) for v in gauge_atoms]+[Yatom]
    atoms = [terms([(1, old_atoms[a]), (1, delta[a])]) if a < 4 else old_atoms[a] for a in range(14)]
    for actual, recorded in zip(atoms, candidate['actual_fourteen_atom_consumer']['all_fourteen_images']):
        state_equal(actual, decoded_state(recorded))
    clock_n, *clock_b = time_column; discriminant = clock_n**2-sum(b*b for b in clock_b)
    time_functions = [*time_column, *[(clock_n**2-clock_b[i]*clock_b[j])/(2*clock_n*discriminant)
                       if i == j else -clock_b[i]*clock_b[j]/(clock_n*discriminant) for i, j in pairs],
                      *[-b/discriminant for b in clock_b]]
    seed = source_nongauge*clock_n+source_magnetic*sum(time_functions[4:7])
    reconstructed = terms([(seed, values)]+list(zip(time_functions, atoms[:13]))+[(clock_n, atoms[13])])
    direct_parts = original_parts(time_column)
    gauge = raw_gauge_coefficients(actual_e, A, section.native)
    connection = s.zeros(4, 12); connection[1:, :] = A
    matter = raw_matter(actual_e, data['phi'], connection)
    onebody = rational(-s.I*matter['E_inverse']*matter['lower'])
    operators = dict(coframe={k: at(v, substitutions) for k, v in cf.items()}, scalar=data,
                     gauge=gauge, matter=rational(s.diag(onebody, -onebody.conjugate())))
    full_parts, full_image = whole_action(operators, jets)
    state_equal(full_parts['scalar_form'], new)
    final = candidate['actual_fourteen_atom_consumer']
    for key, value in full_parts.items():
        target = 'scalar' if key == 'scalar_form' else key
        state_equal(value, decoded_state(final['all_four_component_images'][target]))
        if target in direct_parts and target != 'scalar': state_equal(value, direct_parts[target])
    state_equal(full_image, reconstructed); state_equal(full_image, decoded_state(final['whole_image']))
    assert atoms[13] == old_atoms[13] and atoms[13]
    print('PASS raw original fourteen atoms, unchanged Yukawa and complete four-time family reconstruction', flush=True)
    paths = [Path(__file__), path, HERE/'source_scalar_temporal_form.py',
        HERE/'independent_source_scalar_form_hamiltonian.py', HERE/'independent_source_quantum_gauss_section.py',
        HERE/'independent_source_quantum_ordered_temporal.py', HERE/'independent_source_joint_form_hamiltonian.py',
        HERE/'independent_source_common_hamiltonian.py']+[HERE/(name+'.json') for name in paid]
    out = {'verdict': 'CERTIFIED_ORIGINAL_FOUR_TIME_SCALAR_FORM_AND_FOUR_FIXED_ATOM_REPLACEMENTS',
        'root': ROOT_ID, 'source_sha256': section.native.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks': count, 'candidate_constructor_imported': False,
        'independent_method': 'Original epsilon and native Hodge coefficients; all97 differentiated Gauss solves; separate70 nested momenta; implicit residual3 two-jet; four readouts of the proved-affine original nongauge family; original magnetic Gram and actual fourteen-atom reconstruction.',
        'generic_four_time_weights': encode(weights), 'generic_four_time_coefficients': encode(W),
        'original_affine_coefficient_count': len(collected), 'original_gauge_Gram_identity': gauge_Gram,
        'actual_scalar_consumer': {'Gauss': gauss, 'input_CAR': list(word),
            'complete_old_square': state_encode(old), 'complete_adjoint_form': state_encode(new),
            'four_fixed_correction_images': [state_encode(v) for v in delta],
            'nonzero_shift_derivative_contraction': str(shift_derivative),
            'all97_divergence_and70_nested_actions_equal': True,
            'all_three_shift_corrections_and_scalar_gauge_cross_symbol_retained': True},
        'actual_fourteen_atoms': [state_encode(v) for v in atoms],
        'all_four_component_images': {k: state_encode(v) for k, v in full_parts.items()},
        'source_seed_readout': {'original_canonical_nongauge_germ': str(source_nongauge),
            'raw_magnetic_Gram_diagonal': str(source_magnetic)},
        'whole_image': state_encode(full_image), 'unchanged_original_atoms': list(range(4, 14)),
        'scope': 'Original four-time scalar Pi-dagger Pi realization and exact fixed replacements0..3 in the original fourteen-atom family. All derivatives, original Y and source seed remain. No temporal-series sum, equality of distinct quantization orders, spectrum or lifetime is inferred.',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'independent_source_scalar_temporal_form.json').write_text(
        json.dumps(out, separators=(',', ':'), default=json_integer)+'\n')
    print('PASS independent source scalar temporal form', out['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
