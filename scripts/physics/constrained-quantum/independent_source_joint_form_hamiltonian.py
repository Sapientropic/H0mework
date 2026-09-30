#!/usr/bin/env python3
"""Raw-source audit of the common four-energy form and its full half density.

No joint/scalar form producer is imported. Original density Hessians and
exterior representations generate the operators, while direct differentiation
of the combined inverse half density supplies all hundred-coordinate jets.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_scalar_form_hamiltonian import (
    RawGaussSection, HERE, ROOT, ROOT_ID, bindings, rational, eq, decode, encode,
    terms, current, state_encode, decoded_state, raw_coefficients, form_action,
    adjoint_difference, zero, state_equal)
from independent_source_coframe_live_ordering import RawLiveCoefficients, full, polynomial_action
from independent_source_joint_local_quantum import raw_matter
from independent_source_gauge_legendre import W as WEDGE_PAIR, SIGMA, hodge, matrix_coordinates
from independent_source_reducing_coframe_metric import coefficient_audit
from independent_source_yukawa_reducing_carrier import original_kernel


def raw_gauge_coefficients(e, A, raw):
    y = s.Matrix(s.symbols('raw_A0:36', real=True)); fields = y.reshape(3, 12)
    connection = [sum((fields[i, a]*raw.fund[a] for a in range(12)), s.zeros(7)) for i in range(3)]
    magnetic = rational(s.Matrix.vstack(*(matrix_coordinates(connection[i]*connection[j]-connection[j]*connection[i]).T
                         for i, j in ((1, 2), (2, 0), (0, 1)))))
    constitutive = rational(-WEDGE_PAIR*hodge(e)/SIGMA)
    eq(constitutive.T, constitutive)
    electric = s.Matrix(s.symbols('raw_E0:36', real=True))
    curvature = electric.reshape(3, 12).col_join(magnetic)
    density = s.expand(sum(a*b for a, b in zip(curvature, constitutive*curvature*raw.Gram))/2)
    momentum = s.Matrix([s.diff(density, v) for v in electric])
    hessian = rational(momentum.jacobian(electric))
    eq(hessian, s.kronecker_product(constitutive[:3, :3], raw.Gram))
    electric_inverse = rational(constitutive[:3, :3].inv(method='DM'))
    weight = rational(s.kronecker_product(electric_inverse, raw.Gram.inv()))
    eq(hessian*weight, s.eye(36)); eq(weight*hessian, s.eye(36))
    shift = momentum.subs(dict.fromkeys(electric, 0)); ds = shift.jacobian(y)
    potential = -density.subs(dict.fromkeys(electric, 0))
    point = dict(zip(y, A.reshape(36, 1)))
    return dict(weight=weight, shift=rational(shift.subs(point)), ds=rational(ds.subs(point)),
        potential=s.cancel(potential.subs(point)))


def complete_adjoint_inputs(raw_cf, raw, carrier, candidate):
    inventory, Y, E, P, dual, mask = original_kernel(carrier)
    fullP = s.diag(P, P.conjugate())
    q = raw_cf.q; e = raw_cf.e; inverse = e.inv(); volume = s.factor(e.det())
    gamma = inventory['gamma']
    principals = [rational(s.I*volume*sum((inverse[mu, a]*gamma[a] for a in range(4)), s.zeros(4)))
                  for mu in range(4)]
    E_inverse, free = principals[0].gauss_jordan_solve(s.eye(4)); assert free.rows == 0
    spin = [rational(-s.I*E_inverse*principals[i]) for i in (1, 2, 3)]
    eq(-s.I*volume*E_inverse, raw_cf.N*gamma[0])
    for C, saved in zip(spin, candidate['formal_symmetry']['matter']['generic_all_six_q_spin_factors']):
        eq(C.H, -C); eq(C, decode(saved, {str(v): v for v in q}))
    for T in inventory['gauge']:
        eq(T.H, -T)
        internal = T[:63, :63]
        eq(T, s.kronecker_product(s.eye(4), internal))
    # The source-derived Y-null projection is unchanged at every live q:
    # its original temporal inverse times volume has just been rederived.
    for Yj in Y:
        eq(Yj*P, s.zeros(252)); eq(Yj.H*P, s.zeros(252))
    symbolic_A = s.Matrix(3, 12, s.symbols('native_A0:36', real=True))
    gauge = raw_gauge_coefficients(e, symbolic_A, raw)
    eq(gauge['weight'].T, gauge['weight']); eq(gauge['weight'].conjugate(), gauge['weight'])
    eq(gauge['shift'].conjugate(), gauge['shift']); zero(s.im(gauge['potential']))
    for variable in symbolic_A: eq(gauge['weight'].diff(variable), s.zeros(36))
    zero(s.trace(gauge['weight']*gauge['ds']))
    metric_record = json.loads((HERE/'source_reducing_coframe_metric.json').read_text())
    metric = coefficient_audit(raw_cf, metric_record, fullP)
    return fullP, metric, {'all_six_q_original_spin_principals_anti_Hermitian': True,
        'all12_original_internal_factors_anti_Hermitian_and_commuting_spin': True,
        'all70_original_Y_and_adjoint_zero_on_same_K_at_every_q': True,
        'original36_BF_electric_Hessian_and_magnetic_potential_regenerated': True,
        'generic_gauge_weight_real_symmetric_and_A_independent': True,
        'gauge_shift_real_and_derivative_ordering_constant_zero': True,
        'coframe_complete_live_adjoint_identity': metric['report']}


def build_operators(section, raw_cf, q, x, A):
    e = raw_cf.at(raw_cf.e, q)
    coframe = raw_cf.coefficients(q)
    scalar = raw_coefficients(section.native, e, x, A)
    gauge = raw_gauge_coefficients(e, A, section.native)
    connection = s.zeros(4, 12); connection[1:, :] = A
    matter_raw = raw_matter(e, scalar['phi'], connection)
    H = rational(-s.I*matter_raw['E_inverse']*matter_raw['lower'])
    matter = rational(s.diag(H, -H.conjugate()))
    return dict(coframe=coframe, scalar=scalar, gauge=gauge, matter=matter)


def whole_action(data, jets):
    components = {key: [] for key in ('coframe', 'scalar_form', 'gauge', 'matter_without_Lorentz')}
    gauge = data['gauge']; W, C = gauge['weight'], gauge['shift']
    constant = s.cancel((C.T*W*C)[0]/2+s.I*s.trace(W*gauge['ds'])/2+gauge['potential'])
    for word, (value, gradient, Hessian) in jets.items():
        cf, _ = polynomial_action(data['coframe'], word, value, gradient[:6, :], Hessian[:6, :6])
        sc = form_action(data['scalar'], word, value, gradient[6:, :], Hessian[6:, 6:])
        gg, gh = gradient[67:, :], Hessian[67:, 67:]
        scalar = -sum(v*gh[i, j] for (i, j), v in W.todok().items())/2
        scalar += s.I*(C.T*W*gg)[0]+value*constant
        components['coframe'].append((1, cf))
        components['scalar_form'].append((1, sc))
        components['gauge'].append((scalar, {word: 1}))
        components['matter_without_Lorentz'].append((1, current(data['matter'], {word: value})))
    components = {key: terms(values) for key, values in components.items()}
    return components, terms((1, values) for values in components.values())


def half_density_derivatives(section, point, number, include_coframe):
    ai, bi = section.free.index(68), section.free.index(79)
    positive = {0, 2, 5, ai, bi}
    z = s.Matrix([s.Symbol('slice_'+str(j), positive=True) if j in positive
                  else s.Symbol('slice_'+str(j), real=True) for j in range(100)])
    # This determinant is generated from the original residual3 orbit, not
    # supplied by either the joint candidate or its normalizing-jet helper.
    fullpoint = section.free_reader.T*z+section.reader.T*section.reader*section.source
    orbit = s.Matrix.hstack(*(T*fullpoint for T in section.T))
    determinant = s.factor((section.reader*orbit).det())
    source_det = s.factor(section.source_minor.det())
    density = s.sign(source_det)*determinant
    zero(density-8*z[ai]**2*z[bi])
    volume = z[0]*z[2]*z[5]
    U = s.sqrt(density)*(volume**s.Rational(number+2, 2) if include_coframe else 1)
    at = dict(zip(z, section.free_reader*point)); U0 = s.simplify(U.subs(at))
    assert U0 > 0
    inverse = 1/U
    first = s.zeros(100, 1); second = s.zeros(100)
    support = sorted(positive if include_coframe else {ai, bi})
    for j in support:
        first[j] = s.simplify(U0*s.diff(inverse, z[j]).subs(at))
        for k in support: second[j, k] = s.simplify(U0*s.diff(inverse, z[j], z[k]).subs(at))
    return first, second, s.factor(density.subs(at)), U0


def transformed_section(section, point, word, gradient, Hessian, include_coframe):
    first, second, rho, U0 = half_density_derivatives(section, point, len(word), include_coframe)
    changed_gradient = gradient+first
    changed_Hessian = Hessian+first*gradient.T+gradient*first.T+second
    geo, jets = section.extension_jet(point, {word: 1}, {word: changed_gradient}, {word: changed_Hessian})
    return jets, first, second, rho, U0


def divergence_coframe(data, raw_cf, metric, q, jets, number):
    sub = dict(zip(raw_cf.q, q)); divK = rational(metric['divK'].subs(sub))
    real_shift = s.cancel(metric['deltaV'].subs(metric['number'], number).subs(sub))
    matrices = [full(rational(M.subs(sub))) for M in metric['hermitian']]
    output = []
    for word, (value, gradient, Hessian) in jets.items():
        g, h = gradient[:6, :], Hessian[:6, :6]
        constant, _ = polynomial_action(data['coframe'], word, value, s.zeros(6, 1), s.zeros(6))
        scalar = -sum(v*h[i, j] for (i, j), v in data['coframe']['K'].todok().items())
        scalar -= (divK.T*g)[0]; scalar += real_shift*value
        output += [(1, constant), (scalar, {word: 1})]
        output += [(-s.I*g[j], current(M, {word: 1})) for j, M in enumerate(matrices)]
    return terms(output), real_shift


def main():
    began = time.monotonic(); path = HERE/'source_joint_form_hamiltonian.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    paid = ('independent_source_scalar_form_hamiltonian', 'independent_source_full_gauss_section',
        'source_yukawa_reducing_carrier', 'independent_source_yukawa_reducing_carrier',
        'source_reducing_coframe_metric', 'independent_source_reducing_coframe_metric',
        'independent_source_gauss_section_measure', 'independent_source_quantum_gauss_section')
    records = {}
    for name in paid:
        records[name] = json.loads((HERE/(name+'.json')).read_text()); count += bindings(records[name])
        assert records[name]['root'] == ROOT_ID
    section = RawGaussSection(); raw_cf = RawLiveCoefficients()
    assert section.native.hashes == candidate['source_sha256']
    P, metric, adjoints = complete_adjoint_inputs(raw_cf, section.native,
        records['source_yukawa_reducing_carrier'], candidate)
    print('PASS independent generic raw BF gauge, full matter and complete coframe formal adjoints', flush=True)
    saved = candidate['actual_consumer']
    q = tuple(map(s.sympify, saved['q'])); x, A = decode(saved['x61']), decode(saved['A36'])
    point = s.Matrix(q).col_join(x).col_join(A.reshape(36, 1))
    word = tuple(saved['input_CAR']); gradient = decode(saved['input_gradient100']); Hessian = decode(saved['input_Hessian100'])
    assert word == (7, 71) and all(P[i, i] == 1 for i in word)
    operators = build_operators(section, raw_cf, q, x, A)
    eq(operators['matter']*P, P*operators['matter'])
    eq(operators['matter'].H*P, P*operators['matter'])
    geo, jets = section.extension_jet(point, {word: 1}, {word: gradient}, {word: Hessian})
    gauss = section.Gauss_checks(point, jets)
    hidden = [w for w, (v, g, h) in jets.items() if v == 0 and (g.todok() or h.todok())]
    assert hidden
    pieces, image = whole_action(operators, jets)
    assert all(pieces.values())
    for name, piece in pieces.items():
        state_equal(piece, decoded_state(saved['all_four_component_images'][name]))
        assert all(len(w) == len(word) and all(P[i, i] == 1 for i in w) for w in piece)
    state_equal(image, decoded_state(saved['whole_image']))
    correction = terms((1, adjoint_difference(operators['scalar'], w, f, g[6:, :])) for w, (f, g, _) in jets.items())
    assert correction; state_equal(correction, decoded_state(saved['scalar_ordering_difference']))
    _, dropped = whole_action(operators, {w: jet for w, jet in jets.items() if jet[0] != 0})
    assert terms([(1, image), (-1, dropped)])
    print('PASS independent original four-energy off-source action, complete Gauss jet and nonzero scalar ordering difference', flush=True)
    transformed, first, second, rho, U0 = transformed_section(section, point, word, gradient, Hessian, True)
    transformed_gauss = section.Gauss_checks(point, transformed)
    rho_jets, _, _, _, _ = transformed_section(section, point, word, gradient, Hessian, False)
    section.Gauss_checks(point, rho_jets)
    normalized_pieces, normalized = whole_action(operators, transformed)
    rho_pieces, _ = whole_action(operators, rho_jets)
    for name, piece in normalized_pieces.items():
        state_equal(piece, decoded_state(saved['all_four_normalized_component_images'][name]))
        assert all(len(w) == len(word) and all(P[i, i] == 1 for i in w) for w in piece)
    expected_cf, real_shift = divergence_coframe(operators, raw_cf, metric, q, rho_jets, len(word))
    state_equal(expected_cf, normalized_pieces['coframe'])
    for name in ('scalar_form', 'gauge', 'matter_without_Lorentz'):
        state_equal(normalized_pieces[name], rho_pieces[name])
    expected = terms([(1, expected_cf)]+[(1, p) for name, p in rho_pieces.items() if name != 'coframe'])
    state_equal(normalized, expected)
    state_equal(normalized, decoded_state(saved['whole_normalized_image']))
    state_equal(expected, decoded_state(saved['independent_half_density_image']))
    assert terms([(1, normalized), (-1, image)])
    assert any(second[i, j] != 0 for i in (0, 2, 5) for j in range(6, 100))
    print('PASS literal combined100 inverse half-density derivatives and independent four-energy divergence readback', flush=True)
    paths = [Path(__file__), path, HERE/'source_joint_form_hamiltonian.py',
        HERE/'independent_source_scalar_form_hamiltonian.py', HERE/'independent_source_quantum_gauss_section.py',
        HERE/'independent_source_joint_local_quantum.py', HERE/'independent_source_coframe_live_ordering.py',
        HERE/'independent_source_reducing_coframe_metric.py', HERE/'independent_source_yukawa_reducing_carrier.py']
    paths += [HERE/(name+'.json') for name in paid]
    output = {'verdict': 'CERTIFIED_COMMON_SOURCE_FOUR_ENERGY_FORM_AND_FULL_HALF_DENSITY_CONSUMER',
        'root': ROOT_ID, 'source_sha256': section.native.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks': count, 'candidate_constructor_imported': False,
        'independent_method': 'Raw epsilon/coframe and native BF density Hessians; occupation-bit full scalar/Dirac/matter representation; complete97 original scalar derivative equations; implicit off-source residual3 inverse; direct100-coordinate inverse half-density differentiation and exterior-slot CAR.',
        'generic_adjoint_inputs': adjoints,
        'same_domain': 'Cc-infinity(Omega100) tensor algebraic Fock(K392), in the source component of the original positive coframe and invertible D9/residual3 chart. The scalar factor uses the new given kinetic form; coframe, gauge and matter retain their original order.',
        'actual_four_energy_consumer': {'point103': encode(point), 'input_CAR': list(word),
            'Gauss': gauss, 'zero_value_nonzero_derivative_words': [list(w) for w in hidden],
            'dropping_zero_value_words_changes_the_total_action': True,
            'all_four_nonzero_images': {name: state_encode(p) for name, p in pieces.items()},
            'whole_image': state_encode(image), 'nonzero_scalar_ordering_difference': state_encode(correction),
            'every_component_preserves_N2_and_K392': True},
        'combined_half_density_consumer': {'rho3_at_point': str(rho), 'U_at_point': str(U0),
            'normalized_inverse_first_derivative': encode(first),
            'normalized_inverse_second_derivative': encode(second), 'actual_cross_coframe_gauge_derivatives_retained': True,
            'Gauss': transformed_gauss, 'coframe_real_potential': str(real_shift),
            'all_four_normalized_images': {name: state_encode(p) for name, p in normalized_pieces.items()},
            'whole_normalized_image': state_encode(normalized),
            'independent_divergence_representation': state_encode(expected)},
        'formal_symmetry_argument': 'All four differential operators preserve the same compact smooth local section domain and the same finite CAR carrier. The source second-class cancellation supplies canonical measure, the unitary residual3 disintegration supplies rho3, and the complete coframe adjoint equation supplies v^(2+Number). The raw scalar adjoint form, real q-only gauge square, and Y-null Hermitian matter multiplication therefore share the coframe positive pairing. Their sum is formally symmetric and densely defined in the local weighted L2 completion.',
        'scope': 'Literal fixed y_source=(N,0,0,0), all live sixq/scalar61/gauge36 coefficients; the source-connected open chart and K392 reducing subtheory. The independent complement and full external-leg inventory remain. Formal symmetry is not a selected self-adjoint extension, convergent temporal elimination, a quantum spectrum, positive energy or a lifetime.',
        'old_scalar_quantum_operator_identified_with_new_form': False,
        'full504_inventory_replaced': False, 'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_joint_form_hamiltonian.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS independent source joint form Hamiltonian', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
