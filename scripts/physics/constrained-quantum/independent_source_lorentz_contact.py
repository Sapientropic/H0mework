#!/usr/bin/env python3
"""Independent untruncated BF/Cartan elimination and real matter-current audit.

The geometric coefficients below are built from Levi-Civita contractions of
the original connection curvature. No second-jet producer or candidate
Hessian is used to construct them.
"""
from __future__ import annotations

from collections import defaultdict
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import re
import sys
import time

import sympy as s

from independent_spectral_splice import ROOT_ID, clean, equal, matrix

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
ROOT = HERE.parents[3]
PAIRS = ((0, 1), (0, 2), (0, 3), (2, 3), (3, 1), (1, 2))
SIGNS = (-1, 1, 1, 1)
J = s.MutableSparseMatrix.zeros(6, 6)
for _a in range(3):
    J[_a, _a+3], J[_a+3, _a] = 1, -1
WEDGE = s.SparseMatrix(6, 6, lambda i, j: s.LeviCivita(*PAIRS[i], *PAIRS[j]))
GENERATORS = []
for _a, _b in PAIRS:
    _value = s.MutableSparseMatrix.zeros(4, 4)
    _value[_a, _b], _value[_b, _a] = SIGNS[_a], -SIGNS[_b]
    GENERATORS.append(_value)


def original_gamma():
    body = (ROOT/'Lean/SaturationMonoid/PhysicsCore/DiracCliffordRepresentation.lean').read_text()
    values = []
    for name in ('Zero', 'One', 'Two', 'Three'):
        literal = re.search(r'def diracGamma'+name+r'\s*:.*?:=\s*!!\[(.*?)\]', body, re.S).group(1)
        values.append(s.SparseMatrix([[s.sympify(v.strip().replace('Complex.I', 'I'))
            for v in row.split(',')] for row in literal.split(';')]))
    for a, b in itertools.product(range(4), repeat=2):
        equal(values[a]*values[b]+values[b]*values[a],
              (2*SIGNS[a] if a == b else 0)*s.eye(4))
    return values


def exterior(e):
    return s.SparseMatrix(6, 6, lambda i, j:
        e[PAIRS[i][0], PAIRS[j][0]]*e[PAIRS[i][1], PAIRS[j][1]]-
        e[PAIRS[i][0], PAIRS[j][1]]*e[PAIRS[i][1], PAIRS[j][0]])


def original_hessian(e):
    """The coefficient of each omega_mu,a omega_nu,b in B(e) wedge [omega,omega]."""
    B = J*exterior(e)
    entries = {}
    for mu, nu in itertools.combinations(range(4), 2):
        q, orientation = (PAIRS.index((mu, nu)), 1) if (mu, nu) in PAIRS else \
            (PAIRS.index((nu, mu)), -1)
        for a, b in itertools.product(range(6), repeat=2):
            bracket = GENERATORS[a]*GENERATORS[b]-GENERATORS[b]*GENERATORS[a]
            coefficient = s.expand(sum(B[c, k]*WEDGE[k, q]*orientation*SIGNS[i]*bracket[i, j]
                for c, (i, j) in enumerate(PAIRS) for k in range(6)))
            if coefficient:
                entries[6*mu+a, 6*nu+b] = coefficient
                entries[6*nu+b, 6*mu+a] = coefficient
    return s.SparseMatrix(24, 24, entries)


def geometric_load(e):
    """Integration by parts of B(e) wedge d(omega), before connection elimination."""
    result = s.MutableSparseMatrix.zeros(24, 64)
    B = J*exterior(e)
    for q, (mu, nu) in enumerate(PAIRS):
        for c in range(6):
            coefficient = s.expand(sum(B[c, k]*WEDGE[k, q] for k in range(6)))
            for a, rho in itertools.product(range(4), repeat=2):
                derivative = s.diff(coefficient, e[a, rho])
                result[6*nu+c, 16*mu+4*a+rho] -= derivative
                result[6*mu+c, 16*nu+4*a+rho] += derivative
    return clean(result)


def torsion_maps(e):
    connection = s.MutableSparseMatrix.zeros(24, 24)
    derivative = s.MutableSparseMatrix.zeros(24, 64)
    for a, (q, (mu, nu)) in itertools.product(range(4), enumerate(PAIRS)):
        row = 6*a+q
        derivative[row, 16*mu+4*a+nu] = 1
        derivative[row, 16*nu+4*a+mu] = -1
        for c in range(6):
            connection[row, 6*mu+c] = sum(GENERATORS[c][a, b]*e[b, nu] for b in range(4))
            connection[row, 6*nu+c] = -sum(GENERATORS[c][a, b]*e[b, mu] for b in range(4))
    return clean(connection), clean(derivative)


def real_bilinear(value):
    real, imag = value.applyfunc(s.re), value.applyfunc(s.im)
    return clean(s.SparseMatrix.vstack(s.SparseMatrix.hstack(real, -imag),
                                      s.SparseMatrix.hstack(-imag, -real)))


def real_linear(value):
    real, imag = value.applyfunc(s.re), value.applyfunc(s.im)
    return clean(s.SparseMatrix.vstack(s.SparseMatrix.hstack(real, -imag),
                                      s.SparseMatrix.hstack(imag, real)))


def original_density_ports(e, gamma):
    inverse = e.inv()
    volume = s.Abs(e.det())
    contracted = [clean(s.I*volume*sum((inverse[mu, a]*gamma[a] for a in range(4)), s.zeros(4)))
                  for mu in range(4)]
    vertices = [clean(contracted[mu]*gamma[a]*gamma[b]/2)
                for mu in range(4) for a, b in PAIRS]
    return contracted[0], vertices


def original_matter_ports(e, gamma):
    temporal, vertices = original_density_ports(e, gamma)
    canonical = [clean(-s.I*temporal.inv()*v) for v in vertices]
    return temporal, vertices, canonical


def apply_one_body(value, vector):
    """Actual two-particle exterior action, retaining repeated internal labels at different modes."""
    result = defaultdict(lambda: s.Integer(0))
    columns = defaultdict(list)
    for (i, j), coefficient in value.todok().items():
        columns[j].append((i, coefficient))
    for state, amplitude in vector.items():
        for line, old in enumerate(state):
            for new, coefficient in columns[old]:
                outgoing = list(state)
                outgoing[line] = new
                if len(set(outgoing)) != len(outgoing):
                    continue
                parity = (-1)**sum(outgoing[i] > outgoing[j]
                    for i in range(len(outgoing)) for j in range(i+1, len(outgoing)))
                result[tuple(sorted(outgoing))] += parity*coefficient*amplitude
    return {key: s.expand(value) for key, value in result.items() if s.expand(value) != 0}


def certify_geometry():
    e = s.Matrix(4, 4, s.symbols('audit_e0:16', real=True))
    determinant = s.expand(e.det(method='domain-ge'))
    flat, hessian = original_hessian(s.eye(4)), original_hessian(e)
    transform = s.kronecker_product(e, s.eye(6))
    numerator = clean(transform.T*flat.inv()*transform)
    equal(transform*hessian*transform.T, determinant*flat)
    equal(hessian*numerator, determinant*s.eye(24))
    equal(numerator*hessian, determinant*s.eye(24))
    equal(hessian, hessian.T)
    assert flat.rank() == 24 and flat.det() == 256
    load = geometric_load(e)
    torsion, curl = torsion_maps(e)
    equal(torsion*numerator*load, determinant*curl)

    # All 72 auxiliary equations, at unrestricted curvature: the internal
    # variance sign occurs in the quadratic/constraint terms, never the BF term.
    variables = [s.Matrix(6, 6, s.symbols(prefix+'0:36', real=True))
                 for prefix in ('audit_B', 'audit_multiplier', 'audit_curvature')]
    B, multiplier, curvature = variables
    signs = s.diag(-1, -1, -1, 1, 1, 1)
    simple = J*exterior(e)
    density = s.expand(sum(WEDGE[k, q]*(B[a, k]*curvature[a, q]
        -signs[a, a]*B[a, k]*(J*B)[a, q]/2
        +signs[a, a]*multiplier[a, k]*(B[a, q]-simple[a, q]))
        for a, k, q in itertools.product(range(6), repeat=3) if WEDGE[k, q]))
    substitution = dict(zip(B, simple)) | dict(zip(multiplier, J*simple-signs*curvature))
    for variable in (*B, *multiplier):
        assert s.expand(s.diff(density, variable).xreplace(substitution)) == 0
    reduced = s.expand(density.xreplace(substitution))
    bf = sum(WEDGE[k, q]*simple[a, k]*curvature[a, q]
             for a, k, q in itertools.product(range(6), repeat=3))
    assert s.expand(reduced-bf+3*determinant) == 0
    for variable in e:
        assert s.expand(s.diff(reduced, variable)-s.diff(density, variable).xreplace(substitution)) == 0
    return e, determinant, flat, hessian, numerator, load, torsion, curl, (B, multiplier, curvature, density)


def certify_real_currents(e, gamma):
    E, density, canonical = original_matter_ports(e, gamma)
    identity, zero = s.eye(4), s.zeros(4)
    transform = s.Matrix.vstack(s.Matrix.hstack(identity, s.I*identity),
                                s.Matrix.hstack(identity, -s.I*identity))/s.sqrt(2)
    momentum = s.Matrix.vstack(s.Matrix.hstack(zero, -identity),
                               s.Matrix.hstack(-identity, zero))
    equal(transform*transform.H, s.eye(8))
    kinetic = real_bilinear(E)
    branch = []
    for V, W in zip(density, canonical):
        A = real_linear(-s.I*W)
        equal(E*(-s.I*W)+V, s.zeros(4))
        equal(kinetic*A, -real_bilinear(V))
        equal(momentum*A, real_bilinear(W))
        M = s.diag(W, -W.conjugate())
        equal(transform*(s.I*A)*transform.H, M)
        branch.append(M)
    # The same change also fixes the independent dual: no adjoint premise.
    dual_transform = -s.I*momentum*transform.H
    expected_dual = s.Matrix.vstack(s.Matrix.hstack(identity, -identity),
                                    s.Matrix.hstack(s.I*identity, s.I*identity))/s.sqrt(2)
    equal(dual_transform, expected_dual)
    return E, density, canonical, branch


def certify_car_ordering(hessian_inverse, branch):
    contraction = clean(sum((coefficient*branch[a]*branch[b]/2
        for (a, b), coefficient in hessian_inverse.todok().items()), s.zeros(8)))
    expected = -9*s.sqrt(30)/100
    equal(contraction, expected*s.eye(8))
    tested = []
    # These are actual source spin modes with a fixed exterior label. Every
    # matrix tensors I_63, so the subset is invariant in the full 504 carrier.
    for state in ((0,), (0, 1), (0, 2), (0, 4)):
        ordered, normal = defaultdict(lambda: s.Integer(0)), defaultdict(lambda: s.Integer(0))
        for (a, b), coefficient in hessian_inverse.todok().items():
            product = apply_one_body(branch[a], apply_one_body(branch[b], {state: s.Integer(1)}))
            single = apply_one_body(branch[a]*branch[b], {state: s.Integer(1)})
            for key in set(product) | set(single):
                ordered[key] += coefficient*product.get(key, 0)/2
                normal[key] += coefficient*(product.get(key, 0)-single.get(key, 0))/2
        expected_single = apply_one_body(contraction, {state: s.Integer(1)})
        for key in set(ordered) | set(normal) | set(expected_single):
            assert s.simplify(ordered[key]-normal[key]-expected_single.get(key, 0)) == 0
        result = {key: s.simplify(value) for key, value in normal.items() if s.simplify(value) != 0}
        if len(state) == 1:
            assert not result and expected_single
        if state == (0, 1):
            assert result == {(0, 1): 9*s.sqrt(30)/25}
        tested.append({'input_spin_modes': list(state), 'normal_ordered_image': [
            [list(key), str(value)] for key, value in sorted(result.items())]})
    return contraction, tested


def main():
    started = time.monotonic()
    candidate_path = HERE/'source_lorentz_contact.json'
    candidate = json.loads(candidate_path.read_bytes())
    assert candidate['root'] == ROOT_ID
    checked_bindings = 0
    for key in ('source_sha256', 'input_sha256'):
        for name, digest in candidate[key].items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
            checked_bindings += 1
    e, determinant, flat, H, K, G, torsion, curl, density_data = certify_geometry()
    gamma = original_gamma()
    report = candidate['generic_geometry']
    local_symbols = {f'e{i}': value for i, value in enumerate(e)}
    def symbolic_matrix(record):
        return s.SparseMatrix(*record['shape'], {(i, j): s.sympify(value, locals=local_symbols)
                             for i, j, value in record['entries']})
    for key, value in (('flat_Hessian', flat), ('flat_inverse', flat.inv()), ('Hessian', H),
                       ('inverse_numerator', K), ('geometry_source_map', G),
                       ('Cartan_torsion_map', torsion), ('coframe_exterior_derivative_map', curl)):
        equal(symbolic_matrix(report[key]), value)
    assert report['generic_independent_coframe_variables'] == 16
    assert report['generic_independent_coframe_derivative_variables'] == 64
    assert report['flat_rank'] == 24 and report['flat_determinant'] == '256'
    print('PASS independent original72 auxiliary Euler, all16 coframe responses, generic24 inverse and all64 Cartan derivative coefficients', flush=True)

    # Import only the public API after rebuilding its source data independently.
    spec = importlib.util.spec_from_file_location('lorentz_contact_api_under_audit', HERE/'source_lorentz_contact.py')
    api = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = api
    spec.loader.exec_module(api)
    model = api.SourceLorentzContact()
    equal(model.hessian(e), H)
    equal(model.inverse_numerator(e), K)
    for actual, expected in zip(model.geometry_maps(e), (G, torsion, curl)):
        equal(actual, expected)
    B, multiplier, curvature, density = density_data
    assert s.expand(api.gravity_density(e, B, multiplier, curvature)-density) == 0

    active = json.loads((BASE/'active-gauge/receipt.json').read_bytes())
    vertices = json.loads((BASE/'matter-vertices/receipt.json').read_bytes())
    occupied = json.loads((BASE/'occupied-response/receipt.json').read_bytes())
    exchange = json.loads((BASE/'matter-vertices/exchange.json').read_bytes())
    N = s.sqrt(s.Rational(54, 125))
    e0 = s.diag(N, 1, 1, 1)
    equal(s.Matrix(active['actual_background']['coframe']).applyfunc(s.sympify), e0)
    E0, V0, W0, branch = certify_real_currents(e0, gamma)
    matter_report = candidate['whole_matter_current_and_existing_Contact']
    primitive = {(row['group'], tuple(row['coordinate'])): matrix(row['operator'])
                 for row in vertices['primitive_vertices']}
    for a, V in enumerate(V0):
        equal(s.kronecker_product(V, s.eye(63)), primitive['Lorentz', (a//6, a%6)])
        equal(V, matrix(matter_report['background_V_spin4'][a]))
        equal(W0[a], matrix(matter_report['background_W_spin4'][a]))
    source_rank = s.Matrix.hstack(*[s.Matrix(list(real_bilinear(v))) for v in V0]).rank()
    assert source_rank == 8 == matter_report['density_source_real_rank_at_actual_background']
    H0 = original_hessian(e0)
    inverse = H0.inv()
    equal(matrix(matter_report['background_Hessian']), H0)
    equal(matrix(matter_report['background_inverse']), inverse)

    # Complete arbitrary-component independent-dual tests include modes outside
    # the occupied twelve, both orientations, and a characteristic time slice.
    primal = s.MutableSparseMatrix.zeros(252, 1)
    dual = s.MutableSparseMatrix.zeros(1, 252)
    for spin, internal in itertools.product(range(4), (0, 7, 20, 62)):
        primal[63*spin+internal, 0] = spin+1+s.I*(internal % 5-2)
        dual[0, 63*spin+internal] = internal % 7-3+s.I*(2-spin)
    de = s.Matrix([s.Integer((i*7+2) % 9-4) for i in range(64)])
    general = s.Matrix([[2, 1, 0, 0], [1, 2, 1, 0], [0, 0, 1, 1], [0, 0, 0, 1]])
    negative = general.copy()
    negative[0, :] = -negative[0, :]
    null_slice = s.Matrix([[1, 1, 0, 0], [1, -1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    fixtures = []
    for label, coframe in (('source', e0), ('positive_nondiagonal', general),
                            ('negative_nondiagonal', negative), ('null_temporal', null_slice)):
        temporal, density_ports = original_density_ports(coframe, gamma)
        raw = model.raw_matter_ports(coframe)
        equal(raw['E'], temporal)
        for actual, expected in zip(raw['V'], density_ports):
            equal(actual, expected)
        current = s.Matrix([s.expand(s.re((dual*s.kronecker_product(V, s.eye(63))*primal)[0]))
                            for V in density_ports])
        equal(model.matter_current(coframe, primal, dual), current)
        substitution = dict(zip(e, coframe))
        geo = clean(G.xreplace(substitution)*de)
        hessian = original_hessian(coframe)
        solved = model.eliminate(coframe, de, primal, dual)
        equal(hessian*solved['connection']+geo+current, s.zeros(24, 1))
        equal(solved['geometry_source'], geo)
        equal(solved['matter_source'], current)
        actual_terms = [solved[key] for key in ('geometry_action', 'cross_action', 'contact_action')]
        total = geo+current
        assert s.simplify(sum(actual_terms)+(total.T*hessian.inv()*total)[0]/2) == 0
        stationary_value = (solved['connection'].T*hessian*solved['connection'])[0]/2+\
            (solved['connection'].T*total)[0]
        assert s.simplify(stationary_value-sum(actual_terms)) == 0
        if label == 'null_temporal':
            assert coframe.det() == -2 and temporal.det() == 0
            try:
                model.matter_ports(coframe)
            except AssertionError:
                canonical_refused = True
            else:
                canonical_refused = False
            assert canonical_refused
        else:
            _, _, expected, _ = certify_real_currents(coframe, gamma)
            for actual, W in zip(model.matter_ports(coframe)['W'], expected):
                equal(actual, W)
        fixtures.append({'kind': label, 'determinant': str(coframe.det()),
                         'nonzero_geometric_cross_matter_terms': [s.simplify(value) != 0 for value in actual_terms]})
    assert any(all(row['nonzero_geometric_cross_matter_terms']) for row in fixtures)
    print('PASS original all252 current ports and Re/independent-dual branch normalization; exact geometry/cross/matter action in both orientations and on null temporal slice', flush=True)

    # The pre-existing Hessian is consumed only at the actual background.
    old = active['algebraic_Schur_steps'][-1]
    assert old['eliminated_groups'] == ['Lorentz']
    equal(inverse, s.SparseMatrix(24, 24, {(i-121, j-121): s.sympify(v)
        for i, j, v in old['algebraic_block_inverse']}))
    lorentz = next(row for row in exchange['source_contact_terms'] if row['groups'] == ['Lorentz'])
    injection = s.SparseMatrix(24, 97, {(a, exchange['source_field_indices'].index(121+a)): 1 for a in range(24)})
    equal(matrix(lorentz['source_map']), injection)
    lorentz_kernel = clean(injection.T*inverse*injection)
    equal(lorentz_kernel, matrix(lorentz['kernel']))
    ward = next(row for row in exchange['source_contact_terms'] if row['groups'] == ['scalar_Ward'])
    ward_kernel = matrix(ward['kernel'])
    assert ward_kernel.todok()
    for row in exchange['source_contact_terms']:
        if row['groups'] not in (['Lorentz'], ['scalar_Ward']):
            equal(matrix(row['kernel']), s.zeros(97))
    equal(matrix(exchange['total_contact_kernel']), lorentz_kernel+ward_kernel)

    frame = matrix(occupied['occupied_frame'])
    seed = s.Matrix(active['actual_background']['primal_H']).applyfunc(s.sympify)
    occupied_primal = frame*seed
    occupied_dual = s.sqrt(2)*occupied_primal.T
    current0 = s.Matrix([s.expand(s.re((occupied_dual*s.kronecker_product(V, s.eye(63))*occupied_primal)[0])) for V in V0])
    actual_connection = s.Matrix(active['actual_background']['lowered_Lorentz_connection']).applyfunc(s.sympify).reshape(24, 1)
    equal(-inverse*current0, actual_connection)
    equal(matrix(matter_report['actual_background_matter_source']), current0)
    equal(matrix(matter_report['actual_original_connection_regenerated']), actual_connection)
    assert s.simplify(-(current0.T*inverse*current0)[0]/2) == -18*s.sqrt(30)/25
    axial = matrix(exchange['canonical_spin_source_axial_map'])
    assert axial.rank() == 4 and source_rank > axial.rank()
    equal(axial.T*inverse*axial, matrix(exchange['canonical_spin_contact_kernel']))
    equal(axial.T*inverse*axial, 3*N/8*s.diag(1, -1, -1, -1))
    print('PASS actual source connection regenerated and exact old Lorentz Contact subset; nonzero Ward remainder retained separately', flush=True)

    contraction, examples = certify_car_ordering(inverse, branch)
    returned_branches, tensor, returned_contraction = model.canonical_contact_coefficients(e0)
    for actual, expected in zip(returned_branches, branch):
        equal(actual, expected)
    independent_tensor = clean(sum((value*s.kronecker_product(branch[a], branch[b])/2
        for (a, b), value in inverse.todok().items()), s.zeros(64)))
    equal(tensor, independent_tensor)
    equal(returned_contraction, contraction)
    car = candidate['canonical_real_CAR_coefficients']
    equal(matrix(car['normal_ordered_quartic_coefficient_spin8']), independent_tensor)
    equal(matrix(car['ordered_CAR_product_contraction_spin8']), contraction)
    branch_counts = defaultdict(int)
    for row, column in independent_tensor.todok():
        i, k = divmod(row, 8)
        j, ell = divmod(column, 8)
        assert i//4 == j//4 and k//4 == ell//4
        branch_counts[str(i//4)+str(k//4)] += 1
    assert dict(branch_counts) == car['all_real_branch_coefficient_counts']
    assert set(branch_counts) == {'00', '01', '10', '11'}
    assert not car['quantum_ordering_prescription_selected']
    assert not car['continuum_coincident_product_or_physical_vacuum_constructed']
    print('PASS complete two-branch quartic coefficient and actual CAR states: normal product versus generated one-body contraction', flush=True)

    paths = [HERE/name for name in ('source_lorentz_contact.py', 'source_lorentz_contact.json',
                                   'independent_source_lorentz_contact.py', 'independent_spectral_splice.py')]
    paths += [BASE/name for name in ('active-gauge/receipt.json', 'matter-vertices/receipt.json',
                                    'matter-vertices/exchange.json', 'occupied-response/receipt.json')]
    output = {
        'root': ROOT_ID,
        'verdict': 'CERTIFIED_UNTRUNCATED_SOURCE_LORENTZ_ELIMINATION_AND_FULL_REAL_MATTER_CONTACT_COEFFICIENTS',
        'source_sha256': candidate['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'candidate_source_and_input_bindings_verified': checked_bindings,
        'scope': candidate['scope'],
        'independent_algorithm': 'Levi-Civita BF contraction and raw matrix commutators; direct original density derivatives; arbitrary independent-real-dual canonical map; sparse exterior CAR action',
        'untruncated_elimination': {
            'auxiliary_Euler_coordinates': 72, 'coframe_response_coordinates': 16,
            'Lorentz_coordinates': 24, 'generic_coframe_variables': 16, 'generic_coframe_derivatives': 64,
            'flat_rank': 24, 'flat_determinant': '256',
            'nonlinear_determinant': '256 det(e)^12',
            'signed_gravity_potential': '-3 det(e)', 'matter_volume': 'abs(det(e))',
            'all_coframe_covariance_and_inverse': True, 'whole_Cartan_torsion_identity': True,
            'connection': '-H(e)^-1 (G(e) de+j_matter)',
            'reduced_action': '-1/2 (G(e)de+j_matter)^T H(e)^-1 (G(e)de+j_matter)',
            'boundary_flux_required_or_compact_variations': True,
            'generic_algebraic_domain': 'all real det(e)!=0, including characteristic temporal slices',
            'canonical_domain': 'additionally the original E temporal principal is invertible',
        },
        'full_source_current': {'complex_matter_dimension': 252, 'real_CAR_dimension': 504,
            'ports': 24, 'real_rank': 8, 'prepared_axial_subreadout_rank': 4,
            'both_branches_from_original_Re_with_independent_dual': True,
            'generated_branch_matrices': 'diag(W_a,-conjugate(W_a)) tensor I63',
            'new_adjoint_or_external_Z': False},
        'actual_nonlinear_elimination_examples': fixtures,
        'actual_background_source_connection_regenerated': True,
        'existing_Contact_scope': {'Lorentz_kernel_nonzero_entries': len(lorentz_kernel.todok()),
            'scalar_Ward_remainder_nonzero_entries': len(ward_kernel.todok()),
            'Lorentz_plus_Ward_equals_whole': True, 'Lorentz_equals_whole': False,
            'other_auxiliary_source_kernels_zero': True},
        'CAR_ordering': {'all_branch_counts': dict(branch_counts),
            'one_body_contraction': '-9*sqrt(30)/100 I504', 'actual_exterior_state_checks': examples,
            'normal_product_retained': True, 'continuum_ordering_prescription_selected': False},
        'actual_producer_API': candidate['public_producer'],
        'remaining_bosonic_Legendre_responsibility': candidate['remaining_bosonic_Legendre_responsibility'],
        'Taylor_or_occupied12_used_as_nonlinear_producer': False,
        'complete_interacting_four_block_spectrum_claimed': False,
        'elapsed_seconds': round(time.monotonic()-started, 3),
    }
    (HERE/'independent_source_lorentz_contact.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS independent original Lorentz/Contact certification', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
