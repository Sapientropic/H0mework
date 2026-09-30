#!/usr/bin/env python3
"""Native-basis and direct orbit-chart audit of the source measure bridge.

Neither candidate constructor nor its projections are imported. A nullspace
basis generates the orthogonal section; the full orbit/slice linear system
generates its coordinate inverse. The finite chart differential is rebuilt
from the original seven-dimensional group and its Maurer form.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time

import sympy as s

from independent_source_gauss_section_measure import RawSectionMeasure
from independent_source_quantum_gauss_section import finite_wedge
from independent_source_gauge_legendre import HERE, ROOT, ROOT_ID, bindings, decode, encode
from independent_source_coframe_live_ordering import rational, eq


def zero(value):
    assert s.cancel(value) == 0, value


def pair(A, B):
    return s.re(-s.trace(A[:3, :3]*B[:3, :3])
                -s.trace(A[3:5, 3:5]*B[3:5, 3:5])-A[5, 5]*B[5, 5])


def solved(A, B):
    result, parameters = A.gauss_jordan_solve(B)
    assert parameters.rows == 0
    result = rational(result)
    eq(A*result, B)
    return result


def algebraic_determinant(A):
    matrix = A.to_DM(extension=True)
    return s.factor(matrix.domain.to_sympy(matrix.det()))


def section_linear(model, candidate):
    native = model.native
    G = s.Matrix(12, 12, lambda i, j: pair(native.fund[i], native.fund[j]))
    eq(G, native.Gram)
    metric = s.diag(G, G, G)
    source = model.section.source[67:, :]
    generators = [s.diag(ad, ad, ad) for ad in native.ads]
    V = rational(s.Matrix.hstack(*(L*source for L in generators)))
    fixed = tuple(j-67 for j in model.section.fixed)
    free = tuple(j for j in range(36) if j not in fixed)
    E = s.eye(36)[:, list(free)]
    rows = s.eye(36)[list(fixed), :]
    F = V.row_join(E)
    inverse = solved(F, s.eye(36))
    eq(inverse*F, s.eye(36))
    reader = inverse[3:, :]
    coordinate = E*reader
    N = s.Matrix.hstack(*(V.T*metric).nullspace())
    assert N.shape == (36, 33)
    Q = rational(N*solved(reader*N, s.eye(33)))
    orthogonal = rational(Q*reader)
    eq(V.T*metric*Q, s.zeros(3, 33))
    eq(reader*Q, s.eye(33))
    eq(orthogonal.T*metric, metric*orthogonal)
    eq(orthogonal*orthogonal, orthogonal)
    eq(coordinate*coordinate, coordinate)
    eq(coordinate*orthogonal, coordinate)
    eq(orthogonal*coordinate, orthogonal)
    eq(rows*coordinate, s.zeros(3, 36))
    eq(coordinate*V, s.zeros(36, 3))
    saved = candidate['actual_section_equivalence']
    for key, value in [('coordinate_embedding', E), ('orthogonal_embedding', Q),
                       ('coordinate_reader', reader), ('Porth', orthogonal),
                       ('Pcoord', coordinate), ('source_forward', F), ('source_inverse', inverse)]:
        eq(value, decode(saved[key]))
    source_saved = candidate['source_orbit']
    eq(V, decode(source_saved['V'])); eq(metric, decode(source_saved['native_gram']))
    eq(rows*V, decode(source_saved['source_minor']))

    # Read the original native coordinates directly from the actual7x7 basis.
    def lean_coordinates(A):
        return s.Matrix([s.re(A[0, 1]), s.im(A[0, 1]), s.re(A[0, 2]), s.im(A[0, 2]),
            s.re(A[1, 2]), s.im(A[1, 2]), s.im(A[0, 0]), -s.im(A[2, 2]),
            s.re(A[3, 4]), s.im(A[3, 4]), s.im(A[3, 3]), s.im(A[5, 5])])
    native_coordinates = s.Matrix.hstack(*(lean_coordinates(B) for B in native.fund))
    eq(native_coordinates, decode(source_saved['native_from_raw']))
    assert native_coordinates.det() == 1
    K = model.K
    spinpair = [K[1]/2, K[0]/2, -K[2]/2]
    orbit_coefficients = solved(s.Matrix.hstack(*(B.reshape(49, 1) for B in K)),
        s.Matrix.hstack(*(B.reshape(49, 1) for B in spinpair)))
    eq(orbit_coefficients, decode(source_saved['python_from_spinpair']))
    minor = s.eye(36)[[18, 6, 0], :]*V*orbit_coefficients
    eq(minor, decode(source_saved['lean_source_minor']))
    g = 3*s.sqrt(2)/5
    eq(minor, s.diag(-g/2, g/2, -g/2)); zero(minor.det()-g**3/8)

    scalar_det = s.factor((native.R.T*native.R).det())
    gauge_det = s.factor(G.det())
    coordinate_det = s.factor((E.T*metric*E).det())
    orthogonal_det = s.factor((Q.T*metric*Q).det())
    section_jacobian = s.sqrt(orthogonal_det/coordinate_det)
    product = s.sqrt(scalar_det*gauge_det**3)
    haar = s.sqrt((native.S.T*G*native.S).det())
    assert scalar_det == s.Rational(1, 256) and gauge_det == 1536
    zero(product-1536*s.sqrt(6)); zero(haar-2*s.sqrt(2))
    zero(section_jacobian-3*s.sqrt(2)/16)
    measure = candidate['native_measure']
    for key, value in [('scalar_coordinate_Gram_det', scalar_det), ('gauge_coordinate_Gram_det', gauge_det),
        ('coordinate33_Gram_det', coordinate_det), ('orthogonal33_Gram_det', orthogonal_det),
        ('source_section_Jacobian_native33_to_native33', section_jacobian),
        ('native103_over_coordinate103', product), ('native_Haar_over_coordinate_Haar', haar)]:
        zero(value-s.sympify(measure[key]))
    a = s.Matrix(s.symbols('a0:36', real=True))
    section = E*E.T*a
    variable_minor = rows*s.Matrix.hstack(*(L*section for L in generators))
    density = -s.factor(variable_minor.det())
    zero(density-8*a[1]**2*a[12])
    zero(density-s.sympify(measure['coordinate_rho3'], locals={str(v): v for v in a}))
    native_density = product*density/haar
    zero(native_density-s.sympify(measure['native103_over_native_Haar_slice_density'], locals={str(v): v for v in a}))
    zero(product/haar-768*s.sqrt(3))
    return {'original_Gram12': encode(G), 'scalar_Gram_determinant': str(scalar_det),
        'gauge_Gram_determinant': str(gauge_det), 'native103_volume_factor': str(product),
        'native_Haar_factor': str(haar), 'source_section_Jacobian': str(section_jacobian),
        'native_slice_density_factor': str(product/haar),
        'orthogonal_section_regenerated_from_native_annihilator_kernel': True,
        'coordinate_inverse_regenerated_by_full36_orbit_section_system': True,
        'Lean_original_cartan_basis_and_actual_source_minor_checked': True,
        'variable_rho3_recomputed_on_coordinate_section': str(density)}, product, haar


def nonlinear_consumer(model, candidate, product, haar):
    native = model.native
    metric = s.diag(s.eye(6), native.R.T*native.R, native.Gram, native.Gram, native.Gram)
    for L in model.section.T:
        eq(L.T*metric+metric*L, s.zeros(103)); zero(s.trace(L))
    actual = candidate['original_nonlinear_chart_consumer']
    u = s.Matrix(list(map(s.sympify, actual['unit_quaternion'])))
    assert u[0] > 0 and u[1] != 0
    zero((u.T*u)[0]-1)
    g = model.quaternion(u)
    eq(g.H*g, s.eye(7)); zero(g.det()-1)
    boson = model.group_boson(u)
    eq(boson.T*metric*boson, metric); zero(algebraic_determinant(boson)-1)
    point = decode(actual['displaced_slice_point'])
    eq(model.section.reader*(point-model.section.source), s.zeros(3, 1))
    assert point != model.section.source and point[68] > 0 and point[79] > 0
    V = rational(s.Matrix.hstack(*(L*point for L in model.section.T)))
    M = model.section.reader*V
    rho = -s.factor(M.det()); zero(rho-8*point[68]**2*point[79])

    # A real local group chart: u(r,t1,t2)=(cos r,sin r sqrt(1-|t|²),sin r t1,sin r t2).
    # Differentiate that map at t=0, then read g^-1 dg in the actual K basis.
    c, t = u[0], u[1]
    du = s.Matrix([[-t, 0, 0], [c, 0, 0], [0, t, 0], [0, 0, t]])
    derivatives = [du[0, j]*model.P+sum((du[h+1, j]*model.K[h] for h in range(3)), s.zeros(7))
                   for j in range(3)]
    maurer = s.Matrix(3, 3, lambda h, j: pair(model.K[h], g.H*derivatives[j]))
    theta = solved(model.stabilizer_Gram, maurer)
    eq(theta.T*model.stabilizer_Gram*theta, 2*du.T*du)
    zero(theta.det()-t*t)
    actual_chart = boson*(V*theta).row_join(model.section.free_reader.T)
    determinant = algebraic_determinant(actual_chart)
    zero(determinant-s.sympify(actual['source_scaled_Jacobian']))
    pullback = s.simplify(product*abs(determinant))
    haar_element = s.sqrt((theta.T*model.stabilizer_Gram*theta).det())
    zero(haar_element-haar*t*t)
    disintegration = s.simplify(haar_element*(product/haar)*rho)
    zero(pullback-disintegration)
    zero(pullback-s.sympify(actual['native_pullback_volume']))
    zero(disintegration-s.sympify(actual['native_Haar_times_slice_volume']))

    # Exterior unitary transport is the same full504 action, not a selected
    # scalar component. Finite CAR exterior powers preserve each occupation.
    matter = model.group_CAR(u)
    assert matter.shape == (504, 504)
    eq(matter.H*matter, s.eye(504))
    word = (144, 396)
    image = finite_wedge(matter, word)
    zero(sum(s.conjugate(v)*v for v in image.values())-1)
    assert all(len(out) == len(word) for out in image)
    eq(boson[:6, :], s.eye(103)[:6, :])
    return {'all_original_generators_preserve_native103_metric': True,
        'actual_nonidentity_group_and_displaced_slice_used': True,
        'actual_group_chart_differential_regenerated_from_7x7_Maurer_form': True,
        'native_Haar_chart_density': str(haar_element), 'actual_native_volume': str(pullback),
        'native_disintegration_identity_checked': True,
        'original_full504_group_unitary': True, 'actual_N2_norm_preserved': True,
        'original_number_weight_unchanged': True,
        'local_norm_consumer': 'Original equivariant sections use the original finite unitary CAR action; number is preserved and coframe unchanged. Native103 volume disintegrates against native Haar as 768*sqrt(3)*rho3 dz100. Hence each original number weight v^(N+2) uses exactly that density on the same local orbit chart.',
        'half_density': 'sqrt(768*sqrt(3)*rho3*v^(N+2)); its constant cancels in U H U^-1.'}


def main():
    started = time.monotonic()
    path = HERE/'source_gauge_slice_coordinates.json'
    candidate = json.loads(path.read_text())
    count = bindings(candidate); assert candidate['root'] == ROOT_ID
    paid = ('independent_source_gauss_section_measure', 'independent_source_quantum_gauss_section',
            'independent_source_quantum_stabilizer')
    for name in paid:
        record = json.loads((HERE/(name+'.json')).read_text())
        count += bindings(record); assert record['root'] == ROOT_ID
    model = RawSectionMeasure(); assert model.native.hashes == candidate['source_sha256']
    linear, product, haar = section_linear(model, candidate)
    print('PASS independent source36 section inverse, native Gram volumes and varying rho3', flush=True)
    nonlinear = nonlinear_consumer(model, candidate, product, haar)
    print('PASS original nonlinear local chart, native Haar disintegration and full504 Fock norm transport', flush=True)
    files = [Path(__file__), path, HERE/'source_gauge_slice_coordinates.py']+[HERE/name for name in (
        'SourceQuantumGaugeSliceCoordinates.lean', 'SourceQuantumResidualGaugeSlice.lean',
        'SourceQuantumNativeDimensions.lean', 'SourceQuantumScalarOrbitDimensions.lean',
        'SourceQuantumConfigurationHilbert.lean', 'SourceQuantumHalfDensityHilbert.lean',
        'independent_source_gauss_section_measure.py', 'independent_source_quantum_gauss_section.py',
        'independent_source_quantum_stabilizer.py')]+[HERE/(name+'.json') for name in paid]
    result = {'verdict': 'CERTIFIED_SOURCE_NATIVE_COORDINATE_SECTIONS_AND_LOCAL_HILBERT_MEASURE_BRIDGE',
        'root': ROOT_ID, 'source_sha256': candidate['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'checked_input_bindings': count, 'candidate_constructor_imported': False,
        'source_linear_sections': linear, 'original_local_nonlinear_measure_consumer': nonlinear,
        'scope': 'Actual source linear section equivalence and native volume conversion on the already generated local nonlinear orbit chart; no global quotient or closed time-reduced Hamiltonian is asserted.',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'independent_source_gauge_slice_coordinates.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent native gauge-slice measure bridge', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
