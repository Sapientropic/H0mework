#!/usr/bin/env python3
"""Same-source coordinate/orthogonal sections and their native volume factors.

The linear section equivalence is at the actual source. The varying density
is independently regenerated from the original residual orbit on the existing
coordinate section; it is not replaced by that linear Jacobian.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_scalar_gauss_reduction import SourceScalarGaussReduction
from source_quantum_gauss_section import exterior
from source_coframe_live_ordering import FREE
from source_gauge_legendre import rational, realify
from source_lorentz_contact import clean, equal, encode


def algebraic_det(matrix):
    domain_matrix = matrix.to_DM(extension=True)
    return domain_matrix.domain.to_sympy(domain_matrix.det())


def main():
    started = time.monotonic()
    source = SourceScalarGaussReduction()
    gauge = source.common.gauge
    S, R = source.stabilizer, source.R
    background = source.common.scalar.exchange.active['actual_background']
    A0 = s.Matrix(background['gauge_connection']).applyfunc(s.sympify)[1:, :]
    gram = s.diag(gauge.gram, gauge.gram, gauge.gram)
    adjoint = [s.diag(*([gauge.ad(S[:, a])]*3)) for a in range(3)]
    b0 = A0.reshape(36, 1)
    V = clean(s.Matrix.hstack(*(L*b0 for L in adjoint)))
    pivots = (0, 6, 18)
    free = tuple(i for i in range(36) if i not in pivots)
    rows = s.eye(36)[list(pivots), :]
    E = s.eye(36)[:, list(free)]
    M = clean(rows*V)
    assert M.det() != 0
    native_orbit_gram = clean(V.T*gram*V)
    Porth = rational(s.eye(36)-V*native_orbit_gram.inv()*V.T*gram)
    Pcoord = rational(s.eye(36)-V*M.inv()*rows)
    Q = rational(Porth*E)
    coordinate_reader = rational(E.T*Pcoord)
    for P in (Porth, Pcoord):
        equal(P*P, P)
        equal(P*V, s.zeros(36, 3))
    equal(Porth.T*gram, gram*Porth)
    equal(rows*Pcoord, s.zeros(3, 36))
    equal(V.T*gram*Q, s.zeros(3, 33))
    equal(Porth*Pcoord, Porth)
    equal(Pcoord*Porth, Pcoord)
    equal(coordinate_reader*Q, s.eye(33))
    equal(Q*coordinate_reader, Porth)
    equal(Pcoord*Q, E)
    forward = V.row_join(E)
    inverse = (M.inv()*rows).col_join(coordinate_reader)
    equal(forward*inverse, s.eye(36))
    equal(inverse*forward, s.eye(36))

    # The Lean readback uses c6=D01,c7=D12 while the raw source uses D02,D12.
    # These two Cartan coordinate matrices represent exactly the same element.
    c = s.Matrix(s.symbols('c0:12', real=True))
    raw_matrix = sum((c[a]*gauge.fundamental[a] for a in range(12)), s.zeros(7))
    native_coordinates = s.Matrix([s.re(raw_matrix[0, 1]), s.im(raw_matrix[0, 1]),
        s.re(raw_matrix[0, 2]), s.im(raw_matrix[0, 2]), s.re(raw_matrix[1, 2]),
        s.im(raw_matrix[1, 2]), s.im(raw_matrix[0, 0]), -s.im(raw_matrix[2, 2]),
        s.re(raw_matrix[3, 4]), s.im(raw_matrix[3, 4]), s.im(raw_matrix[3, 3]),
        s.im(raw_matrix[5, 5])])
    native_from_raw = native_coordinates.jacobian(c)
    expected = s.eye(12); expected[7, 6] = 1
    equal(native_from_raw, expected)
    assert native_from_raw.det() == 1
    # Python S=(A01,S01,-D01); the original SpinPair G=(S01,A01,D01)/2.
    python_from_spinpair = s.Matrix([[0, s.Rational(1, 2), 0],
        [s.Rational(1, 2), 0, 0], [0, 0, -s.Rational(1, 2)]])
    g = s.sympify(background['gauge_connection'][1][1])*2
    lean_rows = s.eye(36)[[18, 6, 0], :]
    lean_minor = clean(lean_rows*V*python_from_spinpair)
    equal(lean_minor, s.diag(-g/2, g/2, -g/2))
    assert s.simplify(lean_minor.det()-g**3/8) == 0

    scalar_gram_det = s.factor((R.T*R).det())
    gauge_gram_det = s.factor(gauge.gram.det())
    coordinate_slice_gram_det = s.factor((E.T*gram*E).det())
    orthogonal_slice_gram_det = s.factor((Q.T*gram*Q).det())
    section_jacobian = s.sqrt(orthogonal_slice_gram_det/coordinate_slice_gram_det)
    native103_factor = s.sqrt(scalar_gram_det*gauge_gram_det**3)
    native_Haar_factor = s.sqrt((S.T*gauge.gram*S).det())
    assert scalar_gram_det == s.Rational(1, 256)
    assert gauge_gram_det == 1536
    assert native103_factor == 1536*s.sqrt(6)
    assert native_Haar_factor == 2*s.sqrt(2)
    equal(s.Matrix([[forward.det()**2*gram.det()]]),
        s.Matrix([[native_orbit_gram.det()*orthogonal_slice_gram_det]]))

    a = s.Matrix(s.symbols('a0:36', real=True))
    section = E*E.T*a
    variable_orbit = s.Matrix.hstack(*(L*section for L in adjoint))
    variable_minor = rows*variable_orbit
    density = -s.factor(variable_minor.det())
    assert s.expand(density-8*a[1]**2*a[12]) == 0
    native_density = s.simplify(native103_factor/native_Haar_factor)*density
    assert s.simplify(native_density/density) == 768*s.sqrt(3)
    print('PASS source36 linear sections and native Gram volume factors', flush=True)

    # The original finite group preserves the native product volume, so the
    # conversion also holds on its nonlinear local orbit chart, not only at
    # the source tangent map. Use a nonidentity group element and a displaced
    # slice point; scalar/current equivariance comes from the same group.
    product_gram = s.diag(s.eye(6), R.T*R, gram)
    cosine, sine = s.Rational(9999, 10001), s.Rational(200, 10001)
    K = clean(sum((S[j, 0]*gauge.fundamental[j] for j in range(12)), s.zeros(7)))
    active_projector = clean(-K*K)
    equal(active_projector*active_projector, active_projector)
    group = s.eye(7)+(cosine-1)*active_projector+sine*K
    equal(group.H*group, s.eye(7))
    scalar_group = clean(source.dual_R.T*realify(exterior(group, 4))*R)
    gauge_group = clean(gauge.gram_inverse*s.Matrix(12, 12, lambda i, j:
        gauge.native_pair(gauge.fundamental[i], group*gauge.fundamental[j]*group.H)))
    boson_group = s.diag(s.eye(6), scalar_group, *([gauge_group]*3))
    equal(clean(boson_group.T*product_gram*boson_group), product_gram)
    assert algebraic_det(boson_group) == 1
    print('PASS original nonidentity group preserves the native103 product metric', flush=True)
    e0 = s.Matrix(background['coframe']).applyfunc(s.sympify)
    point = s.Matrix([e0[j] for j in FREE]).col_join(s.zeros(61, 1)).col_join(b0)
    point[6] += s.Rational(1, 1000)
    point[68] += s.Rational(1, 1000)
    point[79] += s.Rational(1, 2000)
    L = [s.diag(s.zeros(6), clean(source.dual_R.T*sum(
        (S[j, k]*gauge.rho70[j] for j in range(12)), s.zeros(70))*R), adjoint[k])
        for k in range(3)]
    for generator in L:
        equal(clean(generator.T*product_gram+product_gram*generator), s.zeros(103))
    whole_pivots = tuple(67+j for j in pivots)
    whole_free = tuple(j for j in range(103) if j not in whole_pivots)
    If, Ip = s.eye(103)[:, list(whole_free)], s.eye(103)[:, list(whole_pivots)]
    varying_V = clean(s.Matrix.hstack(*(generator*point for generator in L)))
    varying_M = clean(Ip.T*varying_V)
    actual_rho = 8*point[68]**2*point[79]
    assert s.simplify(-varying_M.det()-actual_rho) == 0
    Jscaled = s.Matrix([[1, 0, 0], [0, cosine*sine, -sine*sine],
                       [0, sine*sine, cosine*sine]])
    actual_forward = boson_group*(varying_V*Jscaled).row_join(If)
    orientation = (-1)**sum(row-j for j, row in enumerate(whole_pivots))
    actual_det = s.factor(algebraic_det(actual_forward))
    assert s.simplify(actual_det-orientation*varying_M.det()*sine*sine) == 0
    pullback_volume = s.simplify(native103_factor*abs(actual_det))
    native_disintegrated = s.simplify(native_Haar_factor*sine*sine *
        native103_factor/native_Haar_factor*actual_rho)
    assert s.simplify(pullback_volume-native_disintegrated) == 0

    paths = [HERE/name for name in ('source_gauge_slice_coordinates.py',
        'SourceQuantumGaugeSliceCoordinates.lean', 'SourceQuantumResidualGaugeSlice.lean',
        'SourceQuantumNativeDimensions.lean', 'SourceQuantumScalarOrbitDimensions.lean',
        'SourceQuantumConfigurationHilbert.lean', 'source_scalar_gauss_reduction.py',
        'source_gauge_legendre.py', 'source_gauss_section_measure.py',
        'source_gauss_section_measure.json', 'independent_source_gauss_section_measure.json',
        'source_quantum_gauss_section.py')]
    result = {'root': ROOT_ID, 'source_sha256': source.common.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_orbit': {'gauge_pivots': list(pivots), 'V': encode(V),
            'native_gram': encode(gram), 'source_minor': encode(M),
            'lean_source_minor': encode(lean_minor), 'native_from_raw': encode(native_from_raw),
            'python_from_spinpair': encode(python_from_spinpair)},
        'actual_section_equivalence': {'coordinate_embedding': encode(E),
            'orthogonal_embedding': encode(Q), 'coordinate_reader': encode(coordinate_reader),
            'Porth': encode(Porth), 'Pcoord': encode(Pcoord),
            'both_inverse_and_same_orbit_checked': True,
            'source_forward': encode(forward), 'source_inverse': encode(inverse)},
        'native_measure': {'scalar_coordinate_Gram_det': str(scalar_gram_det),
            'gauge_coordinate_Gram_det': str(gauge_gram_det),
            'coordinate33_Gram_det': str(coordinate_slice_gram_det),
            'orthogonal33_Gram_det': str(orthogonal_slice_gram_det),
            'source_section_Jacobian_native33_to_native33': str(section_jacobian),
            'native103_over_coordinate103': str(native103_factor),
            'native_Haar_over_coordinate_Haar': str(native_Haar_factor),
            'coordinate_rho3': str(density),
            'native103_over_native_Haar_slice_density': str(native_density),
            'connected_source_patch': 'Original regular D9 chart, positive coframe diagonal, a1>0 and a12>0; rho3 is abs(det M) on this patch.',
            'number_weight': 'v^(N+2) is unchanged by either residual gauge section.',
            'normalization': 'All constants are original Gram determinants; no additional field Z or Haar probability normalization.'},
        'original_nonlinear_chart_consumer': {
            'unit_quaternion': list(map(str, (cosine, sine, 0, 0))),
            'displaced_slice_point': encode(point),
            'native_product_metric_preserved': True,
            'finite_group_determinant': '1',
            'source_scaled_Jacobian': str(actual_det),
            'native_pullback_volume': str(pullback_volume),
            'native_Haar_times_slice_volume': str(native_disintegrated),
            'norm_identity': 'The original local equivariant full504 Fock section has norm mu_native_Haar(U) times Integral 768*sqrt(3)*rho3(z)*v(z)^(N+2)*||f(z)||^2 dz100. The actual group chart and orbit volume remain explicit.',
            'half_density_to_dz': 'sqrt(768*sqrt(3)*rho3(z)*v(z)^(N+2)); the constant cancels in the already generated U H U^-1.',
        },
        'scope': 'Source tangent section equivalence and actual coordinate basis volume conversion. The varying rho3 is recomputed on the original coordinate section; no new nonlinear quotient, Hamiltonian domain closure or spectral claim.',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_gauge_slice_coordinates.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source native/coordinate gauge section inverse, original metric volume and rho3 conversion',
          result['elapsed_seconds'], 'seconds', flush=True)
    print(json.dumps(result['native_measure'], indent=2))


if __name__ == '__main__':
    main()
