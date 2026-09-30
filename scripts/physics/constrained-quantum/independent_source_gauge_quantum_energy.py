#!/usr/bin/env python3
"""Raw native-matrix/BF audit of the homogeneous gauge quantum energy.

Curvature is rebuilt by multiplying original7x7 Lie matrices. The original
Hodge density's full36 velocity Hessian supplies the quantum kinetic weight,
and symbolic coordinate polynomials independently exercise its ordered action.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_gauge_legendre import (
    HERE, BASE, ROOT, ROOT_ID, SIGMA, W, source, bindings, clean, decode,
    matrix_coordinates, hodge)
from independent_source_joint_temporal_rates import encode, eq, zero, dot


MAGNETIC_PAIRS = ((1, 2), (2, 0), (0, 1))


def main():
    began = time.monotonic(); path = HERE/'source_gauge_quantum_energy.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    _, _, _, hashes = source.parse_source(ROOT)
    assert candidate['root'] == ROOT_ID and candidate['source_sha256'] == hashes
    fundamental = [s.SparseMatrix(M)*(s.I if imaginary else 1) for _, imaginary, M in source.generators([(0, 1, 2), (3, 4)])]
    Gram = s.Matrix(12, 12, lambda a, b: s.re(-s.trace(fundamental[a][:3, :3]*fundamental[b][:3, :3])-
        s.trace(fundamental[a][3:5, 3:5]*fundamental[b][3:5, 3:5])-fundamental[a][5, 5]*fundamental[b][5, 5]))
    eq(Gram, decode(candidate['native_pairing'])); assert Gram[11, 11] == 1
    coordinate = s.Matrix(s.symbols('native_spatial_connection0:36', real=True))
    field = coordinate.reshape(3, 12)
    connection = [sum((field[i, a]*fundamental[a] for a in range(12)), s.zeros(7)) for i in range(3)]
    B = clean(s.Matrix.vstack(*(matrix_coordinates(connection[i]*connection[j]-connection[j]*connection[i]).T for i, j in MAGNETIC_PAIRS)))
    dB = B.reshape(36, 1).jacobian(list(coordinate))
    for i in range(3):
        for j in range(3): zero(sum(dB[12*j+a, 12*i+a] for a in range(12)))
    # All possible coframe-dependent electric and mixed coefficients are
    # covered by independent symbolic3x3 matrices, using the actual Gram.
    arbitrary_inverse = s.Matrix(3, 3, s.symbols('electric_inverse0:9'))
    arbitrary_mixed = s.Matrix(3, 3, s.symbols('electric_mixed0:9'))
    arbitrary_shift = (arbitrary_mixed*B*Gram).reshape(36, 1)
    arbitrary_W = s.kronecker_product(arbitrary_inverse, Gram.inv())
    zero(s.trace(arbitrary_W*arbitrary_shift.jacobian(list(coordinate))))
    print('PASS original native7x7 curvature/Gram and allnine divergence cancellations for arbitrary coframe coefficients', flush=True)

    active = json.loads((BASE/'active-gauge/receipt.json').read_text()); count += bindings(active)
    source_e = s.Matrix(active['actual_background']['coframe']).applyfunc(s.sympify)
    source_A = s.Matrix(active['actual_background']['gauge_connection']).applyfunc(s.sympify)[1:, :]
    e, A = decode(candidate['actual_coframe']), decode(candidate['actual_spatial_connection'])
    expected_e = source_e.copy(); expected_e[1, 0] = source_e[0, 0]/5
    expected_A = source_A.copy(); expected_A[0, 2] += s.Rational(1, 17); expected_A[1, 7] += s.Rational(1, 19)
    eq(e, expected_e); eq(A, expected_A)
    constitutive = clean(-W*hodge(e)/SIGMA)
    electric = s.Matrix(s.symbols('original_electric_velocity0:36', real=True))
    curvature = electric.reshape(3, 12).col_join(B)
    original_L = s.expand(dot(curvature, constitutive*curvature*Gram)/2)
    momenta = s.Matrix([s.diff(original_L, velocity) for velocity in electric])
    velocity_Hessian = momenta.jacobian(list(electric))
    actual_W, free = velocity_Hessian.gauss_jordan_solve(s.eye(36)); assert free.rows == 0
    C = clean(momenta.subs(dict.fromkeys(electric, 0)))
    magnetic_potential = -original_L.subs(dict.fromkeys(electric, 0))
    eq(actual_W, s.kronecker_product(constitutive[:3, :3].inv(), Gram.inv()))
    eq(C, (constitutive[:3, 3:]*B*Gram).reshape(36, 1))
    dC = C.jacobian(list(coordinate))
    zero(s.trace(actual_W*dC))
    point = dict(zip(coordinate, A.reshape(36, 1)))
    C0 = clean(C.subs(point)); dC0 = clean(dC.subs(point))
    V0 = s.expand(magnetic_potential.subs(point))
    eq(C0, decode(candidate['actual_shift']))
    assert C0.todok()
    commutator = clean(s.I*(dC0.T-dC0))
    eq(commutator, decode(candidate['actual_nonzero_momentum_commutator']))
    assert len(commutator.todok()) == 72

    # Direct polynomial differentiation of the actual local wavepacket jet.
    z = s.Matrix(s.symbols('centered_gauge0:36', real=True))
    ell = s.Matrix([s.Rational(j+1, 41) for j in range(36)])
    radial = s.Matrix([s.Rational((j % 7)-3, 43) for j in range(36)])
    wave = 1+s.I*dot(ell, z)+(dot(radial, z)**2-dot(z, z))/2
    centered_C = C.subs(dict(zip(coordinate, A.reshape(36, 1)+z)))
    origin = dict.fromkeys(z, 0)
    def momentum(j, value): return -s.I*s.diff(value, z[j])-centered_C[j]*value
    kinetic = s.S.Zero
    for (i, j), weight in actual_W.todok().items():
        kinetic += weight*momentum(i, momentum(j, wave)).subs(origin)/2
    kinetic = s.expand(kinetic)
    Hessian = radial*radial.T-s.eye(36); gradient = s.I*ell
    expanded = -s.trace(actual_W*Hessian)/2+s.I*(C0.T*actual_W*gradient)[0]+(C0.T*actual_W*C0)[0]/2
    zero(kinetic-expanded)
    omitted_shift = s.expand(kinetic+s.trace(actual_W*Hessian)/2)
    assert omitted_shift != 0
    for name, value in [('kinetic', kinetic), ('magnetic', V0), ('whole', kinetic+V0), ('omit_shift_defect', omitted_shift)]:
        zero(value-s.sympify(candidate['wavepacket'][name]))
    # The full operator commutator, tested before any momentum eigenvalue
    # substitution. Its first-derivative terms cancel for all36x36 entries.
    for i in range(36):
        for j in range(36):
            at_pair = -Hessian[j, i]+s.I*dC0[j, i]+s.I*C0[j]*gradient[i]+s.I*C0[i]*gradient[j]+C0[i]*C0[j]
            reversed_pair = -Hessian[i, j]+s.I*dC0[i, j]+s.I*C0[i]*gradient[j]+s.I*C0[j]*gradient[i]+C0[j]*C0[i]
            zero(at_pair-reversed_pair-commutator[i, j])
    print('PASS full36 original velocity-Hessian kinetic weight, direct polynomial ordered square and all1296 shifted-momentum commutators', flush=True)

    Pi = s.Matrix(3, 12, lambda i, a: s.Rational((i+3*a)%11-5, 31))
    B0 = clean(B.subs(point))
    velocities = clean(actual_W*(Pi.reshape(36, 1)-C0))
    full_F = velocities.reshape(3, 12).col_join(B0)
    original_density = dot(full_F, constitutive*full_F*Gram)/2
    original_H = dot(Pi.reshape(36, 1), velocities)-original_density
    square_H = ((Pi.reshape(36, 1)-C0).T*actual_W*(Pi.reshape(36, 1)-C0))[0]/2+V0
    zero(original_H-square_H)
    source_K = clean(-W*hodge(source_e)/SIGMA); N = source_e[0, 0]
    source_Hessian = s.kronecker_product(source_K[:3, :3], Gram)
    eq(source_Hessian.inv(), SIGMA/N*s.kronecker_product(s.eye(3), Gram.inv()))
    eq(source_K[:3, 3:], s.zeros(3))
    zero(-dot(B, source_K[3:, 3:]*B*Gram)/2-dot(B, B*Gram)/(2*SIGMA*N))
    # Nonzero A0 and its actual spatial flux are reconstructed with raw
    # matrix commutators, not removed from the gauge component prematurely.
    A0 = s.Matrix([s.Rational(a-5, 37) for a in range(12)])
    matrix_A0 = sum((A0[a]*fundamental[a] for a in range(12)), s.zeros(7))
    matrices_A = [sum((A[i, a]*fundamental[a] for a in range(12)), s.zeros(7)) for i in range(3)]
    spatial_A0 = s.Matrix(3, 12, lambda i, a: s.Rational((i+a)%5-2, 47))
    spatial_Pi = [s.Matrix(3, 12, lambda j, a: s.Rational((i+2*j+a)%7-3, 53)) for i in range(3)]
    ad = [s.Matrix.hstack(*(matrix_coordinates(matrix*fundamental[a]-fundamental[a]*matrix) for a in range(12))) for matrix in matrices_A]
    full_velocity = velocities.reshape(3, 12)+spatial_A0+s.Matrix.vstack(*(matrix_coordinates(matrix*matrix_A0-matrix_A0*matrix).T for matrix in matrices_A))
    original_with_A0 = dot(Pi, full_velocity)-original_density
    Gauss = sum((spatial_Pi[i][i, :].T-ad[i].T*Pi[i, :].T for i in range(3)), s.zeros(12, 1))
    divergence = sum(dot(spatial_Pi[i][i, :].T, A0)+dot(Pi[i, :], spatial_A0[i, :]) for i in range(3))
    zero(original_with_A0-original_H+dot(A0, Gauss)-divergence)
    assert dot(A0, Gauss) != 0 and divergence != 0
    print('PASS raw original-L Legendre transform, exact source specialization and nonzero A0/Gauss/spatial-flux identity', flush=True)
    paths = [Path(__file__), path, HERE/'source_gauge_quantum_energy.py',
        HERE/'independent_source_gauge_legendre.py', BASE/'active-gauge/receipt.json',
        HERE/'source_gauge_legendre.json', HERE/'independent_source_gauge_legendre.json']
    result = {'verdict': 'CERTIFIED_ORIGINAL_NATIVE_GAUGE_CCR_ENERGY_AND_ORDERED_SHIFTED_MOMENTA',
        'root': ROOT_ID, 'source_sha256': hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks': count, 'candidate_constructor_imported': False,
        'independent_method': 'native7x7 matrix commutators and direct entry coordinates; raw Hodge BF density differentiated in all36 velocities; symbolic polynomial quantum action',
        'native_Y_pairing': '1', 'all9_generic_divergence_identities': True,
        'ordering_trace_zero_for_arbitrary_electric_inverse_and_mixed_block': True,
        'all36_original_velocity_Hessian_solved': True,
        'actual_shifted_momentum_commutator_nonzero_entries': 72,
        'all1296_shifted_momentum_commutator_entries_verified': True,
        'actual36_coordinate_wavepacket': {'kinetic': str(kinetic), 'magnetic': str(V0),
            'whole': str(s.expand(kinetic+V0)), 'omit_shift_defect': str(omitted_shift)},
        'original_Legendre_and_source_coefficients_match': True,
        'original_nonzero_A0_Gauss_and_spatial_boundary': {'Gauss_sign': '+div Pi-ad(A)^T Pi',
            'A0_Gauss_readout_nonzero': str(dot(A0, Gauss)), 'boundary_divergence_nonzero': str(divergence),
            'time_connection_term_removed_inside_gauge_block': False},
        'domain': 'C_c^infinity(R36 gauge coordinates) tensor spectator algebraic CAR, at a fixed source-admissible coframe; polynomial differential coefficients preserve compact support',
        'coframe_quantization_or_complete_joint_evolution_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_gauge_quantum_energy.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS independent source gauge quantum energy', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
