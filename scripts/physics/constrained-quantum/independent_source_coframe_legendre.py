#!/usr/bin/env python3
"""Independent coframe Legendre audit of the untruncated Lorentz-reduced action.

The temporal Hessian is reconstructed from the original BF integration by
parts. Metric coordinates identify its actual quotient; no old Jacobi matrix
or pseudoinverse enters the construction.
"""
from __future__ import annotations

from functools import lru_cache
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys
import time

import sympy as s

from independent_source_lorentz_contact import (
    ROOT_ID, HERE, BASE, ROOT, PAIRS, SIGNS, J, WEDGE, GENERATORS,
    clean, equal, matrix, exterior, original_hessian, geometric_load,
    original_gamma, original_density_ports,
)

ETA = s.diag(*SIGNS)
METRIC_COORDINATES = ((0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (1, 2))


def metric_coordinates(h):
    return s.Matrix([h[i, j] for i, j in METRIC_COORDINATES])


def metric_matrix(coordinates):
    result = s.MutableSparseMatrix.zeros(3, 3)
    for value, (i, j) in zip(coordinates, METRIC_COORDINATES):
        result[i, j] = result[j, i] = value
    return result


def metric_covector(coordinates):
    result = s.MutableSparseMatrix.zeros(3, 3)
    for value, (i, j) in zip(coordinates, METRIC_COORDINATES):
        result[i, j] = result[j, i] = value if i == j else value/2
    return result


@lru_cache(None)
def original_geometry():
    e = s.Matrix(4, 4, s.symbols('audit_e0:16', real=True))
    determinant = s.expand(e.det(method='domain-ge'))
    H = original_hessian(e)
    T = s.kronecker_product(e, s.eye(6))
    K = clean(T.T*original_hessian(s.eye(4)).inv()*T)
    G = geometric_load(e)
    E = e[:, 1:]
    h = clean(E.T*ETA*E)
    Dh = metric_coordinates(h).jacobian(list(e))
    six = s.Matrix(s.symbols('audit_h0:6', real=True))
    independent_h = metric_matrix(six)
    metric_hessian = s.hessian(independent_h.det(), six)
    B_numerator = clean(metric_hessian.xreplace(dict(zip(six, metric_coordinates(h)))))
    equal(-4*G[:, :16].T*K*G[:, :16], Dh.T*B_numerator*Dh)
    assert s.expand(metric_hessian.det()+16*independent_h.det()**2) == 0
    # The original temporal BF momentum is f(e), before moving the derivative
    # to the coframe. This fixes the exact boundary generating functional.
    C = J*exterior(e)*WEDGE
    f = s.Matrix([0 if mu == 0 else C[a, PAIRS.index((0, mu))]
                  for mu in range(4) for a in range(6)])
    equal(G[:, :16], -f.jacobian(list(e)))
    assert not any(value.has(*e[:, 0]) for value in f)
    return e, determinant, H, K, G, h, Dh, B_numerator, f


def quotient_right_inverse(e):
    columns = []
    # E^T eta [eta (e^-1[1:,:])^T]=I3, including a null spatial plane.
    source_lift = ETA*e.inv()[1:, :].T
    equal(e[:, 1:].T*ETA*source_lift, s.eye(3))
    for column in range(6):
        basis = s.eye(6)[:, column]
        variation = s.zeros(4)
        variation[:, 1:] = source_lift*metric_matrix(basis)/2
        columns.append(s.Matrix(list(variation)))
    return clean(s.Matrix.hstack(*columns))


def source_null_frame(e):
    columns = []
    for a in range(4):
        variation = s.zeros(4)
        variation[a, 0] = 1
        columns.append(s.Matrix(list(variation)))
    for generator in GENERATORS:
        columns.append(s.Matrix(list(generator*e)))
    return clean(s.Matrix.hstack(*columns))


def quotient_inverse(e, h):
    assert h.det() != 0
    columns = []
    for j in range(6):
        P = metric_covector(s.eye(6)[:, j])
        response = 4*e.det()/h.det()*(s.trace(P*h)*h/2-h*P*h)
        columns.append(metric_coordinates(response))
    return clean(s.Matrix.hstack(*columns))


def actual_geometry(e):
    symbols, _, _, _, _, _, _, _, _ = original_geometry()
    change = dict(zip(symbols, e))
    _, det, H, K, G, h, Dh, Bnum, f = [value.xreplace(change) for value in original_geometry()]
    return {
        'H': H, 'inverse': clean(K/det), 'G': G, 'Gt': G[:, :16], 'Gs': G[:, 16:],
        'h': h, 'Dh': Dh, 'B': clean(Bnum/(4*det)), 'f': f,
        'M': clean(-G[:, :16].T*K*G[:, :16]/det),
    }


def whole_matter_current(e, primal, dual):
    _, vertices = original_density_ports(e, original_gamma())
    return s.Matrix([s.expand(s.re((dual*s.kronecker_product(V, s.eye(63))*primal)[0]))
                     for V in vertices])


def certify_boundary_one_form():
    e, _, _, _, G, _, _, _, f = original_geometry()
    omega = s.Matrix(s.symbols('audit_omega0:24', real=True))
    delta_e = s.Matrix(s.symbols('audit_delta_e0:16', real=True))
    delta_omega = s.Matrix(s.symbols('audit_delta_omega0:24', real=True))
    flux = (f.T*omega)[0]
    original_theta = (f.T*delta_omega)[0]
    after_ibp = ((G[:, :16].T*omega).T*delta_e)[0]
    boundary_variation = sum(s.diff(flux, value)*variation for value, variation in zip(e, delta_e))+\
        sum(s.diff(flux, value)*variation for value, variation in zip(omega, delta_omega))
    assert s.expand(original_theta-after_ibp-boundary_variation) == 0
    return {
        'temporal_flux': 'F0=f(e)^T Omega with f_(i,a)=C[a,(0,i)] for i>0 and f_(0,a)=0',
        'original_gravity_one_form': 'f(e)^T delta(Omega)',
        'after_IBP_one_form': '(Gt(e)^T Omega)^T delta(e)',
        'exact_difference': 'theta_original-theta_IBP=delta(F0)',
        'eliminated_pullback': 'theta_original|Omega*-theta_reduced=delta(F0(e,Omega*))',
        'pullback_retains_velocity_spatial_jet_and_matter_dependence': True,
        'configuration_only_point_transformation_claimed': False,
    }


def density_current_polynomial(e, primal, dual, orientation):
    """Original |det e| e^-1=orientation*adj(e), on one open orientation chart."""
    gamma = original_gamma()
    adjugate = e.adjugate()
    currents = []
    for mu, (a, b) in itertools.product(range(4), PAIRS):
        V = sum((s.I*orientation*adjugate[mu, c]*gamma[c] for c in range(4)), s.zeros(4))*gamma[a]*gamma[b]/2
        currents.append(s.expand(s.re((dual*s.kronecker_product(V, s.eye(63))*primal)[0])))
    return s.Matrix(currents)


def main():
    began = time.monotonic()
    candidate_path = HERE/'source_coframe_legendre.json'
    candidate = json.loads(candidate_path.read_bytes())
    assert candidate['root'] == ROOT_ID
    verified_bindings = 0
    for key in ('source_sha256', 'input_sha256'):
        for name, digest in candidate[key].items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
            verified_bindings += 1
    lorentz_audit = json.loads((HERE/'independent_source_lorentz_contact.json').read_bytes())
    assert lorentz_audit['verdict'] == 'CERTIFIED_UNTRUNCATED_SOURCE_LORENTZ_ELIMINATION_AND_FULL_REAL_MATTER_CONTACT_COEFFICIENTS'
    e, determinant, H, K, G, h, Dh, Bnum, f = original_geometry()
    hcoords = s.Matrix(s.symbols('audit_h0:6', real=True))
    independent_h = metric_matrix(hcoords)
    metric_hessian = s.hessian(independent_h.det(), hcoords)
    inverse_numerator = s.Matrix.hstack(*[metric_coordinates(
        s.trace(metric_covector(s.eye(6)[:, j])*independent_h)*independent_h/2-
        independent_h*metric_covector(s.eye(6)[:, j])*independent_h) for j in range(6)])
    equal(metric_hessian*inverse_numerator, independent_h.det()*s.eye(6))
    equal(inverse_numerator*metric_hessian, independent_h.det()*s.eye(6))
    columns = []
    for j in range(6):
        variation = s.zeros(4)
        variation[:, 1:] = ETA*e.adjugate()[1:, :].T*metric_matrix(s.eye(6)[:, j])/2
        columns.append(s.Matrix(list(variation)))
    Rnum = s.Matrix.hstack(*columns)
    Z = source_null_frame(e)
    equal(Dh*Rnum, determinant*s.eye(6))
    equal(Dh*Z, s.zeros(6, 10))
    adj = e.adjugate()
    assert s.expand(h.det()-adj[0, 0]**2+sum(adj[0, a]**2 for a in range(1, 4))) == 0
    generic = candidate['generic_source_geometry']
    symbols = {f'e{i}': value for i, value in enumerate(e)} | {f'h{i}': value for i, value in enumerate(hcoords)}
    def decode(record):
        return s.SparseMatrix(*record['shape'], {(i, j): s.sympify(v, locals=symbols)
                                              for i, j, v in record['entries']})
    for key, expected in (('spatial_metric', h), ('metric_velocity_map', Dh),
        ('metric_lift_numerator', Rnum), ('universal10_null_frame', Z),
        ('metric_determinant_Hessian', metric_hessian), ('metric_inverse_numerator', inverse_numerator)):
        equal(decode(generic[key]), expected)
    boundary = s.zeros(4, 24)
    C = J*exterior(e)*WEDGE
    for p, (mu, nu) in enumerate(PAIRS):
        for a in range(6):
            boundary[mu, 6*nu+a] += C[a, p]
            boundary[nu, 6*mu+a] -= C[a, p]
    for mu in range(4):
        equal(boundary[mu, :].T.jacobian(list(e)), -G[:, 16*mu:16*(mu+1)])
    equal(decode(generic['boundary_flux_coefficients']), boundary)
    boundary_proof = certify_boundary_one_form()
    print('PASS independent generic16 BF velocity Hessian factorization, exact6 metric inverse,10 null directions and all4 boundary coefficients', flush=True)

    spec = importlib.util.spec_from_file_location('coframe_legendre_api_under_audit', HERE/'source_coframe_legendre.py')
    api = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = api
    spec.loader.exec_module(api)
    model = api.SourceCoframeLegendre()
    frame_records = []
    for record in candidate['exact_frame_consumers']:
        frame = matrix(record['coframe'])
        original = actual_geometry(frame)
        produced = model.geometry(frame)
        for key in ('M', 'G', 'h', 'B'):
            equal(produced[key], original[key])
        equal(produced['D'], original['Dh'])
        R, Z0 = quotient_right_inverse(frame), source_null_frame(frame)
        equal(produced['R'], R)
        equal(original['Dh']*R, s.eye(6))
        if original['h'].det() != 0:
            expected_inverse = quotient_inverse(frame, original['h'])
            equal(original['B']*expected_inverse, s.eye(6))
            equal(produced['quotient_inverse'], expected_inverse)
            assert original['M'].rank() == 6 and produced['null_frame'].cols == 10
        else:
            assert original['h'].rank() == 2 and original['B'].rank() == 4
            assert original['M'].rank() == 4 and produced['null_frame'].cols == 12
        full_null, Q = produced['null_frame'], produced['velocity_inverse']
        equal(original['M']*full_null, s.zeros(16, full_null.cols))
        equal(original['M']*Q*original['M'], original['M'])
        equal(Q*original['M']*Q, Q)
        assert produced['velocity_lift'].row_join(full_null).rank() == 16
        # Every actual tangent is decomposed, including temporal and all
        # Lorentz frame directions, independently of the quotient rank.
        for j in range(16):
            v = s.eye(16)[:, j]
            metric_v, null_v = model.velocity_coordinates(frame, v)
            equal(metric_v, original['Dh']*v)
            equal(R*metric_v+Z0*null_v, v)
        equal(matrix(record['whole_kinetic_Hessian']), original['M'])
        frame_records.append({'determinant': str(frame.det()), 'spatial_metric_determinant': str(original['h'].det()),
                              'rank': original['M'].rank(), 'constraints': full_null.cols})
    a, b = s.symbols('a b', positive=True)
    null_hessian = metric_hessian.xreplace(dict(zip(hcoords, metric_coordinates(s.diag(0, a, b)))))
    assert null_hessian.rank() == 4 and len(null_hessian.nullspace()) == 2
    print('PASS all source velocity charts: full rank6 quotient/10 constraints, null rank4 quotient/12 constraints, full16 tangent decomposition', flush=True)

    matter_record = candidate['full_matter_momentum_and_energy']
    frame = matrix(matter_record['source_coframe'])
    primal, dual = matrix(matter_record['test_primal']), matrix(matter_record['test_dual'])
    spatial = matrix(matter_record['test_spatial_jet'])
    original = actual_geometry(frame)
    current = whole_matter_current(frame, primal, dual)
    equal(current, matrix(matter_record['full252_matter_current']))
    q = original['Gs']*spatial+current
    shift = clean(-original['Gt'].T*original['inverse']*q)
    matter_shift = clean(-original['Gt'].T*original['inverse']*current)
    assert matter_shift.todok()
    equal(matter_shift, matrix(matter_record['matter_induced_momentum_shift']))
    equal(shift, matrix(matter_record['complete_momentum_shift']))
    v = s.Matrix(s.symbols('audit_v0:16', real=True))
    total_source = original['Gt']*v+q
    L = s.expand(-3*frame.det()-(total_source.T*original['inverse']*total_source)[0]/2)
    Pi = s.Matrix([s.diff(L, value) for value in v])
    equal(Pi, original['M']*v+shift)
    equal(model.momentum(frame, v, spatial, primal, dual), Pi)
    assert s.expand(model.lagrangian(frame, v, spatial, primal, dual)-L) == 0
    null = source_null_frame(frame)
    equal(null.T*(Pi-shift), s.zeros(10, 1))
    equal(model.constraints(frame, Pi, spatial, primal, dual), s.zeros(10, 1))
    assert s.expand(model.hamiltonian(frame, Pi, spatial, primal, dual)-(Pi.T*v)[0]+L) == 0
    p = s.Matrix(s.symbols('audit_pi0:16', real=True))
    multipliers = s.Matrix(s.symbols('audit_lambda0:10', real=True))
    R = quotient_right_inverse(frame)
    Q = clean(R*quotient_inverse(frame, original['h'])*R.T)
    expected_H = s.expand(((p-shift).T*Q*(p-shift))[0]/2+3*frame.det()+
                         (q.T*original['inverse']*q)[0]/2+(multipliers.T*null.T*(p-shift))[0])
    assert s.expand(model.hamiltonian(frame, p, spatial, primal, dual, multipliers)-expected_H) == 0
    equal(s.Matrix([s.diff(expected_H, value) for value in p]),
          model.velocity(frame, p, spatial, primal, dual, multipliers))
    assert s.expand(((p-shift).T*Q*(p-shift))[0]-(p.T*Q*p)[0]) != 0
    print('PASS original full252 current supplies nonzero canonical momentum shift and complete source Legendre/Hamilton primary constraints', flush=True)

    # Recompute Euler by differentiating the actual reduced density and its
    # actual jet momenta along four curves, not the candidate envelope formula.
    euler_record = candidate['original_Euler_and_boundary_consumer']
    de = matrix(euler_record['full_first_coframe_jet'])
    dde = matrix(euler_record['full_symmetric_second_coframe_jet'])
    dp = [s.Rational(mu+1, 5)*primal for mu in range(4)]
    dc = [s.Rational(2*mu-1, 7)*dual for mu in range(4)]
    produced = model.euler(frame, de, dde, primal, dual, dp, dc)
    source = original['G']*de+current
    connection = clean(-original['inverse']*source)
    momenta = clean(original['G'].T*connection)
    equal(produced['connection'], connection)
    equal(produced['all_four_coframe_momenta'], momenta)
    u = s.Symbol('audit_curve', real=True)
    force = []
    for j in range(16):
        direction = s.zeros(4)
        direction[j] = 1
        curve = frame+u*direction
        substitution = dict(zip(e, curve))
        curve_current = density_current_polynomial(curve, primal, dual, s.sign(frame.det()))
        curve_source = G.xreplace(substitution)*de+curve_current
        density = -3*curve.det()-(curve_source.T*K.xreplace(substitution)*curve_source)[0]/(2*curve.det())
        force.append(s.cancel(s.diff(density, u).subs(u, 0)))
    force = s.Matrix(force)
    divergence = s.zeros(16, 1)
    connection_derivatives = s.zeros(4, 24)
    current_derivative_checks = 0
    for mu in range(4):
        curve = frame+u*s.Matrix(4, 4, de[16*mu:16*(mu+1), 0])
        curve_de = de+u*dde[mu, :].T
        substitution = dict(zip(e, curve))
        curve_current = density_current_polynomial(curve, primal+u*dp[mu], dual+u*dc[mu], s.sign(frame.det()))
        curve_G = G.xreplace(substitution)
        curve_source = curve_G*curve_de+curve_current
        curve_connection = -K.xreplace(substitution)*curve_source/curve.det()
        curve_momentum = curve_G[:, 16*mu:16*(mu+1)].T*curve_connection
        divergence += curve_momentum.diff(u).subs(u, 0).applyfunc(s.cancel)
        connection_derivatives[mu, :] = curve_connection.diff(u).subs(u, 0).applyfunc(s.cancel).T
        equal(curve_current.diff(u).subs(u, 0), model.current_derivative(
            frame, de[16*mu:16*(mu+1), 0], primal, dual, dp[mu], dc[mu]))
        current_derivative_checks += 24
    euler = clean(force-divergence)
    equal(produced['coframe_force'], force)
    equal(produced['connection_derivative'], connection_derivatives)
    equal(produced['Euler'], euler)
    assert euler.todok()
    for key, expected in (('all16_original_coframe_force', force), ('all16_nontrivial_Euler_readback', euler),
        ('all64_coframe_momenta', momenta), ('all_four_connection_derivatives', connection_derivatives)):
        equal(matrix(euler_record[key]), expected)
    fluxes = clean(boundary.xreplace(dict(zip(e, frame)))*connection)
    equal(produced['boundary_flux'], fluxes)
    equal(model.boundary_flux(frame, connection), fluxes)
    equal(matrix(euler_record['all_four_original_boundary_fluxes']), fluxes)
    print('PASS independently differentiated full64/256 coframe and full matter jets: all16 Euler,96 current/connection derivatives and original boundary pullback', flush=True)

    paths = [HERE/name for name in ('source_coframe_legendre.py', 'source_coframe_legendre.json',
        'independent_source_coframe_legendre.py', 'independent_source_lorentz_contact.py',
        'independent_source_lorentz_contact.json')]
    output = {
        'root': ROOT_ID,
        'verdict': 'CERTIFIED_UNTRUNCATED_COFRAME_LEGENDRE_CONSTRAINTS_AND_ORIGINAL_EULER_BOUNDARY_CONSUMER',
        'scope': candidate['scope'], 'source_sha256': candidate['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'candidate_bindings_verified': verified_bindings,
        'source_factorization': 'M=-Gt^T H^-1 Gt=Dh^T Hess(det h) Dh/(4 det e)',
        'generic_geometry_paid': {'independent_coframe_coordinates': 16, 'velocity_coordinates': 16,
            'spatial_derivative_coordinates': 48, 'metric_coordinates': 6,
            'whole_GL4_metric_right_inverse': True, 'noncharacteristic_rank': 6, 'noncharacteristic_constraints': 10,
            'null_rank': 4, 'null_constraints': 12, 'null_branch_inverted_as_rank6': False,
            'all_source_frame_consumers': frame_records},
        'universal_null_completeness': 'For Dh(deltaE)=0, e^T eta deltaE has skew spatial3x3 block; extend it uniquely to a skew4x4 matrix by its first row. eta e^-T K e^-1 is an original Lorentz generator with the same spatial variation; the remaining variation is exactly the four temporal columns.',
        'null_rank_reason': 'The radical of a real Lorentzian3-plane is at most1. The null induced metric is congruent to diag(0,a,b) with a,b>0; its determinant Hessian has exact rank4, preserved by congruence.',
        'full_matter_current_and_momentum': {'complex_dimension': 252,
            'matter_shift_nonzero_coordinates': len(matter_shift.todok()),
            'shift': 'b=-Gt^T H^-1 (Gs spatial+j_matter)',
            'momentum': 'Pi=M velocity+b', 'constraints': 'Z^T(Pi-b)=0',
            'Hamiltonian': '1/2(Pi-b)^T Q(Pi-b)+3det e+1/2 q^T H^-1 q+lambda^T Z^T(Pi-b)',
            'all16_velocity_Legendre_identity': True, 'actual_primary_constraints': True,
            'omitted_matter_shift_rejected': True},
        'actual_original_Euler': {'first_jet_coordinates': 64, 'second_jet_coordinates': 256,
            'direct_density_coframe_partials': 16, 'direct_spacetime_current_derivatives': current_derivative_checks,
            'direct_connection_derivatives': 96, 'all16_Euler_equal': True,
            'algorithm': 'direct rational source-density derivative and derivative of G_mu^T Omega*(e,de,psi,chi) along genuine field jets',
            'scope': euler_record['scope']},
        'boundary_and_canonical_one_form': {**boundary_proof, 'all_four_spacetime_fluxes_verified': True},
        'Hamilton_Euler_equivalence': 'On Pi=d_v L and v=Q(Pi-b)+Zlambda, differentiate the actual Legendre identity plus the actual primary constraints at fixed canonical Pi. The resulting d_x H_total=-d_x L includes derivatives of the source frames and the complete matter-dependent shift.',
        'actual_producer_API': candidate['public_API'],
        'old_Jacobi_or_occupied12_as_nonlinear_producer': False,
        'complete_gravity_gauge_scalar_matter_Hamiltonian_claimed': False,
        'elapsed_seconds': round(time.monotonic()-began, 3),
    }
    (HERE/'independent_source_coframe_legendre.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS independent nonlinear coframe Legendre/Euler certification', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
