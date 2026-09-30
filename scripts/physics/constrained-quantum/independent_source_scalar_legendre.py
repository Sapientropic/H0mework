#!/usr/bin/env python3
"""Independent density/velocity-Hessian audit of the original full70 scalar.

No candidate constructor or projected-phase constructor is imported. Exterior
matrices are rebuilt by indexed creation/annihilation on occupation words.
The Legendre inverse is solved from the raw density before reading the claim.
"""
from __future__ import annotations

import hashlib
import itertools
import json
from pathlib import Path
import sys
import time

import sympy as s

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
ROOT = HERE.parents[3]
ROOT_ID = 'positiveSmoothUnifiedSource; repaired Dirac-dual; SpinPair.actual; visit10/tick16/materialEntry -> tick17 unchanged'
sys.path.insert(0, str(BASE))
import exact_readout as source

K = s.symbols('k1:4', real=True)


def read(path):
    return json.loads(path.read_bytes())


def clean(value):
    return s.SparseMatrix(value).applyfunc(s.expand)


def equal(left, right):
    assert not clean(left-right).todok()


def scalar_zero(value):
    assert s.cancel(value) == 0


def decode(record):
    return s.SparseMatrix(*record['shape'], {(i, j): s.sympify(v, locals={str(k): k for k in K})
        for i, j, v in record['entries']})


def encode(value):
    return {'shape': list(value.shape), 'entries': [[i, j, str(s.expand(v))]
        for (i, j), v in sorted(s.SparseMatrix(value).todok().items())]}


def check_bindings(record):
    count = 0
    for key in ('source_sha256', 'input_sha256'):
        for name, digest in record.get(key, {}).items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
            count += 1
    return count


def occupation_action(matrix):
    words = list(itertools.combinations(range(7), 4))
    masks = [sum(1 << i for i in word) for word in words]
    index = {mask: i for i, mask in enumerate(masks)}
    result = s.MutableSparseMatrix.zeros(35, 35)
    for col, mask in enumerate(masks):
        for (a, b), coefficient in s.SparseMatrix(matrix).todok().items():
            if not mask & (1 << b):
                continue
            remaining = mask ^ (1 << b)
            if remaining & (1 << a):
                continue
            parity = (mask & ((1 << b)-1)).bit_count() + (remaining & ((1 << a)-1)).bit_count()
            result[index[remaining | (1 << a)], col] += (-1)**parity*coefficient
    return s.SparseMatrix(result)


def real_action(matrix):
    output = s.MutableSparseMatrix.zeros(70, 70)
    for (i, j), z in s.SparseMatrix(matrix).todok().items():
        output[i, j] += s.re(z)
        output[i+35, j+35] += s.re(z)
        output[i+35, j] += s.im(z)
        output[i, j+35] -= s.im(z)
    return clean(output)


def metric(coframe):
    volume = s.Abs(coframe.det())
    assert volume != 0
    spacetime = coframe.T*s.diag(-1, 1, 1, 1)*coframe
    return clean(volume*spacetime.inv()), volume


def density_legendre(record):
    names = 'h00 h01 h02 h03 h11 h12 h13 h22 h23 h33'
    entries = s.symbols(names, real=True)
    h = s.zeros(4)
    for (mu, nu), entry in zip(itertools.combinations_with_replacement(range(4), 2), entries):
        h[mu, nu] = h[nu, mu] = entry
    pi, velocity, temporal, volume, potential = s.symbols('pi velocity A0phi volume potential', real=True)
    w = s.Matrix(s.symbols('D1phi D2phi D3phi', real=True))
    u = s.Matrix([velocity+temporal, *w])
    lagrangian = sum(h[mu, nu]*u[mu]*u[nu]/2 for mu in range(4) for nu in range(4))-volume*potential
    momentum = s.diff(lagrangian, velocity)
    # Solve the affine Legendre map through its velocity Hessian.
    temporal_hessian = s.diff(momentum, velocity)
    offset = momentum.subs(velocity, 0)
    inverse_velocity = (pi-offset)/temporal_hessian
    hamiltonian = s.cancel((pi*velocity-lagrangian).subs(velocity, inverse_velocity))
    symbols = {str(v): v for v in (*entries, pi, velocity, temporal, volume, potential, *w)}
    for key, expression in [('density', lagrangian), ('momentum', momentum),
                            ('velocity', inverse_velocity), ('Hamiltonian', hamiltonian)]:
        scalar_zero(expression-s.sympify(record[key], locals=symbols))
    scalar_zero(s.diff(hamiltonian, pi)-inverse_velocity)
    scalar_zero(momentum.subs(velocity, inverse_velocity)-pi)
    # A direct differential identity proves all coframe/covariant-port chains.
    ports = [*entries, volume, temporal, *w]
    for parameter in ports:
        scalar_zero(s.diff(hamiltonian, parameter)+s.diff(lagrangian, parameter).subs(velocity, inverse_velocity))
    assert len(ports) == record['fixed_momentum_metric_and_connection_variations_checked'] == 15
    scalar_zero(s.diff(hamiltonian, pi, pi)-1/h[0, 0])
    return {'velocity_Hessian': str(temporal_hessian), 'source_solved_velocity': str(inverse_velocity),
        'source_derived_Hamiltonian': str(hamiltonian), 'independent_coefficient_ports': len(ports),
        'full70_extension': 'the original real pairing is the orthogonal sum of these70 raw component densities; scalar potential Hessian is2I70'}


def main():
    started = time.monotonic()
    candidate_path = HERE/'source_scalar_legendre.json'
    candidate = read(candidate_path)
    canonical_path = HERE/'scalar_canonical_phase.json'
    canonical = read(canonical_path)
    active_path = BASE/'active-gauge/receipt.json'
    active = read(active_path)
    real_path = HERE/'real_scalar_car_source.json'
    real = read(real_path)
    assert candidate['root'] == canonical['root'] == real['root'] == ROOT_ID
    binding_count = sum(check_bindings(value) for value in (candidate, canonical, real))
    _, vacuum, _, hashes = source.parse_source(ROOT)
    assert hashes == candidate['source_sha256'] == canonical['source_sha256'] == real['source_sha256']
    words = list(itertools.combinations(range(7), 4))
    v0 = s.Matrix([vacuum.get(word, 0) for word in words]+[0]*35)
    equal(v0, decode(candidate['source_vacuum70']))
    assert (v0.T*v0)[0] == 4
    rho = []
    for _, imaginary, matrix in source.generators([(0, 1, 2), (3, 4)]):
        action = occupation_action(s.Matrix(matrix)*(s.I if imaginary else 1))
        equal(action.H, -action)
        rho.append(real_action(action))
    assert len(rho) == len(candidate['source_rho70']) == 12
    for actual, saved in zip(rho, candidate['source_rho70']):
        equal(actual, decode(saved))
        equal(actual.T, -actual)
    generic = density_legendre(candidate['generic_scalar_component'])
    print('PASS raw occupation-word full70 source representation and density-derived Legendre inverse with all15 coefficient ports', flush=True)

    background = active['actual_background']
    e0 = s.Matrix(background['coframe']).applyfunc(s.sympify)
    gauge = s.Matrix(background['gauge_connection']).applyfunc(s.sympify)
    h0, N = metric(e0)
    assert N.is_positive and s.simplify(N*N) == s.Rational(54, 125)
    equal(e0, decode(candidate['actual_background']['coframe']))
    equal(h0, s.diag(-1/N, N, N, N))
    connections = [clean(sum((gauge[mu, a]*rho[a] for a in range(12)), s.zeros(70))) for mu in range(4)]
    equal(connections[0], s.zeros(70))
    D = [clean(s.I*K[i]*s.eye(70)+connections[i+1]) for i in range(3)]
    # In Fourier space, integration by parts is D(-k)^T=-D(k).
    minus = dict(zip(K, [-k for k in K]))
    for operator in D:
        equal(operator.subs(minus, simultaneous=True).T, -operator)
    stiffness = clean(2*N*s.eye(70)-sum((N*operator.subs(minus, simultaneous=True).T*operator for operator in D), s.zeros(70)))
    full_hessian = s.diag(stiffness, -N*s.eye(70))
    equal(full_hessian, decode(candidate['actual_background']['full140_Hessian']))
    equal(stiffness, -N*decode(canonical['scalar_L']))
    orbit = s.SparseMatrix.hstack(*(R*v0 for R in rho))
    independent = orbit[:, orbit.rref()[1]]
    assert independent.cols == 9
    P = clean(s.eye(70)-independent*(independent.T*independent).inv()*independent.T)
    equal(P, decode(canonical['projector61']))
    R = P[:, canonical['canonical_coordinate_pivots']]
    dual = clean(R*(R.T*R).inv())
    T = s.diag(R, dual)
    equal(T, decode(canonical['canonical_phase_embedding']))
    equal(T.T*full_hessian*T, decode(canonical['canonical_Hamiltonian_hessian']))
    J122 = s.SparseMatrix.vstack(s.SparseMatrix.hstack(s.zeros(61), s.eye(61)),
        s.SparseMatrix.hstack(-s.eye(61), s.zeros(61)))
    equal(J122*T.T*full_hessian*T, decode(canonical['canonical_generator']))
    print('PASS unprojected source140 scalar Hessian and independently rebuilt source-orbit61 canonical122 consumer', flush=True)

    phi = s.Matrix(s.symbols('phi0:70', real=True))
    pi = s.Matrix(s.symbols('pi0:70', real=True))
    for action in rho:
        charge = -(pi.T*action*phi)[0]
        equal(s.Matrix([s.diff(charge, p) for p in pi]), -action*phi)
        equal(-s.Matrix([s.diff(charge, q) for q in phi]), -action*pi)
    q = s.Matrix([s.Rational(j+2, 73) for j in range(70)])
    dq = [s.Matrix([s.Rational((j+3)*(i+2), 79) for j in range(70)]) for i in range(3)]
    A = s.Matrix(4, 12, s.symbols('audit_A0:48', real=True))
    action_q = [action*q for action in rho]
    AQ = [sum((A[mu, a]*action_q[a] for a in range(12)), s.zeros(70, 1)) for mu in range(4)]
    frame_records = candidate['orientation_and_shift_consumers']
    assert len(frame_records) == 2
    orientations = []
    for saved in frame_records:
        frame = decode(saved['coframe'])
        h, volume = metric(frame)
        equal(h, decode(saved['metric_density']))
        assert volume == s.sympify(saved['volume']) == abs(frame.det())
        assert frame.det() == s.sympify(saved['determinant'])
        orientations.append(s.sign(frame.det()))
        w = [dq[i]+AQ[i+1] for i in range(3)]
        b = sum((h[0, i+1]*w[i] for i in range(3)), s.zeros(70, 1))
        u0 = (pi-b)/h[0, 0]
        H = ((pi-b).dot(pi-b)/(2*h[0, 0])-pi.dot(AQ[0])
            -sum(h[i+1, j+1]*w[i].dot(w[j])/2 for i in range(3) for j in range(3))
            +volume*(q-v0).dot(q-v0))
        equal(s.Matrix([s.diff(H, p) for p in pi]), u0-AQ[0])
        for mu, a in itertools.product(range(4), range(12)):
            momentum_mu = h[mu, 0]*u0+sum((h[mu, i+1]*w[i] for i in range(3)), s.zeros(70, 1))
            scalar_zero(s.diff(H, A[mu, a])+momentum_mu.dot(action_q[a]))
        # Independently differentiate e^T eta e and |det e| in every direction.
        for row, col in itertools.product(range(4), repeat=2):
            tangent = s.zeros(4); tangent[row, col] = 1
            volume_tangent = volume*s.trace(frame.inv()*tangent)
            g = frame.T*s.diag(-1, 1, 1, 1)*frame
            dg = tangent.T*s.diag(-1, 1, 1, 1)*frame+frame.T*s.diag(-1, 1, 1, 1)*tangent
            dh = clean(volume_tangent*g.inv()-volume*g.inv()*dg*g.inv())
            t = s.symbols('coframe_t', real=True)
            varied = frame+t*tangent
            local_volume = s.sign(frame.det())*varied.det()
            raw_h = local_volume*(varied.T*s.diag(-1, 1, 1, 1)*varied).inv()
            equal(dh, raw_h.diff(t).subs(t, 0))
            scalar_zero(local_volume.diff(t).subs(t, 0)-volume_tangent)
    assert sorted(orientations) == [-1, 1]
    null_frame = s.Matrix([[1, 1, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    null_h, _ = metric(null_frame)
    assert null_h[0, 0] == 0 and null_h[0, 1] != 0
    assert (null_h[0, 0]*s.eye(70)).rank() == 0
    assert candidate['null_temporal_raw_momentum_retained_but_inverse_rejected']
    print('PASS full12 Gauss action, all48 symbolic connection derivatives on both orientations and all32 coframe derivative chains', flush=True)

    assert candidate['scalar_dimension'] == 70 and candidate['density_volume'] == 'abs(det e)'
    assert candidate['scalar_Gauss_ports']['count'] == 12
    assert candidate['complete_gravity_gauge_constraint_Hamiltonian_claimed'] is False
    assert candidate['full_four_block_spectrum_or_lifetime_claimed'] is False
    assert candidate['normalization_or_source_occurrence_changed'] is False
    assert len(real['all70_sources']) == 70
    paths = [candidate_path, HERE/'source_scalar_legendre.py', Path(__file__), canonical_path, active_path,
             real_path, BASE/'exact_readout.py']
    result = {'verdict': 'CERTIFIED_ORIGINAL_FULL70_LIVE_SCALAR_LEGENDRE_AND_CANONICAL_PORTS',
        'root': ROOT_ID, 'source_sha256': hashes,
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'candidate_or_projected_constructor_imported': False,
        'algorithm': 'raw occupation-bit creation/annihilation exterior action; original velocity-Hessian inversion; direct raw-density differential identities; source Fourier integration by parts; independently regenerated orbit and dual coordinate frame; full48 source connection variation; both-orientation direct coframe derivatives',
        'source_binding_checks': binding_count, 'generic_density_certificate': generic,
        'scalar_real_dimension': 70, 'source_generator_count': 12, 'source_vacuum_norm_squared': 4,
        'source_potential_Hessian': '2 I70; no1/2 or extra realification normalization',
        'chart_scope': 'the original chart0; scalarFrameRelativeCoordinates_zeroChart is the existing exact identity',
        'full140_Hessian': encode(full_hessian),
        'source_orbit_rank': 9, 'peripheral_rank': 61, 'canonical_phase_dimension': 122,
        'background_projection_and_Hamiltonian_generator_recovered': True,
        'all48_symbolic_connection_ports_per_orientation': 48, 'coframe_orientations': list(map(int, orientations)),
        'direct_coframe_derivative_chains_checked': 32,
        'canonical_Gauss': 'dH/dA0^a=-Pi^T rho_a phi; delta phi=-rho_a phi and delta Pi=-rho_a Pi',
        'spatial_ports': 'dH/dAi^a=-sum_nu h^{i nu}(D_nu phi)^T rho_a phi at fixed Pi',
        'Legendre_domain': 'det e !=0 and h00 !=0; null temporal map retains the raw spatial-shift momentum and has no velocity inverse',
        'null_temporal_candidate_guard_reviewed': True,
        'matter_consumer_scope': 'existing FullQuantum.Source full252 Hamiltonian and original70 real-CAR ports provide the common-coordinate interface; the new scalar-only method does not construct or integrate the combined matter Hamiltonian',
        'full_gravity_gauge_constraint_Hamiltonian_or_quantum_evolution_certified': False,
        'full_four_block_spectral_measure_or_lifetime_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'independent_source_scalar_legendre.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS independent original full70 scalar Legendre audit', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
