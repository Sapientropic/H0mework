#!/usr/bin/env python3
"""Independent original-density inverse and retarded-time audit.

No candidate constructor is imported. Source coefficients are rebuilt from
the independent raw action. Inverse certificates are checked on every source
component; the concrete time consumer is solved directly in its invariant
subspace, independently of the candidate resolvent algorithm.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_joint_temporal_rates import RawSource, HERE, BASE, ROOT, ROOT_ID, bindings, clean, encode, eq, zero
from independent_source_full_linear_split import build_raw, real_fourier, assemble, P, K
from independent_source_gauss_quantum_current import polynomial_real_action

Z = s.Symbol('retarded_laplace')
SYMBOLS = {str(x): x for x in (*K, *P, Z)}
SYMBOLS['lambda'] = Z


def read_matrix(record):
    return s.SparseMatrix(*record['shape'], {(i, j): s.sympify(value.replace('lambda', str(Z)), locals=SYMBOLS)
        for i, j, value in record['entries']})


def rational_eq(left, right):
    residue = s.SparseMatrix(left-right).applyfunc(lambda x: s.cancel(x, extension=True))
    assert not residue.todok(), list(residue.todok().items())[:2]


def raw_tail(raw):
    source = build_raw(raw)
    indices, N = source['complement'], source['N']
    E = s.SparseMatrix(source['principal'][0].extract(indices, indices))
    Ei = E.inv()
    constant = source['D'].subs(dict.fromkeys(P, 0)).extract(indices, indices)
    spatial = [matrix.extract(indices, indices) for matrix in source['principal'][1:]]
    coefficients = {
        'dual': [clean((constant*Ei).T), *[clean(-(T*Ei).T) for T in spatial]],
        'primal': [clean(-Ei*constant), *[clean(-Ei*T) for T in spatial]]}
    blocks = {name: real_fourier(values) for name, values in coefficients.items()}
    R = raw.P61[:, list(raw.P61.rref()[1])]
    gram = clean(R.T*R); gram_inv = gram.inv()
    RA = [raw.action(raw.A[i, :], raw.rho70) for i in range(4)]
    L70 = clean(-sum(((s.I*k*s.eye(70)+RA[i+1])**2 for i, k in enumerate(K)), s.zeros(70))-2*s.eye(70))
    blocks['scalar'] = assemble(122, [(0, 61, -N*gram_inv), (61, 0, N*R.T*L70*R)])
    source70 = clean(s.Matrix.hstack(*((N*Y*raw.psi0).extract(indices, [0]) for Y in raw.Y)))
    source61 = clean(source70*R)
    C = clean(-Ei*source61)
    C = C.applyfunc(s.re).col_join(C.applyfunc(s.im)).row_join(s.zeros(480, 61))
    B = s.zeros(61, 480).col_join(source61.T.applyfunc(s.re).row_join(-source61.T.applyfunc(s.im)))
    A = assemble(1082, [(0, 0, blocks['dual']), (480, 480, blocks['scalar']),
        (602, 602, blocks['primal']), (480, 0, B), (602, 480, C)])
    return source, coefficients, blocks, clean(B), clean(C), A, R, gram, L70, E


def certify_matter(coefficients, record):
    A = clean(coefficients[0]+sum((s.I*k*M for k, M in zip(K, coefficients[1:])), s.zeros(240)))
    groups = record['source_components']
    assert len(groups) == 90
    assert sorted(i for row in groups for i in row['indices']) == list(range(240))
    assert len(record['exact_inverse_leaves']) == 8
    owner = {index: number for number, row in enumerate(groups) for index in row['indices']}
    assert all(2 <= len(row['indices']) <= 4 for row in groups)
    leaves = []
    for row in record['exact_inverse_leaves']:
        a, numerator = read_matrix(row['generator']), read_matrix(row['numerator'])
        denominator = s.sympify(row['denominator'], locals=SYMBOLS)
        polynomial = Z*s.eye(a.rows)-a
        # Check supplied certificates by exact coefficient arithmetic; no
        # adjugate or determinant constructor from the producer is reused.
        eq(polynomial*numerator, denominator*s.eye(a.rows))
        eq(numerator*polynomial, denominator*s.eye(a.rows))
        assert s.Poly(denominator, Z).LC() == 1
        leaves.append((a, numerator, denominator))
    off_entries = {(i, j): value for (i, j), value in A.todok().items() if owner[i] != owner[j]}
    off = s.SparseMatrix(240, 240, off_entries)
    eq(off, read_matrix(record['original_between_block_Yukawa']))
    for row in groups:
        eq(A.extract(row['indices'], row['indices']), leaves[row['inverse_leaf']][0])
    edges = {(owner[i], owner[j]) for i, j in off_entries}
    assert len(edges) == record['between_block_feed_count'] == 12
    assert not ({i for i, _ in edges} & {j for _, j in edges})
    # Complete coverage proves off*R0*off=0 for any block diagonal R0.
    # Thus R0+R0*off*R0 is the inverse on both sides, with arbitrary forcing.
    complex_mirror = clean(coefficients[0].conjugate()+sum((s.I*k*M.conjugate() for k, M in zip(K, coefficients[1:])), s.zeros(240)))
    U = assemble(480, [(0, 0, s.eye(240)), (0, 240, s.I*s.eye(240)),
        (240, 0, s.eye(240)), (240, 240, -s.I*s.eye(240))])/s.sqrt(2)
    real = real_fourier(coefficients)
    eq(U*U.H, s.eye(480))
    eq(U*real*U.H, assemble(480, [(0, 0, A), (240, 240, complex_mirror)]))
    eq(complex_mirror, A.conjugate().subs(dict(zip(K, [-k for k in K])), simultaneous=True))
    assert complex_mirror != A.conjugate()
    return {'groups': 90, 'distinct_inverse_leaves': 8, 'source_Yukawa_feeds': 12,
        'all240_coordinates_covered_once': True, 'all_source_diagonal_and_off_blocks_covered': True,
        'both_polynomial_inverse_identities': True, 'real480_unitary_branch_identity': True,
        'coefficient_conjugate_minus_k_not_same_k': True}


def max_norm_bound(matrix):
    entries = matrix.todok()
    rows = [s.simplify(sum(abs(v) for (i, _), v in entries.items() if i == r)) for r in range(matrix.rows)]
    cols = [s.simplify(sum(abs(v) for (_, j), v in entries.items() if j == c)) for c in range(matrix.cols)]
    return s.simplify(s.sqrt(max(rows)*max(cols)))


def main():
    started = time.monotonic()
    path = HERE/'source_full_linear_retarded.json'
    record = json.loads(path.read_text()); checks = bindings(record)
    raw = RawSource(); source, coefficients, blocks, B, C, A, R, gram, L70, E = raw_tail(raw)
    N = source['N']
    assert record['root'] == ROOT_ID and record['source_sha256'] == raw.hashes
    split = json.loads((HERE/'source_full_linear_split.json').read_text())
    for name, matrix in blocks.items(): eq(matrix, read_matrix(split['triangular_tail'][name]))
    eq(B, read_matrix(record['actual_source_maps']['dual_to_scalar']))
    eq(C, read_matrix(record['actual_source_maps']['scalar_to_primal']))
    matter = {name: certify_matter(coefficients[name], record[name+'_inverse']) for name in ('dual', 'primal')}
    print('PASS raw matter240 per branch: all90 components,8 inverse certificates,12 feeds and complete real480 conjugate(-k) identity', flush=True)

    scalar = json.loads((HERE/'scalar_canonical_phase.json').read_text()); checks += bindings(scalar)
    numerator70 = read_matrix(scalar['original_Green_numerator'])
    denominator = s.sympify(scalar['original_Green_denominator'].replace('lambda', str(Z)), locals=SYMBOLS)
    original70 = clean(Z**2*s.eye(70)/N+N*L70)
    eq(original70*numerator70, denominator*raw.P61)
    eq(numerator70*original70, denominator*raw.P61)
    eq(raw.P61*numerator70, numerator70); eq(numerator70*raw.P61, numerator70)
    # Eliminate pi from (zI-As)(q,pi)=(fq,fpi):
    # (z² Gram+N² R.T L R)q=z Gram fq-N fpi.
    # This reconstructs the full inverse by the original momentum equation.
    q_inverse_num = clean(gram.inv()*R.T*numerator70*R*gram.inv()/N)
    q_poly = clean(Z**2*gram+N**2*R.T*L70*R)
    eq(q_poly*q_inverse_num, denominator*s.eye(61))
    scalar_num = assemble(122, [(0, 0, Z*q_inverse_num*gram), (0, 61, -N*q_inverse_num),
        (61, 0, N*R.T*L70*R*q_inverse_num*gram), (61, 61, Z*gram*q_inverse_num)])
    Ms = Z*s.eye(122)-blocks['scalar']
    eq(Ms*scalar_num, denominator*s.eye(122)); eq(scalar_num*Ms, denominator*s.eye(122))
    zero(denominator-s.sympify(record['scalar_inverse']['denominator'], locals=SYMBOLS))
    # Compare the producer's compressed formula, after the independent
    # elimination has already fixed the original Gram placement and signs.
    Q = clean(gram.inv()*R.T*numerator70*R/N)
    recipe = assemble(122, [(0, 0, Z*Q), (0, 61, -N*Q*gram.inv()),
        (61, 0, blocks['scalar'][61:, :61]*Q), (61, 61, Z*gram*Q*gram.inv())])
    eq(recipe, scalar_num)
    print('PASS original70 scalar Green and independently eliminated canonical122 inverse, both polynomial orientations', flush=True)

    consumer = record['actual_two_stage_time_consumer']
    momentum = tuple(map(s.sympify, consumer['momentum'])); replace = dict(zip(K, momentum))
    At = clean(A.subs(replace)); indices = consumer['state_embedding_source_indices']
    injection = s.SparseMatrix(1082, len(indices), {(row, col): 1 for col, row in enumerate(indices)})
    generator = At.extract(indices, indices)
    eq(generator, read_matrix(consumer['state_generator']))
    eq(At*injection, injection*generator)
    initial = s.SparseMatrix(1082, 1, {(consumer['dual_initial_coordinate'], 0): 1})
    state_initial = injection.T*initial
    eq(injection*state_initial, initial); eq(state_initial, read_matrix(consumer['state_initial']))
    assert len(indices) == consumer['exact_invariant_time_state_dimension'] == 24
    cascade = clean(C*blocks['scalar']*B)
    eq(C*B, s.zeros(480)); eq(cascade, read_matrix(consumer['whole_two_hop_third_derivative']))
    jet = initial
    for order in range(1, 4):
        jet = clean(At*jet)
        if order == 2: eq(jet[602:, :], s.zeros(480, 1))
    eq(jet[602:, :], cascade[:, consumer['dual_initial_coordinate']])
    observed = jet[602+consumer['primal_reader_coordinate'], 0]
    zero(observed-s.sympify(consumer['two_hop_third_time_derivative']))
    zero(observed-162*s.sqrt(30)/3125)
    laplace = s.sympify(consumer['actual_safe_laplace'])
    # A direct24-dimensional exact linear solve is independent of all
    # producer leaf/resolvent routines and retains the full1082 backwrite.
    resolved, free = (laplace*s.eye(24)-generator).gauss_jordan_solve(state_initial)
    assert not free.rows
    response = clean(injection*resolved)
    eq(response, read_matrix(consumer['whole1082_response']))
    eq((laplace*s.eye(1082)-At)*response, initial)
    assert response[480:602, :].todok() and response[602:, :].todok()
    # Invariant injection is the exact all-time proof: exp(tA)I=I exp(tG).
    # Finite matrix exponential is entire; no Taylor truncation is used.
    print('PASS direct24-state inverse/full1082 source backwrite and exact nonzero third-time two-stage propagation', flush=True)

    energy = json.loads((HERE/'scalar_momentum_energy.json').read_text())
    energy_audit = json.loads((HERE/'independent_scalar_momentum_energy.json').read_text())
    checks += bindings(energy)+bindings(energy_audit)
    eq(blocks['scalar'], read_matrix(scalar['canonical_generator']))
    alpha = 2*N; beta = s.sympify(energy['coordinate_time_growth_beta'])
    zero(alpha-s.sympify(record['global_bounds']['alpha']))
    zero(beta-s.sympify(record['global_bounds']['beta']))
    assert s.simplify(beta-alpha).is_positive
    for name in ('dual', 'primal'):
        matrix = blocks[name]
        for k in K: eq(matrix.diff(k)+matrix.diff(k).H, s.zeros(480))
        H = clean((matrix.subs(dict.fromkeys(K, 0))+matrix.subs(dict.fromkeys(K, 0)).H)/2)
        # Hermitian Gershgorin/Cauchy gives H<=alpha I and -H<=alpha I.
        row_sums = [s.simplify(sum(abs(v) for (i, _), v in H.todok().items() if i == r)) for r in range(480)]
        assert max(row_sums) == alpha
    b, c = max_norm_bound(B), max_norm_bound(C)
    zero(b-s.sympify(record['global_bounds']['B_norm_bound']))
    zero(c-s.sympify(record['global_bounds']['C_norm_bound']))
    zero(beta/N-s.sympify(record['global_bounds']['proper_clock_beta']))
    assert record['global_bounds']['active289_or_active126_uniform_beta_claimed'] is False
    print('PASS three-momentum Hermitian-part bounds, same scalar comparison energy and full1082 retarded half-plane', flush=True)

    orbit = json.loads((HERE/'source_stationary_cauchy_orbit.json').read_text())
    orbit_audit = json.loads((HERE/'independent_source_stationary_cauchy_orbit.json').read_text())
    checks += bindings(orbit)+bindings(orbit_audit)
    assert orbit_audit['verdict'] == 'CERTIFIED_ACTUAL_SOURCE_CAUCHY_ORBIT_AND_FULL_STATIONARY_LINEARIZATION'
    phase = record['physical_phase_restoration']
    indices = source['complement']; omega = source['frequency']
    rp = [orbit['primal_integer_rates'][i] for i in indices]
    rd = [orbit['independent_dual_integer_rates'][i] for i in indices]
    assert list(map(s.sympify, phase['primal_complement_rates'])) == rp
    assert list(map(s.sympify, phase['dual_complement_rates'])) == rd
    Rp = s.SparseMatrix(240, 240, {(i, i): x for i, x in enumerate(rp)})
    Rd = s.SparseMatrix(240, 240, {(i, i): x for i, x in enumerate(rd)})
    eq(Rd*E+E*Rp, s.zeros(240)); assert Rd != -Rp
    t, initial_t = s.symbols('time initial_time', real=True)
    phase_generators = []
    for rates in (rd, rp):
        phase_generators.append(polynomial_real_action(s.I*omega*s.diag(*rates)))
    for rate in set(rd+rp):
        angle = omega*rate*t
        rotation = s.Matrix([[s.cos(angle), -s.sin(angle)], [s.sin(angle), s.cos(angle)]])
        angular = s.Matrix([[0, -omega*rate], [omega*rate, 0]])
        eq(rotation.diff(t), angular*rotation)
        eq((rotation.T*rotation).applyfunc(s.trigsimp), s.eye(2))
        eq((rotation.subs(t, initial_t)*rotation.subs(t, -initial_t)).applyfunc(s.trigsimp), s.eye(2))
    for generator_phase in phase_generators: eq(generator_phase+generator_phase.T, s.zeros(480))
    print('PASS independently certified actual source orbit, distinct dual/primal endpoint rotations and retarded delta identity', flush=True)

    paths = [Path(__file__), path, HERE/'source_full_linear_retarded.py',
        HERE/'independent_source_full_linear_split.py', HERE/'independent_source_full_linear_split.json',
        HERE/'source_full_linear_split.json', HERE/'scalar_canonical_phase.json',
        HERE/'scalar_momentum_energy.json', HERE/'independent_scalar_momentum_energy.json',
        HERE/'independent_source_stationary_cauchy_orbit.py', HERE/'independent_source_stationary_cauchy_orbit.json',
        HERE/'source_stationary_cauchy_orbit.json']
    result = {'root': ROOT_ID, 'source_sha256': raw.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'verdict': 'CERTIFIED_COMPLETE1082_SOURCE_RETARDED_INVERSE_AND_ACTUAL_ORBIT_TIME_PROPAGATOR',
        'candidate_constructor_imported': False, 'source_binding_checks': checks,
        'independent_method': 'original raw density coefficients; polynomial inverse certificate verification with complete component coverage; original scalar momentum elimination; direct24-state exact solve and full1082 backwrite',
        'matter_inverse': matter,
        'scalar_inverse': {'original70_projected_both_sides': True, 'canonical122_both_sides': True,
            'momentum_sign_and_Gram_placement_from_original_density': True},
        'complete_arbitrary_forcing': {'dimension': 1082, 'order': ['independent_dual480', 'scalar122', 'primal480'],
            'two_sided_proof': 'Each diagonal inverse is certified on both sides over the full source polynomial field. Forward substitution gives Rd, Rs(BRd+fs), Rp(CRs(BRd+fs)+fp); substituting source forcing (zI-A)u cancels successively in the same three rows. This verifies both inverse orientations for arbitrary full1082 data, not only the concrete witness.',
            'all_original_cross_maps_retained': True},
        'exact_time_consumer': {'invariant_dimension': 24, 'full_dimension': 1082,
            'momentum': list(map(str, momentum)), 'third_derivative': str(observed),
            'invariant_embedding_and_initial_identity': True, 'direct_linear_solve_agrees_with_full_resolvent': True,
            'Galerkin_or_time_series_truncation': False},
        'retarded_analytic_argument': {
            'alpha': str(alpha), 'beta': str(beta), 'all_three_real_momentum_directions': True,
            'source_scalar_comparison_energy_consumed': True,
            'whole_bound': 'exp(beta*abs(t))*(2+m(k)+m(k)*(b+c)*abs(t)+m(k)*b*c*t^2/2)',
            'Duhamel_reason': 'The only off-block paths have one or two edges. Each integration simplex has volume |t| or t^2/2, while all diagonal flow products are bounded by exp(beta*abs(t)), with exactly one scalar factor m(k).',
            'Laplace_and_delta': 'For Re(z)>beta the matrix exponential bound gives absolute Laplace convergence; integration by parts gives (zI-A)^-1. The jump E(0)=I gives (partial_t-A)(Theta(t)E)=delta I. The rational certificates represent this same inverse, with any removable written denominator zeros interpreted by continuation.',
            'uniform_bound_for_active126_claimed': False, 'positive_comparison_norm_is_physical_Hilbert': False},
        'actual_original_phase': {'all_time_orbit_independently_certified': True,
            'different_independent_dual_and_primal_rates_retained': True,
            'endpoint_formula': 'R(t) Theta(t-s) exp((t-s)Astat(k)) R(s)^-1',
            'public_time_state_API': 'retarded_time_expression/original_time_state return the ordinary finite exponential factor; the retarded distribution is assembled by multiplying by Theta(t-s), with zero past. A negative-time ordinary factor alone is not the retarded propagator.',
            'equation': 'Aoriginal(t,k)=Rprime(t)R(t)^-1+R(t)Astat(k)R(t)^-1; differentiating both endpoints gives the original homogeneous equation and the jump R(s)R(s)^-1=I.',
            'orthogonal_endpoint_maps_preserve_bounds': True, 'proper_clock': 'tau=N*t'},
        'interacting_composite_spectral_measure_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'independent_source_full_linear_retarded.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS independent complete source retarded audit', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
