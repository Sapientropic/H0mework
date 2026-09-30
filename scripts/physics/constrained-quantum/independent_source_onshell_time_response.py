#!/usr/bin/env python3
"""Independent original source Cauchy audit at zero and nonzero transfer energy.

Use already audited source affine maps, direct matrix powers and the original
289 polynomial action. The new time/response constructors are not imported.
The new nonzero-frequency external legs and currents are rebuilt separately.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix as DM

from independent_source_forced_hamiltonian_reduction import (
    HERE, BASE, ROOT, ROOT_ID, LAM, DOMAIN, FIELD, Z, matrix, saved, eye,
    zero, coefficient, original_operator, decode, check_bindings)
from independent_source_onshell_phase_forcing import raw_canonical_reader, evaluated, equal
from independent_source_spatial_active_phase_splice import RawSpatialActive, exact
from independent_source_common_phase_time import check_compact, matrix_bounds, absolute_bound, real_phase
from independent_source_gauge_legendre import realify
from independent_source_joint_temporal_rates import encode


def constant(M): return M.convert_to(DOMAIN).to_sparse()


def degree(M):
    return max((power[0] for row in M.rep.values() for entry in row.values() for power in entry), default=-1)


def value_at(M, z):
    z = DOMAIN.from_sympy(s.sympify(z))
    result = DM.zeros(M.shape, DOMAIN)
    for n in range(degree(M)+1): result += constant(coefficient(M, n)).scalarmul(z**n)
    return result


def new_actual_sources(candidate, raw):
    names = ['matter-vertices/receipt.json', 'matter-vertices/exchange.json',
        'matter-modes/source.json', 'full-phase/receipt.json', 'kinetic-residue/receipt.json']
    vertices, exchange, modes, phase, residue = [json.loads((BASE/name).read_text()) for name in names]
    checks = sum(check_bindings(row) for row in (vertices, exchange, modes, phase, residue))
    assert candidate['source_sha256'] == vertices['source_sha256'] == modes['source_sha256']
    F = decode(modes['source_isometry']); Q = decode(phase['phase_generator'])
    H0 = decode(modes['original_H_constant']); Hs = list(map(decode, modes['original_H_spatial']))
    D = decode(vertices['full_stationary_Dirac_operator'])
    norm = s.sympify(residue['right_normalization_factor']); spin_scale = s.sympify(residue['source_spin_scale'])
    kinetic = decode(residue['kinetic_pair_matrix'])
    S = s.SparseMatrix(s.kronecker_product(raw.raw.gamma[0]*s.diag(-1, -1, 1, 1), s.eye(63)))
    scale, omega = s.sympify(modes['time_scale']), s.sympify(phase['source_frequency'])
    a = 3*s.sqrt(2)/8
    high, low = s.Matrix([-a, 0, 4*a/3]), s.Matrix([0, 0, -2*a/3])
    legs = []
    for degree0, k, supplied in zip((4, 4, 2, 2), (high, low, low, high), candidate['legs'], strict=True):
        radius = s.sqrt((k.T*k)[0]); direction = k/radius
        spin = s.Matrix([0, 1]) if direction[2] == -1 else s.Matrix([1+direction[2], direction[0]+s.I*direction[1]])/s.sqrt(2*(1+direction[2]))
        block = next(b for b in modes['blocks'] if b['degree'] == degree0 and b['chirality'] == 1 and b['kind'] == 'singlet')
        u = s.SparseMatrix(F[:, block['first_column']:block['first_column']+2]*spin)
        H = scale*(H0+sum((k[j]*Hs[j]/s.sqrt(2) for j in range(3)), s.SparseMatrix.zeros(252)))
        energy = s.simplify((u.H*H*u)[0]); stationary = energy-omega*block['phase_charge']
        derivative = -s.I*stationary
        symbol = evaluated(D, k, derivative)
        equal(H*u, energy*u); equal(symbol*u, s.zeros(252, 1)); equal(u.H*S*symbol, s.zeros(1, 252))
        equal(Q*u, block['phase_charge']*u)
        assert s.simplify((u.H*u)[0]) == 1
        assert s.simplify((norm*u).H*kinetic*(norm*u))[0] == 1
        equal(u, decode(supplied['vector'])); equal(norm*u, decode(supplied['action_vector']))
        equal(k, decode(supplied['momentum']))
        assert energy == s.sympify(supplied['energy'])
        legs.append(dict(u=norm*u, k=k, derivative=derivative, energy=energy))
    assert [leg['energy'] for leg in legs] == [51*s.sqrt(15)/100, 21*s.sqrt(15)/50, 21*s.sqrt(15)/50, 51*s.sqrt(15)/100]
    assert legs[0]['energy']+legs[2]['energy'] == legs[1]['energy']+legs[3]['energy']
    equal(legs[0]['k']+legs[2]['k'], legs[1]['k']+legs[3]['k'])
    operators = {row['field']: decode(row['operator']) for row in vertices['active_289_bosonic_source_operators']}
    order = exchange['source_field_indices']
    injection = s.SparseMatrix(289, 97, {(field, j): 1 for j, field in enumerate(order)})
    def pairing(V, outgoing, incoming):
        right = evaluated(V, incoming['k'], incoming['derivative'])
        left = evaluated(V, outgoing['k'], outgoing['derivative'])
        return s.simplify((outgoing['u'].H*S*(right*incoming['u']))[0]+((left*outgoing['u']).H*S*incoming['u'])[0])
    def current(outgoing, incoming): return s.SparseMatrix([s.simplify(spin_scale*pairing(operators[field], outgoing, incoming)/2) for field in order])
    records = []
    for out, inc, supplied in zip((1, 3), (0, 2), candidate['currents'], strict=True):
        j = current(legs[out], legs[inc]); z = s.simplify(legs[inc]['derivative']-legs[out]['derivative'])
        k = legs[inc]['k']-legs[out]['k']
        equal(j, decode(supplied['current97'])); equal(injection*j, decode(supplied['current289']))
        factored = s.SparseMatrix(injection*j*s.sqrt(10)).applyfunc(s.simplify)
        equal(factored, decode(supplied['factored_current289']))
        assert s.sympify(supplied['physical_current_factor']) == 1/s.sqrt(10)
        for key in ('local_source_compatibility_map', 'independent_dual_source_map'):
            M = evaluated(decode(exchange[key]), k, z); equal(M*j, s.zeros(M.rows, 1))
        scalar = next(row for row in exchange['source_contact_terms'] if row['groups'] == ['scalar_Ward'])
        equal(evaluated(decode(scalar['source_map']), k, z)*j, s.zeros(9, 1))
        for row in vertices['primitive_vertices']:
            if row['group'] == 'scalar': assert pairing(decode(row['operator']), legs[out], legs[inc]) == 0
        assert z != 0 and s.re(z) == 0
        records.append(dict(k=tuple(k), frequency=z, factor=1/s.sqrt(10), current=exact(factored), actual=injection*j, current97=j))
    equal(current(legs[3], legs[0]), s.zeros(97, 1)); equal(current(legs[1], legs[2]), s.zeros(97, 1))
    return records, exchange, checks, {'energies': list(map(str, [leg['energy'] for leg in legs])),
        'full252_primal_and_independent_dual_shells': True, 'source_kinetic_residue_norm': True,
        'actual97_vertex_currents': True, 'source70_scalar_and24_dual_contractions_zero': True,
        'total_two_body_energy_and_momentum': True, 'current_geometric_factor_restored': '1/sqrt(10)'}


def source_operators(raw, canonical, scalar_reader, A0reader, de, dA, source, forced, spatial, old, sign):
    k, z, j = source['k'], source['frequency'], source['current']
    A = exact(decode(old['Hamiltonian_generator']) if sign == 1 else decode(old['Hamiltonian_generator']).conjugate())
    X = exact(decode(spatial['active_embedding']))
    slice_reader = matrix(s.Matrix.vstack(de[(1, 2, 3, 6, 7, 11), :], raw.phase.spatial.at(raw.phase.spatial.reader, k)*dA[12:, :]))
    ward = matrix(evaluated(raw.ward, k, LAM)); slice_inverse = constant(slice_reader*ward).inv().convert_to(FIELD)
    fix = lambda value: value-ward*slice_inverse*slice_reader*value
    L = fix(saved(forced['full289_field_lift']))
    particular = fix(saved(forced['full289_field_particular'])*matrix(j.to_Matrix()))
    F = saved(forced['physical_forcing'])*matrix(j.to_Matrix())
    Wsource = saved(forced['original_Ward_map'])
    zero(value_at(Wsource, z)*j)
    f = value_at(F, z)
    assert not f.is_zero_matrix
    B = DM.zeros((289, 126), DOMAIN); Qvalue = DM.zeros(B.shape, DOMAIN)
    for n in range(degree(L)+1):
        Ln = constant(coefficient(L, n)); B += Ln*A**n
        for r in range(n): Qvalue += (Ln*A**r).scalarmul(DOMAIN.from_sympy(z)**(n-1-r))
    affine = value_at(particular, z)+Qvalue*f
    M0, M1 = [constant(coefficient(canonical, n)) for n in range(2)]
    S0, S1 = [constant(coefficient(scalar_reader, n)) for n in range(2)]
    zero(M0*B+M1*B*A-X)
    zf = DOMAIN.from_sympy(z)
    affine_phase = (M0+M1.scalarmul(zf))*affine+M1*B*f
    Hpoly = original_operator(raw.raw.active, k)
    H = [constant(coefficient(Hpoly, n)) for n in range(degree(Hpoly)+1)]
    homogeneous = sum((Hr*B*A**n for n, Hr in enumerate(H)), DM.zeros(B.shape, DOMAIN))
    zero(homogeneous)
    source_euler = value_at(Hpoly, z)*affine
    for n in range(1, len(H)):
        for r in range(n): source_euler += (H[n]*B*A**r*f).scalarmul(zf**(n-1-r))
    zero(source_euler-j)
    assert not (value_at(Hpoly, z)*affine).is_zero_matrix
    base, normal = [exact(raw.phase.at(value, k)) for value in (raw.phase.G12base, raw.phase.Piphi)]
    orbit = exact(raw.raw.O.T); sourceA0 = exact(A0reader)*j
    shift = exact(raw.raw.Ob*(raw.raw.Ob.T*raw.raw.Ob).inv()*raw.raw.S.T)*sourceA0
    scalar_dynamic = S0*B+S1*B*A
    scalar_affine = (S0+S1.scalarmul(zf))*affine+S1*B*f
    zero(base*X+orbit*scalar_dynamic); zero(scalar_dynamic-normal*X)
    zero(base*affine_phase+orbit*scalar_affine-sourceA0)
    zero(scalar_affine-normal*affine_phase-shift)
    zero(constant(slice_reader)*B); zero(constant(slice_reader)*affine)
    assert not affine.is_zero_matrix and not shift.is_zero_matrix
    wrong_ward, wrong_force = value_at(Wsource, 0)*j, f-value_at(F, 0)
    if z != 0: assert not wrong_ward.is_zero_matrix and not wrong_force.is_zero_matrix
    return dict(A=A, X=X, B=B, f=f, affine=affine, affine_phase=affine_phase,
        M0=M0, M1=M1, S0=S0, S1=S1, H=H, Hpoly=Hpoly, base=base, normal=normal,
        orbit=orbit, sourceA0=sourceA0, shift=shift, slice_reader=constant(slice_reader),
        wrong_force=wrong_force, fix=fix)


def whole_time_consumer(data, source, supplied, nonzero):
    A, B, X, f, a, ap = [data[name] for name in ('A', 'B', 'X', 'f', 'affine', 'affine_phase')]
    z, factor = source['frequency'], source['factor']; zf = DOMAIN.from_sympy(z)
    order = 20
    # Explicit sums of powers, independently of the producer's rate recurrence.
    powers = [f]
    for _ in range(order+len(data['H'])+1): powers.append(A*powers[-1])
    rates, fields, phases = [], [], []
    for n in range(order+len(data['H'])+2):
        wn = sum((powers[n-1-r].scalarmul(zf**r) for r in range(n)), DM.zeros(f.shape, DOMAIN))
        rates.append(wn); fields.append(B*wn+a.scalarmul(zf**n)); phases.append(X*wn+ap.scalarmul(zf**n))
    assert rates[0].is_zero_matrix and not fields[0].is_zero_matrix and not fields[1].is_zero_matrix
    for n in range(order+1):
        zero(rates[n+1]-A*rates[n]-f.scalarmul(zf**n))
        zero(sum((Hr*fields[n+r] for r, Hr in enumerate(data['H'])), DM.zeros(source['current'].shape, DOMAIN))-source['current'].scalarmul(zf**n))
        Pi = data['S0']*fields[n]+data['S1']*fields[n+1]
        zero(data['base']*phases[n]+data['orbit']*Pi-data['sourceA0'].scalarmul(zf**n))
        zero(Pi-data['normal']*phases[n]-data['shift'].scalarmul(zf**n))
        zero(data['M0']*fields[n]+data['M1']*fields[n+1]-phases[n])
    saved_time = supplied['time_consumer'] if nonzero else supplied['actual_time_consumer']
    betaA = s.sympify(saved_time['generator_norm_upper'] if nonzero else saved_time['source_generator_norm_upper'])
    boundsA = matrix_bounds(A)
    assert s.simplify(betaA**2-boundsA['row']*boundsA['column']) >= 0
    beta = betaA+s.ceiling(abs(z)) if nonzero else betaA
    assert beta >= betaA+abs(z)
    h = 1/(2*beta)
    assert h == s.sympify(saved_time['elapsed_source_time'])
    if nonzero: assert beta == s.sympify(saved_time['generator_plus_frequency_upper'])
    partial_field = sum((fields[n].scalarmul(DOMAIN.from_sympy(h**n/s.factorial(n))) for n in range(order+1)), DM.zeros((289, 1), DOMAIN))
    partial_phase = sum((phases[n].scalarmul(DOMAIN.from_sympy(h**n/s.factorial(n))) for n in range(order+1)), DM.zeros((1214, 1), DOMAIN))
    check_compact(partial_field, saved_time['factored_field_Taylor_readback' if nonzero else 'factored_partial_field289'])
    check_compact(partial_phase, saved_time['factored_phase_Taylor_readback' if nonzero else 'factored_partial_phase1214'])
    bound = lambda v: sum(absolute_bound(value) for value in v.to_Matrix())
    force_bound = bound(f)
    assert s.simplify(force_bound-s.sympify(saved_time['force_norm_upper' if nonzero else 'source_force_norm_upper'])) == 0
    boundsB, boundsX = matrix_bounds(B), matrix_bounds(X)
    assert boundsB['integer'] == saved_time['field_embedding_norm_upper']
    assert boundsX['integer'] == saved_time['phase_embedding_norm_upper']
    denominator = 2**(order+1)*s.factorial(order+1)
    response_error = 2*force_bound/(beta*denominator)
    affine_error, phase_affine_error = (2*bound(a)/denominator, 2*bound(ap)/denominator) if nonzero else (0, 0)
    field_error = s.simplify(factor*(boundsB['integer']*response_error+affine_error))
    phase_error = s.simplify(factor*(boundsX['integer']*response_error+phase_affine_error))
    assert s.simplify(field_error-s.sympify(saved_time['physical_field_remainder_upper'])) == 0
    assert s.simplify(phase_error-s.sympify(saved_time['physical_phase_remainder_upper'])) == 0
    assert field_error > 0 and phase_error > 0
    if nonzero:
        zero(a-exact(decode(saved_time['nonzero_total_initial_field'])))
        check_compact(fields[1], saved_time['nonzero_initial_field_rate'])
        zero(data['sourceA0']-exact(decode(saved_time['source_Gauss_amplitude12'])))
        zero(data['shift']-exact(decode(saved_time['normal_scalar_momentum_amplitude70'])))
    else:
        zero(a-exact(decode(supplied['factored_initial_source_field289'])))
        zero(fields[1]-exact(decode(supplied['factored_initial_field_rate289'])))
        check_compact(ap, supplied['factored_initial_source_phase1214'])
        zero(data['sourceA0']-exact(decode(supplied['factored_nonzero_source_Gauss12'])))
        zero(data['shift']-exact(decode(supplied['factored_normal_scalar_momentum_shift70'])))
    return {'frequency': str(z), 'momentum': list(map(str, source['k'])),
        'full289_all_order_identity': True, 'full12_Gauss_and_normal_scalar_graph': True,
        'whole21_derivative_vectors': True, 'zero_physical_initial_and_nonzero_original_initial_field': True,
        'source_normalization': str(factor), 'elapsed_source_time': str(h),
        'source_generator_norm_upper': str(betaA), 'source_generator_plus_frequency_upper': str(beta),
        'field_remainder_upper': str(field_error), 'phase_remainder_upper': str(phase_error),
        'wrong_zero_frequency_current_and_forcing_rejected': bool(nonzero)}, {
            'fields': fields, 'phases': phases, 'partial_field': partial_field, 'partial_phase': partial_phase, 'h': h}


def nonzero_tree(source, data, supplied, exchange):
    A, f, z = data['A'], data['f'], source['frequency']
    xi = (DM.eye(A.shape, DOMAIN).scalarmul(DOMAIN.from_sympy(z))-A).lu_solve(f)
    zero(xi-exact(decode(supplied['factored_source_response126'])))
    zero(f-exact(decode(supplied['factored_source_forcing126'])))
    field = data['B']*xi+data['affine']; phase = data['X']*xi+data['affine_phase']
    zero(field-exact(decode(supplied['factored_full289_response'])))
    check_compact(phase, supplied['factored_common_phase1214_response'])
    check_compact(data['affine_phase'], supplied['factored_affine_phase1214'])
    check_compact(data['wrong_force'], supplied['wrong_zero_frequency_forcing_nonzero_defect'])
    zero(value_at(data['Hpoly'], z)*field-source['current'])
    k = source['k']; j97 = exact(s.SparseMatrix(source['current97']/source['factor']).applyfunc(s.simplify))
    A79 = exact(evaluated(decode(exchange['canonical_operator']), k, z))
    J79 = exact(evaluated(decode(exchange['canonical_source_map']), k, z))
    dynamic79 = A79.lu_solve(J79*j97)
    local = exact(evaluated(decode(exchange['contact_field_response']), k, z))*j97
    dynamic = exact(evaluated(decode(exchange['canonical_field_lift']), k, z))*dynamic79
    zero(field-value_at(data['fix'](matrix((local+dynamic).to_Matrix())), z))
    equal((value_at(data['Hpoly'], z)*field).to_Matrix()*source['factor'], source['actual'])
    return field, local, dynamic


def original_phase(raw, data, vectors, supplied, source):
    saved_orbit = supplied['original_orbit_phase']
    unit = s.Rational(12, 13)+s.I*s.Rational(5, 13); omega = 18*s.sqrt(15)/125
    internal = [(degree, word) for degree in (6, 2, 4) for word in itertools.combinations(range(7), degree)]
    rp = [1-2*int(spin >= 2)-2*int(degree == 6) for spin in range(4) for degree, _ in internal]
    rd = [1-2*int(spin >= 2)+2*int(degree == 6) for spin in range(4) for degree, _ in internal]
    Up = s.diag(*[s.expand_complex(unit**r) for r in rp]); Ud = s.diag(*[s.expand_complex(unit**r) for r in rd])
    S = real_phase(rp, omega, unit)
    phase, field = vectors['partial_phase'], vectors['partial_field']
    coframe_rows = [raw.indices['coframe', (a, mu)] for a in range(4) for mu in range(4)]
    de = field.extract(coframe_rows, [0]).to_Matrix().reshape(4, 4)
    chain = saved_orbit['full_delta_chi_E_and_source_chi_deltaE_chain']
    equal(de, decode(chain['actual_full_original_coframe_variation']))
    assert de[:, 0].todok()
    E = raw.source['principal'][0]
    dE = s.kronecker_product(raw.raw.coefficient_derivatives(raw.e, de)[1][0], s.eye(63))
    equal(Ud*E*Up, E); equal(Ud*dE*Up, dE)
    vector = phase.to_Matrix(); p = (-vector[962:, :]-s.I*vector[710:962, :]).T
    dchi = (s.I*p-raw.raw.chi0*dE)*E.inv()
    canonical = -s.I*(dchi*Ud*E+raw.raw.chi0*Ud*dE)
    equal(canonical, p*Up.inv())
    moved_phase = (S*phase).to_Matrix()
    equal((-moved_phase[962:, :]-s.I*moved_phase[710:962, :]).T, canonical)
    omission = s.I*raw.raw.chi0*Ud*dE
    assert s.SparseMatrix(omission).todok(); equal(omission, decode(chain['omit_source_chi_deltaE_nonzero_defect']))
    fullU, fullK = s.SparseMatrix.eye(289), s.SparseMatrix.zeros(289)
    for label, U, rates in (('primal_H', Up, rp), ('dual_H', Ud, rd)):
        smallU = raw.occupied_real.T*realify(U)*raw.occupied_real
        smallK = raw.occupied_real.T*realify(s.I*omega*s.diag(*rates))*raw.occupied_real
        equal(realify(U)*raw.occupied_real, raw.occupied_real*smallU)
        ids = [raw.indices[label, (im, spin, color)] for im in range(2) for spin in range(4) for color in range(3)]
        for i, row in enumerate(ids):
            for j, col in enumerate(ids): fullU[row, col], fullK[row, col] = smallU[i, j], smallK[i, j]
    U, K = exact(fullU), exact(fullK)
    zero(U.transpose()*U-DM.eye((289, 289), DOMAIN)); zero(U*source['current']-source['current'])
    H = data['H']; actual_jets = []
    for r in range(len(H)):
        jet = sum(((K**(r-l)*vectors['fields'][l]).scalarmul(DOMAIN.from_sympy(s.binomial(r, l)))
            for l in range(r+1)), DM.zeros((289, 1), DOMAIN))
        actual_jets.append(U*jet)
    actual_euler = DM.zeros((289, 1), DOMAIN)
    for r in range(len(H)):
        shifted = sum(((H[n]*K**(n-r)).scalarmul(DOMAIN.from_sympy(s.binomial(n, r)*(-1)**(n-r)))
            for n in range(r, len(H))), DM.zeros((289, 289), DOMAIN))
        actual_euler += U*shifted*U.transpose()*actual_jets[r]
    zero(actual_euler-source['current'])
    check_compact(U*field, saved_orbit['factored_phase_rotated_field'])
    end = saved_orbit['exact_original_endpoint_readout']; rows = end['source_rows']
    initial_rotated = S*phase; values = []
    for row in rows:
        if 103 <= row < 607: base, local = 103, row-103
        elif 710 <= row < 1214: base, local = 710, row-710
        else:
            values.append(initial_rotated.to_Matrix()[row]); continue
        j = local % 252; angle = omega*rp[j]*vectors['h']
        left, right = initial_rotated.to_Matrix()[base+j], initial_rotated.to_Matrix()[base+252+j]
        values.append(s.cos(angle)*left-s.sin(angle)*right if local < 252 else s.sin(angle)*left+s.cos(angle)*right)
    equal(s.Matrix(values), decode(end['values']))
    return {'momentum': list(map(str, source['k'])), 'full289_original_nonzero_time_Euler_jets': True,
        'independent_dual_and_source_chi_deltaE_canonical_chain': True,
        'both_original_phase_endpoints': True, 'proper_clock': 'tau=N*t, N=3*sqrt(30)/25'}


def main():
    began = time.monotonic()
    names = ['source_onshell_cauchy_response.json', 'source_nonzero_frequency_onshell_response.json',
        'source_onshell_phase_forcing.json', 'independent_source_onshell_phase_forcing.json',
        'source_forced_hamiltonian_reduction.json', 'independent_source_forced_hamiltonian_reduction.json',
        'source_spatial_active_phase_splice.json', 'independent_source_spatial_active_phase_splice.json',
        'retained_hamiltonian_reduction.json', 'independent_source_common_phase_time.json']
    constant_candidate, nonzero_candidate, ingress, _, forced, _, spatial, _, catalog, _ = [json.loads((HERE/name).read_text()) for name in names]
    records = [json.loads((HERE/name).read_text()) for name in names]
    checks = sum(check_bindings(row) for row in records)
    assert all(row['root'] == ROOT_ID for row in records)
    raw = RawSpatialActive(); canonical, scalar_reader, A0reader, de, dA = raw_canonical_reader(raw)
    new_sources, exchange, checked, legs = new_actual_sources(nonzero_candidate, raw); checks += checked
    print('PASS independent nonzero-energy full252 legs, original currents and exact action normalization', flush=True)
    old = next(row for row in catalog['source_momenta'] if any(s.sympify(value) != 0 for value in row['momentum']))
    cases, phases, trees = [], [], []
    for nonzero, candidate in ((False, constant_candidate), (True, nonzero_candidate)):
        for i, sign in enumerate((1, -1)):
            if nonzero: source = new_sources[i]
            else:
                row = ingress['currents'][i]
                source = dict(k=tuple(decode(row['transfer'])[1:, 0]/s.I), frequency=s.S.Zero,
                    factor=s.sympify(row['physical_current_factor']), current=exact(decode(row['scaled_current289'])))
            data = source_operators(raw, canonical, scalar_reader, A0reader, de, dA, source,
                forced['source_momenta'][i], spatial['fibers'][i], old, sign)
            report, vectors = whole_time_consumer(data, source, candidate['consumers'][i], nonzero)
            cases.append(report)
            if nonzero: trees.append(nonzero_tree(source, data, candidate['consumers'][i], exchange))
            else: phases.append(original_phase(raw, data, vectors, candidate['consumers'][i], source))
            print('PASS complete289 all-order forced Cauchy, source12 Gauss,21 vector coefficients and strict time bounds', str(source['frequency']), sign, flush=True)
    direct = s.simplify(-(new_sources[1]['actual'].T*trees[0][0].to_Matrix())[0]*new_sources[0]['factor'])
    contact = s.simplify((new_sources[1]['actual'].T*trees[0][1].to_Matrix())[0]*new_sources[0]['factor'])
    dynamic = s.simplify((new_sources[1]['actual'].T*trees[0][2].to_Matrix())[0]*new_sources[0]['factor'])
    assert s.simplify(direct+contact+dynamic) == 0
    assert direct == s.sympify(nonzero_candidate['direct_tree_kernel'])
    assert contact == s.sympify(nonzero_candidate['Contact_bilinear']) == -81*s.sqrt(30)/1000
    assert dynamic == s.sympify(nonzero_candidate['canonical_dynamic_bilinear'])
    assert constant_candidate['current_not_switched_off_before_initial_time'] is True
    assert constant_candidate['zero_total_initial_field_or_Theta_truncated_Ward_current_used'] is False
    paths = [HERE/name for name in [*names, 'source_onshell_cauchy_response.py',
        'source_nonzero_frequency_onshell_response.py', 'independent_source_onshell_time_response.py',
        'independent_source_onshell_phase_forcing.py', 'independent_source_forced_hamiltonian_reduction.py',
        'independent_source_spatial_active_phase_splice.py', 'independent_source_common_phase_time.py']]
    result = {'root': ROOT_ID, 'source_sha256': ingress['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'verdict': 'CERTIFIED_TRUE_ONSHELL_ZERO_AND_NONZERO_FREQUENCY_COMMON_CAUCHY_RESPONSES',
        'checked_input_bindings': checks, 'candidate_constructors_imported': False,
        'source_cases': cases, 'actual_nonzero_frequency_legs': legs, 'original_orbit_phase': phases,
        'nonzero_frequency_tree': {'direct': str(direct), 'Contact': str(contact), 'canonical': str(dynamic)},
        'whole_time_argument': 'w^(n)(0)=sum_{r=0}^{n-1} A^(n-1-r) zeta^r f gives the entire unique solution wdot=A w+exp(zeta*t)f,w(0)=0. Complete matrix identities independently checked above imply every original289 Euler and full12 Gauss coefficient. Original field=Bw+affine*exp(zeta*t) has its generated nonzero initial field.',
        'strict_error_argument': 'The source row/column sums bound ||A||2 by260. At h=1/(2 beta), beta=260 or261>=||A||+|zeta|, exp(beta*h)<2. The inhomogeneous tail is <=2||f||1/(beta*2^21*21!), and a nonconstant affine exponential adds <=2||affine||1/(2^21*21!). Original source factors and the independently computed field/phase embedding norms are restored.',
        'current_scope': 'Actual specified full252 external states and the two signed nonzero spatial momenta. Currents exist throughout the Cauchy interval; no Heaviside cutoff or zero-initial original field is substituted. Imaginary-frequency tree values are meromorphic readbacks.',
        'quantum_spectrum_or_proton_lifetime_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_onshell_time_response.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent actual zero/nonzero on-shell source time responses', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
