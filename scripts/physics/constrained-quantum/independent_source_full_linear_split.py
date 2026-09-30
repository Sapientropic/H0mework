#!/usr/bin/env python3
"""Raw-density complete linear source split with its nonzero scalar cascade.

The occupied frame is rebuilt from exterior labels. All158 vertices come
from the original coframe principal, connection, volume and repaired wedge
Yukawa map. Real and imaginary field components are split before Fourier
substitution, while the independent dual is kept as an independent row.
"""
from __future__ import annotations

from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import time
import sympy as s

from independent_source_joint_temporal_rates import RawSource, HERE, BASE, ROOT, ROOT_ID, bindings, clean, decode, encode, eq, zero
from independent_source_gauge_legendre import ETA
from independent_source_gauss_quantum_current import polynomial_real_action
from independent_source_lorentz_contact import real_bilinear

P = s.symbols('p0:4', real=True)
K = s.symbols('k1:4', real=True)
SYMBOLS = {str(x): x for x in (*P, *K)}


def read_matrix(record):
    return s.SparseMatrix(*record['shape'], {(i, j): s.sympify(value, locals=SYMBOLS) for i, j, value in record['entries']})


def affine(matrix):
    result = [clean(matrix.subs(dict.fromkeys(P, 0))), *[clean(matrix.diff(p)) for p in P]]
    eq(matrix, result[0]+sum((p*M for p, M in zip(P, result[1:])), s.zeros(*matrix.shape)))
    assert all(not M.free_symbols for M in result)
    return result


def real_fourier(coefficients):
    return clean(polynomial_real_action(coefficients[0])+sum((s.I*k*polynomial_real_action(M)
        for k, M in zip(K, coefficients[1:])), s.zeros(2*coefficients[0].rows)))


def assemble(size, blocks):
    result = s.MutableSparseMatrix.zeros(size, size)
    for row, col, block in blocks:
        for (i, j), value in block.todok().items(): result[row+i, col+j] += value
    return clean(result)


def build_raw(raw):
    active = raw.active['actual_background']
    e = s.Matrix(active['coframe']).applyfunc(s.sympify)
    A = raw.A
    omega = s.Matrix(active['lowered_Lorentz_connection']).applyfunc(s.sympify)
    N = s.sympify(raw.active['source_lapse']); frequency = s.sympify(raw.active['source_frequency'])
    internal = [(degree, word) for degree in (6, 2, 4) for word in itertools.combinations(range(7), degree)]
    occupied = [63*spin+internal.index((2, (color, 5))) for spin in range(4) for color in range(3)]
    complement = [index for index in range(252) if index not in occupied]
    O = s.eye(252)[:, occupied]; C = s.eye(252)[:, complement]
    principal4 = raw.principals(e)
    principal = [s.kronecker_product(T, s.eye(63)) for T in principal4]
    phase = s.diag(*[(1 if spin >= 2 else -1)+2*int(degree == 6) for spin in range(4) for degree, _ in internal])
    spin = [s.kronecker_product(T, s.eye(63)) for T in raw.spin]
    connection = [clean(raw.action(A[mu, :], raw.rho252)+sum((omega[mu, a]*spin[a] for a in range(6)), s.zeros(252))) for mu in range(4)]
    Y = raw.yukawa(raw.v)
    D = clean(sum((principal[mu]*(P[mu]*s.eye(252)+connection[mu]) for mu in range(4)), s.zeros(252))+
        N*Y-s.I*frequency*principal[0]*phase)
    vertices = []
    for mu in range(4):
        for a in range(12): vertices.append(('gauge_A', [mu, a], clean(principal[mu]*raw.rho252[a])))
    for mu in range(4):
        for a in range(6): vertices.append(('Lorentz', [mu, a], clean(principal[mu]*spin[a])))
    for a in range(4):
        for nu in range(4):
            direction = s.zeros(4); direction[a, nu] = 1
            dvolume, dprincipal4, _ = raw.coefficient_derivatives(e, direction)
            dprincipal = [s.kronecker_product(T, s.eye(63)) for T in dprincipal4]
            V = sum((dprincipal[mu]*(P[mu]*s.eye(252)+connection[mu]) for mu in range(4)), s.zeros(252))
            V += dvolume*Y-s.I*frequency*dprincipal[0]*phase
            vertices.append(('coframe', [a, nu], clean(V)))
    for a, Ya in enumerate(raw.Y): vertices.append(('scalar', [int(a >= 35), a % 35], clean(N*Ya)))
    return {'e': e, 'N': N, 'frequency': frequency, 'O': O, 'C': C, 'occupied': occupied, 'complement': complement,
        'principal': principal, 'phase': phase, 'D': D, 'vertices': vertices, 'connection': connection, 'Y': Y}


def main():
    began = time.monotonic(); path = HERE/'source_full_linear_split.json'
    candidate = json.loads(path.read_text()); checks = bindings(candidate)
    raw = RawSource(); source_data = build_raw(raw)
    assert candidate['root'] == ROOT_ID and candidate['source_sha256'] == raw.hashes
    occupied = json.loads((BASE/'occupied-response/receipt.json').read_text())
    vertices = json.loads((BASE/'matter-vertices/receipt.json').read_text())
    phase = json.loads((BASE/'full-phase/receipt.json').read_text())
    scalar = json.loads((HERE/'scalar_canonical_phase.json').read_text())
    for record in (occupied, vertices, phase, scalar): checks += bindings(record)
    O, C, N = source_data['O'], source_data['C'], source_data['N']
    indices_O, indices_C = source_data['occupied'], source_data['complement']
    projector = O*O.H
    eq(O, read_matrix(occupied['occupied_frame'])); eq(O, read_matrix(candidate['source_inventory']['occupied_frame']))
    eq(projector, read_matrix(candidate['source_inventory']['occupied_Hermitian_projector']))
    eq(C, read_matrix(candidate['source_inventory']['complement_frame']))
    eq(O.H*O, s.eye(12)); eq(C.H*C, s.eye(240)); eq(O.H*C, s.zeros(12, 240))
    eq(projector, projector.H); eq(projector*projector, projector)
    eq(projector+C*C.H, s.eye(252))
    D = source_data['D']; E = source_data['principal'][0]
    eq(D, N*read_matrix(vertices['full_stationary_Dirac_operator']))
    eq(source_data['phase'], read_matrix(phase['phase_generator']))
    K0 = clean(D.subs(dict.fromkeys(P, 0)))
    eq(K0, N*read_matrix(phase['stationary_primal_constant']))
    eq(K0*raw.psi0, s.zeros(252, 1)); eq(raw.chi0*K0, s.zeros(1, 252))
    dual_phase = clean(E*source_data['phase']*E.inv())
    for matrix in [*source_data['principal'], *[V for group, _, V in source_data['vertices'] if group == 'scalar']]:
        eq(dual_phase*matrix, matrix*source_data['phase'])
    for matrix in [*source_data['principal'], K0, source_data['Y'], source_data['phase'],
            sum((source_data['principal'][mu]*source_data['connection'][mu] for mu in range(4)), s.zeros(252))]:
        eq(matrix.extract(indices_C, indices_O), s.zeros(240, 12)); eq(matrix.extract(indices_O, indices_C), s.zeros(12, 240))
    print('PASS occupied frame from original exterior labels, Hermitian projector and both stationary Dirac/phase blocks', flush=True)

    counts = Counter(); right_scalar = left_scalar = 0
    scalar_vertices = []
    for (group, coordinate, V), saved, inventory in zip(source_data['vertices'], vertices['primitive_vertices'], candidate['source_inventory']['all158_coefficient_checks']):
        assert (group, coordinate) == (saved['group'], saved['coordinate']) == (inventory['group'], inventory['coordinate'])
        eq(V, read_matrix(saved['operator']))
        cross = []
        for matrix in affine(V):
            right, left = matrix.extract(indices_C, indices_O), matrix.extract(indices_O, indices_C)
            cross.append([len(right.todok()), len(left.todok())])
        assert cross == inventory['cross_nonzero_entries_constant_p0_p1_p2_p3']
        if group == 'scalar':
            scalar_vertices.append(V)
            right_scalar += bool(V.extract(indices_C, indices_O).todok())
            left_scalar += bool(V.extract(indices_O, indices_C).todok())
            eq(raw.chi0*V, s.zeros(1, 252))
        else: assert all(right == left == 0 for right, left in cross)
        counts[group] += 1
    assert sum(counts.values()) == len(source_data['vertices']) == 158
    assert dict(counts) == candidate['source_inventory']['primitive_counts']
    assert right_scalar == 24 and left_scalar == 0
    B70 = clean(s.Matrix.hstack(*((V*raw.psi0).extract(indices_C, [0]) for V in scalar_vertices)))
    eq(B70, read_matrix(candidate['source_inventory']['actual_scalar_source']))
    assert B70.rank() == 9 and B70.applyfunc(s.re).col_join(B70.applyfunc(s.im)).rank() == 18
    P61 = raw.P61; R = P61[:, list(P61.rref()[1])]; Ginv = clean((R.T*R).inv())
    J = raw.O[:, raw.active['J_independent_columns']]
    eq(R, read_matrix(candidate['scalar_peripheral61_frame'])); eq(J, read_matrix(candidate['scalar_active9_frame']))
    eq(B70*J, s.zeros(240, 9)); eq(B70*P61, B70)
    eq(R*Ginv*R.T+J*(J.T*J).inv()*J.T, s.eye(70))
    print('PASS all158 raw vertices/all790 incoming coefficient matrices; actual24 scalar crosses and source9complex/18real image retained', flush=True)

    # Derive the full70 scalar Euler symbol from its original density.
    h = raw.metric(source_data['e'])
    RA = [raw.action(raw.A[mu, :], raw.rho70) for mu in range(4)]
    for T in RA:
        eq(T*raw.v, s.zeros(70, 1)); eq(T*P61, P61*T)
    scalar_symbol = clean(-sum((h[mu, nu]*(P[mu]*s.eye(70)+RA[mu])*(P[nu]*s.eye(70)+RA[nu])
        for mu in range(4) for nu in range(4)), s.zeros(70))-2*N*s.eye(70))
    eq(scalar_symbol, read_matrix(candidate['full_scalar_operator']))
    eq(J.T*scalar_symbol*R, s.zeros(9, 61)); eq(R.T*scalar_symbol*J, s.zeros(61, 9))
    for mu in range(4): eq(R.T*(P[mu]*s.eye(70)+RA[mu])*raw.O, s.zeros(61, 12))
    active = raw.active
    H289 = s.MutableSparseMatrix.zeros(289, 289)
    for row, col, powers, value in active['Fourier_Jacobi_entries']:
        H289[row, col] += s.sympify(value)*s.prod(p**n for p, n in zip(P, powers))
    groups = {group: [i for i, field in enumerate(active['fields']) if field['group'] == group] for group in ('scalar_J', 'primal_H', 'dual_H')}
    D12 = D.extract(indices_O, indices_O)
    eq(H289.extract(groups['scalar_J'], groups['scalar_J']), J.T*scalar_symbol*J)
    eq(H289.extract(groups['dual_H'], groups['primal_H']), real_bilinear(D12))
    eq(H289.extract(groups['primal_H'], groups['dual_H']), real_bilinear(D12.subs({p: -p for p in P}, simultaneous=True)).T)
    by_key = {(group, tuple(coordinate)): V for group, coordinate, V in source_data['vertices']}
    mixed_bosons = 0
    for row, field in enumerate(active['fields']):
        key = field['group'], tuple(field['coordinate'])
        if key in by_key: V = by_key[key]
        elif field['group'] == 'scalar_J':
            V = clean(sum((J[a, field['coordinate'][0]]*scalar_vertices[a] for a in range(70)), s.zeros(252)))
        else: continue
        mixed_bosons += 1
        for col in groups['primal_H']:
            imaginary, spin, color = active['fields'][col]['coordinate']
            value = (raw.chi0*V)[indices_O[3*spin+color]]
            zero(s.re(s.I**imaginary*value).expand()-H289[row, col])
        for col in groups['dual_H']:
            imaginary, spin, color = active['fields'][col]['coordinate']
            value = (V.subs(dict.fromkeys(P, 0))*raw.psi0)[indices_O[3*spin+color]]
            zero(s.re(s.I**imaginary*value).expand()-H289[row, col])
    assert mixed_bosons == 97
    print('PASS original scalar70/active9 split and every original289 matter/scalar/97boson mixed leg', flush=True)

    # The real scalar canonical pair follows Pi=-dot(phi)/N. It is generated
    # here from that original kinetic density, not read from the candidate.
    spatial_scalar = sum(((s.I*k*s.eye(70)+RA[i+1])**2 for i, k in enumerate(K)), s.zeros(70))+2*s.eye(70)
    As = s.zeros(122); As[:61, 61:] = -N*Ginv
    As[61:, :61] = clean(-N*R.T*spatial_scalar*R)
    eq(As, read_matrix(scalar['canonical_generator']))
    EC = E.extract(indices_C, indices_C); KC = K0.extract(indices_C, indices_C)
    ECinverse = EC.inv(); spatial_C = [matrix.extract(indices_C, indices_C) for matrix in source_data['principal'][1:]]
    primal = [clean(-ECinverse*KC), *[clean(-ECinverse*T) for T in spatial_C]]
    dual = [clean((KC*ECinverse).T), *[clean(-(T*ECinverse).T) for T in spatial_C]]
    Ap, Ad = real_fourier(primal), real_fourier(dual)
    B61 = clean(B70*R)
    primal_force, free = EC.gauss_jordan_solve(-B61); assert free.rows == 0
    Cblock = primal_force.applyfunc(s.re).col_join(primal_force.applyfunc(s.im)).row_join(s.zeros(480, 61))
    Jchi = B61.T.applyfunc(s.re).row_join(-B61.T.applyfunc(s.im))
    Bblock = s.zeros(61, 480).col_join(Jchi)
    eq(EC*primal[0]+KC, s.zeros(240)); eq(dual[0].T*EC-KC, s.zeros(240))
    for V, ap, ad in zip(spatial_C, primal[1:], dual[1:]):
        eq(EC*ap+V, s.zeros(240)); eq(ad.T*EC+V, s.zeros(240))
    eq(R*As[:61, :]*Bblock, -N*R*Ginv*Jchi)
    eq(Cblock*Bblock, s.zeros(480))
    cascade = clean(Cblock*As*Bblock); assert cascade.todok()
    blocks = {'dual': Ad, 'scalar': As, 'primal': Ap, 'dual_to_scalar': Bblock,
        'scalar_to_primal': Cblock, 'third_time_cascade': cascade}
    for name, value in blocks.items(): eq(value, read_matrix(candidate['triangular_tail'][name]))
    for A in (Ad, As, Ap): eq(A.subs({k: -k for k in K}, simultaneous=True), A.conjugate())
    print('PASS independent real dual480 -> scalar122 -> primal480 equations, force signs and nonzero cubic-time cascade', flush=True)

    # Rebuild the complete native1310 action before comparing its split.
    # Start in block coordinates and then permute into the old289 ordering.
    bosons = [i for i, field in enumerate(active['fields']) if field['group'] not in ('scalar_J', 'primal_H', 'dual_H')]
    boson_row = {index: row for row, index in enumerate(bosons)}
    assert len(bosons) == 232
    scalar_frame = J.row_join(R)
    scalar_reader = ((J.T*J).inv()*J.T).col_join(Ginv*R.T)
    matter_frame = s.Matrix.vstack(s.Matrix.hstack(O, s.zeros(252, 12), C, s.zeros(252, 240)),
                                  s.Matrix.hstack(s.zeros(252, 12), O, s.zeros(252, 240), C))
    natural_frame = assemble(1310, [(0, 0, s.eye(232)), (232, 232, scalar_frame),
        (302, 302, matter_frame), (806, 806, matter_frame)])
    natural_reader = assemble(1310, [(0, 0, s.eye(232)), (232, 232, scalar_reader),
        (302, 302, matter_frame.T), (806, 806, matter_frame.T)])
    permutation = s.MutableSparseMatrix.zeros(1310, 1310)
    for old, field in enumerate(active['fields']):
        group, coord = field['group'], field['coordinate']
        if old in boson_row: canonical = boson_row[old]
        elif group == 'scalar_J': canonical = 232+coord[0]
        else:
            imaginary, spin, color = coord
            canonical = (302 if group == 'primal_H' else 806)+12*imaginary+3*spin+color
        permutation[canonical, old] = 1
    for i in range(61): permutation[241+i, 289+i] = 1
    for i in range(480):
        permutation[326+i, 350+i] = 1
        permutation[830+i, 830+i] = 1
    T = clean(natural_frame*permutation); Ti = clean(permutation.T*natural_reader)
    eq(T*Ti, s.eye(1310)); eq(Ti*T, s.eye(1310))
    common = candidate['complete_common_action_carrier']
    eq(T, read_matrix(common['source_field_embedding'])); eq(Ti, read_matrix(common['source_field_retraction']))
    assert common['old_bosonic_field_indices'] == bosons
    adjoint = lambda M: clean(M.subs({p: -p for p in P}, simultaneous=True).T)
    full_pair = real_bilinear(D)
    original_blocks = [(0, 0, H289.extract(bosons, bosons)), (232, 232, scalar_symbol),
        (806, 302, full_pair), (302, 806, adjoint(full_pair))]
    for old in bosons:
        field = active['fields'][old]; row = boson_row[old]
        key = field['group'], tuple(field['coordinate'])
        if key in by_key:
            V = by_key[key]
            primal_reader = raw.chi0*V
            dual_reader = (V.subs(dict.fromkeys(P, 0))*raw.psi0).T
            primal_real = primal_reader.applyfunc(s.re).row_join(-primal_reader.applyfunc(s.im))
            dual_real = dual_reader.applyfunc(s.re).row_join(-dual_reader.applyfunc(s.im))
            original_blocks += [(row, 302, primal_real), (302, row, adjoint(primal_real)),
                (row, 806, dual_real), (806, row, adjoint(dual_real))]
        if field['group'] == 'gauge_A':
            nu, a = field['coordinate']
            # Vary the original covariant scalar kinetic density, then
            # integrate its derivative on delta(phi) by parts.
            mixed_column = clean(-sum((h[mu, nu]*(P[mu]*s.eye(70)+RA[mu])*raw.rho70[a]*raw.v
                for mu in range(4)), s.zeros(70, 1)))
            original_blocks += [(232, row, mixed_column), (row, 232, adjoint(mixed_column))]
    all_scalar_source = s.Matrix.hstack(*(V*raw.psi0 for V in scalar_vertices))
    scalar_dual = all_scalar_source.T.applyfunc(s.re).row_join(-all_scalar_source.T.applyfunc(s.im))
    original_blocks += [(232, 806, scalar_dual), (806, 232, scalar_dual.T)]
    original = assemble(1310, original_blocks)
    complement_pair = real_bilinear(D.extract(indices_C, indices_C))
    tail_action = assemble(1021, [(0, 0, R.T*scalar_symbol*R), (0, 541, Jchi), (541, 0, Jchi.T),
        (541, 61, complement_pair), (61, 541, adjoint(complement_pair))])
    split_action = assemble(1310, [(0, 0, H289), (289, 289, tail_action)])
    eq(T.T*original*T, split_action); eq(Ti.T*split_action*Ti, original)
    eq(adjoint(original), original)
    assert len(original.todok()) == common['raw_full_Jacobi_nonzero_entries'] == 7358
    eq(Jchi, read_matrix(common['tail_scalar_dual_cross']))
    print('PASS independent full1310 raw Jacobi density and both explicit source-carrier congruences, including scalar/gauge and scalar/dual cross terms', flush=True)

    phase_receipt = json.loads((HERE/'retained_hamiltonian_reduction.json').read_text()); checks += bindings(phase_receipt)
    assert len(phase_receipt['source_momenta']) == len(candidate['actual_phase_inventory_at_source_momenta'])
    phase_rows = []
    for old, saved in zip(phase_receipt['source_momenta'], candidate['actual_phase_inventory_at_source_momenta']):
        assert old['momentum'] == saved['momentum']
        substitution = dict(zip(K, map(s.sympify, old['momentum'])))
        tail = s.MutableSparseMatrix.zeros(1082, 1082)
        tail[:480, :480] = Ad.subs(substitution); tail[480:602, 480:602] = As.subs(substitution); tail[602:, 602:] = Ap.subs(substitution)
        tail[480:602, :480] = Bblock; tail[602:, 480:602] = Cblock
        assert list(tail.shape) == saved['actual_tail_generator_shape'] == [1082, 1082]
        assert len(tail.todok()) == saved['actual_tail_generator_nonzero_entries']
        active_generator = read_matrix(old['Hamiltonian_generator'])
        phase_form = read_matrix(old['nondegenerate_phase_form'])
        eq(active_generator.H*phase_form+phase_form*active_generator, s.zeros(126))
        assert old['dynamic_quotient_dimension'] == saved['active_phase_dimension'] == 126
        assert saved['full_phase_dimension'] == 126+1082 == 1208
        phase_rows.append({'momentum': old['momentum'], 'complex_Fourier_fiber_dimension': 1208,
            'zero_momentum_real_dimension': 1208 if all(s.sympify(v) == 0 for v in old['momentum']) else None,
            'triangular_characteristic_factorization': True})
    assert candidate['Jacobi_field_partition'] == {'active': 289, 'peripheral_scalar': 61,
        'matter_complement_real': 960, 'whole_original_real_fields': 1310}
    print('PASS complete1310 Jacobi field inventory and exact1208 fibers at the two previously certified source momenta', flush=True)
    paths = [Path(__file__), path, HERE/'source_full_linear_split.py',
        HERE/'independent_source_joint_temporal_rates.py', HERE/'independent_source_gauss_quantum_current.py',
        HERE/'scalar_canonical_phase.json', HERE/'retained_hamiltonian_reduction.json',
        HERE/'independent_retained_hamiltonian_reduction.json', BASE/'active-gauge/receipt.json',
        BASE/'occupied-response/receipt.json', BASE/'matter-vertices/receipt.json', BASE/'full-phase/receipt.json']
    result = {'verdict': 'CERTIFIED_COMPLETE_SOURCE_LINEAR_SPLIT_AND_NONZERO_SCALAR_COMPLEMENT_RESPONSE',
        'root': ROOT_ID, 'source_sha256': raw.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks': checks, 'candidate_constructor_imported': False,
        'independent_method': 'raw density coframe derivatives, native connection and repaired wedge Yukawa; exterior-label occupied frame; original real scalar/Dirac-dual coefficient equations before Fourier substitution',
        'occupied_complex_dimension': 12, 'complement_complex_dimension': 240,
        'all158_vertices_and790_incoming_coefficients_checked': True,
        'actual_scalar_crosses': {'right_nonzero_vertices': 24, 'left_nonzero_vertices': 0,
            'background_source_complex_rank': 9, 'background_source_real_rank': 18,
            'all_active9_sources_zero_and_complete_source_in_peripheral61': True},
        'original289_interface': {'scalar9_self_block': True, 'both_occupied_real_matter_blocks': True,
            'all97_boson_primal_dual_mixed_rows': True, 'full_scalar70_operator': True},
        'complete_original_action': {'real_dimension': 1310, 'raw_density_nonzero_entries': 7358,
            'explicit_field_embedding_and_inverse_independently_rebuilt': True,
            'both_congruence_directions': True, 'formal_adjoint': True,
            'full70_scalar_native_gauge_mixed_rows_retained': True,
            'scalar_independent_dual_cross_retained': True},
        'tail_equations': {'real_dimensions': [480, 122, 480], 'independent_dual_not_adjoint': True,
            'realification_before_Fourier': True, 'Pi_scalar_equals_minus_phi_dot_over_N': True,
            'dual_to_scalar_and_scalar_to_primal_nonzero': True, 'C_times_B_zero': True,
            'C_times_scalar_generator_times_B_nonzero': True,
            'all_time_response': 'The ordered block equations uniquely generate the two nested finite-matrix Duhamel integrals; no feedback block is dropped.'},
        'Jacobi_real_field_dimension': 1310, 'phase_fiber_inventory': phase_rows,
        'Fourier_reality_scope': 'At nonzero k these are complex Fourier fibers of the real position-space system; a real unordered +/-k pair combines the conjugate fibers. The source zero mode itself has1208 real phase dimensions.',
        'uniform_new_active_quotient_rank_or_interacting_spectrum_claimed': False,
        'nonlinear_occupied12_invariant_sector_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_full_linear_split.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS independent full linear source split', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
