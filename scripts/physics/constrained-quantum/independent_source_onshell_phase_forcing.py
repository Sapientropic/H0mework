#!/usr/bin/env python3
"""Original252 legs, raw289 currents and canonical affine source audit.

Neither new producer is imported. Independently reconstructed spinors feed
the original vertex matrices. The physical126 equation is solved directly;
raw BF/Dirac momenta and the original full12 Gauss read back its whole field.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix as DM

from independent_source_forced_hamiltonian_reduction import (
    HERE, BASE, ROOT, ROOT_ID, P, LAM, DOMAIN, FIELD, Z, matrix, saved, eye,
    zero, coefficient, degree, original_operator, decode, check_bindings)
from independent_source_spatial_active_phase_splice import RawSpatialActive, exact
from independent_source_joint_temporal_rates import encode
from independent_source_gauge_legendre import W


def equal(a, b):
    difference = s.SparseMatrix(a-b).applyfunc(lambda x: s.simplify(s.expand(x)))
    assert not difference.todok(), list(difference.todok().items())[:3]


def evaluated(value, momentum, time=0):
    values = [s.sympify(time), *[s.I*k for k in momentum]]
    return s.SparseMatrix(s.SparseMatrix(value).xreplace({v: values[int(str(v)[1:])]
        for v in value.free_symbols if str(v) in ('p0', 'p1', 'p2', 'p3')}))


def actual_legs_and_currents(candidate, vertices, modes, phase, residue, exchange, gamma0):
    frame = decode(modes['source_isometry'])
    projector = decode(modes['free_projection'])
    kinetic = decode(residue['kinetic_pair_matrix'])
    norm = s.sympify(residue['right_normalization_factor'])
    spin_scale = s.sympify(residue['source_spin_scale'])
    assert s.simplify(spin_scale*norm**2) == 1
    S = s.SparseMatrix(s.kronecker_product(gamma0*s.diag(-1, -1, 1, 1), s.eye(63)))
    D = decode(vertices['full_stationary_Dirac_operator'])
    H0 = decode(modes['original_H_constant'])
    Hspace = list(map(decode, modes['original_H_spatial']))
    scale, omega = s.sympify(modes['time_scale']), s.sympify(phase['source_frequency'])
    charge = decode(phase['phase_generator'])
    directions = ([0, 0, 1], [s.Rational(4, 5), 0, s.Rational(-3, 5)],
                  [0, 0, -1], [s.Rational(-4, 5), 0, s.Rational(3, 5)])
    radius = 15*s.sqrt(2)/32
    legs = []
    for degree0, n, supplied in zip((4, 4, 2, 2), directions, candidate['legs'], strict=True):
        n = s.Matrix(n)
        # A direct positive Pauli eigenvector, independently of the producer's
        # projector-column construction, with its exact source norm retained.
        spin = s.Matrix([0, 1]) if n[2] == -1 else s.Matrix([1+n[2], n[0]+s.I*n[1]])/s.sqrt(2*(1+n[2]))
        block = next(b for b in modes['blocks'] if b['degree'] == degree0 and b['chirality'] == 1 and b['kind'] == 'singlet')
        u = s.SparseMatrix(frame[:, block['first_column']:block['first_column']+2]*spin)
        k = radius*n
        h = scale*(H0+sum((k[j]*Hspace[j]/s.sqrt(2) for j in range(3)), s.SparseMatrix.zeros(252)))
        energy = s.simplify((u.H*h*u)[0])
        stationary = s.simplify(energy-omega*block['phase_charge'])
        symbol = evaluated(D, k, -s.I*stationary)
        equal(h*u, energy*u); equal(symbol*u, s.zeros(252, 1)); equal(u.H*S*symbol, s.zeros(1, 252))
        equal(projector*u, u); equal(charge*u, block['phase_charge']*u)
        assert s.simplify((u.H*u)[0]) == 1 and s.simplify((norm*u).H*kinetic*(norm*u))[0] == 1
        equal(u, decode(supplied['vector'])); equal(norm*u, decode(supplied['action_vector']))
        equal(k, decode(supplied['momentum'])); equal(spin, decode(supplied['spin']))
        assert energy == s.sympify(supplied['energy']) == 189*s.sqrt(15)/400
        assert stationary == s.sympify(supplied['stationary_energy'])
        legs.append(dict(u=u, normalized=norm*u, k=k, frequency=-s.I*stationary, energy=energy))
    operators = {row['field']: decode(row['operator']) for row in vertices['active_289_bosonic_source_operators']}
    order = exchange['source_field_indices']
    injection = s.SparseMatrix(289, 97, {(field, j): 1 for j, field in enumerate(order)})
    def current(outgoing, incoming):
        answer = []
        for field in order:
            right = evaluated(operators[field], incoming['k'], incoming['frequency'])
            left = evaluated(operators[field], outgoing['k'], outgoing['frequency'])
            value = (outgoing['normalized'].H*S*(right*incoming['normalized']))[0]
            value += ((left*outgoing['normalized']).H*S*incoming['normalized'])[0]
            answer.append(s.simplify(spin_scale*value/2))
        return s.SparseMatrix(answer)
    currents = []
    for a, b, supplied in zip((1, 3), (0, 2), candidate['currents'], strict=True):
        j = current(legs[a], legs[b]); k = legs[b]['k']-legs[a]['k']
        assert legs[a]['energy'] == legs[b]['energy']
        equal(j, decode(supplied['current97']))
        equal(injection*j, decode(supplied['current289']))
        factored = s.SparseMatrix(injection*j*s.sqrt(5)).applyfunc(s.simplify)
        equal(factored, decode(supplied['scaled_current289']))
        assert s.sympify(supplied['physical_current_factor']) == 1/s.sqrt(5)
        for key in ('local_source_compatibility_map', 'independent_dual_source_map'):
            M = evaluated(decode(exchange[key]), k)
            equal(M*j, s.zeros(M.rows, 1))
        scalar = next(row for row in exchange['source_contact_terms'] if row['groups'] == ['scalar_Ward'])
        equal(evaluated(decode(scalar['source_map']), k)*j, s.zeros(9, 1))
        for row in vertices['primitive_vertices']:
            if row['group'] != 'scalar': continue
            V = decode(row['operator'])
            R = evaluated(V, legs[b]['k'], legs[b]['frequency'])
            L = evaluated(V, legs[a]['k'], legs[a]['frequency'])
            value = (legs[a]['normalized'].H*S*(R*legs[b]['normalized']))[0]
            value += ((L*legs[a]['normalized']).H*S*legs[b]['normalized'])[0]
            assert s.simplify(value) == 0
        currents.append(dict(j=j, full=injection*j, factored=factored, k=tuple(k)))
    equal(current(legs[3], legs[0]), s.zeros(97, 1))
    equal(current(legs[1], legs[2]), s.zeros(97, 1))
    equal(legs[0]['k']+legs[2]['k'], legs[1]['k']+legs[3]['k'])
    return legs, currents


def raw_canonical_reader(raw):
    indices = raw.indices
    select = lambda rows: s.SparseMatrix(len(rows), 289, {(i, a): 1 for i, a in enumerate(rows)})
    de = select([indices['coframe', (a, mu)] for a in range(4) for mu in range(4)])
    dO = select([indices['Lorentz', (mu, a)] for mu in range(4) for a in range(6)])
    dA = select([indices['gauge_A', (mu, a)] for mu in range(4) for a in range(12)])
    dB = select([indices['gauge_B', (pair, a)] for pair in range(6) for a in range(12)])
    def matter(group):
        return raw.occupied_real*select([indices[group, (im, spin, color)]
            for im in range(2) for spin in range(4) for color in range(3)])
    psi, chi = matter('primal_H'), matter('dual_H')
    scalar_rows = [j for j, f in enumerate(raw.raw.active['fields']) if f['group'] == 'scalar_J']
    phi = raw.raw.O[:, raw.raw.active['J_independent_columns']]*select(scalar_rows)
    Piphi = -(LAM*phi+raw.raw.O*dA[:12, :])/raw.source['N']
    PiA = s.kronecker_product(W[:, :3].T, raw.raw.Gram)*dB
    Pie = raw.Gt.T*dO+raw.dGt*de
    pmatter = raw.Epair*chi+raw.ecoefficient*de
    q = s.Matrix.vstack(de[(5, 9, 10, 13, 14, 15), :], raw.graph.Rd.T*phi, dA[12:, :], psi)
    p = s.Matrix.vstack(Pie[(5, 9, 10, 13, 14, 15), :], raw.graph.R.T*Piphi, PiA, pmatter)
    return matrix(q.col_join(p)), matrix(Piphi), select([indices['gauge_A', (0, a)] for a in range(12)]), de, dA


def consumer(raw, reader, Piphi_reader, A0_reader, de, dA, source, supplied, forcing, spatial, old, exchange, sign):
    k = source['k']; j = matrix(source['factored'])
    A0 = decode(old['Hamiltonian_generator'])
    if sign == -1: A0 = A0.conjugate()
    A = matrix(A0)
    X = saved(spatial['active_embedding'])
    cf = matrix(s.Matrix.vstack(de[(1, 2, 3, 6, 7, 11), :], raw.phase.spatial.at(raw.phase.spatial.reader, k)*dA[12:, :]))
    ward = matrix(evaluated(raw.ward, k, LAM))
    Wslice = cf*ward
    assert degree(Wslice) == 0
    Winv = Wslice.convert_to(DOMAIN).inv().convert_to(FIELD)
    fix = lambda value: value-ward*Winv*cf*value
    dyn = fix(saved(forcing['full289_field_lift']))
    particular = fix(saved(forcing['full289_field_particular'])*j)
    Q = reader*dyn
    # Explicit polynomial powers replace the producer's Horner division.
    remainder = DM.zeros(Q.shape, FIELD); quotient = DM.zeros(Q.shape, FIELD)
    for n in range(degree(Q)+1):
        Qn = coefficient(Q, n)
        remainder += Qn*A**n
        for t in range(n): quotient += (Qn*A**t).scalarmul(Z**(n-1-t))
    zero(remainder-X)
    zero(Q-X-quotient*(eye(126).scalarmul(Z)-A))
    F = saved(forcing['physical_forcing'])*j
    affine = reader*particular+quotient*F
    zero(affine-saved(supplied['factored_affine_phase_polynomial']))
    f = coefficient(F, 0).convert_to(DOMAIN)
    # Direct original126 solve: no candidate/common Green routine is called.
    xi = (-exact(A0)).lu_solve(f).to_sparse().convert_to(FIELD)
    zero(xi-saved(supplied['factored_physical_response126']))
    zero(matrix(f.to_Matrix())-saved(supplied['factored_physical_forcing126']))
    response = X*xi; phase = response+coefficient(affine, 0)
    zero(response-saved(supplied['factored_common1214_retarded_response']))
    zero(X*matrix(f.to_Matrix())-saved(supplied['factored_common1214_forcing']))
    zero(phase-saved(supplied['factored_full_source_phase']))
    fields = coefficient(dyn, 0)*xi+coefficient(particular, 0)
    zero(fields-saved(supplied['factored_full289_source_response']))
    zero(coefficient(reader, 0)*fields-phase)
    H = coefficient(original_operator(raw.raw.active, k), 0)
    zero(H*fields-j); zero(coefficient(cf, 0)*fields)
    equal((H*fields).to_Matrix()/s.sqrt(5), source['full'])
    T = matrix(raw.phase.projection(k))
    zero(T*response-response)
    zero((eye(1214)-T)*phase-(eye(1214)-T)*coefficient(affine, 0))
    Pi = coefficient(Piphi_reader, 0)*fields
    extra = Pi-matrix(raw.phase.at(raw.phase.Piphi, k))*phase
    fullG = matrix(raw.phase.at(raw.phase.G12, k))*phase+matrix(raw.raw.O.T)*extra
    nativeG = matrix(raw.phase.at(raw.phase.C, k))*phase
    zero(nativeG); zero(fullG-matrix(A0_reader)*j)
    zero(fullG-saved(supplied['factored_source_induced_full12_Gauss']))
    zero(extra-saved(supplied['factored_source_induced_normal_scalar_momentum']))
    normal = raw.raw.Ob*(raw.raw.Ob.T*raw.raw.Ob).inv()*raw.raw.S.T
    zero(extra-matrix(normal*A0_reader)*j)
    assert not fullG.is_zero_matrix and not extra.is_zero_matrix
    # A second source response uses the old79 restriction, rather than the
    # new descriptor forcing. Same Ward representative fixes all289 fields.
    A79 = exact(evaluated(decode(exchange['canonical_operator']), k))
    J79 = exact(evaluated(decode(exchange['canonical_source_map']), k))
    j97 = exact(s.SparseMatrix(source['j']*s.sqrt(5)).applyfunc(s.simplify))
    c79 = A79.lu_solve(J79*j97)
    local = exact(evaluated(decode(exchange['contact_field_response']), k))*j97
    propagated = exact(evaluated(decode(exchange['canonical_field_lift']), k))*c79
    reference = matrix((local+propagated).to_Matrix())
    zero(fields-coefficient(fix(reference), 0))
    assert not (H*matrix(local.to_Matrix())).is_zero_matrix
    return {'momentum': list(map(str, k)), 'physical126_direct_original_solve': True,
        'source_generated_forcing_before_response': True,
        'all289_original_equations_and_source_normalization': True,
        'canonical_reader_from_original_BF_and_independent_Dirac_momenta': True,
        'canonical_polynomial_division_and_affine_source_part': True,
        'full12_Gauss_equals_actual_A0_source': True,
        'stabilizer3_Gauss_zero': True, 'broken_scalar_normal_momentum_source_nonzero': True,
        'independent_original79_plus_Contact_matches_same_Ward_representative': True}, fields.to_Matrix(), local.to_Matrix(), propagated.to_Matrix()


def main():
    began = time.monotonic()
    names = ['source_onshell_phase_forcing.json', 'source_forced_hamiltonian_reduction.json',
        'independent_source_forced_hamiltonian_reduction.json', 'source_spatial_active_phase_splice.json',
        'independent_source_spatial_active_phase_splice.json', 'retained_hamiltonian_reduction.json']
    records = [json.loads((HERE/name).read_text()) for name in names]
    candidate, forced, forced_audit, spatial, spatial_audit, catalog = records
    assert all(record['root'] == ROOT_ID for record in records)
    checks = sum(check_bindings(record) for record in records)
    external_names = ['matter-vertices/receipt.json', 'matter-vertices/exchange.json',
        'matter-modes/source.json', 'full-phase/receipt.json', 'kinetic-residue/receipt.json']
    vertices, exchange, modes, phase, residue = [json.loads((BASE/name).read_text()) for name in external_names]
    checks += sum(check_bindings(r) for r in (vertices, exchange, modes, phase, residue))
    assert candidate['source_sha256'] == vertices['source_sha256'] == modes['source_sha256'] == phase['source_sha256']
    raw = RawSpatialActive()
    legs, currents = actual_legs_and_currents(candidate, vertices, modes, phase, residue, exchange, raw.raw.gamma[0])
    print('PASS independent four normalized full252 legs, original energies, all70 scalar and exact Ward currents', flush=True)
    reader, Piphi, A0, de, dA = raw_canonical_reader(raw)
    old = next(row for row in catalog['source_momenta'] if any(s.sympify(v) != 0 for v in row['momentum']))
    reports, fields, contacts, propagated = [], [], [], []
    for i, sign in enumerate((1, -1)):
        report, field, local, dynamic = consumer(raw, reader, Piphi, A0, de, dA, currents[i],
            candidate['common_phase_consumers'][i], forced['source_momenta'][i], spatial['fibers'][i], old, exchange, sign)
        reports.append(report); fields.append(field); contacts.append(local); propagated.append(dynamic)
        print('PASS original126 direct solve, raw1214 momenta, full289 Euler and actual sourced12 Gauss', sign, flush=True)
    direct = s.simplify(-(currents[1]['full'].T*fields[0])[0]/s.sqrt(5))
    contact = s.simplify((currents[1]['full'].T*contacts[0])[0]/s.sqrt(5))
    dynamic = s.simplify((currents[1]['full'].T*propagated[0])[0]/s.sqrt(5))
    assert s.simplify(direct+contact+dynamic) == 0
    assert direct == s.sympify(candidate['elastic_direct_tree_kernel'])
    assert contact == s.sympify(candidate['Contact_bilinear']) == -9*s.sqrt(30)/100
    assert dynamic == s.sympify(candidate['canonical_dynamic_bilinear']) and dynamic != 0
    assert candidate['quantum_spectrum_or_proton_pole_generated'] is False
    paths = [HERE/name for name in [*names, 'source_onshell_phase_forcing.py',
        'independent_source_onshell_phase_forcing.py', 'independent_source_forced_hamiltonian_reduction.py',
        'independent_source_spatial_active_phase_splice.py']]+[BASE/name for name in external_names]
    output = {'root': ROOT_ID, 'source_sha256': candidate['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'verdict': 'CERTIFIED_ACTUAL_ONSHELL_SOURCE_CURRENTS_AND_AFFINE_COMMON_ACTION',
        'scope': candidate['scope'], 'checked_input_bindings': checks,
        'candidate_constructors_imported': False, 'source_fibers': reports,
        'all_four_action_normalized_energies': [str(leg['energy']) for leg in legs],
        'actual97_current_support': [len(current['j'].todok()) for current in currents],
        'actual_direct_tree_kernel': str(direct), 'actual_Contact_bilinear': str(contact),
        'actual_canonical_bilinear': str(dynamic),
        'independent_algorithm': 'Direct Pauli eigenvector formula and original252 operators/vertices; full polynomial division by explicit powers; direct126 and independent79 linear solves; original BF/Dirac canonical reader and all12 Gauss.',
        'normalization_review': 'All four legs use the source action pole factor 2^(-1/4). The geometric sqrt5 current factor is restored in every original289 equation and in both bilinear legs. No arbitrary Z is introduced.',
        'response_scope': 'The actual elastic external legs have zero transfer energy and the two signed nonzero momenta. The existing retarded rational kernel is read meromorphically at z=0; no convergent zero-frequency Laplace integral is claimed.',
        'quantum_spectrum_or_proton_lifetime_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_onshell_phase_forcing.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS independent actual on-shell affine source consumer', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
