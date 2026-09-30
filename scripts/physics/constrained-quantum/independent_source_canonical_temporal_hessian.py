#!/usr/bin/env python3
"""Original canonical equation audit of the all-momentum temporal Hessian.

The candidate constructor is not imported. A square172 system directly solves
all canonical readers and fixed rows, before either temporal Schur elimination.
Original BF and independent-dual momenta determine the coordinate readers.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix as DM

from independent_source_spatial_active_phase_splice import (
    RawSpatialActive, DOMAIN, field_number, exact, HERE, BASE, ROOT, ROOT_ID,
    bindings, clean, eq, encode, read_matrix, P, K)
from independent_source_physical_phase_splice import canonical
from independent_source_gauge_legendre import W
from independent_source_full_linear_split import affine
from independent_source_forced_hamiltonian_reduction import (
    matrix as time_polynomial, saved as time_saved, coefficient as time_coefficient,
    degree as time_degree, eye as time_identity, FIELD as TIME_FIELD, LAM, Z)

POLY = DOMAIN.poly_ring(*K)
FREE = (5, 9, 10, 13, 14, 15)
FIXED = (1, 2, 3, 6, 7, 11)


def polynomial(matrix):
    if isinstance(matrix, DM): return matrix.convert_to(POLY)
    rows = {}
    for (i, j), value in s.SparseMatrix(matrix).todok().items():
        coefficients = s.Poly(value, *K)
        v = POLY.zero
        for powers, coefficient in coefficients.terms():
            term = POLY.convert(field_number(coefficient), DOMAIN)
            for x, power in zip(POLY.gens, powers): term *= x**power
            v += term
        if v: rows.setdefault(i, {})[j] = v
    return DM(rows, matrix.shape, POLY).to_sparse()


def star(matrix): return polynomial(matrix.to_Matrix().H)
def identity(n): return polynomial(s.eye(n))
def no(matrix): assert matrix.is_zero_matrix

def at(matrix, k): return exact(matrix.to_Matrix().subs(dict(zip(K, k))))

def select(indices, n): return s.SparseMatrix(len(indices), n, {(i, j): 1 for i, j in enumerate(indices)})


class OriginalCanonicalTemporal:
    def __init__(self):
        self.m = RawSpatialActive(); m = self.m
        self.record = m.retained
        self.indices = {(r['group'], tuple(r['coordinate'])): i for i, r in enumerate(self.record['retained_fields'])}
        self.time = [self.indices['coframe', (a, 0)] for a in range(4)]
        self.A0 = [self.indices['gauge_A', (0, a)] for a in range(12)]
        scalar = [self.indices['scalar_J', (a,)] for a in range(9)]
        self.fixed = scalar+[121+i for i in scalar]+[self.indices['coframe', divmod(i, 4)] for i in FIXED]
        old = m.row
        self.section = polynomial(read_matrix(old['velocity_quotient_section']))
        retract = polynomial(read_matrix(old['velocity_quotient_retraction']))
        self.Omega = polynomial(read_matrix(self.record['presymplectic_form']))
        self.energy = polynomial(read_matrix(self.record['Legendre_energy_hessian']))
        radical = identity(242)-self.section*retract
        no(self.Omega*radical); no(self.energy*radical)
        self.reader289 = self.raw_reader()

    def raw_reader(self):
        m = self.m; index = m.indices
        e = select([index['coframe', (a, mu)] for a in range(4) for mu in range(4)], 289)
        omega = select([index['Lorentz', (mu, a)] for mu in range(4) for a in range(6)], 289)
        gauge = select([index['gauge_A', (mu, a)] for mu in range(4) for a in range(12)], 289)
        B = select([index['gauge_B', (pair, a)] for pair in range(6) for a in range(12)], 289)
        def matter(name):
            return select([index[name, (im, spin, color)] for im in range(2) for spin in range(4) for color in range(3)], 289)
        pcoframe = clean(m.Gt.T*omega+m.dGt*e)
        pgauge = clean(s.kronecker_product(W[:, :3].T, m.raw.Gram)*B)
        pdirac = clean(m.occupied_real.T*(m.Epair*m.occupied_real*matter('dual_H')+m.ecoefficient*e))
        positions = e[list(FREE), :].col_join(gauge[12:, :]).col_join(matter('primal_H'))
        momenta = pcoframe[list(FREE), :].col_join(pgauge).col_join(pdirac)
        return clean(positions.col_join(momenta))

    def generate(self):
        lift = clean(self.m.lift.subs(dict(zip(P[1:], [s.I*k for k in K]))))
        reader = clean(self.reader289*lift)
        first = reader.applyfunc(lambda x: s.expand(x).coeff(P[0], 0))
        velocity = reader.applyfunc(lambda x: s.expand(x).coeff(P[0], 1))
        eq(reader, first+P[0]*velocity)
        canonical_reader = polynomial(first.row_join(velocity))*self.section
        time_reader = polynomial(select(self.time, 242))*self.section
        A0_reader = polynomial(select(self.A0, 242))*self.section
        fixed_reader = polynomial(select(self.fixed, 242))*self.section
        # Solve the original complete square system; no candidate nullspace
        # chart or candidate inverse is used as a premise.
        system = DM.vstack(canonical_reader, time_reader, A0_reader, fixed_reader)
        assert system.shape == (172, 172)
        zero_system = at(system, (0, 0, 0)); inverse0 = polynomial(zero_system.inv())
        increment = system-polynomial(zero_system)
        twist = inverse0*increment
        no(twist*twist)
        inverse = (identity(172)-twist)*inverse0
        no(system*inverse-identity(172)); no(inverse*system-identity(172))
        embedding = inverse.extract(range(172), range(148))
        no(DM.vstack(canonical_reader, time_reader, A0_reader)*embedding-identity(148))
        no(fixed_reader*embedding)
        full = self.section*embedding
        symplectic = star(full)*self.Omega*full
        no(symplectic-polynomial(s.diag(-canonical(66), s.zeros(16))))
        energy = star(full)*self.energy*full
        no(energy-star(energy))
        basis = polynomial(s.diag(s.eye(136), self.m.raw.S.row_join(self.m.graph.S)))
        energy = star(basis)*energy*basis
        keep = [*range(136), *range(145, 148)]
        B = energy.extract(range(136, 145), range(136, 145))
        B0 = at(B, (0, 0, 0)); no(B-polynomial(B0))
        inverseB = polynomial(B0.inv()); no(B*inverseB-identity(9)); no(inverseB*B-identity(9))
        graph = -inverseB*energy.extract(range(136, 145), keep)
        injection = s.zeros(148, 139)
        for j, i in enumerate(keep): injection[i, j] = 1
        injection[136:145, :] = graph.to_Matrix()
        injection = polynomial(injection)
        no(energy.extract(range(136, 145), range(148))*injection)
        reduced = star(injection)*energy*injection
        no(reduced-star(reduced)); no(reduced.extract(range(136, 139), range(132, 139)))
        H = reduced.extract(range(136), range(136)); yy = H.extract(range(132, 136), range(132, 136))
        yz = H.extract(range(132, 136), range(132)); zz = H.extract(range(132), range(132))
        yy0 = at(yy, (0, 0, 0)); no(yy-polynomial(yy0)); yyi = polynomial(yy0.inv())
        derivative = -yyi*yz; no(yy*derivative+yz)
        schur = zz-star(yz)*yyi*yz; no(schur-star(schur))
        print('PASS independent full172 canonical equations, polynomial two-sided inverse and original148 phase/energy', flush=True)
        print('PASS independent broken9 and original4-time Schur with all-three-k full132 Hessian', flush=True)
        return dict(embedding=embedding, canonical_reader=canonical_reader, system=system, inverse=inverse,
                    energy=energy, basis=basis, scalar_embedding=injection, reduced=reduced, H=H,
                    Hyy=yy, Hyz=yz, Hzz=zz, y_z=derivative, Schur=schur,
                    Gauss=reduced.extract(range(136,139),range(132)), section=self.section,
                    broken_A0_block=B, source_shear172=twist)


def adjoint_constant(matrix): return exact(matrix.to_Matrix().H)

def original_carrier(model):
    m = model.m; occupied = m.occupied_real
    E = s.zeros(1214, 132)
    for i in range(6): E[i, i] = 1; E[607+i, 66+i] = 1
    for i in range(36): E[67+i, 6+i] = 1; E[674+i, 72+i] = 1
    E[103:607, 42:66] = occupied; E[710:1214, 108:132] = occupied
    E, tail, tail_reader = exact(E), exact(m.tail), exact(m.tail_reader)
    reader = adjoint_constant(E)
    whole, inverse = DM.hstack(E, tail), DM.vstack(reader, tail_reader)
    no(whole*inverse-exact(s.eye(1214))); no(inverse*whole-exact(s.eye(1214)))
    phase = -adjoint_constant(whole)*exact(m.phase.J)*whole
    no(phase-exact(s.diag(-canonical(66), m.tail_form)))
    checked = 0; C, psi, chi = m.source['C'], m.raw.psi0, m.raw.chi0
    for group, coordinate, vertex in m.source['vertices']:
        if group == 'coframe' and coordinate[1] == 0:
            for coefficient in affine(vertex):
                eq(C.H*coefficient*psi, s.zeros(240, 1))
                eq(chi*coefficient*C, s.zeros(1, 240)); checked += 1
        if group == 'scalar': eq(chi*vertex*psi, s.zeros(1, 1))
    for mu in range(4):
        connection = sum((m.raw.A[mu, a]*m.raw.rho70[a] for a in range(12)), s.zeros(70))
        eq(connection*m.raw.v, s.zeros(70, 1))
    assert checked == 20
    no(reader*tail)
    print('PASS independent full1214 canonical inverse and all20 original time-vertex tail coefficients', flush=True)
    return dict(E=E, reader=reader, tail=tail, tail_reader=tail_reader)


def physical_consumer(model, data, carrier, sign):
    m = model.m; k = tuple(sign*v for v in m.k)
    record = json.loads((HERE/'source_spatial_active_phase_splice.json').read_text())['fibers'][0 if sign == 1 else 1]
    X = exact(read_matrix(record['active_embedding'])); active = carrier['reader']*X
    no(carrier['E']*active-X)
    omega = -adjoint_constant(active)*exact(canonical(66))*active
    old_omega = exact(m.cached('nondegenerate_phase_form', sign)); no(omega-old_omega)
    physical = adjoint_constant(active)*at(data['Schur'], k)*active
    no(physical-exact(m.cached('Hamiltonian_energy', sign)))
    fields = exact(read_matrix(record['original289_field_map']))*exact(m.cached('quotient_section', sign))
    times = [m.indices['coframe', (a, 0)] for a in range(4)]
    derivative = fields.extract(times, range(126))
    no(at(data['y_z'], k)*active-derivative)
    whole_H = exact(s.diag(physical.to_Matrix(), m.tail_H.subs(dict(zip(K, k)))))
    whole_Omega = exact(s.diag(omega.to_Matrix(), m.tail_form))
    whole_A = exact(s.diag(m.cached('Hamiltonian_generator', sign), m.tail_A.subs(dict(zip(K, k)))))
    no(whole_Omega*whole_A-whole_H)
    reader = DM.vstack(exact(read_matrix(record['active_reader'])), carrier['tail_reader'])
    whole_X = DM.hstack(X, carrier['tail'])
    no(exact(m.phase.J)*adjoint_constant(reader)*whole_H*reader*whole_X-whole_X*whole_A)
    print('PASS independent actual126 energy/time graph and complete1208 original generator', sign, flush=True)
    return {'momentum': list(map(str, k)), 'active_canonical132_embedding': encode(active.to_Matrix()),
            'source_time_graph_on_active126': encode(derivative.to_Matrix()),
            'complete1208_energy_and_generator_equal': True, 'whole_source_time_graph_tail_zero': True}, active, omega


def true_current_consumer(model, data, carrier, sign, shifted):
    m = model.m
    name = 'source_nonzero_frequency_onshell_response' if shifted else 'source_onshell_phase_forcing'
    record = json.loads((HERE/(name+'.json')).read_text()); bindings(record)
    index = 0 if sign == 1 else 1; source = record['currents'][index]
    saved = record['consumers' if shifted else 'common_phase_consumers'][index]
    frequency = s.sympify(saved['actual_time_frequency']) if shifted else s.S.Zero
    k = tuple(map(s.sympify, saved['momentum'])); sub = dict(zip(P, [frequency, *[s.I*v for v in k]]))
    j = exact(read_matrix(source['factored_current289' if shifted else 'scaled_current289']))
    field = exact(read_matrix(saved['factored_full289_response' if shifted else 'factored_full289_source_response']))
    no(exact(m.original.subs(sub))*field-j)
    canonical_reader = exact(model.reader289)
    actual_z = canonical_reader*field
    # All actual canonical components are reconstructed from the full field;
    # no compressed phase record is used as a proposed full source vector.
    phase = carrier['E']*actual_z
    spatial = json.loads((HERE/'source_spatial_active_phase_splice.json').read_text())['fibers'][index]
    active = carrier['reader']*exact(read_matrix(spatial['active_embedding']))
    affine_z, original_force, source_remainder = affine_from_current(model, k, sign, j, frequency)
    no(source_remainder-active)
    force = exact(read_matrix(saved['factored_source_forcing126' if shifted else 'factored_physical_forcing126']))
    response = exact(read_matrix(saved['factored_source_response126' if shifted else 'factored_physical_response126']))
    no(force-original_force); no(actual_z-active*response-affine_z)
    affine = carrier['E']*affine_z
    if shifted:
        for key, value in (('factored_common_phase1214_response', phase), ('factored_affine_phase1214', affine)):
            compressed = saved[key]; assert compressed['complete_vector_dimension'] == 1214
            no(value.extract(compressed['source_rows'], [0])-exact(read_matrix(compressed['values'])))
    else:
        no(phase-exact(read_matrix(saved['factored_full_source_phase'])))
        a = read_matrix(saved['factored_affine_phase_polynomial']).subs(s.Symbol('source_laplace'), frequency)
        no(affine-exact(a))
    readback = exact(read_matrix(model.record['retained_source_readback']).subs(sub))
    original_source = DM.vstack(readback*j, DM.zeros((121, 1), DOMAIN))
    s148 = adjoint_constant(at(data['basis'], k))*adjoint_constant(at(data['embedding'], k))*adjoint_constant(at(data['section'], k))*original_source
    s139 = adjoint_constant(at(data['scalar_embedding'], k))*s148
    contact = exact(read_matrix(model.record['auxiliary_only_contact']).subs(sub))
    offset = canonical_reader*contact*j; z0 = actual_z-offset
    yrows = [m.indices['coframe', (a, 0)] for a in range(4)]
    arows = [m.indices['gauge_A', (0, a)] for a in range(12)]
    y = field.extract(yrows, [0]); a0native = field.extract(arows, [0])
    Wbasis = exact(m.raw.S.row_join(m.graph.S)); A0 = Wbasis.inv()*a0native
    u148 = DM.vstack(z0, y, A0); Omega148 = exact(s.diag(-canonical(66), s.zeros(16)))
    no((Omega148.scalarmul(field_number(frequency))-at(data['energy'], k))*u148-s148)
    u139 = DM.vstack(z0, y, A0.extract(range(9, 12), [0]))
    Omega139 = exact(s.diag(-canonical(66), s.zeros(7)))
    no((Omega139.scalarmul(field_number(frequency))-at(data['reduced'], k))*u139-s139)
    yy, yz, derivative = [at(data[name], k) for name in ('Hyy', 'Hyz', 'y_z')]
    source_y = s139.extract(range(132, 136), [0])
    particular = -derivative*offset-yy.inv()*source_y
    no(y-derivative*actual_z-particular)
    effective = s139.extract(range(132), [0])-adjoint_constant(yz)*yy.inv()*source_y
    descriptor = exact(-canonical(66)).scalarmul(field_number(frequency))-at(data['Schur'], k)
    no(descriptor*z0-adjoint_constant(at(data['Gauss'], k))*A0.extract(range(9, 12), [0])-effective)
    projected = adjoint_constant(active)*(effective-descriptor*(affine_z-offset))
    omega = exact(m.cached('nondegenerate_phase_form', sign))
    no(projected-omega*force)
    no((omega.scalarmul(field_number(frequency))-adjoint_constant(active)*at(data['Schur'], k)*active)*response-projected)
    # Independently use original scalar covariant velocity and raw native
    # Gauss currents, including the inhomogeneous normal scalar momentum.
    scalar_rows = [i for i, f in enumerate(m.raw.active['fields']) if f['group'] == 'scalar_J']
    phi = clean(m.raw.Ob*field.to_Matrix()[scalar_rows, :])
    Pi = clean(-(frequency*phi+m.raw.O*a0native.to_Matrix())/m.source['N'])
    predicted = clean(m.phase.at(m.phase.Piphi, k)*phase.to_Matrix())
    normal = clean(Pi-predicted)
    full_Gauss = clean(m.phase.at(m.phase.G12base, k)*phase.to_Matrix()+m.raw.O.T*Pi)
    eq(full_Gauss, j.to_Matrix()[arows, :]); assert full_Gauss.todok()
    print('PASS independent true-current original289, both Schur covectors,126 forcing and full12 Gauss', sign, frequency, flush=True)
    return {'momentum': list(map(str, k)), 'frequency': str(frequency),
            'physical_source_factor': source['physical_current_factor'],
            'source_time_covector': encode(source_y.to_Matrix()),
            'original_auxiliary_canonical_offset': encode(offset.to_Matrix()),
            'generated_affine_time_response': encode(particular.to_Matrix()),
            'actual_full_time_response': encode(y.to_Matrix()),
            'full132_dynamic_equations_and_all4_time_equations': True,
            'original126_forcing_from_Schur_covector': encode(projected.to_Matrix()),
            'full12_original_Gauss_equals_actual_A0_current': encode(full_Gauss),
            'normal_scalar_source_preserved': encode(normal),
            'Contact_added_once_before_canonical_readback': True}


def affine_from_current(model, k, sign, j, frequency):
    """Explicit source polynomial powers, before reading any Green solution."""
    m = model.m
    record = json.loads((HERE/'source_forced_hamiltonian_reduction.json').read_text())
    supplied = record['source_momenta'][0 if sign == 1 else 1]
    source = time_polynomial(j.to_Matrix())
    coframe = select([m.indices['coframe', divmod(a, 4)] for a in FIXED], 289)
    gauge = select([m.indices['gauge_A', (mu+1, a)] for mu in range(3) for a in range(12)], 289)
    gauge_slice = clean(m.phase.spatial.at(m.phase.spatial.reader, k)*gauge)
    C = time_polynomial(coframe.col_join(gauge_slice))
    ward = time_polynomial(m.ward.subs(dict(zip(P, [LAM, *[s.I*v for v in k]]))))
    M = C*ward; assert time_degree(M) == 0
    inverse = M.convert_to(DOMAIN).inv().convert_to(TIME_FIELD)
    def fixed(value): return value-ward*inverse*C*value
    lift = fixed(time_saved(supplied['full289_field_lift']))
    particular = fixed(time_saved(supplied['full289_field_particular'])*source)
    reader = time_polynomial(model.reader289)
    Q = reader*lift; A = time_polynomial(m.cached('Hamiltonian_generator', sign))
    remainder = DM.zeros(Q.shape, TIME_FIELD); quotient = DM.zeros(Q.shape, TIME_FIELD)
    for n in range(time_degree(Q)+1):
        coefficient = time_coefficient(Q, n)
        remainder += coefficient*A**n
        for t in range(n): quotient += (coefficient*A**t).scalarmul(Z**(n-1-t))
    no(Q-remainder-quotient*(time_identity(126).scalarmul(Z)-A))
    forcing = time_saved(supplied['physical_forcing'])*source
    particular_canonical = reader*particular+quotient*forcing
    evaluate = lambda value: exact(value.to_Matrix().subs(LAM, frequency))
    return evaluate(particular_canonical), evaluate(forcing), evaluate(remainder)


def main():
    started = time.monotonic(); path = HERE/'source_canonical_temporal_hessian.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    paid = ('independent_retained_matter_action', 'independent_retained_hamiltonian_reduction',
            'source_temporal_dirac_reduction', 'independent_source_temporal_dirac_reduction',
            'independent_source_spatial_phase_tangent', 'independent_source_physical_phase_splice',
            'source_spatial_active_phase_splice', 'independent_source_spatial_active_phase_splice',
            'independent_source_full_linear_split', 'independent_source_common_phase_time',
            'source_onshell_phase_forcing', 'independent_source_onshell_phase_forcing',
            'source_nonzero_frequency_onshell_response', 'independent_source_onshell_time_response',
            'source_forced_hamiltonian_reduction', 'independent_source_forced_hamiltonian_reduction')
    records = {name: json.loads((HERE/(name+'.json')).read_text()) for name in paid}
    for record in records.values():
        count += bindings(record); assert record['root'] == ROOT_ID
    model = OriginalCanonicalTemporal(); assert model.m.raw.hashes == candidate['source_sha256']
    data = model.generate(); saved = candidate['all_k_matrices']
    aliases = {'canonical_embedding':'embedding', 'canonical_with_A0_energy':'energy', 'A0_basis':'basis'}
    names = ('canonical_embedding', 'canonical_with_A0_energy', 'A0_basis', 'scalar_embedding',
             'broken_A0_block', 'H', 'Hyy', 'Hyz', 'Hzz', 'y_z', 'Schur', 'Gauss')
    for name in names: no(data[aliases.get(name, name)]-polynomial(read_matrix(saved[name])))
    # The candidate's smaller shear is its own coordinate readout. Its
    # nilpotence and the independently unique canonical embedding are checked.
    candidate_shear = polynomial(read_matrix(saved['source_shear'])); no(candidate_shear*candidate_shear)
    eq(model.reader289, read_matrix(candidate['all_k_construction']['original_field_reader132_by289']))
    no(at(data['Hyy'], (0, 0, 0))+exact(read_matrix(records['source_temporal_dirac_reduction']['source_J'])))
    for name in ('H', 'Hyy', 'Hyz', 'Hzz', 'y_z', 'Schur', 'Gauss'):
        value = data[name].to_Matrix()
        no(polynomial(value.subs(dict(zip(K, -s.Matrix(K))), simultaneous=True))-polynomial(value.conjugate()))
    assert data['Hyz'].nnz() == candidate['temporal_derivative']['generic_Hyz_nonzero_entries'] == 127
    assert data['Schur'].nnz() == candidate['temporal_derivative']['generic_Schur_nonzero_entries'] == 4280
    carrier = original_carrier(model)
    record = candidate['whole_canonical_carrier']
    for key, name in (('active_embedding1214','E'), ('active_reader132','reader'),
                      ('tail_embedding1214','tail'), ('tail_reader1082','tail_reader')):
        no(carrier[name]-exact(read_matrix(record[key])))
    assert record['original_time_vertex_coefficients_checked'] == 20
    physical = []
    for sign, expected in zip((1, -1), candidate['signed_nonzero_physical_consumers'], strict=True):
        actual, _, _ = physical_consumer(model, data, carrier, sign)
        for key in ('active_canonical132_embedding', 'source_time_graph_on_active126'):
            eq(read_matrix(actual[key]), read_matrix(expected[key]))
        assert actual['momentum'] == expected['momentum']; physical.append(actual)
    sources = []
    for index, (shifted, sign) in enumerate((a, b) for a in (False, True) for b in (1, -1)):
        actual = true_current_consumer(model, data, carrier, sign, shifted)
        expected = candidate['actual_onshell_consumers'][index]
        for key, value in actual.items():
            if isinstance(value, dict) and 'shape' in value: eq(read_matrix(value), read_matrix(expected[key]))
            else: assert value == expected[key], key
        sources.append(actual)
    print('PASS every advertised all-k matrix and all actual source consumers independently equal', flush=True)
    paths = [Path(__file__), path, HERE/'source_canonical_temporal_hessian.py',
             HERE/'independent_source_spatial_active_phase_splice.py', HERE/'independent_source_full_linear_split.py',
             HERE/'independent_source_spatial_phase_tangent.py', HERE/'independent_source_forced_hamiltonian_reduction.py']
    paths += [HERE/(name+'.json') for name in paid]
    result = {'verdict':'CERTIFIED_ORIGINAL_ALL_MOMENTUM_CANONICAL_TIME_HESSIAN_AND_TRUE_SOURCE_CONSUMERS',
        'root':ROOT_ID, 'source_sha256':model.m.raw.hashes,
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks':count, 'candidate_constructor_imported':False,
        'independent_method':'Raw epsilon BF and independent-dual current readers; direct172 square canonical equations; all-k sparse polynomial two-sided inverse; original148 energy congruence and both Schur eliminations; explicit source-polynomial powers before consuming Green data; full289 and1214 true-current readback.',
        'all_three_spatial_momenta_polynomial_identities':True,
        'direct172_original_canonical_equations_and_both_inverses':True,
        'full148_original_phase_and_native_A0_energy':True,
        'original_time_Jacobian_equals_negative_Hyy':True,
        'original_Hyy':encode(data['Hyy'].to_Matrix()),
        'whole4_by132_branch_derivative_and132_by132_Schur':True,
        'Hyz_nonzero_entries':data['Hyz'].nnz(), 'Schur_nonzero_entries':data['Schur'].nnz(),
        'both1214_complete_carrier_inverses_and_original_phase':True,
        'all20_original_time_vertex_tail_coefficients_zero':True,
        'full70_scalar_source_bilinears_and_background_covariant_derivatives_zero':True,
        'opposite_momentum_reality_checked':True,
        'affine_source_generated_by_explicit_polynomial_powers_before_Green_response':True,
        'signed_nonzero_physical_consumers':physical,
        'actual_onshell_consumers':sources,
        'response_scope':candidate['response_scope'],
        'nonlinear_neighborhood_or_quantum_spectrum_generated':False,
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'independent_source_canonical_temporal_hessian.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS independent source canonical temporal Hessian',result['elapsed_seconds'],'seconds',flush=True)


if __name__ == '__main__': main()
