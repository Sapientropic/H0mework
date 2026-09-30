#!/usr/bin/env python3
"""Original real Dirac-dual density and its scalar current in canonical coordinates.

Realification acts on position-space differential coefficients before spatial
Fourier substitution.  The complex branches then carry the normalization of
the real action itself, with no change to the previously generated external
leg residue or a new Hilbert-adjoint identification.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, SourceExchange, decode, P as SYMBOL
from spectral_splice import clean, equal, encode

K = s.symbols('k1:4', real=True)


def realify(value):
    """Real-coordinate map of a complex position-space coefficient."""
    assert all(not entry.free_symbols for entry in value.todok().values())
    real, imag = value.applyfunc(s.re), value.applyfunc(s.im)
    return clean(s.SparseMatrix.vstack(s.SparseMatrix.hstack(real, -imag),
                                      s.SparseMatrix.hstack(imag, real)))


def real_bilinear(value):
    """Re(chi*V*psi) on independent (Re chi,Im chi) and (Re psi,Im psi)."""
    assert all(not entry.free_symbols for entry in value.todok().values())
    real, imag = value.applyfunc(s.re), value.applyfunc(s.im)
    return clean(s.SparseMatrix.vstack(s.SparseMatrix.hstack(real, -imag),
                                      s.SparseMatrix.hstack(-imag, -real)))


def main():
    started = time.monotonic()
    source = SourceExchange()
    ports_path = HERE/'full-matter-ports.json'
    ports = json.loads(ports_path.read_text())
    phase_path = HERE/'scalar_canonical_phase.json'
    phase = json.loads(phase_path.read_text())
    for row in [ports, phase]:
        assert row['root'] == ROOT_ID and row['source_sha256'] == source.vertices['source_sha256']
    E = decode(ports['density_temporal_principal'])
    Ei = decode(ports['density_temporal_inverse'])
    equal(E*Ei, s.eye(252)); equal(Ei*E, s.eye(252))
    original = clean(source.N*source.D)
    equal(original.diff(SYMBOL[0]), E)
    spatial = [clean(original.diff(p)) for p in SYMBOL[1:]]
    constant = clean(original.subs(dict.fromkeys(SYMBOL, 0)))
    equal(original, E*SYMBOL[0]+constant+sum((p*A for p, A in zip(SYMBOL[1:], spatial)), s.zeros(252)))
    complex_coefficients = [clean(-Ei*A) for A in [constant, *spatial]]
    real_coefficients = list(map(realify, complex_coefficients))
    # Fourier is applied only now.  Taking real/imaginary parts of the
    # already-Fourier-transformed H(k) would alter the spatial derivative.
    real_drift = clean(real_coefficients[0]+sum((s.I*k*A for k, A in zip(K, real_coefficients[1:])), s.zeros(504)))
    complex_drift = clean(complex_coefficients[0]+sum((s.I*k*A for k, A in zip(K, complex_coefficients[1:])), s.zeros(252)))
    H = clean(s.I*complex_drift)
    expected_H = decode(ports['stationary_Hamiltonian_coefficients']['constant'])+sum(
        (k*decode(ports['stationary_Hamiltonian_coefficients'][str(k)]) for k in K), s.zeros(252))
    equal(H, expected_H)
    kinetic_pairing = real_bilinear(E)
    equal(kinetic_pairing*real_coefficients[0], -real_bilinear(constant))
    for real_A, native_A in zip(real_coefficients[1:], spatial):
        equal(kinetic_pairing*real_A, -real_bilinear(native_A))

    # All real canonical pairings come from Re(i p*dpsi), not a positive
    # adjoint condition.  For p=u+i v, P=(-v,-u) and q=(x,y).
    I, Z = s.eye(252), s.zeros(252)
    momentum_from_complex_parts = s.SparseMatrix.vstack(s.SparseMatrix.hstack(Z, -I),
                                                       s.SparseMatrix.hstack(-I, Z))
    equal(momentum_from_complex_parts**2, s.eye(504))
    kinetic_inverse = clean(realify(Ei)*s.diag(I, -I))
    equal(kinetic_pairing*kinetic_inverse, s.eye(504))
    equal(kinetic_inverse*kinetic_pairing, s.eye(504))
    minus_k = dict(zip(K, [-k for k in K]))
    dual_real_drift = clean(-real_drift.subs(minus_k, simultaneous=True).T)
    dual_complex_coefficients = [clean(Ei.T*constant.T), *[clean(-Ei.T*A.T) for A in spatial]]
    dual_native_real = clean(realify(dual_complex_coefficients[0])+sum(
        (s.I*k*realify(A) for k, A in zip(K, dual_complex_coefficients[1:])), s.zeros(504)))
    equal(kinetic_pairing.T*dual_native_real, dual_real_drift*kinetic_pairing.T)
    print('PASS original504 real canonical action, full spatial differential coefficients and independent dual flow', flush=True)

    U = clean(s.SparseMatrix.vstack(s.SparseMatrix.hstack(I, s.I*I),
                                    s.SparseMatrix.hstack(I, -s.I*I))/s.sqrt(2))
    equal(U*U.H, s.eye(504)); equal(U.H*U, s.eye(504))
    for M, AR in zip(complex_coefficients, real_coefficients):
        equal(U*AR*U.H, s.diag(M, M.conjugate()))
    quantum_matrix = clean(s.I*real_drift)
    expected_branches = s.diag(H, clean(-H.subs(minus_k, simultaneous=True).conjugate()))
    equal(U*quantum_matrix*U.H, expected_branches)
    # Formal unit CAR use eta=-i P, with eta row transforming by U^-1.
    # This generates (p/sqrt2,-bar(p)/sqrt2), matching the Re action's 1/2.
    dual_branch_map = clean(-s.I*momentum_from_complex_parts*U.H)
    expected_dual_map = clean(s.SparseMatrix.vstack(s.SparseMatrix.hstack(I, -I),
                                                    s.SparseMatrix.hstack(s.I*I, s.I*I))/s.sqrt(2))
    equal(dual_branch_map, expected_dual_map)
    equal(s.I*dual_branch_map*U, momentum_from_complex_parts)
    naive = clean(s.SparseMatrix.vstack(
        s.SparseMatrix.hstack(complex_drift.applyfunc(s.re), -complex_drift.applyfunc(s.im)),
        s.SparseMatrix.hstack(complex_drift.applyfunc(s.im), complex_drift.applyfunc(s.re))))
    wrong_order = clean(naive-real_drift)
    assert wrong_order.todok()
    wrong_spatial = [clean(wrong_order.diff(k)) for k in K]
    assert all(value.todok() for value in wrong_spatial)
    print('PASS complex-branch all-k identity and source-generated half/sqrt2 normalization; wrong Fourier-first realification rejected', flush=True)

    raw_vertices = [decode(row['operator']) for row in source.vertices['primitive_vertices'] if row['group'] == 'scalar']
    raw_ports = [row for row in ports['primitive_ports'] if row['group'] == 'scalar']
    scalar_rows = []
    imaginary_witnesses = []
    for index, (V, row) in enumerate(zip(raw_vertices, raw_ports)):
        W = clean(-s.I*Ei*V)
        equal(W, decode(row['Hamiltonian_coefficients']['constant']))
        AR = realify(clean(-s.I*W))
        raw_real_current = real_bilinear(V)
        equal(kinetic_pairing*AR, -raw_real_current)
        equal(E*(-s.I*W)+V, s.zeros(252))
        formal_quantum = clean(s.I*AR)
        equal(U*formal_quantum*U.H, s.diag(W, -W.conjugate()))
        # Re(p W psi)=P^T AR q, including every scalar component's exact
        # independent-dual real bilinear.  Complex rho is not substituted.
        direct_current_map = clean(momentum_from_complex_parts*AR)
        equal(direct_current_map, real_bilinear(W))
        scalar_rows.append({'scalar_coordinate': index,
            'original_real_density_bilinear': encode(raw_real_current),
            'real_canonical_current_matrix': encode(AR),
            'formal_unit_CAR_matrix': encode(formal_quantum),
            'complex_port': encode(W)})
        # A purely imaginary coordinate pairing displays the distinction
        # without imposing any property on arbitrary static CAR states.
        for (i, j), value in V.todok().items():
            if s.im(value) != 0:
                imaginary_witnesses.append({'scalar_coordinate': index, 'dual_coordinate': i,
                    'primal_coordinate': j, 'complex_density': str(value),
                    'real_density': str(s.re(value))})
                break
    assert len(scalar_rows) == 70 and imaginary_witnesses
    R = decode(phase['scalar_coordinate_embedding'])
    canonical_rows = []
    for j, saved in enumerate(phase['projected_CAR_couplings']):
        V = clean(sum((R[a, j]*raw_vertices[a] for a in range(70) if R[a, j]), s.zeros(252)))
        W = clean(-s.I*Ei*V)
        equal(V, decode(saved['density_vertex'])); equal(W, decode(saved['canonical_matter_vertex']))
        AR = realify(clean(-s.I*W))
        equal(kinetic_pairing*AR, -real_bilinear(V))
        equal(U*(s.I*AR)*U.H, s.diag(W, -W.conjugate()))
        assert AR.todok()
        canonical_rows.append({'canonical_scalar_coordinate': j,
            'real_current_matrix': encode(AR), 'formal_unit_CAR_matrix': encode(s.I*AR),
            'original_real_density_bilinear': encode(real_bilinear(V))})
    assert len(canonical_rows) == 61
    print('PASS all70 original504 real source bilinears and61 canonical real currents, with exact two complex branches', flush=True)

    # The scalar source is a real coordinate.  Its phase-space forcing is
    # the original -P61 times these real currents, with no scalar doubling.
    P61 = decode(phase['projector61'])
    equal(P61*R, R)
    canonical_source = decode(phase['canonical_source_injection'])
    equal(canonical_source, s.SparseMatrix.vstack(s.zeros(61, 70), -R.T))
    paths = [phase_path, HERE/'scalar_canonical_phase.py', ports_path,
             BASE/'matter-vertices/receipt.json', BASE/'full-phase/receipt.json',
             BASE/'full-quantum/receipt.json', BASE/'kinetic-residue/receipt.json',
             ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/FullQuantum/CAR.lean']
    output = {'root': ROOT_ID, 'source_sha256': source.vertices['source_sha256'],
        'scope': 'ORIGINAL_REAL504_CANONICAL_MATTER_ACTION_SCALAR_SOURCE_AND_FORMAL_UNIT_CAR_READOUT',
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'real_coordinate_rule': 'q=(Re psi,Im psi); P=(-Im p_CAR,-Re p_CAR); Re(i p_CAR dot(psi))=P^T dot(q)',
        'original_dual_to_real_momentum': encode(kinetic_pairing),
        'complex_momentum_parts_to_real_P': encode(momentum_from_complex_parts),
        'position_space_complex_drift_coefficients': [encode(value) for value in complex_coefficients],
        'position_space_real_drift_coefficients': [encode(value) for value in real_coefficients],
        'real_drift_symbol': encode(real_drift), 'independent_real_dual_symbol': encode(dual_real_drift),
        'formal_unit_CAR_generator': encode(quantum_matrix),
        'Fourier_rule': 'realify every original differential coefficient first; then partial_j=i*k_j',
        'complex_branch_unitary': encode(U), 'complex_branch_dual_map_from_p_real_imag': encode(dual_branch_map),
        'branch_generator_identity': 'U*(i*A_R(k))*U^dagger=diag(H(k),-conjugate(H(-k)))',
        'formal_real_CAR': 'eta=-i P; {q_i,eta_j}=delta_ij is the formal unit-CAR readout of i eta dot(q)',
        'normalized_branch_annihilators': '(psi/sqrt2,conjugate(psi)/sqrt2)',
        'normalized_branch_momenta': '(p_CAR/sqrt2,-conjugate(p_CAR)/sqrt2)',
        'normalization_identity': 'Re(i p dot(psi)-p H psi)=1/2*(i p dot(psi)-p H psi)+1/2*(-i conjugate(p) dot(conjugate(psi))-conjugate(p H psi))',
        'normalization_origin': 'the 1/2 is exactly Re and the 1/sqrt2 is the unitary complex-branch basis; the prior pole residue and external leg normalization are unchanged',
        'real_scalar_current': 'rho_real,A=Re(p_CAR W_A psi)=P^T realify(-i W_A)q=-Re(chi V_A psi)',
        'real_scalar_interaction': 'H_int,classical=sum_A phi_A P^T A_R(W_A)q; its scalar force is rho_real',
        'formal_CAR_scalar_matrix': 'i*realify(-i W_A); its two branches are W_A and -conjugate(W_A)',
        'all70_sources': scalar_rows, 'all61_canonical_sources': canonical_rows,
        'complex_is_not_real_current_witness': imaginary_witnesses[0],
        'Fourier_first_realification_defects_by_spatial_direction': [len(value.todok()) for value in wrong_spatial],
        'realification_dimension': 504, 'new_independent_physical_modes_claimed': False,
        'positive_Hilbert_quantum_completion_claimed': False,
        'conjugate_interaction_added_by_hand': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'real_scalar_car_source.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS original real scalar/CAR source and normalization consumer', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
