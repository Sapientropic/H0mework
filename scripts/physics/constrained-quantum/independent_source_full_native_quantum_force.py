#!/usr/bin/env python3
"""Fixed-full-Pi native forces from original Lagrangian field variations.

The scalar and BF densities are varied at fixed velocities, before their
original momentum equations are solved. This is independent of the candidate
Hamiltonian differentiation. Full exterior representations and occupation-bit
CAR then consume every native force and temporal Gauss row.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time

import sympy as s

import source_full_native_quantum_force as candidate
from independent_source_joint_local_quantum import representations
from independent_source_common_hamiltonian import original_inventory, raw_matter
from independent_source_gauge_legendre import (
    bindings, hodge, matrix_coordinates, W, SIGMA, ETA, encode, decode)
from independent_source_lorentz_quantum_section import BitAction, total, equal

HERE, ROOT = candidate.HERE, candidate.ROOT
BASE = HERE.parent


def rational(A):
    return s.SparseMatrix(A).applyfunc(s.cancel)


def scalar(value):
    return s.cancel(s.expand(value))


def real_car(M):
    return rational(s.diag(M, -M.conjugate()))


def same(A, B):
    difference = total((1, A), (-1, B))
    assert not difference, list(difference.items())[:3]


def native_gram(fundamental):
    def pair(A, B):
        return s.re(-s.trace(A[:3, :3]*B[:3, :3])
                    -s.trace(A[3:5, 3:5]*B[3:5, 3:5])-A[5, 5]*B[5, 5])
    return s.Matrix(12, 12, lambda i, j: pair(fundamental[i], fundamental[j]))


def magnetic_data(A, fundamental):
    matrices = [sum((A[k, a]*fundamental[a] for a in range(12)), s.zeros(7))
                for k in range(3)]
    pairs = ((1, 2), (2, 0), (0, 1))
    magnetic = s.Matrix.vstack(*(matrix_coordinates(matrices[i]*matrices[j]
                               -matrices[j]*matrices[i]).T for i, j in pairs))
    derivatives = []
    for k in range(3):
        for generator in fundamental:
            rows = []
            for i, j in pairs:
                variation = s.zeros(7)
                if i == k:
                    variation += generator*matrices[j]-matrices[j]*generator
                if j == k:
                    variation += matrices[i]*generator-generator*matrices[i]
                rows.append(matrix_coordinates(variation).T)
            derivatives.append(s.Matrix.vstack(*rows))
    return rational(magnetic), derivatives


def lagrangian_forces(e, phi, A, inventory):
    fundamental, rho, matter, adjoint, vacuum, _ = inventory
    volume = s.Abs(e.det())
    metric = rational(volume*e.inv()*ETA*e.inv().T)
    generators = [sum((A[k, a]*rho[a] for a in range(12)), s.zeros(70)) for k in range(3)]
    spatial = [T*phi for T in generators]
    shift = sum((metric[0, k+1]*spatial[k] for k in range(3)), s.zeros(70, 1))
    # P_i = h_i0*(Pi-b)/h00 + h_ij U_j is the original spatial
    # scalar momentum after solving only its temporal momentum equation.
    spatial_constant = [sum((metric[k+1, l+1]*spatial[l] for l in range(3)), s.zeros(70, 1))
                        -metric[k+1, 0]*shift/metric[0, 0] for k in range(3)]
    constant, momentum = s.zeros(106, 1), s.zeros(106)
    constant[:70, :] = sum((generators[k].T*spatial_constant[k] for k in range(3)), s.zeros(70, 1))
    constant[:70, :] -= 2*volume*(phi-vacuum)
    momentum[:70, :70] = sum((metric[k+1, 0]*generators[k].T/metric[0, 0]
                             for k in range(3)), s.zeros(70))
    for k in range(3):
        for a in range(12):
            row, direction = 70+12*k+a, rho[a]*phi
            constant[row] = (direction.T*spatial_constant[k])[0]
            momentum[row, :70] = metric[k+1, 0]*direction.T/metric[0, 0]

    Gram = native_gram(fundamental)
    constitutive = rational(-W*hodge(e)/SIGMA)
    equal(constitutive, constitutive.T)
    electric, mixed = constitutive[:3, :3], constitutive[:3, 3:]
    electric_inverse = rational(electric.inv())
    B, derivatives = magnetic_data(A, fundamental)
    # The original BF density has P_E=(K_E E+K_mix B)Gram.
    # Substitution in P_B supplies its field Euler derivative dB:P_B.
    magnetic_constant = rational((constitutive[3:, 3:]
        -constitutive[3:, :3]*electric_inverse*mixed)*B*Gram)
    magnetic_momentum = rational(s.kronecker_product(constitutive[3:, :3]*electric_inverse, s.eye(12)))
    for j, derivative in enumerate(derivatives):
        constant[70+j] += sum(a*b for a, b in zip(derivative, magnetic_constant))
        momentum[70+j, 70:] = derivative.reshape(1, 36)*magnetic_momentum
    weight = rational(s.kronecker_product(electric_inverse, Gram.inv()))
    gauge_shift = rational(mixed*B*Gram).reshape(36, 1)
    shift_jacobian = s.Matrix.hstack(*(rational(mixed*dB*Gram).reshape(36, 1) for dB in derivatives))
    assert scalar(s.trace(weight*shift_jacobian)) == 0
    # The ordering trace is linear in A. Check its complete36 coefficients,
    # so its derivative contributes no omitted force at any A.
    for j in range(36):
        direction = s.zeros(3, 12); direction[j] = 1
        _, dB = magnetic_data(direction, fundamental)
        derivative_shift = s.Matrix.hstack(*(rational(mixed*d*Gram).reshape(36, 1) for d in dB))
        assert scalar(s.trace(weight*derivative_shift)) == 0

    data = raw_matter(e, phi, s.zeros(1, 12).col_join(A))
    raw = original_inventory()
    Y = raw['scalar']+[s.I*T for T in raw['scalar']]
    one = [real_car(s.I*volume*data['E_inverse']*T) for T in Y]
    one += [real_car(s.I*data['E_inverse']*data['D'][k+1]*T)
            for k in range(3) for T in raw['gauge']]
    H = real_car(-s.I*data['E_inverse']*data['lower'])
    principal = s.diag(-s.eye(70)/(2*metric[0, 0]), -weight/2)
    first = rational((s.I*shift/metric[0, 0]).col_join(s.I*weight*gauge_shift))
    potential = (shift.T*shift)[0]/(2*metric[0, 0])
    potential -= sum(metric[k+1, l+1]*(spatial[k].T*spatial[l])[0]/2 for k in range(3) for l in range(3))
    potential += volume*((phi-vacuum).T*(phi-vacuum))[0]
    potential += (gauge_shift.T*weight*gauge_shift)[0]/2
    potential -= sum(a*b for a, b in zip(B, constitutive[3:, 3:]*B*Gram))/2
    return dict(constant=rational(constant), momentum=rational(momentum), one=one,
        principal=principal, first=first, potential=scalar(potential), matter=H,
        scalar_shift=shift, gauge_shift=gauge_shift, volume=volume,
        matter_A0=[real_car(-s.I*data['E_inverse']*data['D'][0]*T) for T in raw['gauge']],
        Gram=Gram)


def compare_coefficients(model, data, raw):
    equal(raw['constant'], data['identity_force'])
    equal(-s.I*raw['momentum'], data['first_force'])
    for left, right in zip(raw['one'], data['onebody_force']):
        equal(left, right)
    equal(raw['principal'], data['H_native_principal'])
    equal(raw['first'], data['H_native_first'])
    assert scalar(raw['potential']-data['H_native_identity']) == 0
    equal(raw['matter'], data['H_matter'])
    for left, right in zip(raw['matter_A0'], data['A0_matter_derivative']):
        equal(left, right)
    assert raw['scalar_shift'].todok() and raw['gauge_shift'].todok()
    assert raw['momentum'][:70, :70].todok()


def primitive_frames(model, inventory):
    fundamental, rho, matter, adjoint, vacuum, _ = inventory
    active = json.loads((BASE/'active-gauge/receipt.json').read_text())
    orbit = rational(s.Matrix.hstack(*(T*vacuum for T in rho)))
    chosen = active['J_independent_columns']
    assert list(orbit.rref()[1]) == chosen and len(chosen) == 9
    O = orbit[:, chosen]
    equal(O, model.scalar_frame[:, :9])
    projector = rational(s.eye(70)-O*(O.T*O).inv()*O.T)
    R = projector[:, list(projector.rref()[1])]
    equal(R, model.scalar_frame[:, 9:])
    equal(model.scalar_frame.T*model.scalar_force_lift, s.eye(70))
    equal(vacuum, model.phi0)
    for a in range(12):
        equal(rho[a], model.rho[a]); equal(adjoint[a], model.ad[a])
        equal(matter[a], model.common.rho[a])
    return {'active289_original_J_independent_columns': chosen,
        'literal_O70x9_equals_original_active289_J9': True,
        'original_orthogonal_peripheral61_and_full70_dual_lift': True}


def noether_coefficients(model, data, raw, inventory):
    _, rho, matter, adjoint, vacuum, _ = inventory
    field = data['phi'].col_join(data['A'].reshape(36, 1))
    torque = s.zeros(12, 1)
    for a in range(12):
        L = s.diag(rho[a], adjoint[a], adjoint[a], adjoint[a])
        R = s.diag(matter[a], matter[a].conjugate())
        V = L*field
        equal(L*raw['principal']+raw['principal']*L.T, s.zeros(106))
        equal(L*raw['first']-s.I*raw['momentum'].T*V, s.zeros(106, 1))
        current = sum((V[j]*raw['one'][j] for j in range(106)), s.zeros(504))
        equal(current+R*raw['matter']-raw['matter']*R, s.zeros(504))
        equal(raw['matter_A0'][a], -s.I*R)
        torque[a] = scalar((V.T*raw['constant'])[0])
        expected = -2*raw['volume']*((data['phi']-vacuum).T*rho[a]*vacuum)[0]
        assert scalar(torque[a]-expected) == 0
    derivative = rational(s.Matrix.vstack(*(-2*(T*vacuum).T for T in rho)))
    assert derivative.rank() == 9 and torque.todok()
    equal(model.native.S.T*torque, s.zeros(3, 1))
    equal(model.native.B.T*derivative, -2*model.scalar_frame[:, :9].T)
    equal(model.native.B.T*torque, -2*raw['volume']*model.scalar_frame[:, :9].T*(data['phi']-vacuum))
    return {'all12_complete_operator_coefficient_Noether_identities': True,
        'torque': encode(torque), 'rank_of_phi_torque_derivative': 9,
        'residual3_zero_and_original_broken9_contact_projection': True}


def bit_consumer(model, data, raw, inventory, jet):
    CAR = BitAction()
    values = {word: row['value'] for word, row in jet.items() if row['value']}
    expected = model.apply(data, jet)
    independent = []
    for j in range(106):
        central = {word: raw['constant'][j]*row['value']
                   -s.I*(raw['momentum'][j, :]*row['gradient'][16:, :])[0]
                   for word, row in jet.items()}
        result = total((1, central), (1, CAR.Q(raw['one'][j], values)))
        same(result, expected[j]); independent.append(result)
    _, rho, matter, adjoint, _, _ = inventory
    gauss = model.gauss(data, jet)
    field = data['phi'].col_join(data['A'].reshape(36, 1))
    for a in range(12):
        V = s.diag(rho[a], adjoint[a], adjoint[a], adjoint[a])*field
        central = {word: -s.I*(V.T*row['gradient'][16:, :])[0] for word, row in jet.items()}
        current = s.diag(matter[a], matter[a].conjugate())
        same(total((1, central), (s.I, CAR.Q(current, values))), gauss[a])
    # Y is literally reconstructed once in raw_matter. Repeating its whole
    # contribution changes this new full504 CAR consumer.
    yukawa_force = sum((data['phi'][j]*raw['one'][j] for j in range(70)), s.zeros(504))
    duplicated_Y = CAR.Q(yukawa_force, values)
    assert duplicated_Y
    mapped = model.scalar_readback(independent)
    return {'input_words': [list(word) for word in values],
        'all106_independent_bit_CAR_force_images_equal': True,
        'all12_original_A0_bit_CAR_images_equal': True,
        'Gauss_nonzero_rows_on_unconstrained_germ': sum(bool(row) for row in gauss),
        'force_nonzero_rows': sum(bool(row) for row in independent),
        'duplicate_original_Y_defect_words': len(duplicated_Y),
        'scalar_J9_and_peripheral61_reconstruct_full70': True}


def source_Gauss(model, inventory):
    current = candidate.SourceJointCurrentHilbertSection()
    values = {(): s.Rational(2, 7), (137, 391): s.Rational(3, 11)}
    gradients = {w: s.Matrix([s.Rational((j+len(w)) % 5-2, 47)
                              +s.I*s.Rational((2*j+len(w)) % 7-3, 53) for j in range(100)]) for w in values}
    Hessians = {w: s.zeros(100) for w in values}
    jet = current.section.extend_jet(*current.inverse_half_density_jet(values, gradients, Hessians))
    data = model.coefficients(model.phi0, model.A0)
    saved = model.gauss(data, jet)
    assert not any(saved)
    _, rho, matter, adjoint, _, _ = inventory
    field = model.phi0.col_join(model.A0.reshape(36, 1))
    CAR = BitAction()
    values122 = {w: row['value'] for w, row in jet.items() if row['value']}
    for a in range(12):
        V = s.diag(rho[a], adjoint[a], adjoint[a], adjoint[a])*field
        orbital = {w: -s.I*(V.T*row['gradient'][16:, :])[0] for w, row in jet.items()}
        R = s.diag(matter[a], matter[a].conjugate())
        same(total((1, orbital), (s.I, CAR.Q(R, values122))), {})
    return {'fresh_raw100_words': [list(w) for w in values], 'generated122_words': len(jet),
        'all12_Gauss_zero_read_from_generated_jet': True, 'Gauss_zero_input_required': False}


def main():
    started = time.monotonic()
    path = HERE/'source_full_native_quantum_force.json'
    receipt = json.loads(path.read_text()); count = bindings(receipt)
    assert receipt['root'] == candidate.ROOT_ID
    model = candidate.SourceFullNativeQuantumForce()
    inventory = representations()
    assert inventory[-1] == model.common.source_hashes
    frame = primitive_frames(model, inventory)
    phi = model.phi0+s.Matrix([s.Rational((3*j+1) % 7-3, 127) for j in range(70)])
    A = model.A0+s.Matrix(3, 12, lambda k, a: s.Rational((2*k+3*a+1) % 11-5, 131))
    lapse = model.e0[0, 0]
    time_column = (lapse, -lapse/19, lapse/23, lapse/29)
    data = model.coefficients(phi, A, time_column)
    raw = lagrangian_forces(data['e'], phi, A, inventory)
    compare_coefficients(model, data, raw)
    print('PASS original scalar/BF field Euler, all106 fixed-Pi coefficients and full504 currents', flush=True)
    noether = noether_coefficients(model, data, raw, inventory)
    print('PASS all12 original operator Noether identities and rank9 source torque', flush=True)
    jet = {}
    for k, word in enumerate(((), (137, 391), (13, 202, 454))):
        gradient = s.Matrix([s.Rational((j+2*k) % 7-3, 59)
                             +s.I*s.Rational((3*j+k) % 5-2, 61) for j in range(122)])
        jet[word] = {'value': s.Rational(k+2, 17), 'gradient': gradient, 'Hessian': s.zeros(122)}
    consumer = bit_consumer(model, data, raw, inventory, jet)
    assert consumer['Gauss_nonzero_rows_on_unconstrained_germ'] == 12
    assert consumer['force_nonzero_rows'] == 106
    source = source_Gauss(model, inventory)
    print('PASS new vacuum/N2/N3 bitCAR and actual source-generated Gauss12 zero', flush=True)
    paths = [Path(__file__), path, HERE/'source_full_native_quantum_force.py',
        HERE/'independent_source_joint_local_quantum.py', HERE/'independent_source_common_hamiltonian.py',
        HERE/'independent_source_gauge_legendre.py', HERE/'independent_source_lorentz_quantum_section.py',
        HERE/'independent_source_joint_charge_conservation.py', HERE/'source_joint_current_hilbert_section.py',
        HERE/'source_joint_current_hilbert_section.json', BASE/'active-gauge/receipt.json', BASE/'active-gauge/compute.py']
    result = {'root': candidate.ROOT_ID, 'verdict': 'CERTIFIED_FULL_NATIVE_FIXED_PI_FORCES_GAUSS12_AND_BROKEN_TORQUE',
        'source_sha256': receipt['source_sha256'], 'candidate_binding_checks': count,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'method': 'Original scalar and raw7x7 BF field variations at fixed velocity, followed by the independently solved original momentum equation; raw wedge/Dirac matter and independent full504 occupation-bit action.',
        'shifted_e': encode(data['e']), 'active_scalar_frame': frame, 'noether': noether,
        'unconstrained_bit_consumer': consumer, 'actual_source_Gauss': source,
        'ordering': 'All36 coefficients of the raw gauge ordering-divergence trace vanish. Scalar generators have trace zero. Original Y is consumed once.',
        'scope': 'K=0 homogeneous coefficients at fixed original full canonical Pi, on the original full504 finite CAR. Broken9 produce the displayed nonzero torque, distinct from Lorentz6 plus residual3 null Ward9. No current94 force transport is inferred.',
        'seconds': round(time.monotonic()-started, 3)}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS independent full native force', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
