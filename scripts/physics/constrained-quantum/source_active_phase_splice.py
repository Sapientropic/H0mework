#!/usr/bin/env python3
"""Source zero-momentum active Ward quotient in the actual physical slice."""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID
from source_full_linear_split import decode, P, K
from source_lorentz_contact import clean, equal, encode, GAMMA
from source_physical_phase_splice import SourcePhysicalPhaseSplice, zero
from source_coframe_live_ordering import FREE, DEPENDENT
from source_stabilizer_phase_reduction import canonical_J


def operator_action(operator, field, generator):
    time = P[0]
    operator = clean(operator.subs(dict.fromkeys(P[1:], 0)))
    degree = max(s.degree(v, time) for v in operator.todok().values())
    answer = s.zeros(operator.rows, field.cols)
    jet = field
    for order in range(degree+1):
        coefficient = operator.applyfunc(lambda x: s.expand(x).coeff(time, order))
        answer += coefficient*jet
        jet = jet*generator
    return clean(answer)


def main():
    started = time.monotonic()
    m = SourcePhysicalPhaseSplice(); c, split = m.chart, m.split
    retained = json.loads((HERE/'retained_matter_action.json').read_text())
    records = json.loads((HERE/'retained_hamiltonian_reduction.json').read_text())
    old = next(row for row in records['source_momenta'] if row['momentum'] == ['0', '0', '0'])
    generator = decode(old['consistent_generator'])
    quotient_section = decode(old['quotient_section'])
    size = generator.rows
    phase = clean(decode(old['velocity_quotient_section'])*decode(old['consistent_initial_data_embedding']))
    Y = phase[:121, :]
    kinetic = decode(retained['retained_time_coefficients'][2])
    zero(kinetic*(phase[121:, :]-Y*generator))
    lift = decode(retained['retained_field_lift'])
    full = operator_action(lift, Y, generator)
    U = decode(retained['normal_coordinate_change'])
    ward = clean(lift*U[:, 112:121])
    fields = split.active['fields']
    index = {(r['group'], tuple(r['coordinate'])): j for j, r in enumerate(fields)}
    gauge_rows = [index['coframe', (j//4, j%4)] for j in DEPENDENT]
    gauge_rows += [index['gauge_A', (j//12+1, j%12)] for j in c.gauge_pivots]
    Wg = clean(ward[gauge_rows, :].subs(dict.fromkeys(P[1:], 0)))
    assert not Wg.free_symbols
    assert Wg.det() != 0
    parameter = clean(-Wg.inv()*full[gauge_rows, :])
    fixed = clean(full+operator_action(ward, parameter, generator))
    zero(fixed[gauge_rows, :])
    zero(fixed[:9, :])
    print('PASS original126 consistent jets, full289 auxiliary lift and actual9 Ward-to-source-slice transformation', flush=True)
    de = s.Matrix.vstack(*(fixed[index['coframe', (a, mu)], :] for a in range(4) for mu in range(4)))
    domega = s.Matrix.vstack(*(fixed[index['Lorentz', (mu, a)], :] for mu in range(4) for a in range(6)))
    dA = s.Matrix.vstack(*(fixed[index['gauge_A', (mu, a)], :] for mu in range(4) for a in range(12)))
    psi_coords = s.Matrix.vstack(*(fixed[index['primal_H', (im, spin, color)], :] for im in range(2) for spin in range(4) for color in range(3)))
    chi_coords = s.Matrix.vstack(*(fixed[index['dual_H', (im, spin, color)], :] for im in range(2) for spin in range(4) for color in range(3)))
    psi = clean(split.O*(psi_coords[:12, :]+s.I*psi_coords[12:, :]))
    chi = clean(split.O*(chi_coords[:12, :]+s.I*chi_coords[12:, :]))
    model = c.common.coframe
    geometry = model.geometry(c.e0)
    Gt = geometry['G'][:, :16]
    background_omega = s.Matrix(split.active['actual_background']['lowered_Lorentz_connection']).applyfunc(s.sympify).reshape(24, 1)
    delta_Gt_omega = s.zeros(16, 16)
    for j in range(16):
        derivative = model.G[:, :16].diff(model.e[j])
        delta_Gt_omega[:, j] = model.at(derivative, c.e0).T*background_omega
    Pi_e = clean(Gt.T*domega+delta_Gt_omega*de)
    # The original BF auxiliary has Pi_A=magnetic(B)*native Gram.
    delta_Bmag = s.Matrix.vstack(*(fixed[index['gauge_B', (pair, a)], :] for pair in range(3, 6) for a in range(12)))
    Pi_A = clean(s.kronecker_product(s.eye(3), c.gauge.gram)*delta_Bmag)
    inverse_e, determinant = c.e0.inv(), c.e0.det()
    dE_chi = s.zeros(252, 16)
    for j in range(16):
        delta = s.zeros(4); delta[j] = 1
        dd = determinant*s.trace(inverse_e*delta)
        di = -inverse_e*delta*inverse_e
        dE4 = clean(s.I*sum(((dd*inverse_e[0, a]+determinant*di[0, a])*GAMMA[a] for a in range(4)), s.zeros(4)))
        dE_chi[:, j] = (split.chi0*s.kronecker_product(dE4, s.eye(63))).T
    p = clean(-s.I*(split.E.T*chi+dE_chi*de))
    q = s.Matrix.vstack(de[list(FREE), :], s.zeros(61, size), dA[12:, :], psi.applyfunc(s.re), psi.applyfunc(s.im))
    momentum = s.Matrix.vstack(Pi_e[list(FREE), :], s.zeros(61, size), Pi_A, -p.applyfunc(s.im), -p.applyfunc(s.re))
    whole = clean(q.col_join(momentum))
    zero(m.Ggrad*whole)
    physical = clean(m.chart_reader*whole)
    equal(m.chart_tangent*physical, whole)
    for ward_jet in old['original_Ward_jet_coordinates']:
        zero(physical*decode(ward_jet))
    consistent_reader = physical
    physical = clean(physical*quotient_section)
    equal(consistent_reader, physical*decode(old['quotient_map']))
    omega = clean(-physical.T*canonical_J(604)*physical)
    expected = decode(old['nondegenerate_phase_form'])
    equal(omega, expected)
    zero(physical.T*canonical_J(604)*m.tail_embedding)
    print('PASS actual BF/coframe, gauge auxiliary and full delta-p source readback; active126 symplectic congruence and tail orthogonality', flush=True)
    omega_inverse = clean(expected.inv(method='DM'))
    active_reader = clean(-omega_inverse*physical.T*canonical_J(604))
    equal(active_reader*physical, s.eye(126)); zero(active_reader*m.tail_embedding)
    zero(m.tail_reader*physical)
    common = clean(physical.row_join(m.tail_embedding))
    reader = clean(active_reader.col_join(m.tail_reader))
    equal(reader*common, s.eye(1208)); equal(common*reader, s.eye(1208))
    full_form = clean(-common.T*canonical_J(604)*common)
    equal(full_form, s.diag(expected, m.omega))
    # The energy is the original retained action's descended energy and the
    # raw complementary density; no independent completed spectrum is used.
    old_A, old_H = decode(old['Hamiltonian_generator']), decode(old['Hamiltonian_energy'])
    equal(expected*old_A, old_H)
    equal(consistent_reader*generator, physical*old_A*decode(old['quotient_map']))
    m.hamiltonian_and_phase()
    tail_A = m.generator.subs(dict.fromkeys(K, 0))
    tail_H = m.hessian.subs(dict.fromkeys(K, 0))
    split_generator, split_energy = s.diag(old_A, tail_A), s.diag(old_H, tail_H)
    canonical_energy = clean(reader.T*split_energy*reader)
    canonical_generator = clean(canonical_J(604)*canonical_energy)
    equal(canonical_generator*common, common*split_generator)
    equal(common.T*canonical_energy*common, split_energy)
    zero(canonical_energy-canonical_energy.T)
    # A real source jet with every active coordinate represented passes
    # through the old original field action and this complete common carrier.
    datum = s.Matrix([s.Rational((5*j+1)%13-6, 17) for j in range(126)])
    actual = clean(physical*datum)
    derivative = clean(canonical_generator*actual)
    equal(active_reader*derivative, old_A*datum)
    zero(m.tail_reader*derivative)
    print('PASS both1208 common-carrier inverses, original block-energy congruence and actual source canonical generator intertwining', flush=True)
    paths = [HERE/name for name in ('source_active_phase_splice.py', 'source_physical_phase_splice.py',
        'source_physical_phase_splice.json', 'source_stabilizer_phase_reduction.py',
        'source_stabilizer_phase_reduction.json', 'independent_source_stabilizer_phase_reduction.json',
        'retained_matter_action.json', 'independent_retained_matter_action.json',
        'retained_hamiltonian_reduction.json', 'independent_retained_hamiltonian_reduction.json',
        'source_stationary_cauchy_orbit.json', 'independent_source_stationary_cauchy_orbit.json')]
    paths += [BASE/'active-gauge/receipt.json']
    result = {'root': ROOT_ID, 'source_sha256': split.vertices['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'scope': 'ACTUAL_ZERO_MOMENTUM_COMMON1208_CANONICAL_SOURCE_PHASE_AND_ORIGINAL126_PLUS1082_ACTION',
        'source_momentum': [0, 0, 0], 'source_slice_Ward_minor': encode(Wg),
        'Ward_parameter_from_consistent138': encode(parameter),
        'original289_field_readback_from_consistent138': encode(fixed),
        'actual_active126_embedding': encode(physical), 'actual_active126_reader': encode(active_reader),
        'common1208_both_inverses_checked': True,
        'common_coordinate_recipe': 'X=[X_active126,X_tail1082]; inverse=[R_active126;R_tail1082], both productsI1208',
        'original_momentum_readback': 'delta Pi_e=Gt^T delta Omega+(delta Gt)^T Omega_source, Pi_A=delta B_magnetic*Gram, delta p=-i delta chi E-i chi_source delta E; real matter momenta=(-Im p,-Re p)',
        'BF_boundary': 'The coframe readback is the already source-generated reduced BF one-form, whose difference from the original BF potential is the exact variation of its original BF boundary. Its nonconstant Gt term is retained before differentiation.',
        'quotient_section_handling': 'The original quotient section need not intertwine the full field time generator. Construct the source field/auxiliary/Ward slice on138 consistent coordinates first; its canonical reader annihilates every original Ward jet and factors through the paid126 quotient.',
        'original_phase_form_congruence': 'X^T Omega_canonical X=diag(Omega_active,Omega_tail), Omega_canonical=-J604',
        'original_energy_congruence': 'X^T H_canonical X=diag(H_active,H_tail); H_active is the original retained-action energy and H_tail keeps its nonzero scalar-dual cross and source Noether phase shift',
        'actual_canonical_generator_intertwining': True,
        'actual_active_datum': encode(actual), 'actual_canonical_time_derivative': encode(derivative),
        'global_momentum_active_rank_or_intertwining_claimed': False,
        'nonlinear_energy_or_quantum_spectrum_replaced_by_linear_readout': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_active_phase_splice.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS original active physical phase splice', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
