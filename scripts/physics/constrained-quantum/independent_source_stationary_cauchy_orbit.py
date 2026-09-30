#!/usr/bin/env python3
"""Independent all-time source orbit and full-action co-rotation audit.

Original integer phase weights come from chirality and exterior degree. A
Laurent phase variable verifies the coefficient identities for arbitrary time,
not a set of sampled times. The literal1500 Cauchy rates and original1310
Euler rows are read through the independent raw first-order producer.
"""
from __future__ import annotations

import hashlib
import itertools
import json
from pathlib import Path
import time
import sympy as s

from independent_source_first_order_cauchy import IndependentFirstOrder, load_fields, original_1310_at_initial, count_real
from independent_source_full_linear_split import build_raw
from independent_source_joint_temporal_rates import HERE, BASE, ROOT, ROOT_ID, bindings, clean, decode, encode, eq, zero


def main():
    began = time.monotonic(); path = HERE/'source_stationary_cauchy_orbit.json'
    candidate = json.loads(path.read_text()); checks = bindings(candidate)
    model = IndependentFirstOrder(); raw = model.raw
    assert candidate['root'] == ROOT_ID and candidate['source_sha256'] == raw.hashes
    cauchy = json.loads((HERE/'source_first_order_cauchy.json').read_text())
    cauchy_audit = json.loads((HERE/'independent_source_first_order_cauchy.json').read_text())
    phase = json.loads((BASE/'full-phase/receipt.json').read_text())
    for record in (cauchy, cauchy_audit, phase): checks += bindings(record)
    fields = load_fields(cauchy['analytic_Cauchy_source_construction']['nonempty_source_witness']['literal_source_fields'])
    spatial = [{key: s.zeros(*value.shape) for key, value in fields.items()} for _ in range(3)]
    produced = model.rhs(fields, spatial)
    assert count_real(fields) == count_real(produced['rates']) == 1500
    for name, value in produced['rates'].items(): eq(value, decode(candidate['actual_original_source_rates'][name]))
    initial = original_1310_at_initial(model, fields, spatial, produced)
    internal = [(degree, word) for degree in (6, 2, 4) for word in itertools.combinations(range(7), degree)]
    rp = [-(1 if spin >= 2 else -1)-2*int(degree == 6) for spin in range(4) for degree, _ in internal]
    rd = [-(1 if spin >= 2 else -1)+2*int(degree == 6) for spin in range(4) for degree, _ in internal]
    assert rp == candidate['primal_integer_rates'] == phase['primal_rates_in_units_frequency']
    assert rd == candidate['independent_dual_integer_rates'] == phase['dual_rates_in_units_frequency']
    Rp, Rd = (s.SparseMatrix(252, 252, {(j, j): rate for j, rate in enumerate(rates)}) for rates in (rp, rd))
    frequency = s.sympify(raw.active['source_frequency'])
    zero(frequency-s.sympify(candidate['source_frequency']))
    eq(fields['psi'], raw.psi0); eq(fields['chi'], raw.chi0)
    for name in ('e', 'Omega', 'A', 'F', 'phi', 'U'): eq(produced['rates'][name], s.zeros(*fields[name].shape))
    eq(produced['rates']['psi'], s.I*frequency*Rp*raw.psi0)
    eq(produced['rates']['chi'], s.I*frequency*raw.chi0*Rd)
    assert produced['rates']['psi'].todok() and produced['rates']['chi'].todok()
    print('PASS independent literal1500 rates/original1310 Euler and both source-derived integer phase representations', flush=True)

    matrices = {}
    for mu, gamma in enumerate(raw.gamma):
        principal = s.kronecker_product(s.I*gamma, s.eye(63))
        matrices['principal_'+str(mu)] = principal
        for a, spin in enumerate(raw.spin): matrices[f'Lorentz_{mu}_{a}'] = s.kronecker_product(s.I*gamma*spin, s.eye(63))
        for a, rho in enumerate(raw.rho63): matrices[f'gauge_{mu}_{a}'] = s.kronecker_product(s.I*gamma, rho)
    for a, Y in enumerate(raw.Y): matrices['scalar_'+str(a)] = Y
    assert len(matrices) == 146
    matrices = {name: s.SparseMatrix(matrix) for name, matrix in matrices.items()}
    phase_variable = s.Symbol('unit_phase', nonzero=True)
    primal_phase = s.SparseMatrix(252, 252, {(j, j): phase_variable**rate for j, rate in enumerate(rp)})
    dual_phase = s.SparseMatrix(252, 252, {(j, j): phase_variable**rate for j, rate in enumerate(rd)})
    counts = {}
    for name, matrix in matrices.items():
        # Exact Laurent coefficients prove the whole time identity after
        # unit_phase=exp(i omega t), and preserve every differentiated jet.
        transported = s.SparseMatrix(matrix.rows, matrix.cols, {(i, j): value*phase_variable**(rd[i]+rp[j]) for (i, j), value in matrix.todok().items()})
        eq(transported, matrix)
        eq(Rd*matrix+matrix*Rp, s.zeros(252))
        counts[name] = len(matrix.todok())
    assert counts == candidate['full_density_phase_support_counts']
    for mu in range(4):
        E = matrices['principal_'+str(mu)]
        eq(Rd*E+E*Rp, s.zeros(252))
        for coefficient in (E*Rp, Rd*E):
            eq(Rd*coefficient+coefficient*Rp, s.zeros(252))
    # Each higher time derivative simply multiplies an entry by powers of
    # its two integer rates; it never changes this zero total phase weight.
    print('PASS all146 raw density Laurent identities and temporal-jet supports for every real time', flush=True)

    native = build_raw(raw)
    assert len(native['vertices']) == 158
    for _, _, V in native['vertices']:
        eq(Rd*V+V*Rp, s.zeros(252))
    e, phi = fields['e'], fields['phi']
    omega = s.zeros(6, 1).col_join(fields['Omega'])
    original_K = raw.lower(e, phi, raw.A, omega)
    E = s.kronecker_product(raw.principals(e)[0], s.eye(63))
    stationary_primal = clean(original_K+s.I*frequency*E*Rp)
    stationary_dual = clean(original_K-s.I*frequency*Rd*E)
    eq(stationary_primal, stationary_dual)
    eq(stationary_primal, native['D'].subs(dict.fromkeys(s.symbols('p0:4', real=True), 0)))
    eq(stationary_primal*raw.psi0, s.zeros(252, 1))
    eq(raw.chi0*stationary_dual, s.zeros(1, 252))
    eq(Rd*stationary_primal+stationary_primal*Rp, s.zeros(252))
    # These are the actual original matter Euler rows at arbitrary phase,
    # including the original temporal derivative rather than an alias clock.
    psi = primal_phase*raw.psi0; chi = raw.chi0*dual_phase
    psi_dot = s.I*frequency*Rp*psi
    chi_dot = s.I*frequency*chi*Rd
    eq(E*psi_dot+original_K*psi, s.zeros(252, 1))
    eq(chi*original_K-chi_dot*E, s.zeros(1, 252))
    # The phase maps are invertible for every real t. The kinetic density
    # acquires exactly the same shifted term at arbitrary perturbed fields.
    for name, matrix in matrices.items():
        if name.startswith('principal_'):
            eq(dual_phase*matrix*primal_phase, matrix)
            eq(dual_phase*matrix*(s.I*frequency*Rp*primal_phase), s.I*frequency*matrix*Rp)
    print('PASS all158 raw vertices, exact complete Dirac-dual stationary shift and actual all-time original matter Euler rows', flush=True)

    # Chart denominators involve only the stationary bosons; they stay equal
    # to their original nonzero source values along the explicit orbit.
    A0, D9 = model.A0(fields['phi'], fields['U'][0, :].T)
    zero(D9.det()-256)
    source_chart = cauchy['analytic_Cauchy_source_construction']['nonempty_source_witness']
    for expression in ('source_time_minor_determinant', 'source_D9_determinant', 'source_coframe_determinant',
                       'source_spatial_metric_determinant', 'source_scalar_time_coefficient', 'source_native_gauge_time_metric'):
        assert s.sympify(source_chart[expression]) != 0
    paths = [Path(__file__), path, HERE/'source_stationary_cauchy_orbit.py',
        HERE/'independent_source_first_order_cauchy.py', HERE/'independent_source_first_order_cauchy.json',
        HERE/'independent_source_full_linear_split.py', HERE/'source_first_order_cauchy.json',
        HERE/'source_full_linear_split.json', BASE/'full-phase/receipt.json', BASE/'active-gauge/receipt.json']
    result = {'verdict': 'CERTIFIED_ACTUAL_SOURCE_CAUCHY_ORBIT_AND_FULL_STATIONARY_LINEARIZATION',
        'root': ROOT_ID, 'source_sha256': raw.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks': checks, 'candidate_orbit_constructor_imported': False,
        'independent_method': 'raw literal1500 RHS/original1310 Euler; chirality and exterior-degree weights; exact146 Laurent coefficient identities and original158 density vertices',
        'initial_source': initial,
        'all_time_orbit': {'stationary_original_bosons': True, 'both_independent_phase_rates_nonzero': True,
            'density_coefficient_count': 146, 'vertex_count': 158,
            'arbitrary_phase_Laurent_identity_not_time_sampling': True,
            'original_full252_primal_and_dual_Euler_zero_for_arbitrary_phase': True,
            'every_bilinear_time_jet_preserves_zero_total_phase_weight': True,
            'specific_literal_orbit_stays_in_source_chart_for_all_real_time': True},
        'full_time_Euler_argument': [
            'Every original matter density coefficient has zero total dual/primal phase weight. Multiplication by integer rate powers keeps that support, so all time/spatial jet bilinears and coframe/connection/scalar variations retain their source values.',
            'The bosons, curvature, auxiliary fields and their jets are stationary. Their original Euler rows and introduced constraints therefore remain the verified source-zero values; the two independent matter Euler systems vanish by the displayed exact phase factorization.',
            'The explicit orbit is analytic and remains in the same noncharacteristic source chart. The previously certified constrained Cauchy uniqueness identifies its germ with the same-source Cauchy producer; this does not assert global evolution for other initial data.'],
        'linearization_identification': {
            'complete_nonlinear_density_transform': 'For arbitrary bosonic fields each coefficient is a real linear combination of the checked146 matrices. Pulling back psi=Up xi and chi=zeta Ud gives the original stationary density, with the sole time-jet contribution i omega E Rp; pure bosonic terms are unchanged.',
            'Jacobi': 'Differentiate this full density identity at the constant source. The source_full_linear_split1310 Jacobi operator is consequently the stationary representation of variation along the actual source orbit, with both perturbation phases and their temporal derivatives retained.',
            'independent_dual_replaced_by_Hilbert_adjoint': False,
            'proper_time_reparameterized': False},
        'general_initial_data_stationarity_or_global_Cauchy_claimed': False,
        'interacting_composite_spectrum_or_lifetime_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_stationary_cauchy_orbit.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS independent actual source orbit and stationary action', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
