#!/usr/bin/env python3
"""The literal source phase orbit in the complete constrained Cauchy system.

The original bosons are stationary and the independent matter pair follows
the original two phase representations. Full original density coefficients,
including coframe-current and Yukawa terms, transport all its jets. This
identifies the source co-rotating Jacobi operator with variation about an
actual orbit of the already constructed spacetime Cauchy producer.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, decode
from source_first_order_cauchy import SourceFirstOrderCauchy, zero_spatial, encode_fields
from source_lorentz_contact import clean, equal, encode, GAMMA
from source_full_linear_split import SourceFullLinearSplit


def phase_support(matrix, primal_rates, dual_rates):
    entries = s.SparseMatrix(matrix).todok()
    assert all(dual_rates[row]+primal_rates[col] == 0 for row, col in entries)
    return len(entries)


def main():
    started = time.monotonic()
    saved = json.loads((HERE/'source_first_order_cauchy.json').read_text())
    certified = json.loads((HERE/'independent_source_first_order_cauchy.json').read_text())
    phase = json.loads((BASE/'full-phase/receipt.json').read_text())
    split = SourceFullLinearSplit(); model = SourceFirstOrderCauchy()
    fields = {key: decode(value) for key, value in
              saved['analytic_Cauchy_source_construction']['nonempty_source_witness']['literal_source_fields'].items()}
    rates = model.rhs(fields, zero_spatial(fields))['rates']
    rp, rd = phase['primal_rates_in_units_frequency'], phase['dual_rates_in_units_frequency']
    Rp, Rd = s.diag(*rp), s.diag(*rd)
    omega = s.sympify(phase['source_frequency'])
    equal(fields['psi'], split.psi0); equal(fields['chi'], split.chi0)
    for key in ('e', 'Omega', 'A', 'F', 'phi', 'U'):
        equal(rates[key], s.zeros(*rates[key].shape))
    equal(rates['psi'], s.I*omega*Rp*fields['psi'])
    equal(rates['chi'], s.I*omega*fields['chi']*Rd)
    assert rates['psi'].todok() and rates['chi'].todok()
    print('PASS literal source full1500 Cauchy rates: stationary bosons and both original phase representations', flush=True)
    common = model.common
    density_matrices = {}
    # These span every live coframe/Lorentz/native-connection coefficient of
    # the complete first-order real density, rather than its source value only.
    gammas = [clean(s.kronecker_product(s.I*G, s.eye(63))) for G in GAMMA]
    for mu, E in enumerate(gammas):
        density_matrices['principal_'+str(mu)] = E
        for a, spin in enumerate(common.coframe.lorentz.spin):
            density_matrices[f'Lorentz_{mu}_{a}'] = clean(E*s.kronecker_product(spin, s.eye(63)))
        for a, rho in enumerate(common.rho):
            density_matrices[f'gauge_{mu}_{a}'] = clean(E*rho)
    for a, Y in enumerate(common.yukawa_basis):
        density_matrices['scalar_'+str(a)] = Y
        density_matrices['scalar_'+str(a+35)] = s.I*Y
    counts = {key: phase_support(M, rp, rd) for key, M in density_matrices.items()}
    # Temporal phase differentiation is part of the original matter jets.
    # Multiplication by either diagonal rate keeps every density support.
    for E in gammas:
        phase_support(E*Rp, rp, rd)
        phase_support(Rd*E, rp, rd)
        equal(Rd*E+E*Rp, s.zeros(252))
    for V in split.V:
        phase_support(V, rp, rd)
    data = common.matter_data(fields['e'], fields['phi'], split.A)
    Omega = s.zeros(6, 1).col_join(fields['Omega'])
    original_lower = clean(data['lower_without_Lorentz']+sum(
        (value*V for value, V in zip(Omega, data['Lorentz_ports'])), s.zeros(252)))
    stationary = clean(original_lower+s.I*omega*data['E']*Rp)
    equal(stationary, split.K0)
    equal(original_lower-s.I*omega*Rd*data['E'], stationary)
    equal(stationary*fields['psi'], s.zeros(252, 1))
    equal(fields['chi']*stationary, s.zeros(1, 252))
    for mu in range(4):
        equal(data['principal'][mu], [split.E, *split.Ei][mu])
    assert certified['literal_original_source']['all_rows_zero']
    assert certified['literal_original_source']['all_introduced_constraints_zero']
    print('PASS all146 original density coefficients,158 Jacobi vertices and exact complete stationary Dirac shift', flush=True)
    inputs = [HERE/name for name in ('source_stationary_cauchy_orbit.py', 'source_first_order_cauchy.py',
        'source_first_order_cauchy.json', 'independent_source_first_order_cauchy.json',
        'source_full_linear_split.py', 'source_full_linear_split.json', 'source_common_hamiltonian.py',
        'source_lorentz_contact.py')]
    inputs.extend([BASE/'full-phase/receipt.json', BASE/'active-gauge/receipt.json'])
    bindings = {}
    for source in (saved, certified, phase):
        for key in ('source_sha256', 'input_sha256'):
            for name, expected in source.get(key, {}).items():
                path = ROOT/name
                actual = hashlib.sha256(path.read_bytes()).hexdigest()
                assert actual == expected, name
                bindings[name] = actual
    bindings.update({str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs})
    result = {'root': ROOT_ID, 'source_sha256': saved['source_sha256'], 'input_sha256': bindings,
        'scope': 'ACTUAL_ORIGINAL_SOURCE_CAUCHY_ORBIT_AND_COMPLETE_STATIONARY_JACOBI_IDENTIFICATION',
        'orbit': 'bosons(t)=bosons_source; psi(t)=exp(i*omega*t*Rp)*psi0; chi(t)=chi0*exp(i*omega*t*Rd)',
        'primal_integer_rates': rp, 'independent_dual_integer_rates': rd,
        'source_frequency': str(omega), 'proper_clock': 'tau=N*t, N='+str(split.N),
        'actual_original_source_rates': encode_fields(rates),
        'full_density_phase_support_counts': counts,
        'all158_original_vertex_coefficients_phase_stationary': True,
        'all_original_density_coefficients_including_temporal_phase_jets_checked': True,
        'stationary_full252_primal_and_dual_constant_exact': True,
        'original_Euler_all_time_argument': [
            'Every original matter coefficient has rd(row)+rp(column)=0. Thus every bilinear of the displayed matter orbit and any of its time/spatial jets is the same as its value at0; all coframe variations and their derivatives use the same checked coefficient span.',
            'The original bosons and their jets are constant. Their1310 Euler rows, auxiliary equations and initial constraints at0 are already checked on the literal source. The preceding coefficient identity transports the bosonic equations and constraints for every real t.',
            'The primal and independent-dual Euler equations factor by their invertible phase matrices. The original temporal derivatives give Kstationary=Koriginal+i*omega*E*Rp=Koriginal-i*omega*Rd*E, exactly the complete generator used by full_linear_split.',
            'The explicit analytic orbit stays in the same source noncharacteristic chart. Local Cauchy uniqueness identifies it with the original constrained spacetime producer for its literal source initial data.'],
        'Jacobi_consumer': 'Transform perturbations by the same two phase matrices and differentiate the full original density. Its time derivative contributes the checked stationary shift; its remaining coefficients are time independent by the146 coefficient identities. The full1310 common carrier in source_full_linear_split is therefore the stationary representation of variation along this actual orbit.',
        'general_initial_data_orbit_stationarity_claimed': False,
        'retarded_linear_response_is_interacting_composite_spectrum': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_stationary_cauchy_orbit.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS actual source Cauchy orbit and full linearization bridge', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
