#!/usr/bin/env python3
"""Independent complete source time evolution and two-endpoint phase audit.

The time producer is not imported. Source matrix powers, original momentum
variation, and chirality/exterior-degree phases are reconstructed separately.
"""
from __future__ import annotations

from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path
import time

import sympy as s
from sympy.polys.matrices import DomainMatrix as DM

from independent_source_common_retarded_phase import (
    load_original_fiber, bound_record, DOMAIN, exact, coefficient, zero,
    HERE, ROOT, ROOT_ID, decode, encode)
from independent_source_joint_temporal_rates import BASE, read_gamma, PAIRS


def conjugate(A):
    return exact(A.to_Matrix().conjugate())


def check_compact(vector, record):
    boundaries = (0, 6, 67, 103, 355, 607, 613, 674, 710, 962, 1214)
    rows = {0, vector.shape[0]-1}
    for start, end in zip(boundaries, boundaries[1:]):
        if start < vector.shape[0]:
            rows.add(next((j for j in range(start, min(end, vector.shape[0]))
                           if vector.rep.get(j, {}).get(0, DOMAIN.zero)), start))
    assert sorted(rows) == record['source_rows']
    assert vector.shape[0] == record['complete_vector_dimension']
    zero(vector.extract(sorted(rows), [0])-exact(decode(record['values'])))


@lru_cache(maxsize=None)
def absolute_bound(value):
    return s.simplify(abs(s.re(value))+abs(s.im(value)))


def matrix_bounds(A):
    row = [s.S.Zero for _ in range(A.shape[0])]
    column = [s.S.Zero for _ in range(A.shape[1])]
    for i, entries in A.rep.items():
        for j, value in entries.items():
            weight = absolute_bound(DOMAIN.to_sympy(value))
            row[i] += weight; column[j] += weight
    largest_row, largest_column = map(s.simplify, (max(row), max(column)))
    integer = int(s.ceiling(max(largest_row, largest_column)))
    assert integer >= largest_row and integer >= largest_column
    return {'row': largest_row, 'column': largest_column,
            'operator2': s.sqrt(largest_row*largest_column), 'integer': integer}


def real_phase(rates, frequency, unit=None):
    """Original real canonical map, made directly as 252 two-plane actions."""
    entries = {(j, j): 1 for j in range(1214)} if unit is not None else {}
    for base in (103, 710):
        for j, rate in enumerate(rates):
            if unit is None:
                entries[base+j, base+252+j] = -frequency*rate
                entries[base+252+j, base+j] = frequency*rate
            else:
                value = s.expand_complex(unit**rate)
                real, imag = s.re(value), s.im(value)
                entries[base+j, base+j] = real
                entries[base+j, base+252+j] = -imag
                entries[base+252+j, base+j] = imag
                entries[base+252+j, base+252+j] = real
    return exact(s.SparseMatrix(1214, 1214, entries))


def raw_phase_consumer(candidate, fiber, u0, w0):
    orbit, checks = bound_record('source_stationary_cauchy_orbit.json')
    audit, count = bound_record('independent_source_stationary_cauchy_orbit.json'); checks += count
    assert audit['verdict'] == 'CERTIFIED_ACTUAL_SOURCE_CAUCHY_ORBIT_AND_FULL_STATIONARY_LINEARIZATION'
    cauchy, count = bound_record('source_first_order_cauchy.json'); checks += count
    fields = cauchy['analytic_Cauchy_source_construction']['nonempty_source_witness']['literal_source_fields']
    e0, psi0, chi0 = [decode(fields[name]) for name in ('e', 'psi', 'chi')]
    internal = [(degree, word) for degree in (6, 2, 4)
                for word in itertools.combinations(range(7), degree)]
    rp = [1-2*int(spin >= 2)-2*int(degree == 6)
          for spin in range(4) for degree, _ in internal]
    rd = [1-2*int(spin >= 2)+2*int(degree == 6)
          for spin in range(4) for degree, _ in internal]
    assert rp == orbit['primal_integer_rates'] == candidate['canonical_phase']['primal_source_integer_rates']
    assert rd == orbit['independent_dual_integer_rates'] and rd != [-r for r in rp]
    omega = s.sympify(orbit['source_frequency'])
    assert omega == 18*s.sqrt(15)/125 and s.simplify(e0[0, 0]**2-s.Rational(54, 125)) == 0
    gamma = read_gamma()
    principal = [s.kronecker_product(s.I*G, s.eye(63)) for G in gamma]
    spins = [s.kronecker_product(gamma[a]*gamma[b]/2, s.eye(63)) for a, b in PAIRS]
    # Every coefficient has zero Laurent phase weight, proving every real
    # time identity rather than checking a selection of phases.
    for E in principal:
        for matrix in [E, *[E*spin for spin in spins]]:
            for (i, j), value in matrix.todok().items():
                assert value != 0 and rd[i]+rp[j] == 0
    for spin in spins:
        for i, j in spin.todok(): assert rp[i] == rp[j]

    inverse = e0.inv(); volume = e0.det(); assert volume > 0
    E = sum((inverse[0, a]*principal[a] for a in range(4)), s.zeros(252))*volume
    derivatives = []
    for index in range(16):
        direction = s.zeros(4); direction[index] = 1
        differential = volume*(s.trace(inverse*direction)*inverse-inverse*direction*inverse)
        derivative = sum((differential[0, a]*principal[a] for a in range(4)), s.zeros(252))
        for i, j in derivative.todok(): assert rd[i]+rp[j] == 0
        derivatives.append(derivative)
    for j in (0, 4, 8, 12): zero(exact(derivatives[j]))

    splice, count = bound_record('source_spatial_active_phase_splice.json'); checks += count
    retained, count = bound_record('retained_hamiltonian_reduction.json'); checks += count
    active = next(row for row in retained['source_momenta'] if tuple(map(s.sympify, row['momentum'])) == fiber['k'])
    original = exact(decode(splice['fibers'][0]['original289_field_map']))
    field = original*exact(decode(active['quotient_section']))*w0.extract(range(126), [0])
    manifest_path = BASE/'active-gauge/receipt.json'
    manifest = json.loads(manifest_path.read_text())['fields']
    rows = [next(j for j, entry in enumerate(manifest)
                 if entry['group'] == 'coframe' and tuple(entry['coordinate']) == (a, mu))
            for a in range(4) for mu in range(4)]
    de = field.extract(rows, [0]).to_Matrix().reshape(4, 4)
    for j, index in enumerate((5, 9, 10, 13, 14, 15)):
        assert coefficient(de[index]) == u0.rep[j][0]
    assert all(de[a, 0] != 0 for a in range(4))
    saved = candidate['original_phase_chain']
    zero(exact(de)-exact(decode(saved['actual_full_original_coframe_variation'])))
    zero(exact(de[:, 0])-exact(decode(saved['actual_nonzero_temporal_coframe_column'])))
    dE = exact(sum((de[j]*derivatives[j] for j in range(16)), s.zeros(252)))
    assert not dE.is_zero_matrix
    unit = s.Rational(12, 13)+s.I*s.Rational(5, 13)
    assert s.expand(unit*s.conjugate(unit)) == 1
    Up = exact(s.diag(*[s.expand_complex(unit**r) for r in rp]))
    Ud = exact(s.diag(*[s.expand_complex(unit**r) for r in rd]))
    ED, psi, chi = exact(E), exact(psi0), exact(chi0)
    zero(Ud*ED*Up-ED); zero(Ud*dE*Up-dE)
    q = u0.extract(range(103, 355), [0])+u0.extract(range(355, 607), [0]).scalarmul(coefficient(s.I))
    p = -(u0.extract(range(962, 1214), [0])+u0.extract(range(710, 962), [0]).scalarmul(coefficient(s.I))).transpose()
    dchi = (p.scalarmul(coefficient(s.I))-chi*dE)*ED.inv()
    original_momentum = (dchi*Ud*ED+chi*Ud*dE).scalarmul(coefficient(-s.I))
    expected = p*Up.inv(); zero(original_momentum-expected)
    S, Kcan = real_phase(rp, omega, unit), real_phase(rp, omega)
    moved = S*u0
    actual_p = -(moved.extract(range(962, 1214), [0])+moved.extract(range(710, 962), [0]).scalarmul(coefficient(s.I))).transpose()
    zero(actual_p-expected)
    omission = (chi*Ud*dE).scalarmul(coefficient(s.I))
    assert not omission.is_zero_matrix
    zero(omission-exact(decode(saved['omit_source_chi_deltaE_nonzero_defect'])))
    for spin in map(exact, spins):
        value = dchi*ED*spin*psi+chi*ED*spin*q+chi*dE*spin*psi
        transformed = dchi*Ud*ED*spin*Up*psi+chi*Ud*ED*spin*Up*q+chi*Ud*dE*spin*Up*psi
        zero(value-transformed)
    Omega = -fiber['J']
    zero(S.transpose()*S-DM.eye((1214, 1214), DOMAIN))
    zero(S.transpose()*Omega*S-Omega)
    zero(Kcan.transpose()+Kcan); zero(Kcan.transpose()*Omega+Omega*Kcan)
    return S, Kcan, rp, omega, checks, rows


def main():
    started = time.monotonic()
    candidate, checks = bound_record('source_common_phase_time.json')
    retarded, count = bound_record('independent_source_common_retarded_phase.json'); checks += count
    assert retarded['verdict'] == 'CERTIFIED_SOURCE_COMMON_PHYSICAL_RETARDED_RESPONSE_AND_PROJECTED_JUMP'
    plus, minus = load_original_fiber(1), load_original_fiber(-1)
    checks += plus['checks']+minus['checks']
    assert candidate['source_sha256'] == plus['hashes'] == minus['hashes']
    for name in ('X', 'R', 'T', 'A', 'H', 'Omega'):
        zero(minus[name]-conjugate(plus[name]))
    X, R, A, H, Omega = [plus[name] for name in ('X', 'R', 'A', 'H', 'Omega')]
    original_Omega = -plus['J']; opposite_R = minus['R']
    zero(original_Omega*X-opposite_R.transpose()*Omega)
    splice, count = bound_record('source_spatial_active_phase_splice.json'); checks += count
    u0 = exact(decode(splice['fibers'][0]['actual_phase_datum']))
    um = exact(decode(splice['fibers'][1]['actual_phase_datum']))
    zero(um-conjugate(u0)); w0 = R*u0; zero(X*w0-u0)
    check_compact(u0, candidate['actual_full_time_recursions']['original_initial_datum'])
    check_compact(w0, candidate['actual_full_time_recursions']['full_split_initial_datum'])
    # Keep raw powers separately; factorial division happens after taking
    # powers, independently of the producer's coefficient recurrence.
    powers, negative = [w0], [minus['R']*um]
    coefficients, physical = [], []
    for j in range(21):
        if j:
            powers.append(A*powers[-1]); negative.append(minus['A']*negative[-1])
        zero(negative[j]-conjugate(powers[j]))
        coefficient_j = powers[j].scalarmul(coefficient(s.Rational(1, s.factorial(j))))
        physical_j = X*coefficient_j
        zero(R*physical_j-coefficient_j)
        zero(plus['C']*physical_j); zero(plus['F']*physical_j)
        zero(minus['X']*negative[j] - conjugate(X*powers[j]))
        if j:
            zero((original_Omega*physical_j).scalarmul(coefficient(j))-opposite_R.transpose()*H*coefficients[j-1])
        coefficients.append(coefficient_j); physical.append(physical_j)
    print('PASS independent all21 full1208 powers, original1214 Hamiltonian equations and paired spatial constraints', flush=True)

    normA, normX = matrix_bounds(A), matrix_bounds(X)
    for actual, key in ((normA, 'generator'), (normX, 'embedding')):
        for name, value in actual.items():
            assert s.simplify(value-s.sympify(candidate['source_bounds'][key][name])) == 0
    elapsed = s.Rational(1, 2*normA['integer'])
    saved_time = candidate['actual_controlled_time_value']
    assert elapsed == s.sympify(saved_time['elapsed_time']) and saved_time['order'] == 20
    partial = sum((coefficients[j].scalarmul(coefficient(elapsed**j)) for j in range(21)), DM.zeros((1208, 1), DOMAIN))
    ambient = X*partial; check_compact(ambient, saved_time['stationary_value'])
    initial_bound = sum(absolute_bound(v) for v in w0.to_Matrix())
    split_remainder = 2*initial_bound/(2**21*s.factorial(21))
    physical_remainder = normX['integer']*split_remainder
    assert s.simplify(split_remainder-s.sympify(saved_time['split_remainder_upper_bound'])) == 0
    assert s.simplify(physical_remainder-s.sympify(saved_time['original_phase_remainder_upper_bound'])) == 0
    assert split_remainder > 0 and not saved_time['finite_partial_sum_declared_exact_solution']
    cascade = candidate['complete_tail_cascade']
    dual, primal = cascade['dual_initial_source_coordinate'], cascade['primal_reader_source_coordinate']
    impulse = exact(s.SparseMatrix(1208, 1, {(126+dual, 0): 1}))
    for order in range(1, 4):
        impulse = A*impulse
        if order < 3: zero(impulse.extract(range(728, 1208), [0]))
    third = DOMAIN.to_sympy(impulse.rep[728+primal][0])
    assert s.simplify(third-s.sympify(cascade['whole1208_third_primal_derivative'])) == 0
    assert third == 162*s.sqrt(30)/3125
    print('PASS complete source time value, rigorous coefficient norm remainder and genuine third-order tail cascade', flush=True)

    S, Kcan, rates, omega, count, coframe_rows = raw_phase_consumer(candidate, plus, u0, w0)
    checks += count
    at_start = S*u0; phaseX, phaseR = S*X, R*S.transpose()
    zero(phaseR*at_start-w0); zero(phaseX*phaseR*at_start-at_start)
    zero(phaseR*phaseX-DM.eye((1208, 1208), DOMAIN))
    jump_probe = exact(s.SparseMatrix(1214, 1, {(67, 0): 1}))
    defect = phaseX*phaseR*jump_probe-plus['T']*jump_probe
    assert not defect.is_zero_matrix
    first = Kcan*at_start+S*physical[1]
    second = Kcan*Kcan*at_start+(Kcan*S*physical[1]+S*physical[2]).scalarmul(coefficient(2))
    L0 = phaseX*A*phaseR
    zero(first-(Kcan+L0)*at_start)
    # Differentiating L(t)=S(t) A S(t)^-1 contributes [K,L].
    original_second = ((Kcan+L0)*(Kcan+L0)+Kcan*L0-L0*Kcan)*at_start
    zero(second-original_second)
    saved = candidate['actual_nonzero_initial_phase']
    for vector, name in ((at_start, 'initial_state'), (defect, 'moving_vs_frozen_jump_nonzero_control'),
                         (first, 'original_first_derivative'), (second, 'original_second_derivative')):
        check_compact(vector, saved[name])
    phase_partial = (S*ambient).to_Matrix()
    endpoint = saved['future_value_with_exact_second_endpoint_rotation']
    expected = []
    for row in endpoint['source_rows']:
        base = 103 if 103 <= row < 607 else 710 if 710 <= row < 1214 else None
        if base is None:
            expected.append(phase_partial[row]); continue
        index = (row-base) % 252; angle = omega*rates[index]*elapsed
        pair = s.Matrix([[s.cos(angle), -s.sin(angle)], [s.sin(angle), s.cos(angle)]])
        value = pair*s.Matrix([phase_partial[base+index], phase_partial[base+252+index]])
        expected.append(value[int(row-base >= 252)])
    saved_values = decode(endpoint['values'])
    assert not s.SparseMatrix(s.Matrix(expected)-saved_values).applyfunc(s.expand).todok()
    print('PASS raw all16 coframe momentum chain, arbitrary phase weights, two actual endpoints and moving initial jump', flush=True)

    paths = [Path(__file__), HERE/'source_common_phase_time.py', HERE/'source_common_phase_time.json',
        HERE/'independent_source_common_retarded_phase.py', HERE/'independent_source_common_retarded_phase.json',
        HERE/'source_stationary_cauchy_orbit.json', HERE/'independent_source_stationary_cauchy_orbit.json',
        HERE/'source_first_order_cauchy.json', HERE/'source_spatial_active_phase_splice.json',
        HERE/'retained_hamiltonian_reduction.json', BASE/'active-gauge/receipt.json']
    result = {'root': ROOT_ID, 'source_sha256': plus['hashes'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks': checks,
        'verdict': 'CERTIFIED_COMPLETE_SOURCE_TIME_ACTION_AND_ORIGINAL_TWO_ENDPOINT_CAUCHY_PHASE',
        'candidate_time_constructor_imported': False,
        'scope': 'Existing two nonzero opposite spatial momenta; complete classical linearized constrained source phase, not interacting quantum spectral evolution.',
        'momenta': [list(map(str, plus['k'])), list(map(str, minus['k']))],
        'complete_time_consumer': {'split_dimension': 1208, 'original_dimension': 1214,
            'verified_coefficient_count': 21, 'verified_original_Hamiltonian_recurrences': 20,
            'all_order_spatial_constraint_and_opposite_momentum_checks': True,
            'source_generator_integer_bound': normA['integer'], 'source_embedding_integer_bound': normX['integer'],
            'elapsed_source_time': str(elapsed), 'split_remainder': str(s.cancel(split_remainder)),
            'original_phase_remainder': str(s.cancel(physical_remainder)),
            'actual_third_order_dual_scalar_primal_entry': str(third)},
        'original_phase_consumer': {'raw_manifest_coframe_rows': coframe_rows,
            'all16_coframe_entries_read_from_original289_map': True, 'all4_time_column_entries_nonzero': True,
            'all16_principal_and24_coframe_current_coefficients_covariant_for_arbitrary_time': True,
            'actual_chi0_deltaE_omission_nonzero': True,
            'real_canonical_momentum_phase_derived_from_independent_chi': True,
            'actual_source_nonzero_start_and_distinct_Ts_jump': True,
            'complete_first_second_original_time_derivatives_checked': True,
            'second_endpoint_source_sine_cosine_rotation_checked': True},
        'analytic_review': 'The finite source matrix norm proves absolute entire exponential convergence and termwise differentiation on every compact time interval. The 20th partial sum is bounded by the explicit positive 21st-order tail, not declared exact. Source phase maps are real orthogonal and symplectic, preserving this evaluation error. The original two-endpoint propagator has S(t) on the left and S(s)^-1 on the right; its causal jump is T(s), and differentiating gives Kcan+S(t)X A_split R S(t)^-1.',
        'quantum_spectral_measure_open_channel_or_lifetime_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'independent_source_common_phase_time.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent common source time action', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
