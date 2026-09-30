#!/usr/bin/env python3
"""Independent whole-source constrained retarded response audit.

Only frozen lower matrices are consumed; the new response producer is not
imported. Complete1208 normal systems are solved from independently recovered
SCCs by direct elimination, instead of using its active/scalar/matter inverse
recipes. Original source constraint rows are checked in ambient1214 space.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix as DM

from independent_source_active_retarded_inverse import DOMAIN, exact, coefficient, source_SCCs, zero
from independent_source_full_linear_split import read_matrix, K
from independent_source_physical_phase_splice import canonical, rectangular
from independent_source_joint_temporal_rates import HERE, ROOT, ROOT_ID, bindings, decode, encode


def bound_record(name):
    record = json.loads((HERE/name).read_text())
    assert record['root'] == ROOT_ID
    return record, bindings(record)


def load_original_fiber(sign):
    splice, checks = bound_record('source_spatial_active_phase_splice.json')
    audit, n = bound_record('independent_source_spatial_active_phase_splice.json'); checks += n
    assert audit['verdict'] == 'CERTIFIED_ACTUAL_NONZERO_PAIRED_MOMENTUM_SOURCE_COMMON_PHASE_AND_ORIGINAL_INTERTWINING'
    phase, n = bound_record('source_physical_phase_splice.json'); checks += n
    phase_audit, n = bound_record('independent_source_physical_phase_splice.json'); checks += n
    retained, n = bound_record('retained_hamiltonian_reduction.json'); checks += n
    full, n = bound_record('source_full_linear_split.json'); checks += n
    spatial, n = bound_record('source_spatial_phase_tangent.json'); checks += n
    independent_spatial, n = bound_record('independent_source_spatial_phase_tangent.json'); checks += n
    assert all(record['source_sha256'] == splice['source_sha256'] for record in
               (audit, phase, phase_audit, retained, full, spatial, independent_spatial))
    row = splice['fibers'][0 if sign == 1 else 1]
    k = tuple(map(s.sympify, row['momentum'])); point = dict(zip(K, k))
    reference = next(r for r in retained['source_momenta'] if any(s.sympify(x) != 0 for x in r['momentum']))
    old = lambda name: read_matrix(reference[name]) if sign == 1 else read_matrix(reference[name]).conjugate()
    Xa, Ra = exact(read_matrix(row['active_embedding'])), exact(read_matrix(row['active_reader']))
    Xt = exact(read_matrix(phase['original_nonlinear_chart_tangent']))*exact(read_matrix(phase['tail_embedding_into_actual1208']))
    Ot = exact(read_matrix(phase['tail_original_symplectic_form'])); J = exact(canonical(607))
    # Solve each one-term original tail symplectic row directly for its
    # covector reader; no new inverse, symplectic form or normalization enters.
    rhs = -(Xt.transpose()*J)
    result = {}
    assert sum(len(row) for row in Ot.rep.values()) == 1082
    for i, values in Ot.rep.items():
        assert len(values) == 1
        j, value = next(iter(values.items()))
        result[j] = {column: entry/value for column, entry in rhs.rep.get(i, {}).items()}
    Rt = DM(result, (1082, 1214), DOMAIN).to_sparse()
    zero(Ot*Rt-rhs); zero(Rt*Xt-DM.eye((1082, 1082), DOMAIN))
    X, R = DM.hstack(Xa, Xt), DM.vstack(Ra, Rt)
    T = X*R
    zero(R*X-DM.eye((1208, 1208), DOMAIN)); zero(T*T-T); zero(R*T-R); zero(T*X-X)
    tail = full['triangular_tail']
    at = lambda name: read_matrix(tail[name]).subs(point)
    At = exact(rectangular(1082, 1082, [(0, 0, at('dual')), (480, 480, at('scalar')),
        (602, 602, at('primal')), (480, 0, at('dual_to_scalar')), (602, 480, at('scalar_to_primal'))]))
    Aa, Ha, Oa = [exact(old(name)) for name in ('Hamiltonian_generator', 'Hamiltonian_energy', 'nondegenerate_phase_form')]
    Ht = exact(read_matrix(phase['original_tail_Hamiltonian']['original_density_Hamiltonian_hessian']).subs(point))
    A = exact(rectangular(1208, 1208,
        [(0, 0, Aa.to_Matrix()), (126, 126, At.to_Matrix())]))
    H = exact(rectangular(1208, 1208, [(0, 0, Ha.to_Matrix()), (126, 126, Ht.to_Matrix())]))
    O = exact(rectangular(1208, 1208, [(0, 0, Oa.to_Matrix()), (126, 126, Ot.to_Matrix())]))
    zero(O*A-H)
    C = exact(read_matrix(spatial['Gauss']).subs(point))
    F = exact(read_matrix(spatial['slice_reader']).subs(point))
    zero(C*X); zero(F*X)
    return dict(sign=sign, k=k, X=X, R=R, T=T, A=A, H=H, Omega=O, J=J, C=C, F=F,
                checks=checks, hashes=splice['source_sha256'])


def solve_whole_system(A, forcing, z):
    """Direct block normal-equation solves for the complete original1208."""
    groups = source_SCCs(A)
    solutions = []; stored_rows = {}
    for i, group in enumerate(groups):
        rhs = forcing.extract(group, range(forcing.shape[1]))
        for j in range(i):
            feed = A.extract(group, groups[j])
            if not feed.is_zero_matrix: rhs += feed*solutions[j]
        for j in range(i+1, len(groups)): zero(A.extract(group, groups[j]))
        diagonal = DM.eye((len(group), len(group)), DOMAIN).scalarmul(z)-A.extract(group, group)
        value = diagonal.lu_solve(rhs).to_sparse()
        zero(diagonal*value-rhs)
        solutions.append(value)
        for local, row in value.rep.items(): stored_rows[group[local]] = dict(row)
    answer = DM(stored_rows, forcing.shape, DOMAIN).to_sparse()
    zero(answer.scalarmul(z)-A*answer-forcing)
    return answer, list(map(len, groups))


def compare_readout(value, record):
    nonzero = sorted(value.rep)
    rows = sorted(set([0, value.shape[0]-1, *nonzero[:8], *nonzero[-8:]]))
    assert rows == record['rows'] and record['whole_vector_dimension'] == value.shape[0]
    zero(value.extract(rows, [0])-exact(decode(record['values'])))


def actual_consumer(sign, record, tail_record, active_record):
    fiber = load_original_fiber(sign)
    X, R, T, A = [fiber[key] for key in ('X', 'R', 'T', 'A')]
    assert list(map(str, fiber['k'])) == record['momentum']
    seed = s.Matrix([s.Rational((7*j+2)%17-8, 31)+s.I*s.Rational((11*j+3)%19-9, 37) for j in range(1214)])
    if sign == -1: seed = seed.conjugate()
    ambient = exact(seed); f = T*ambient; split = R*ambient
    assert not (ambient-f).is_zero_matrix
    zero(f-X*split); zero(R*f-split); zero(fiber['C']*f); zero(fiber['F']*f)
    active = next(row for row in active_record['source_fibres'] if any(s.sympify(k) != 0 for k in row['momentum']))
    beta_active = s.sympify(active['actual_consumer']['source_norm_bound']['beta'])
    beta_tail = s.sympify(tail_record['global_bounds']['beta'])
    assert s.simplify(beta_active-s.sympify(record['source_active_beta'])) == 0
    assert s.simplify(beta_tail-s.sympify(record['source_tail_beta'])) == 0
    zsym = s.sympify(record['laplace']); z = coefficient(zsym)
    assert s.simplify(s.re(zsym)-beta_active) > 0 and s.simplify(s.re(zsym)-beta_tail) > 0
    column = tail_record['actual_two_stage_time_consumer']['dual_initial_coordinate']
    assert column == record['dual_forcing_coordinate_in_tail']
    dual = DM({126+column: {0: DOMAIN.one}}, (1208, 1), DOMAIN)
    right_input = split.scalarmul(z)-A*split
    rhs = DM.hstack(split, right_input, dual)
    solved, groups = solve_whole_system(A, rhs, z)
    left = solved.extract(range(1208), [0]); recovered = solved.extract(range(1208), [1])
    cascade_split = solved.extract(range(1208), [2])
    zero(recovered-split)
    response, cascade = X*left, X*cascade_split
    zero(response.scalarmul(z)-X*(A*(R*response))-f)
    zero(T*response-response); zero(fiber['C']*response); zero(fiber['F']*response)
    zero(X*recovered-f)
    zero(cascade.scalarmul(z)-X*(A*(R*cascade))-X*dual)
    assert not cascade_split.extract(range(126+480, 126+602), [0]).is_zero_matrix
    assert not cascade_split.extract(range(126+602, 1208), [0]).is_zero_matrix
    compare_readout(response, record['response_readout']); compare_readout(cascade, record['two_stage_response_readout'])
    # Original source coefficients prove every-column projected identities.
    zero(R*X-DM.eye((1208, 1208), DOMAIN)); zero(X*R-T)
    assert record['strict_incompatible_forcing_rejected'] is True
    assert record['explicit_projection_changes_actual_source'] is True
    return fiber, response, cascade, {'momentum': record['momentum'], 'laplace': str(zsym),
        'whole1208_direct_normal_systems_solved': True, 'SCC_dimensions': groups,
        'whole1214_left_and_right_inverse_to_source_T': True,
        'original_Gauss_and_slice_rows_annihilate_response': True,
        'actual_incompatible_source_has_nonzero_projection_defect': True,
        'explicit_admitted_source_Tu_verified': True,
        'original_dual_scalar_primal_cascade_nonzero': True,
        'source_active_bound': str(beta_active), 'source_tail_bound': str(beta_tail)}


def main():
    began = time.monotonic(); path = HERE/'source_common_retarded_phase.json'
    candidate = json.loads(path.read_text()); checks = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    active, n = bound_record('source_active_retarded_inverse.json'); checks += n
    active_audit, n = bound_record('independent_source_active_retarded_inverse.json'); checks += n
    tail, n = bound_record('source_full_linear_retarded.json'); checks += n
    tail_audit, n = bound_record('independent_source_full_linear_retarded.json'); checks += n
    assert all(r['source_sha256'] == candidate['source_sha256'] for r in (active, active_audit, tail, tail_audit))
    plus, response, cascade, report_p = actual_consumer(1, candidate['actual_consumers'][0], tail, active)
    checks += plus['checks']
    print('PASS direct complete1208 solve, source1214 projected inverses and genuine two-stage forcing', flush=True)
    minus, response_m, cascade_m, report_m = actual_consumer(-1, candidate['actual_consumers'][1], tail, active)
    checks += minus['checks']
    zero(response_m-exact(response.to_Matrix().conjugate()))
    zero(cascade_m-exact(cascade.to_Matrix().conjugate()))
    for key in ('X', 'R', 'T', 'A'): zero(minus[key]-exact(plus[key].to_Matrix().conjugate()))
    print('PASS opposite source momentum/Laplace reality and all-column source jump/projector factors', flush=True)
    assert candidate['retarded_distribution']['actual_onshell_current_to_phase_forcing_installed'] is False
    assert candidate['whole1082_scalar_dual_cross_or_growth_modes_removed'] is False
    assert candidate['interacting_composite_measure_or_proton_lifetime_generated'] is False
    paths = [HERE/name for name in ('independent_source_common_retarded_phase.py', 'source_common_retarded_phase.py',
        'source_common_retarded_phase.json', 'independent_source_active_retarded_inverse.py',
        'source_active_retarded_inverse.json', 'independent_source_active_retarded_inverse.json',
        'source_full_linear_retarded.json', 'independent_source_full_linear_retarded.json',
        'source_spatial_active_phase_splice.json', 'independent_source_spatial_active_phase_splice.json',
        'source_spatial_phase_tangent.json', 'independent_source_spatial_phase_tangent.json',
        'source_physical_phase_splice.json', 'independent_source_physical_phase_splice.json',
        'source_full_linear_split.json', 'retained_hamiltonian_reduction.json', 'scalar_canonical_phase.json')]
    result = {'root': ROOT_ID, 'source_sha256': candidate['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'verdict': 'CERTIFIED_SOURCE_COMMON_PHYSICAL_RETARDED_RESPONSE_AND_PROJECTED_JUMP',
        'scope': candidate['scope'], 'checked_input_bindings': checks, 'candidate_constructor_imported': False,
        'source_fibres': [report_p, report_m],
        'generic_inverse_review': 'The paid complete active and tail inverses apply to the exact original diagonal source generators assembled here. RX=I, XR=T, TX=X and RT=R yield both (zI-A)G=T and G(zI-A)=T for G=X diag(Ra,Rt)R, A=X diag(Aa,At)R, as well as TG=GT=G. No ambient identity replaces the actual source projector.',
        'source_recipe_review': 'The producer scalar canonical formula is exactly the signed old Q/Gram/L numerator recipe. Its real matter branches use coefficient conjugation and -k before recombination, retaining the original between-block Yukawa. All two-stage tail feeds remain. The active leaf characteristic quotients and source DAG are inherited unchanged; the formal K(z) parser preserves the actual scalar field operations.',
        'forcing_contract_review': 'The independently reconstructed ambient seed has u-Tu!=0. The strict producer computes this literal exact predicate and raises, while the separate projection API returns both Tu and the defect. The compatible forcing tested above is generated by the same T; no Ward compatibility is assumed for arbitrary CAR or static states.',
        'retarded_distribution_review': 'The paid active entire bound and tail polynomial-times-exponential bound give convergence on their common half-plane. The zero-past source evolution X diag(exp(tAa),exp(tAt))R has right limitXR=T, hence (partial_t-A)Gret=delta T. This is the stationary classical representation; original-time endpoints remain a separate same-orbit consumer.',
        'source_current_to_phase_forcing_quantum_spectrum_or_lifetime_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_common_retarded_phase.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent source common physical retarded phase', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
