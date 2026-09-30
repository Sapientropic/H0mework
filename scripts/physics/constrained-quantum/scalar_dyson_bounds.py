#!/usr/bin/env python3
"""Source-generated momentum-uniform bounds for the actual Dyson primitives.

The norm is the Euclidean norm of finite coefficient vectors/matrices, not a
physical Hilbert completion. For E(t,p)=exp(t L(p)), differentiation of
E'=L E gives (D^alpha E)'=L D^alpha E+sum_j alpha_j L_j D^(alpha-e_j) E.
The exact source logarithmic norm bound below is uniform in p. Variation of
constants and induction then give |D^alpha E| <= |t|^r exp(|t| Lambda) C^alpha.
Integrating the actual primitive yields the displayed |t|^(r+1)/(r+1) bound.
No commuting-matrix assumption is used. The two scalar induction integrals
are checked symbolically; every source catalogue coefficient and initial
vector is checked separately.
"""
from __future__ import annotations

from collections import defaultdict
import hashlib
import json
import time

import sympy as s

from dynamic import HERE, ROOT, ROOT_ID, decode
from full_matter_ports import clean, equal, encode
from scalar_dyson_time import ScalarDysonTime, KIN, KOUT, KAPPA

PBOUND, RBOUND, TBOUND = s.symbols('P R T', nonnegative=True)


def exact_abs(value):
    return s.simplify(s.sqrt(s.expand(value * s.conjugate(value))))


def maximum(values):
    answer = s.simplify(s.Max(*values))
    assert answer.is_real and answer.is_nonnegative
    for value in values:
        assert s.simplify(answer - value).is_nonnegative is True, (answer, value)
    return answer


def norms(matrix):
    """Exact source row/column sums and a verified Euclidean operator majorant."""
    rows = [s.Integer(0)] * matrix.rows
    columns = [s.Integer(0)] * matrix.cols
    for (i, j), value in matrix.todok().items():
        value = exact_abs(value)
        assert value.is_nonnegative is True
        rows[i] += value
        columns[j] += value
    row_max = maximum([s.simplify(value) for value in rows])
    column_max = maximum([s.simplify(value) for value in columns])
    absolute_sum = s.simplify(sum(rows))
    upper = s.simplify(s.sqrt(row_max * column_max))
    assert s.simplify(absolute_sum - upper).is_nonnegative is True
    return {'absolute_entry_sum': absolute_sum, 'maximum_row_sum': row_max,
            'maximum_column_sum': column_max, 'operator_two_norm_upper_bound': upper,
            'nonzero_entries': len(matrix.todok())}


def record_norms(data):
    return {key: int(value) if isinstance(value, int) else str(value) for key, value in data.items()}


def coefficients(matrix, variables):
    entries = defaultdict(dict)
    for indices, value in matrix.todok().items():
        for monomial, coefficient in s.Poly(value, *variables).terms():
            entries[monomial][indices] = coefficient
    parts = {monomial: s.SparseMatrix(*matrix.shape, value) for monomial, value in sorted(entries.items())}
    rebuilt = sum((s.prod(x ** n for x, n in zip(variables, monomial)) * value
                   for monomial, value in parts.items()), s.zeros(*matrix.shape))
    equal(matrix, rebuilt)
    return parts


def polynomial_majorants(matrix, variables):
    rows, by_degree = [], defaultdict(lambda: s.Integer(0))
    for monomial, value in coefficients(matrix, variables).items():
        bound = norms(value)
        by_degree[sum(monomial)] += bound['operator_two_norm_upper_bound']
        rows.append({'monomial': list(monomial), 'coefficient': encode(value), **record_norms(bound)})
    total = s.expand(sum(value * RBOUND ** degree for degree, value in by_degree.items()))
    return {'coefficient_bounds': rows, 'by_degree': dict(by_degree), 'bound': total}


def check_affine_source_matrix(A, variables):
    constant = clean(A.subs(dict.fromkeys(variables, 0)))
    linear = [clean(A.diff(p)) for p in variables]
    assert all(not (set(variables) & M.free_symbols) for M in linear)
    equal(A, constant + sum((p * M for p, M in zip(variables, linear)), s.zeros(*A.shape)))
    return constant, linear


def main():
    began = time.monotonic()
    native = ScalarDysonTime()
    catalogue = json.loads((HERE / 'scalar_dyson_time.json').read_text())
    audit = json.loads((HERE / 'independent_scalar_dyson_time.json').read_text())
    assert catalogue['root'] == audit['root'] == ROOT_ID
    for path, expected in audit['input_sha256'].items():
        assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == expected, path
    N = s.sympify(native.source['source_lapse'])

    H = native.H
    for j in range(3):
        equal(H[f'k{j+1}'], H[f'k{j+1}'].H)
    A0 = native.A['constant']
    growth = clean((A0 + A0.H) / 2)
    assert growth.todok()
    growth_bound = norms(growth)['operator_two_norm_upper_bound']
    full_free_bounds = {key: record_norms(norms(value)) for key, value in native.A.items()}
    for value in native.A.values():
        for indices in native.target_blocks + native.input_blocks:
            part = value.extract(indices, indices)
            equal(part + part.H, s.zeros(len(indices)))
    print('PASS source full252 spatial Hermiticity; grade6/grade2 full generators skew-Hermitian; full free logarithmic growth bound', growth_bound, flush=True)

    scalar_bounds = {}
    all_degree_bounds = defaultdict(list)
    scalar_full_bounds = polynomial_majorants(native.scalar_A, KAPPA)
    for zero, blocks, A in ((False, native.phase_blocks, native.scalar_A),
                            (True, native.zero_blocks, native.scalar_zero_A)):
        for number, ids in enumerate(blocks):
            part = A.extract(ids, ids)
            # L contains As^T, so its Hermitian part is the real symmetric
            # part below. All matter tensor factors contribute exactly zero.
            symmetric = clean((part.T + part.conjugate()) / 2)
            equal(symmetric, symmetric.H)
            bound = polynomial_majorants(symmetric, KAPPA)
            scalar_bounds[(zero, number)] = bound
            for degree in range(3):
                all_degree_bounds[degree].append(bound['by_degree'].get(degree, s.Integer(0)))
    global_growth_coefficients = {degree: maximum(values) for degree, values in all_degree_bounds.items()}
    global_growth = s.expand(sum(value * RBOUND**degree for degree, value in global_growth_coefficients.items()))
    vertex_bounds = [record_norms(norms(W)) for W in native.W]
    vertex_sum = s.simplify(sum(s.sympify(row['operator_two_norm_upper_bound']) for row in vertex_bounds))
    print('PASS source scalar244 coefficient majorants and all61 canonical vertex bounds; global Lambda(R)=', global_growth, flush=True)

    cache, checks = {}, []
    derivative_bounds = [[], [], []]
    v_bounds = []
    frozen_outgoing_defects = 0
    generators = {zero: dict(native.catalogue(zero=zero)) for zero in (False, True)}
    for row in catalogue['primitive_states']:
        zero, branch, sign, key = row['zero_mode'], row['branch'], row['sign'], tuple(row['key'])
        assert key in generators[zero]
        cache_key = (zero, branch, key)
        if cache_key not in cache:
            cache[cache_key] = native.state(key, generators[zero][key], 1, branch, zero=zero)
        state = cache[cache_key]
        # The actual physical transfer is installed before differentiating.
        # Freezing pout independently would omit the outgoing derivative.
        substitution = dict(zip(KOUT, [p if zero else p + sign * k for p, k in zip(KIN, KAPPA)]))
        physical_L = clean(state['signal_L'].subs(substitution, simultaneous=True))
        constant_L, Li = check_affine_source_matrix(physical_L, KIN)
        phase_size = len(state['phase_indices'])
        d = len(state['target_indices'])
        f = len(state['input_indices'])
        expected_growth = s.kronecker_product(
            clean((state['scalar_part'].T + state['scalar_part'].conjugate()) / 2), s.eye(d * f))
        equal((physical_L + physical_L.H) / 2, expected_growth)
        expected_linear = []
        for j, linear in enumerate(Li):
            equal(linear + linear.H, s.zeros(linear.rows))
            incoming = native.A[f'k{j+1}'].extract(state['input_indices'], state['input_indices'])
            outgoing = native.A[f'k{j+1}'].extract(state['target_indices'], state['target_indices'])
            if branch == -1:
                incoming, outgoing = -incoming.conjugate(), -outgoing.conjugate()
            expected = s.kronecker_product(s.eye(phase_size),
                -s.kronecker_product(s.eye(f), outgoing) + s.kronecker_product(incoming.T, s.eye(d)))
            equal(linear, expected)
            bound = norms(linear)['operator_two_norm_upper_bound']
            derivative_bounds[j].append(bound)
            expected_linear.append(bound)
            frozen = clean(state['signal_L'].diff(KIN[j]))
            if clean(linear - frozen).todok():
                frozen_outgoing_defects += 1
        vector = decode(row['signal_initial'])
        # Sign only changes the actual Fourier sine coefficients. Rebuild all
        # 1160 exact initial vectors from the source catalogue before bounding.
        if sign == 1:
            equal(vector, state['signal_initial'])
        else:
            mirrored = s.SparseMatrix(vector.rows, 1, {})
            block_size = d * f
            for pos in range(phase_size):
                source_phase = state['phase_indices'][pos]
                factor = -1 if 61 <= source_phase < 122 else 1
                mirrored[pos*block_size:(pos+1)*block_size, :] = factor * state['signal_initial'][pos*block_size:(pos+1)*block_size, :]
            equal(vector, mirrored)
        assert not (set(KIN) | set(KOUT) | set(KAPPA)) & vector.free_symbols
        vector_norm_squared = s.simplify(sum(value * s.conjugate(value) for value in vector.todok().values()))
        assert vector_norm_squared.is_positive is True
        vector_norm = s.simplify(s.sqrt(vector_norm_squared))
        v_bounds.append(vector_norm)
        local_growth = scalar_bounds[(zero, key[0])]['bound']
        difference = s.Poly(global_growth - local_growth, RBOUND)
        assert all(s.simplify(value).is_nonnegative is True for value in difference.all_coeffs())
        checks.append({'key': list(key), 'zero_mode': zero, 'branch': branch, 'sign': sign,
            'signal_dimension': physical_L.rows,
            'physical_transfer_installed_before_differentiation': True,
            'affine_in_physical_incoming_momentum': True,
            'all_derivative_generators_skew_Hermitian': True,
            'logarithmic_growth_from_scalar_only': True,
            'Lambda_R': str(local_growth), 'momentum_derivative_bounds': list(map(str, expected_linear)),
            'initial_coefficient_norm_squared': str(vector_norm_squared),
            'initial_coefficient_norm': str(vector_norm)})
    assert len(checks) == 1160
    C = [maximum(values) for values in derivative_bounds]
    V = maximum(v_bounds)
    assert frozen_outgoing_defects == 3 * len(checks)
    print('PASS all1160 actual catalogue coefficient bounds after pout=pin+/-kappa; Cj=', C, 'max||v||=', V, flush=True)

    # Generic scalar induction identities, not finitely sampled multi-indices.
    order = s.Symbol('r', integer=True, positive=True)
    degree = s.Symbol('d', integer=True, nonnegative=True)
    t = s.Symbol('time_length', positive=True)
    u = s.Symbol('integration_time', positive=True)
    derivative_integral = s.integrate(order * u**(order-1), (u, 0, t))
    primitive_integral = s.integrate(u**degree, (u, 0, t))
    assert s.simplify(derivative_integral - t**order) == 0
    assert s.simplify(primitive_integral - t**(degree+1)/(degree+1)) == 0

    paths = [HERE / name for name in [
        'full-matter-ports.json', 'scalar_canonical_phase.json', 'scalar_joint_hamiltonian.json',
        'scalar_dyson_time.py', 'scalar_dyson_time.json', 'independent_scalar_dyson_time.json',
        'scalar_dyson_fixed_N.json', 'independent_scalar_dyson_fixed_N.json', 'scalar_dyson_bounds.py']]
    scalar_records = [{'zero_mode': zero, 'component': number,
        'coefficient_bounds': value['coefficient_bounds'], 'Lambda_R': str(value['bound'])}
        for (zero, number), value in scalar_bounds.items()]
    result = {'root': ROOT_ID, 'source_sha256': native.source['source_sha256'],
        'scope': 'SOURCE_ALL61_DYSON_COEFFICIENT_SMOOTH_MOMENTUM_BOUNDS_AND_COMPACT_SUPPORT_TRANSPORT',
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'norm_convention': 'Euclidean norm on finite coefficient vectors and its induced matrix norm; this is not a physical Hilbert-state completion or an adjoint identification of the independent dual',
        'source_lapse': str(N), 'full252_A_coefficients': full_free_bounds,
        'all_three_full252_spatial_Hamiltonians_Hermitian': True,
        'full252_constant_Hamiltonian_Hermitian': False,
        'full252_constant_Hermiticity_defect_nonzero_entries': len((H['constant']-H['constant'].H).todok()),
        'full252_growth_Hermitian_part': encode(growth),
        'full252_freeflow_beta': str(growth_bound),
        'full252_freeflow_bound': '||exp(t*A(p))||_2 <= exp(|t|*beta), uniformly in every real incoming p; the momentum coefficients are skew-Hermitian',
        'grade6_grade2_all_coefficients_skew_Hermitian': True,
        'source_scalar244_absolute_coefficient_majorants': scalar_full_bounds['coefficient_bounds'],
        'source_scalar244_operator_majorant_R': str(scalar_full_bounds['bound']),
        'source_scalar_component_logarithmic_majorants': scalar_records,
        'all61_canonical_W_bounds': vertex_bounds, 'all61_sum_operator_bound': str(vertex_sum),
        'catalogue_coefficient_checks': checks, 'catalogue_count': len(checks),
        'global_Lambda_R': str(global_growth),
        'global_momentum_derivative_bounds': list(map(str, C)),
        'global_initial_coefficient_norm_bound': str(V),
        'incoming_momentum_dependence_of_growth_bound': 'none; P labels compact input support, not a UV cutoff',
        'frozen_outgoing_momentum_negative_control_defects': frozen_outgoing_defects,
        'multiindex_bound': 'r=|alpha|, E(t,p)=exp(t L(p)); ||partial_p^alpha E(t,p)||_2 <= |t|^r exp(T*Lambda_R) product_j C_j^alpha_j for |t|<=T and |kappa_j|<=R',
        'primitive_bound': '||partial_p^alpha Y(t,p)||_2 <= |t|^(r+1)/(r+1) exp(T*Lambda_R) ||v||_2 product_j C_j^alpha_j; Y is the actual augmented-exponential primitive from scalar_dyson_time',
        'derivative_equation': '(partial^alpha E)prime=L partial^alpha E+sum_j alpha_j L_j partial^(alpha-e_j)E; partial^alpha E(0)=0 for |alpha|>0',
        'proof_mechanism': 'Gronwall using the checked Hermitian part gives the uniform semigroup bound; variation of constants and induction in r use sum_j alpha_j=r; the symbolic integral r*integral_0^t s^(r-1)ds=t^r closes the induction; integrating the coefficient signal gives t^(r+1)/(r+1)',
        'commuting_L_or_derivative_generators_assumed': False,
        'generic_scalar_integral_identities_checked': {'derivative': str(derivative_integral), 'primitive': str(primitive_integral)},
        'smoothness': 'all actual L are affine in p and v is independent of p; entire finite matrix exponentials and the displayed uniform derivative bounds preserve C-infinity compact-momentum tests',
        'N1_support': 'input K maps into K+kappa or K-kappa; identity plus all61 source scalar pair maps into K union (K+kappa) union (K-kappa); zero mode leaves K unchanged',
        'support_cube': 'if every input coordinate |p_j|<=P and |kappa_j|<=R, N1 output has |p_j|<=P+R; neither P nor R is a physical cutoff',
        'fixed_N_support': 'for antisymmetric f(p1,...,pN;i1,...,iN), each surviving scalar Dyson word acts at most once on each particle line by the source grade law; each line lies in K_l union(K_l+kappa)union(K_l-kappa), hence the per-particle cube remains P+R',
        'general_m_insertions_coarse_support': 'without using the grade zero, m shifts give P+mR; the sharper fixed-N scalar bound uses the certified source one-line termination',
        'ordered_integral_consumer': 'apply the local coefficient bounds to ordered_integral_step; tensor factors retain their original boson order and the exact source momentum shifts',
        'proper_clock_conversion': 'tau=N*t, so a proper-time window T_tau uses T=T_tau/N and A_tau=A/N; no replacement by N*sqrt2 and no external Z',
        'continuous_scalar_kappa_convolution_bound_claimed': False,
        'unbounded_boson_domain_or_Hilbert_spectrum_completion_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began,3)}
    (HERE / 'scalar_dyson_bounds.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS source smooth compact-momentum Dyson bounds', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
