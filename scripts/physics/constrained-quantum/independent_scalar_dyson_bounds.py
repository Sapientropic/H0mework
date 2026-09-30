#!/usr/bin/env python3
"""Audit all source Dyson coefficient bounds without the bound/time constructors.

The original action supplies the 252 drift. Original phase coordinates and
entrywise coefficient differentiation reconstruct the complete catalogue.
Analytic consequences use the displayed matrix ODE and norm inequalities;
this audit does not claim a Lean implementation of a smooth function domain.
"""
from __future__ import annotations

from collections import defaultdict, Counter
from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path
import re
import time

import sympy as s

from independent_scalar_dyson_time import (
    OriginalAction, ROOT_ID, source, clean, equal, decode, validate, partition,
    coefficient_derivative, zero, K, KIN, KOUT, KAP,
)

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
ROOT = HERE.parents[3]
R = s.Symbol('R', nonnegative=True)


def read(path):
    return json.loads(path.read_bytes())


def number(value):
    return s.sympify(value, locals={'R': R})


@lru_cache(maxsize=None)
def modulus(value):
    result = s.simplify(s.sqrt(s.re(value)**2+s.im(value)**2))
    assert result.is_nonnegative is True and not result.free_symbols
    return result


def largest(values):
    result = s.Integer(0)
    for value in values:
        difference = s.simplify(value-result)
        if difference.is_nonnegative is True:
            result = value
        else:
            assert s.simplify(-difference).is_nonnegative is True, (result, value)
    return s.simplify(result)


norm_cache = {}


def direct_norms(matrix):
    entries = tuple(sorted(matrix.todok().items()))
    key = (matrix.shape, entries)
    if key in norm_cache:
        return norm_cache[key]
    # The weighted Cauchy inequality gives ||M||_2^2 <= rowmax*colmax.
    # Only real/imaginary constant source coefficients are used here.
    rows = [s.Integer(0) for _ in range(matrix.rows)]
    columns = [s.Integer(0) for _ in range(matrix.cols)]
    for (i, j), value in entries:
        absolute = modulus(value)
        rows[i] += absolute
        columns[j] += absolute
    rows, columns = [list(map(s.simplify, values)) for values in (rows, columns)]
    rowmax, colmax = largest(rows), largest(columns)
    result = {'maximum_row_sum': rowmax, 'maximum_column_sum': colmax,
              'absolute_entry_sum': s.simplify(sum(rows)),
              'operator_two_norm_upper_bound': s.simplify(s.sqrt(rowmax*colmax)),
              'nonzero_entries': len(entries)}
    norm_cache[key] = result
    return result


def check_norms(matrix, row):
    computed = direct_norms(matrix)
    for name, value in computed.items():
        assert s.simplify(value-number(row[name])) == 0, (name, value, row[name])
    return computed['operator_two_norm_upper_bound']


def polynomial_bound(matrix, rows):
    assembled = zero(*matrix.shape)
    degree_bounds = defaultdict(lambda: s.Integer(0))
    seen = set()
    for row in rows:
        powers = tuple(row['monomial'])
        assert len(powers) == 3 and powers not in seen
        assert all(isinstance(n, int) and n >= 0 for n in powers)
        seen.add(powers)
        part = decode(row['coefficient'])
        assert part.shape == matrix.shape and not part.free_symbols
        assembled += s.prod(p**a for p, a in zip(KAP, powers))*part
        degree_bounds[sum(powers)] += check_norms(part, row)
    equal(matrix, assembled)
    degree_bounds = {degree: s.simplify(value) for degree, value in degree_bounds.items()}
    return s.expand(sum(value*R**degree for degree, value in degree_bounds.items())), degree_bounds


def main():
    started = time.monotonic()
    candidate_path = HERE/'scalar_dyson_bounds.json'
    candidate = read(candidate_path)
    assert candidate['root'] == ROOT_ID
    bound = validate(candidate)
    paths = {name: HERE/name for name in (
        'scalar_canonical_phase.json', 'independent_scalar_canonical_phase.json',
        'scalar_joint_hamiltonian.json', 'independent_scalar_joint_hamiltonian.json',
        'full-matter-ports.json', 'scalar_dyson_time.json', 'independent_scalar_dyson_time.json',
        'scalar_dyson_fixed_N.json', 'independent_scalar_dyson_fixed_N.json',
        'wavepacket_audit.json',
    )}
    records = {name: read(path) for name, path in paths.items()}
    for record in records.values():
        assert record['root'] == ROOT_ID
        bound += validate(record)
    scalar, pair, matter, time_data = [records[name] for name in (
        'scalar_canonical_phase.json', 'scalar_joint_hamiltonian.json',
        'full-matter-ports.json', 'scalar_dyson_time.json')]
    assert records['independent_scalar_dyson_time.json']['verdict'] == \
        'CERTIFIED_ALL61_SOURCE_N1_TIME_PRIMITIVES_AND_ONE_ORDERED_N2_COEFFICIENT'
    assert records['wavepacket_audit.json']['verdict'] == \
        'CERTIFIED_ARBITRARY_MOMENTUM_WAVEPACKET_GRADE_AND_ALTERNATING_ORDERED_WORDS'
    assert not records['wavepacket_audit.json']['continuous_smooth_compact_domain_closed']

    active_path, phase_path, vertices_path = [BASE/name for name in (
        'active-gauge/receipt.json', 'full-phase/receipt.json', 'matter-vertices/receipt.json')]
    active, phase, vertices = map(read, (active_path, phase_path, vertices_path))
    _, vacuum, degrees, hashes = source.parse_source(ROOT)
    assert hashes == candidate['source_sha256'] == scalar['source_sha256'] == matter['source_sha256']
    gamma_path = ROOT/'Lean/SaturationMonoid/PhysicsCore/DiracCliffordRepresentation.lean'
    gamma = []
    for name in ('Zero', 'One', 'Two', 'Three'):
        literal = re.search(r'def diracGamma'+name+r'\s*:.*?:=\s*!!\[(.*?)\]',
                            gamma_path.read_text(), re.S).group(1)
        gamma.append(s.SparseMatrix([[s.sympify(v.strip().replace('Complex.I', 'I'))
            for v in row.split(',')] for row in literal.split(';')]))
    action = OriginalAction(active, phase, vertices, vacuum, degrees, gamma)
    raw = action.holonomic(action.configuration(zero(289, 1)), s.Matrix(K))
    A = clean(-raw['inverse_E']*raw['K'])
    equal(raw['E']*A+raw['K'], zero(252))
    coefficients = matter['stationary_Hamiltonian_coefficients']
    H = {name: decode(row) for name, row in coefficients.items()}
    equal(A, -s.I*(H['constant']+sum((k*H[str(k)] for k in K), zero(252))))
    affine = {'constant': clean(A.subs(dict.fromkeys(K, 0))),
              **{str(k): clean(A.diff(k)) for k in K}}
    equal(A, affine['constant']+sum((k*affine[str(k)] for k in K), zero(252)))
    assert all(not value.free_symbols for value in affine.values())
    for k in K:
        equal(H[str(k)], H[str(k)].H)
        equal(affine[str(k)]+affine[str(k)].H, zero(252))
    defect = clean(H['constant']-H['constant'].H)
    assert len(defect.todok()) == candidate['full252_constant_Hermiticity_defect_nonzero_entries'] == 48
    growth = clean((affine['constant']+affine['constant'].H)/2)
    equal(growth, decode(candidate['full252_growth_Hermitian_part']))
    beta = direct_norms(growth)['operator_two_norm_upper_bound']
    assert s.simplify(beta-number(candidate['full252_freeflow_beta'])) == 0
    assert beta == 6*s.sqrt(30)/25
    for name, value in affine.items():
        check_norms(value, candidate['full252_A_coefficients'][name])

    inside = [d for d in degrees for _ in itertools.combinations(range(7), d)]
    ids = {d: [spin*63+i for spin in range(4) for i, degree in enumerate(inside) if degree == d]
           for d in degrees}
    out_blocks, in_blocks = partition(ids[6], A), partition(ids[2], A)
    assert out_blocks == time_data['matter_target_blocks'] and in_blocks == time_data['matter_input_blocks']
    for value in affine.values():
        for block in out_blocks+in_blocks:
            local = value.extract(block, block)
            equal(local+local.H, zero(len(block)))
    W = [clean(-s.I*raw['inverse_E']*decode(row['density_vertex']))
         for row in scalar['projected_CAR_couplings']]
    target, domain = set(ids[6]), set(ids[2])
    assert target.isdisjoint(domain)
    vertex_bounds = []
    for value, row, saved in zip(W, scalar['projected_CAR_couplings'], candidate['all61_canonical_W_bounds']):
        equal(value, decode(row['canonical_matter_vertex']))
        assert all(i in target and j in domain for i, j in value.todok())
        vertex_bounds.append(check_norms(value, saved))
    assert len(W) == len(candidate['all61_canonical_W_bounds']) == 61
    assert s.simplify(sum(vertex_bounds)-number(candidate['all61_sum_operator_bound'])) == 0
    print('PASS raw full252 A=-E^-1 K=-iH; all spatial Hj Hermitian, real constant defect48, beta=6sqrt30/25; all61 vertices', flush=True)

    # Obtain the actual real scalar pair from its two original complex flows.
    Ac = clean(decode(scalar['canonical_generator']).subs(dict(zip(K, KAP)), simultaneous=True))
    plus = s.SparseMatrix(122, 244, {
        **{(j,j):1/s.sqrt(2) for j in range(61)},
        **{(j,61+j):s.I/s.sqrt(2) for j in range(61)},
        **{(61+j,122+j):1/s.sqrt(2) for j in range(61)},
        **{(61+j,183+j):s.I/s.sqrt(2) for j in range(61)}})
    minus = plus.conjugate()
    As = clean(plus.H*Ac*plus+minus.H*Ac.subs(dict(zip(KAP, [-p for p in KAP])), simultaneous=True)*minus)
    Az = clean(Ac.subs(dict.fromkeys(KAP, 0)))
    equal(As, decode(pair['real_phase_generator']).subs(dict(zip(K, KAP)), simultaneous=True))
    equal(Az, decode(pair['zero_mode']['generator']))
    scalar_A = {False: As, True: Az}
    blocks = {key: partition(list(range(value.rows)), value) for key, value in scalar_A.items()}
    full_scalar, _ = polynomial_bound(As, candidate['source_scalar244_absolute_coefficient_majorants'])
    assert s.simplify(full_scalar-number(candidate['source_scalar244_operator_majorant_R'])) == 0
    scalar_rows = {(row['zero_mode'], row['component']): row
                   for row in candidate['source_scalar_component_logarithmic_majorants']}
    assert len(scalar_rows) == sum(map(len, blocks.values())) == 120
    local_growth, degree_bound_lists = {}, defaultdict(list)
    for iszero, components in blocks.items():
        for index, block in enumerate(components):
            part = scalar_A[iszero].extract(block, block)
            symmetric = clean((part.T+part.conjugate())/2)
            equal(symmetric, symmetric.H)
            row = scalar_rows[iszero,index]
            value, per_degree = polynomial_bound(symmetric, row['coefficient_bounds'])
            assert s.simplify(value-number(row['Lambda_R'])) == 0
            local_growth[iszero,index] = value
            for degree in range(3):
                degree_bound_lists[degree].append(per_degree.get(degree, 0))
    Lambda = s.expand(sum(largest(values)*R**degree for degree, values in degree_bound_lists.items()))
    assert s.simplify(Lambda-number(candidate['global_Lambda_R'])) == 0
    assert s.simplify(Lambda-(27*s.sqrt(30)/100+27*s.sqrt(15)*R/125+9*s.sqrt(30)*R**2/50)) == 0
    print('PASS original scalar pair/zero flow, all120 logarithmic component majorants; Lambda independent of matter momentum', flush=True)

    out_map = {i: n for n, block in enumerate(out_blocks) for i in block}
    in_map = {j: n for n, block in enumerate(in_blocks) for j in block}
    catalogues = {}
    for iszero in (False, True):
        phase_map = {i: n for n, block in enumerate(blocks[iszero]) for i in block}
        cat = defaultdict(dict)
        for a, value in enumerate(W):
            for phase_index in ((a,) if iszero else (a, a+61)):
                for (i,j), coefficient in value.todok().items():
                    cat[phase_map[phase_index], out_map[i], in_map[j]][phase_index,i,j] = coefficient
        catalogues[iszero] = cat
    expected_keys = {(z, b, sign, key) for z in (False, True) for b in (1,-1)
        for sign in ((1,) if z else (1,-1)) for key in catalogues[z]}
    def key(row): return row['zero_mode'], row['branch'], row['sign'], tuple(row['key'])
    time_rows = {key(row): row for row in time_data['primitive_states']}
    bound_rows = {key(row): row for row in candidate['catalogue_coefficient_checks']}
    assert len(time_rows) == len(time_data['primitive_states']) == len(bound_rows) == \
        len(candidate['catalogue_coefficient_checks']) == candidate['catalogue_count'] == 1160
    assert set(time_rows) == set(bound_rows) == expected_keys
    derivative_maxima, vector_norms = [[], [], []], []
    cache, reports = {}, []
    omitted_outgoing = 0
    for identity, row in time_rows.items():
        iszero, branch, sign, source_key = identity
        check = bound_rows[identity]
        scalar_ids = blocks[iszero][source_key[0]]
        out_ids, in_ids = out_blocks[source_key[1]], in_blocks[source_key[2]]
        assert (scalar_ids, out_ids, in_ids) == (row['phase_indices'], row['target_indices'], row['input_indices'])
        r, d, f = len(scalar_ids), len(out_ids), len(in_ids)
        S = scalar_A[iszero].extract(scalar_ids, scalar_ids)
        cache_key = (iszero, branch, source_key)
        if cache_key not in cache:
            derivatives, constants, defects = [], [], 0
            for k in K:
                left = affine[str(k)].extract(out_ids, out_ids)
                right = affine[str(k)].extract(in_ids, in_ids)
                if branch == -1:
                    left, right = -left.conjugate(), -right.conjugate()
                # Direct index differentiation includes BOTH physical momenta.
                # pout=pin+sign*kappa has dpout/dpin=1 for either sign.
                D = coefficient_derivative(zero(r), left, right)
                equal(D+D.H, zero(r*d*f))
                frozen = coefficient_derivative(zero(r), zero(d), right)
                assert clean(D-frozen).todok()
                defects += 1
                derivatives.append(D)
                constants.append(direct_norms(D)['operator_two_norm_upper_bound'])
            # The entire physical Hermitian part follows entrywise from the
            # source scalar block and two complete skew-Hermitian matter blocks.
            left0 = affine['constant'].extract(out_ids, out_ids)
            right0 = affine['constant'].extract(in_ids, in_ids)
            if branch == -1:
                left0, right0 = left0.conjugate(), right0.conjugate()
            L0 = coefficient_derivative(S, left0, right0)
            hermitian = coefficient_derivative(clean((S+S.H)/2), zero(d), zero(f))
            equal((L0+L0.H)/2, hermitian)
            cache[cache_key] = constants, defects
        constants, defects = cache[cache_key]
        # Actual outgoing transfer changes only a skew-Hermitian constant;
        # verify it for this branch/sign, rather than freezing kout.
        transfer_left = zero(d)
        for p, k in zip(KAP, K):
            part = affine[str(k)].extract(out_ids, out_ids)
            if branch == -1:
                part = -part.conjugate()
            transfer_left += (0 if iszero else sign*p)*part
        equal(transfer_left+transfer_left.H, zero(d))
        omitted_outgoing += defects
        for j, constant in enumerate(constants):
            assert s.simplify(constant-number(check['momentum_derivative_bounds'][j])) == 0
            derivative_maxima[j].append(constant)
        v = zero(r*d*f,1)
        for (phase_index,i,j), value in catalogues[iszero][source_key].items():
            weight = 1 if iszero else (1 if phase_index < 61 else sign*s.I)/s.sqrt(2)
            vertex = value if branch == 1 else -s.conjugate(value)
            slot = scalar_ids.index(phase_index)*d*f+in_ids.index(j)*d+out_ids.index(i)
            v[slot,0] = s.expand(-s.I*weight*vertex)
        equal(v, decode(row['signal_initial']))
        assert not v.free_symbols and v.todok()
        squared = s.simplify(sum(modulus(value)**2 for value in v.todok().values()))
        value = s.simplify(s.sqrt(squared))
        assert squared.is_positive is True
        assert s.simplify(squared-number(check['initial_coefficient_norm_squared'])) == 0
        assert s.simplify(value-number(check['initial_coefficient_norm'])) == 0
        vector_norms.append(value)
        assert check['signal_dimension'] == r*d*f
        assert s.simplify(number(check['Lambda_R'])-local_growth[iszero,source_key[0]]) == 0
        assert all(s.simplify(c).is_nonnegative is True
                   for c in s.Poly(Lambda-local_growth[iszero,source_key[0]],R).all_coeffs())
        for flag in ('physical_transfer_installed_before_differentiation',
                     'affine_in_physical_incoming_momentum',
                     'all_derivative_generators_skew_Hermitian', 'logarithmic_growth_from_scalar_only'):
            assert check[flag]
        reports.append({'zero_mode':iszero, 'branch':branch, 'sign':sign, 'key':list(source_key),
            'signal_dimension':r*d*f, 'source_initial_and_norm_checked':True,
            'both_physical_momentum_derivatives_checked':True, 'source_logarithmic_bound_checked':True})
    C = [largest(values) for values in derivative_maxima]
    V = largest(vector_norms)
    assert all(s.simplify(c-number(saved)) == 0 for c,saved in zip(C,candidate['global_momentum_derivative_bounds']))
    assert C == [6*s.sqrt(30)/25]*3
    assert V == number(candidate['global_initial_coefficient_norm_bound']) == 12*s.sqrt(15)/25
    assert omitted_outgoing == candidate['frozen_outgoing_momentum_negative_control_defects'] == 3480
    assert Counter(r['zero_mode'] for r in reports) == {False:760,True:400}
    print('PASS all1160 exact source primitives, incoming/outgoing differentiation, initial norms; frozen-outgoing defects3480', flush=True)

    # Check the all-order antiderivatives in the opposite direction to the
    # constructor's integrator; the multi-index recurrence uses sum alpha=r.
    order = s.Symbol('r', integer=True, positive=True)
    u = s.Symbol('u', positive=True)
    assert s.diff(u, u) == 1 and s.limit(u, u, 0, dir='+') == 0
    assert s.simplify(s.diff(u**order,u)-order*u**(order-1)) == 0
    assert s.limit(u**order,u,0,dir='+') == 0
    assert s.simplify(s.diff(u**(order+1)/(order+1),u)-u**order) == 0
    assert s.limit(u**(order+1)/(order+1),u,0,dir='+') == 0
    # Real source disjointness is the non-repeated-line support proof, not a
    # finite N sample: once a line reaches Lambda6, every later source entry
    # on that line is zero, while other-line actions leave its label fixed.
    assert target.isdisjoint(domain) and all(i in target and j in domain for value in W for i,j in value.todok())
    assert not candidate['commuting_L_or_derivative_generators_assumed']
    assert not candidate['continuous_scalar_kappa_convolution_bound_claimed']
    assert not candidate['unbounded_boson_domain_or_Hilbert_spectrum_completion_claimed']
    assert s.simplify(number(candidate['source_lapse'])-number(scalar['source_lapse'])) == 0
    input_paths = [candidate_path, HERE/'scalar_dyson_bounds.py', *paths.values(),
        active_path,phase_path,vertices_path,gamma_path,BASE/'exact_readout.py',
        HERE/'independent_spectral_splice.py',HERE/'independent_scalar_dyson_time.py',
        HERE/'WavepacketGrade.lean',HERE/'WavepacketInteraction.lean',HERE/'WavepacketAudit.lean',
        HERE/'independent_scalar_dyson_bounds.py']
    result = {'verdict':'CERTIFIED_ALL1160_SOURCE_DYSON_SMOOTH_MOMENTUM_BOUNDS_AND_FINITE_TRANSFER_SUPPORT',
        'root':ROOT_ID,'source_sha256':hashes,
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in input_paths},
        'candidate_bounds_constructor_imported':False,'candidate_time_constructor_imported':False,
        'algorithm':'raw original252 drift; independent conjugate scalar pair; complete source block catalogue; direct coefficient-index physical derivative; real/imaginary weighted-Cauchy row/column norm bounds; exact source initial vectors; symbolic antiderivative differentiation',
        'source_binding_checks':bound,'full252_A_equals_negative_i_H':True,
        'full252_H0_Hermiticity_defect_entries':48,'full252_spatial_Hj_Hermitian':True,
        'full252_uniform_freeflow_beta':str(beta),'restricted_grade6_grade2_generators_skew_Hermitian':True,
        'scalar_component_count':120,'global_Lambda_R':str(Lambda),
        'global_physical_momentum_derivative_bounds':list(map(str,C)),
        'global_initial_vector_norm':str(V),'source_vertex_count':61,
        'source_vertex_sum_norm_upper_bound':str(s.simplify(sum(vertex_bounds))),
        'primitive_count':len(reports),'pair_primitive_count':760,'zero_primitive_count':400,
        'primitive_checks':reports,'frozen_outgoing_derivative_defects':omitted_outgoing,
        'all_order_derivation':{
            'base':'Herm(L) consists exactly of the checked scalar block; ||Herm(L)||<=Lambda(R) bounds both exp(tL) and exp(-tL) by exp(|t|Lambda)',
            'recurrence':'F_alpha prime=L F_alpha+sum_j alpha_j L_j F_(alpha-e_j), F_alpha(0)=0 for |alpha|>0; L affine in physical incoming p',
            'induction':'variation of constants preserves exp(|t|Lambda); sum_j alpha_j=|alpha| and r integral_0^t u^(r-1)du=t^r',
            'signal_bound':'||partial_p^alpha exp(tL)||<=|t|^r exp(T Lambda) product C_j^alpha_j for |t|<=T, |kappa_j|<=R',
            'primitive_bound':'||partial_p^alpha Y(t,p)||<=|t|^(r+1)/(r+1) exp(T Lambda)||v|| product C_j^alpha_j',
            'all_integer_orders_not_sampled':True,'matrix_derivatives_assumed_commuting':False,
            'proof_status':'exact source matrix identities and constants plus the displayed general finite-dimensional ODE/variation-of-constants argument; not a Lean theorem for the smooth-domain integral interchange',
        },
        'support_transport':{
            'single_line':'finite source transfer shifts K to K+/-kappa; multiplication by the smooth source coefficient does not enlarge support',
            'source_grade':'all entries map Lambda2 into disjoint Lambda6; the second occurrence of any particle line is zero even with intervening other-line actions',
            'fixed_N':'each surviving line is shifted at most once, so a per-line cube P becomes P+R, not P+N R',
            'finite_transfer_not_continuous_kappa_integral':True,
            'supports_are_test_domains_not_physical_UV_cutoffs':True,
            'wavepacket_word_theorem':'SourceWavepacketInteraction.time_ordered_family_word_zero',
        },
        'norm_is_finite_coefficient_Euclidean_not_physical_Hilbert':True,
        'independent_dual_replaced_by_Hilbert_adjoint':False,
        'proper_clock':'tau=N*t; proper-time window T_tau uses T=T_tau/N',
        'Lean_Cinfinity_compact_domain_and_integral_exchange_installed':False,
        'continuous_scalar_transfer_convolution_constructed':False,
        'physical_free_boson_state_domain_or_full_spectrum_claimed':False,
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'independent_scalar_dyson_bounds.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS all-order momentum estimate derivation and original finite-transfer support',result['elapsed_seconds'],'seconds',flush=True)


if __name__ == '__main__':
    main()
