#!/usr/bin/env python3
"""Actual cubic source germ audited from direct Taylor and original density.

Only the particular coefficient-left formal energy is tested. Its third
coefficient is neither the original Hamiltonian nor a summed temporal root.
"""
from __future__ import annotations

from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path
import time
import sympy as s

from independent_source_temporal_gauss_relations import (
    RawGaussSection, RawLiveCoefficients, HERE, ROOT, ROOT_ID, bindings,
    rational, eq, decode, encode, zero, magnetic,
    free_add, free_scale, free_multiply, field_number, DOMAIN)


def direct_cubic_energy(N):
    n = s.Symbol('n', positive=True); b = s.symbols('b0:3', real=True); ys = (n, *b)
    point = dict(zip(ys, (N, 0, 0, 0))); delta = n*n-sum(x*x for x in b)
    pairs = ((0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (1, 2))
    weights = [*ys, *[(n*n-b[i]*b[j])/(2*n*delta) if i == j else -b[i]*b[j]/(n*delta)
                     for i, j in pairs], *[-x/delta for x in b]]
    # The original vacuum form family has one time-independent positive
    # pairing. Independent real weights therefore identify each atom with
    # its formal adjoint, making reversal of actual finite words legitimate.
    polynomials = [s.Poly(s.cancel(2*n*delta*f), *ys) for f in weights]
    monomials = sorted(set().union(*(set(p.monoms()) for p in polynomials)))
    coefficient_matrix = s.Matrix([[p.coeff_monomial(m) for p in polynomials]
                                   for m in monomials])
    assert coefficient_matrix.rank() == 13
    source = [s.Rational(9, 5), 0, 0, 0]+[s.Rational(324, 625)]*3+[0]*6
    seed = s.factor(sum(a*f for a, f in zip(source, weights)))
    letters = [{(a,): DOMAIN.one} for a in range(13)]
    @lru_cache(None)
    def derivative(part, indices):
        value = seed if part == -1 else weights[part]
        for i in indices: value = s.diff(value, ys[i])
        return s.simplify(value.subs(point))
    J = [-derivative(-1, (a, a)) for a in range(4)]
    def fac(indices): return s.prod(s.factorial(indices.count(a)) for a in range(4))
    def prod(indices, vector):
        value = {(): DOMAIN.one}
        for i in indices: value = free_multiply(value, vector[i])
        return value
    u = [free_scale(1/J[a], free_add(*(free_scale(derivative(j, (a,)), letters[j]) for j in range(13)))) for a in range(4)]
    quadratic = list(itertools.combinations_with_replacement(range(4), 2))
    cubic = list(itertools.combinations_with_replacement(range(4), 3))
    v = []
    for a in range(4):
        residual = [free_scale(-derivative(-1, tuple(sorted((a, *indices))))/fac(indices), prod(indices, u)) for indices in quadratic]
        residual += [free_scale(-derivative(j, tuple(sorted((a, r)))), free_multiply(letters[j], u[r])) for j in range(13) for r in range(4)]
        v.append(free_scale(-1/J[a], free_add(*residual)))
    energy = [free_scale(derivative(-1, indices)/fac(indices), prod(indices, u)) for indices in cubic]
    for a, b in quadratic:
        crossed = free_add(free_multiply(u[a], v[b]), free_multiply(v[a], u[b]))
        energy.append(free_scale(derivative(-1, (a, b))/fac((a, b)), crossed))
    energy += [free_scale(derivative(j, (a,)), free_multiply(letters[j], v[a])) for j in range(13) for a in range(4)]
    energy += [free_scale(derivative(j, indices)/fac(indices), free_multiply(letters[j], prod(indices, u))) for j in range(13) for indices in quadratic]
    third = free_add(*energy)
    for c in third.values(): zero(s.im(DOMAIN.to_sympy(c)))
    difference = free_add(third, free_scale(-1, {tuple(reversed(w)): c for w, c in third.items()}))
    assert len(third) == 244 and len(difference) == 168
    return {w: DOMAIN.to_sympy(c) for w, c in difference.items()}


def main():
    started = time.monotonic(); path = HERE/'source_temporal_energy_adjoint.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    paid = ('independent_source_scalar_temporal_form', 'independent_source_temporal_coframe_pairing',
        'independent_source_temporal_gauss_relations')
    for name in paid:
        d = json.loads((HERE/(name+'.json')).read_text()); count += bindings(d)
        assert d['verdict'].startswith('CERTIFIED_')
    raw, section = RawLiveCoefficients(), RawGaussSection()
    assert section.native.hashes == candidate['source_sha256']
    difference = direct_cubic_energy(raw.N)
    print('PASS original thirteen real four-time weights: independent polynomial rank13', flush=True)
    mixed = {w: c for w, c in difference.items() if 0 in w}; assert len(mixed) == 30
    saved_words = {tuple(row['word']): s.sympify(row['coefficient']) for row in candidate['formal_calculation']['actual_coframe_containing_terms']}
    assert mixed == saved_words
    for w in difference:
        if 0 in w:
            assert w.count(0) == 1 and all(a in (0, 1, 2, 3, 10, 11, 12) for a in w)
    q = raw.q; L = raw.e[1:, 1:]
    c = s.Matrix(s.symbols('coordinate_cross0:3'))
    nongauge, gauge = rational(L.inv().T*c), L*c
    symbols = {**{i+1: nongauge[i] for i in range(3)}, **{i+10: gauge[i] for i in range(3)}}
    # For f=q_r*h(A)^2/2 only the single-q/two-A third derivative survives.
    # Differentiate the original coefficient product at the position of T;
    # every q-q principal and drift term has the same cancelled product.
    cancelled = s.S.Zero; mixed_coefficient = s.zeros(6, 1)
    for w, coefficient in mixed.items():
        j, k = [a for a in w if a != 0]; x, y = symbols[j], symbols[k]
        cancelled += coefficient*x*y
        if w[0] == 0: derivative = (x*y).diff
        elif w[1] == 0: derivative = lambda t, x=x, y=y: x*s.diff(y, t)
        else: derivative = lambda _: s.S.Zero
        mixed_coefficient -= 2*coefficient*raw.K*s.Matrix([derivative(t) for t in q])/raw.N
    zero(cancelled)
    mixed_coefficient = rational(mixed_coefficient)
    eq(mixed_coefficient, decode(candidate['generic_mixed_symbol']['six_q_coefficient'], {str(v): v for v in (*q, *c)}))
    print('PASS independent direct cubic Taylor words and full live-coframe mixed differential symbol', flush=True)

    row = candidate['actual_consumer']; point = decode(row['base103']); A = decode(row['gauge36'])
    eq(point[67:, :].reshape(3, 12), A)
    eq(point[:67, :], section.source[:67, :])
    j, r = row['slice_coordinate'], row['q_direction']; assert (j, r) == (80, 0)
    inverse = section.implicit_jets(point)
    lam = rational((section.free_reader*inverse['tangent'])[j, :].T)
    eq(lam, decode(row['actual_gauge_covector103']))
    eq(lam[:67, :], s.zeros(67, 1)); eq(inverse['V'].T*lam, s.zeros(3, 1))
    B = magnetic(section.native, A); eq(B, decode(row['native_B']))
    mom = s.Matrix(s.symbols('pA0:36'))
    cross_matrix = s.Matrix(3, 3, lambda i, k: -s.I*(B[k, :]*mom[12*i:12*(i+1), :])[0])
    cross = s.Matrix([cross_matrix[2, 1]-cross_matrix[1, 2], cross_matrix[0, 2]-cross_matrix[2, 0], cross_matrix[1, 0]-cross_matrix[0, 1]])
    cross_value = rational(cross.jacobian(mom)*lam[67:, :])
    eq(cross_value, s.Matrix([-s.I/589, 0, 0])); eq(cross_value, decode(row['coordinate_cross_value']))
    origin = dict(zip(q, point[:6, 0])); values = dict(zip(c, cross_value))
    actual = s.cancel(mixed_coefficient[r].subs(origin).subs(values))
    # Independently evaluate each ordered germ from its first q coefficient
    # jets, keeping the complete original coframe drift. No projected or
    # assumed commuting coframe coefficient enters.
    K = rational(raw.K.subs(origin)); drift = rational(-s.I*raw.drift.subs(origin)/raw.N)
    scalar_atoms = {a: s.cancel(v.subs(values)) for a, v in symbols.items()}
    atom0 = {a: v.subs(origin) for a, v in scalar_atoms.items()}
    atom1 = {a: rational(s.Matrix([s.diff(v, t).subs(origin) for t in q])) for a, v in scalar_atoms.items()}
    direct = {}; frozen = s.S.Zero
    for w, coefficient in mixed.items():
        a, b = [letter for letter in w if letter]
        value = drift[r]*atom0[a]*atom0[b]
        if w[0] == 0:
            value -= 2*(K[r, :]*(atom1[a]*atom0[b]+atom0[a]*atom1[b]))[0]/raw.N
        elif w[1] == 0:
            value -= 2*atom0[a]*(K[r, :]*atom1[b])[0]/raw.N
        direct[w] = s.cancel(value)
        frozen += coefficient*drift[r]*atom0[a]*atom0[b]
    expected_words = {tuple(item['word']): s.sympify(item['value']) for item in row['individual_nested_word_values']}
    assert direct == expected_words
    result = s.cancel(sum(mixed[w]*direct[w] for w in mixed)); zero(result-actual); zero(frozen)
    zero(result-s.sympify(row['actual_K3_minus_K3_adjoint']))
    zero(result-6623*s.sqrt(30)/145673515584); assert result != 0
    print('PASS actual same-chart vacuum Gauss cubic germ and all30 original word actions:', result, flush=True)
    files = [Path(__file__), path, HERE/'source_temporal_energy_adjoint.py',
        HERE/'independent_source_temporal_gauss_relations.py', HERE/'independent_source_quantum_gauss_section.py',
        HERE/'independent_source_coframe_live_ordering.py']+[HERE/(n+'.json') for n in paid]
    out = {'verdict': 'CERTIFIED_ACTUAL_ORDERED_K3_ADJOINT_DEFECT_ON_SOURCE_VACUUM_GAUSS_GERM',
        'root': ROOT_ID, 'source_sha256': section.native.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'source_binding_checks': count, 'candidate_constructor_imported': False,
        'independent_method': 'Closed Taylor formulas from original thirteen scalar weights; original raw BF coframe symbol and implicit residual3 inverse; gauge curvature from native commutators; complete thirty-word evaluation using original first coefficient jets and drift.',
        'free_cubic_word_count': 244, 'free_reversal_word_count': 168,
        'original_thirteen_weights_independently_rank_checked': True,
        'all_actual_coframe_words': 30, 'complete_fourth_order_principal_and_coframe_drift_cancel': True,
        'actual_germ': {'input': row['input'], 'Gauss_horizontal_covector103': encode(lam),
            'original_coordinate_cross': encode(cross_value), 'original_ordered_K3_adjoint_defect': str(result),
            'incorrectly_frozen_coframe_result': str(s.cancel(frozen)), 'same_original_q_and_scalar_source': True},
        'germ_coverage': 'On the vacuum all actual one-body/normal currents and Y vanish. All words without atom0 lack q derivatives and retain q0-1. Every atom0 word has only one coframe block and two first-order gauge-cross blocks. The common fourth-order q-q-A-A coefficient cancels; lower jets vanish. Gauge derivatives of cross coefficients multiply the vanished first gauge jet. The Gauss slice fixes q, so chart-curvature terms cannot contribute the surviving single-q/two-A jet.',
        'adjoint_scope': 'The source four-time form atoms have the same positive pairing, real coefficients and compact invariant test domain. Their finite-composition adjoints reverse words. The witness disproves symmetry of this specified K3, not the original form family, another derived reduction, or existence of a proton.',
        'new_quantum_ordering_or_series_sum_installed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'independent_source_temporal_energy_adjoint.json').write_text(json.dumps(out, separators=(',', ':'))+'\n')
    print('PASS independent temporal energy adjoint', out['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
