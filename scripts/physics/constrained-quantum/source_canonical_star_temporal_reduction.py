#!/usr/bin/env python3
"""Source temporal reduction by the original canonical Weyl graph retraction.

Only the actual four primary pairs (eta, pi_y) supply extra Weyl variables.
Coefficients are compositions of the original full canonical/Fock operators.
The retraction is not multiplicative on arbitrary extended observables; its
automorphic lift and projected Heisenberg action are the physical consumers.
"""
from __future__ import annotations

from collections import Counter
from functools import lru_cache
from math import factorial
import hashlib
import itertools
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID, decode
from source_quantum_ordered_temporal import (
    OrderedTemporalCoefficients, DOMAIN, add, scale, multiply, multiindices)
from source_quantum_temporal_symbol import J0, N
from source_spatial_active_phase_splice import field_element
from independent_source_coframe_live_ordering import RawLiveCoefficients, rational
from source_lorentz_contact import clean, equal, encode
from source_common_hamiltonian import SourceCommonHamiltonian
from source_quantum_grade_structure import occupation_grade, matrix_grade
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state


ZERO = (0, 0, 0, 0)
II = field_element(s.I)
HALF = DOMAIN.one/2


def bound(name):
    record = json.loads((HERE/(name+'.json')).read_text())
    assert record['root'] == ROOT_ID
    for group in ('source_sha256', 'input_sha256'):
        for path, digest in record.get(group, {}).items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    return record


def collect(rows):
    result = {}
    for key, value in rows:
        result[key] = result.get(key, DOMAIN.zero)+value
    return {key: value for key, value in result.items() if value != DOMAIN.zero}


def ext_add(*polynomials):
    return collect((key, value) for p in polynomials for key, value in p.items())


def ext_scale(c, p):
    c = field_element(c) if not isinstance(c, type(DOMAIN.one)) else c
    return {key: c*value for key, value in p.items() if c*value != DOMAIN.zero}


@lru_cache(None)
def temporal_products(a, b, c, d, zero_primary_only):
    """Literal eta/pi Weyl monomial product, including both derivative signs."""
    answer = []
    for r in itertools.product(*(range(min(x, y)+1) for x, y in zip(a, d))):
        for t in itertools.product(*(range(min(x, y)+1) for x, y in zip(b, c))):
            eta = tuple(a[i]+c[i]-r[i]-t[i] for i in range(4))
            pi = tuple(b[i]+d[i]-r[i]-t[i] for i in range(4))
            if zero_primary_only and pi != ZERO: continue
            value = (II*HALF)**(sum(r)+sum(t))*(-1)**sum(t)
            for i in range(4):
                value *= factorial(a[i])*factorial(d[i])*factorial(b[i])*factorial(c[i])
                value /= (factorial(a[i]-r[i])*factorial(d[i]-r[i])*
                          factorial(b[i]-t[i])*factorial(c[i]-t[i])*factorial(r[i])*factorial(t[i]))
            answer.append((eta, pi, value))
    return tuple(answer)


def star(left, right, order, zero_primary_only=False):
    answer = {}
    for (n, a, b, word), value in left.items():
        for (m, c, d, other), coefficient in right.items():
            if n+m > order: continue
            for eta, pi, factor in temporal_products(a, b, c, d, zero_primary_only):
                key = (n+m, eta, pi, word+other)
                answer[key] = answer.get(key, DOMAIN.zero)+value*coefficient*factor
    return {key: value for key, value in answer.items() if value != DOMAIN.zero}


def commutator(left, right, order, zero_primary_only=False):
    return ext_add(star(left, right, order, zero_primary_only),
                   ext_scale(-1, star(right, left, order, zero_primary_only)))


def embed(polynomial, degree=0):
    return {(degree, ZERO, ZERO, word): value for word, value in polynomial.items()}


def evaluate_normal_zero(polynomial, order):
    rows = [{} for _ in range(order+1)]
    for (degree, eta, pi, word), value in polynomial.items():
        if eta == ZERO and pi == ZERO:
            rows[degree][word] = rows[degree].get(word, DOMAIN.zero)+value
    return [{w: c for w, c in row.items() if c != DOMAIN.zero} for row in rows]


def involution(polynomial):
    switch = lambda a: 14 if a == 13 else 13 if a == 14 else a
    return {tuple(switch(a) for a in reversed(word)):
            field_element(s.conjugate(DOMAIN.to_sympy(value))) for word, value in polynomial.items()}


class SourceCanonicalStarTemporalReduction:
    def __init__(self, order=3, yukawa='none'):
        assert yukawa in ('none', 'original', 'adjoint')
        self.order = order; self.original = OrderedTemporalCoefficients()
        self.atoms = [{(j,): DOMAIN.one} for j in range(13)]
        if yukawa != 'none':
            self.atoms[0] = add(self.atoms[0], {(13 if yukawa == 'original' else 14,): DOMAIN.one})
        self.H = self.family(-1)
        self.F = [self.family(a) for a in range(4)]

    def family(self, equation):
        rows = []
        # A primary commutator differentiates H once before source evaluation.
        # Its Taylor jet must therefore be one eta degree deeper than F's.
        max_eta = self.order+int(equation == -1)
        for alpha in multiindices(max_eta):
            coefficient = self.original.taylor(-1, alpha, equation)
            if coefficient: rows.append(((0, alpha, ZERO, ()), coefficient))
            if sum(alpha) >= max_eta: continue
            for a in range(13):
                coefficient = self.original.taylor(a, alpha, equation)
                if coefficient:
                    rows.extend(((1, alpha, ZERO, word), coefficient*value)
                                for word, value in self.atoms[a].items())
        return collect(rows)

    def generator(self, D):
        rows = []
        for a in range(4):
            pi = tuple(int(i == a) for i in range(4))
            for n, coefficient in enumerate(D[a]):
                rows.extend(((n, ZERO, pi, word), -value) for word, value in coefficient.items())
        return collect(rows)

    def conjugate(self, D, polynomial, inverse=False, projected=False):
        """exp(ad_star(-pi.D)/i), computed by literal temporal Weyl products."""
        G = self.generator(D)
        if projected:
            polynomial = {key: c for key, c in polynomial.items() if key[2] == ZERO}
        result = polynomial; term = polynomial
        for k in range(1, self.order+1):
            term = ext_scale(DOMAIN.convert(-1 if inverse else 1)/(II*k),
                commutator(G, term, self.order, zero_primary_only=projected))
            result = ext_add(result, term)
        return result

    def retract(self, D, polynomial):
        # ad_G can preserve or raise primary-momentum degree, never lower it.
        # Thus its positive-pi ideal is invariant and this exact pruning keeps
        # the same evaluation as the full conjugation, not a momentum truncation.
        return evaluate_normal_zero(self.conjugate(D, polynomial, projected=True), self.order)

    def lift(self, D, polynomial):
        return self.conjugate(D, embed(polynomial), inverse=True)

    def generate(self):
        D = [[{} for _ in range(self.order+1)] for _ in range(4)]
        stages = []
        for n in range(1, self.order+1):
            residual = [self.retract(D, row)[n] for row in self.F]
            for a in range(4): D[a][n] = scale(-1/J0[a, a], residual[a])
            for row in self.F: assert all(not p for p in self.retract(D, row)[:n+1])
            stages.append({'order': n, 'time_word_counts': [len(row[n]) for row in D],
                           'all_four_original_projected_rows_zero': True})
        return D, self.retract(D, self.H), stages

    def jordan_reconstruction(self, D, polynomial):
        """Independent projection formula derived from the two star placements."""
        def series_product(a, b):
            return [add(*(multiply(a[j], b[n-j]) for j in range(n+1))) for n in range(self.order+1)]
        def jordan(a, b):
            return [scale(HALF, add(x, y)) for x, y in zip(series_product(a, b), series_product(b, a))]
        output = [{} for _ in range(self.order+1)]
        for (degree, eta, pi, word), coefficient in polynomial.items():
            if pi != ZERO: continue
            indices = tuple(i for i, n in enumerate(eta) for _ in range(n))
            permutations = tuple(set(itertools.permutations(indices)))
            for permutation in permutations:
                value = [{} for _ in range(self.order+1)]; value[degree] = {word: coefficient/len(permutations)}
                for a in reversed(permutation): value = jordan(D[a], value)
                output = [add(a, b) for a, b in zip(output, value)]
        return output


def verify_extended_consumers(model, D, energy):
    order = model.order
    f, g = {(1,): DOMAIN.one}, {(10,): DOMAIN.one}
    Lf, Lg = model.lift(D, f), model.lift(D, g)
    expected_f = [f]+[{} for _ in range(order)]
    assert model.retract(D, Lf) == expected_f
    assert all(key[1] == ZERO for key in (*Lf, *Lg))
    assert star(Lf, Lg, order) == model.lift(D, multiply(f, g))
    raw = commutator(Lf, model.H, order, zero_primary_only=True)
    reduced = model.retract(D, raw)
    assert reduced == [add(multiply(f, e), scale(-1, multiply(e, f))) for e in energy]
    for constraint in model.F:
        weak = model.retract(D, commutator(Lf, constraint, order, zero_primary_only=True))
        assert not any(weak)
    for a in range(4):
        index = tuple(int(i == a) for i in range(4))
        eta, pi = {(0, index, ZERO, ()): DOMAIN.one}, {(0, ZERO, index, ()): DOMAIN.one}
        assert model.retract(D, pi) == [{} for _ in range(order+1)]
        assert model.retract(D, eta) == D[a]
        product = model.retract(D, star(eta, pi, order))
        assert product == [{(): II*HALF}]+[{} for _ in range(order)]
    for polynomial in (model.H, *model.F):
        assert model.retract(D, polynomial) == model.jordan_reconstruction(D, polynomial)
    return {'actual_base_observables': ['nongauge_shift_atom1', 'native_gauge_cross_atom10'],
        'R_L_identity': True, 'L_star_product_preserved': True,
        'original_lifted_Heisenberg_action': 'R([L(f),H]_star)=[f,R(H)]_star through epsilon^3',
        'all_four_original_secondary_weak_commutators_zero': True,
        'all_four_original_primary_readbacks_zero': True,
        'nonmultiplicative_control': 'R(eta_a star pi_a)=i/2, while R(eta_a) star R(pi_a)=0',
        'literal_temporal_star_equals_derived_Jordan_recursion': True,
        'lift_term_counts': [len(Lf), len(Lg)]}


def original_total_hamiltonian(model, D, energy):
    """Generate the original primary multipliers from secondary preservation."""
    order = model.order
    multipliers = [[{} for _ in range(order+1)] for _ in range(4)]
    def total():
        # generator stores -pi.D; the original total Hamiltonian has +pi.Lambda.
        return ext_add(model.H, ext_scale(-1, model.generator(multipliers)))
    def projected_rate(observable):
        # Positive primary degree must be retained until after this product:
        # [F, pi.Lambda] contains its source J0.Lambda at primary degree zero.
        bracket = commutator(observable, total(), order, zero_primary_only=True)
        return model.retract(D, ext_scale(DOMAIN.one/II, bracket))
    stages = []
    for n in range(1, order+1):
        residual = [projected_rate(F)[n] for F in model.F]
        for a in range(4): multipliers[a][n] = scale(-1/J0[a, a], residual[a])
        assert all(not p for F in model.F for p in projected_rate(F)[:n+1])
        stages.append({'order': n, 'multiplier_word_counts': [len(p[n]) for p in multipliers],
                       'all_four_original_secondary_rates_zero': True})
    assert model.retract(D, total()) == energy
    for a in range(4):
        index = tuple(int(i == a) for i in range(4))
        eta = {(0, index, ZERO, ()): DOMAIN.one}
        pi = {(0, ZERO, index, ()): DOMAIN.one}
        assert not any(projected_rate(pi))
        assert projected_rate(eta) == multipliers[a]
        intrinsic = [scale(DOMAIN.one/II, add(*(add(multiply(D[a][j], energy[n-j]),
            scale(-1, multiply(energy[n-j], D[a][j]))) for j in range(n+1))))
            for n in range(order+1)]
        assert multipliers[a] == intrinsic
    f = {(1,): DOMAIN.one}
    expected = [scale(DOMAIN.one/II, add(multiply(f, e), scale(-1, multiply(e, f)))) for e in energy]
    assert projected_rate(model.lift(D, f)) == expected
    return multipliers, {'stages': stages, 'source_time_rate_convention': 'dot A=[A,H_T]_star/i',
        'total_Hamiltonian': 'H_T=H+sum pi_y,a Lambda_a; Lambda depends on retained operators only.',
        'source_multiplier_recursion': 'At order m the remaining new term is J0 Lambda_m. It is solved directly from R([F,H_T]/i)=0, without deleting primary-degree1 terms before their star commutator.',
        'all_eight_original_constraint_projected_rates_zero': True,
        'original_time_coframe_rate_equals_reduced_commutator': 'R([eta_a,H_T]/i)=Lambda_a=[D_a,R(H)]/i through epsilon^3 for every a.',
        'R_total_H_equals_generated_energy': True,
        'lifted_observable_dynamics_with_original_total_H_verified': True,
        'multiplier_coefficients': [[polynomial_json(p) for p in row] for row in multipliers]}


def source_fock_consumer(D, energy, D0, energy0):
    def grades(row):
        records = []
        for n, polynomial in enumerate(row):
            assert all(len(word) == n and all(0 <= a <= 13 for a in word) for word in polynomial)
            counts = dict(sorted(Counter(word.count(13) for word in polynomial).items()))
            records.append({'order':n,'word_count':len(polynomial),
                'Y_grade_word_counts':{str(g):v for g,v in counts.items()},
                'words_not_eliminated_by_N0_grade_bound':sum(v for g,v in counts.items() if g <= 0),
                'words_not_eliminated_by_N1_grade_bound':sum(v for g,v in counts.items() if g <= 1),
                'words_not_eliminated_by_N2_grade_bound':sum(v for g,v in counts.items() if g <= 2)})
        return records
    strip = lambda p:{word:value for word,value in p.items() if 13 not in word}
    assert [[strip(p) for p in row] for row in D] == D0
    assert [strip(p) for p in energy] == energy0
    time_grades = [grades(row) for row in D]; energy_grades = grades(energy)
    # A real finite evaluation minor extracts every original atom from the
    # complete covariant H0 family, so no independent Gauss-kernel premise is
    # added to the formal graph.
    original = OrderedTemporalCoefficients()
    clocks = [(N,*[N*s.Rational(i,4) for i in triple])
              for triple in __import__('itertools').product((-1,0,1),repeat=3)]
    values = s.Matrix([[s.simplify(f.subs(dict(zip(original.y,clock))))
                       for f in original.coefficients] for clock in clocks])
    _, rows = values.T.rref(); assert len(rows) == 13
    minor = values[list(rows),:]; determinant = s.factor(minor.det()); assert determinant != 0
    assert all(clock[0]**2 > sum(v*v for v in clock[1:]) for clock in clocks)
    common = SourceCommonHamiltonian()
    background = common.scalar.exchange.active['actual_background']
    e = s.Matrix(background['coframe']).applyfunc(s.sympify)
    A = s.Matrix(background['gauge_connection']).applyfunc(s.sympify)
    phi = common.scalar.vacuum
    E = common.matter_data(e,phi,A)['E']
    raw = sum(((phi[j]+s.I*phi[j+35])*Y for j,Y in enumerate(common.yukawa_basis)),s.zeros(252))
    single = clean(-s.I*e.det()*E.inv()*raw)
    full = clean(s.diag(single,-single.conjugate()))
    matrix_grade(full,1); equal(full*full,s.zeros(504))
    incoming = (144,396); state = {incoming:s.S.One}
    assert occupation_grade(incoming) == 0
    once = apply_superposition(full,state)
    twice = apply_superposition(full,once)
    thrice = apply_superposition(full,twice)
    assert once and twice and not thrice
    assert twice == {(a,b):-2*N*N for a in (0,2) for b in (252,254)}
    assert all(len(word)==2 and occupation_grade(word)==1 for word in once)
    assert all(len(word)==2 and occupation_grade(word)==2 for word in twice)
    grade2 = {w:c for w,c in energy[2].items() if w.count(13)==2}
    assert set(grade2) == {(13,13)}
    coefficient = DOMAIN.to_sympy(grade2[(13,13)])
    image = weighted_sum([(coefficient/N**2,twice)])
    assert image == {(a,b):s.sqrt(30)/30 for a in (0,2) for b in (252,254)}
    norm_squared = s.simplify(sum(s.conjugate(v)*v for v in image.values()))
    assert norm_squared == s.Rational(2,15)
    assert {w:c for w,c in energy[3].items() if w.count(13)==3} == {(13,13,13): energy[3][(13,13,13)]}
    assert s.simplify(DOMAIN.to_sympy(energy[3][(13,13,13)])-s.sqrt(30)/216)==0
    reducing = json.loads((HERE/'source_yukawa_reducing_carrier.json').read_text())
    P = decode(reducing['generated_reducing_projector_real504'])
    assert s.trace(P)==392
    equal(full*P,s.zeros(504));equal(full.H*P,s.zeros(504))
    assert all(P[i,i]==0 for i in incoming)
    assert all(P[i,i]==0 for word in once|twice for i in word)
    old = json.loads((HERE/'source_quantum_ordered_temporal.json').read_text())['positive_pairing_consumer']
    assert image == {tuple(w):s.sympify(v) for w,v in old['actual_second_order_grade2_image']}
    return {'actual_time_word_grades':time_grades,'actual_energy_word_grades':energy_grades,
        'H0_restriction_equals_independently_generated_branch':True,
        'fullY_adjoint_letter14_absent':True,
        'direct_Lean_consumer':'SourceFockFilteredWords.weighted_tensor_word_vanishes: distribute each actual differential/CAR atom into its finite boson tensor CAR terms, preserving their original order; assign weight1 to Y and0 to the other factors. Every word with more than N raises vanishes on the original N-particle sector.',
        'same_original_domain':'All14 atoms preserve total occupation and compact smooth support. The source scalar form correction uses only grade0 currents; eta and pi_y act on a separate boson factor and have grade0. No CAR source-spinor translation is used.',
        'residual_Gauss':{'original_time_evaluation_minor':encode(minor),
            'original_time_evaluation_rows':list(rows),'determinant':str(determinant),
            'independent_real_coefficient_functions':13,
            'argument':'The original full H0(n,b) and isolated Y have native residual3 covariance on the existing source chart; the real invertible13 coefficient minor extracts each actual atom. All D/E words and the generator -pi_y.D therefore commute with the same Gs. The inner-star automorphism, linear evaluation R and automorphic lift L preserve that Gauss section. R is not asserted to preserve arbitrary products.'},
        'source392_restriction':'The original source-generated projector reduces every actual atom in both directions and Y annihilates its full Fock space. Removing all words containing13 gives precisely the independently generated H0 D/E polynomials. The full112 complementary modes and mixed outside-occupation sectors remain present.',
        'actual_N2_complement_consumer':{'input_CAR':list(incoming),'all_input_and_output_modes_in_original_P_complement':True,
            'scope':'The source-point Fock fiber value of the original Gauss smooth section; Y squared is multiplication, so extension does not change this value. The norm is a fiber Fock norm, not a spatial integral norm or spectral pole.',
            'original_Y_image':encode_state(once),'original_Y_squared_image':encode_state(twice),
            'atom13_normalization':'Y/N_source from the actual fixed original four-time decomposition',
            'new_E2_grade2_word_coefficient':str(coefficient),'new_E2_grade2_image':encode_state(image),
            'Fock_norm_squared':str(norm_squared),'all_grade3_E3_terms_zero_on_N2':True,
            'original_Y_cubed_image':encode_state(thrice),
            'old_E2_raises_two_image_reproduced_from_original70_Yukawa':True},
        'r_smaller_than_N_bound_installed':False,
        'no_Hermitian_full_time_graph_or_proton_identification_inferred':True}


def canonical_K2_counterterm():
    raw = RawLiveCoefficients(); q = raw.q
    at = dict(zip(q, (1, 0, 1, 0, 0, 1)))
    B = rational(raw.K/raw.N); B0 = rational(B.subs(at))
    d = [rational(B.diff(x).subs(at)) for x in q]
    d2 = [[rational(B.diff(x, y).subs(at)) for y in q] for x in q]
    matrix = rational(4*sum((B0[i, j]*d2[i][j] for i in range(6) for j in range(6)), s.zeros(6))-
        8*sum((d[i][j, :].T*d[j][i, :] for i in range(6) for j in range(6)), s.zeros(6)))
    p = s.Matrix(s.symbols('canonical_kappa0:6', real=True)); f = (p.T*B*p)[0]
    literal = s.expand(2*sum(s.diff(f, q[i], q[j]).subs(at)*s.diff(f, p[i], p[j]).subs(at)-
        s.diff(f, q[i], p[j]).subs(at)*s.diff(f, p[i], q[j]).subs(at) for i in range(6) for j in range(6)))
    assert s.expand(literal-(p.T*matrix*p)[0]) == 0
    correction = rational(-matrix/(16*J0[0, 0]))
    assert s.simplify(correction[0, 0]+s.sqrt(30)/320) == 0
    return {'source_q': [1, 0, 1, 0, 0, 1], 'Lambda2_quadratic_matrix': encode(matrix),
        'K2_star_minus_commuting_quadratic_matrix': encode(correction),
        'canonical_kappa0_squared_coefficient': str(correction[0, 0]),
        'complete_model_coverage': 'On the vacuum, only the lapse derivative has coframe momenta, with quadratic part K(q)pp/N. Its other scalar/gauge terms and all three shift derivatives have no coframe momenta. Mixed second contractions therefore have coframe-momentum degree0, and fourth contractions also have degree0. The displayed degree2 coefficient is an exact complete-model coefficient.',
        'retained_canonical_variables': 'Original q6,kappa6 inside z100,p100. The13 temporal invariant readouts are never assigned canonical brackets.'}


def polynomial_json(polynomial):
    return [{'word': list(word), 'coefficient': str(DOMAIN.to_sympy(value))}
            for word, value in sorted(polynomial.items())]


def actual_K3_consumer(new_energy, original):
    old_model = OrderedTemporalCoefficients(); old_model.atoms[0] = {(0,): DOMAIN.one}
    _, old_energy, _ = old_model.generate(3)
    assert new_energy[:3] == old_energy[:3]
    delta = add(new_energy[3], scale(-1, old_energy[3]))
    defect = add(old_energy[3], scale(-1, involution(old_energy[3])))
    assert add(delta, scale(-1, involution(delta))) == scale(-1, defect)
    assert not add(new_energy[3], scale(-1, involution(new_energy[3])))
    mixed = {w: v for w, v in defect.items() if 0 in w}
    saved = {tuple(row['word']): field_element(s.sympify(row['coefficient']))
             for row in original['formal_calculation']['actual_coframe_containing_terms']}
    assert mixed == saved and len(mixed) == 30
    values = {tuple(row['word']): field_element(s.sympify(row['value']))
              for row in original['actual_consumer']['individual_nested_word_values']}
    actual = sum((coefficient*values[word] for word, coefficient in mixed.items()), DOMAIN.zero)
    assert actual == field_element(6623*s.sqrt(30)/145673515584)
    average = scale(HALF, add(old_energy[3], involution(old_energy[3])))
    assert len(add(new_energy[3], scale(-1, average))) == 240
    return {'original_actual_vacuum_Gauss_germ': original['actual_consumer']['input'],
        'same_complete30_word_consumer_bound': True,
        'old_K3_adjoint_difference': str(DOMAIN.to_sympy(actual)),
        'generated_correction_adjoint_difference': str(DOMAIN.to_sympy(-actual)),
        'new_K3_actual_adjoint_difference': '0 by the generated complete word identity on the same original operators',
        'new_K3_minus_averaged_old_nonzero_free_word_count': 240,
        'scope': 'The correction is generated by the original projected four equations. The 240-word comparison is an algebraic readout, not an assertion that every difference survives actual operator relations.'}


def main():
    started = time.monotonic()
    names = ('source_common_weyl_symbol', 'independent_source_common_weyl_symbol',
        'source_scalar_temporal_form', 'independent_source_scalar_temporal_form',
        'source_temporal_dirac_reduction', 'source_temporal_energy_adjoint',
        'independent_source_temporal_energy_adjoint', 'source_quantum_grade_structure',
        'source_yukawa_reducing_carrier', 'independent_source_yukawa_reducing_carrier',
        'source_quantum_stabilizer', 'independent_source_quantum_stabilizer')
    paid = {name: bound(name) for name in names}
    h0 = SourceCanonicalStarTemporalReduction(3, 'none')
    D0, E0, stages0 = h0.generate()
    assert all(p == involution(p) for row in D0 for p in row)
    assert all(p == involution(p) for p in E0)
    print('PASS literal four-pair Weyl conjugation and original H0 projected equations through order3', flush=True)
    dynamics0 = verify_extended_consumers(h0, D0, E0)
    print('PASS R/L, lifted algebra and original projected Heisenberg dynamics; R nonmultiplicativity retained', flush=True)
    full = SourceCanonicalStarTemporalReduction(3, 'original')
    sharp = SourceCanonicalStarTemporalReduction(3, 'adjoint')
    D, E, stages = full.generate(); Ds, Es, _ = sharp.generate()
    _, old_full_energy, _ = full.original.generate(3)
    assert E[:3] == old_full_energy[:3]
    assert Ds == [[involution(p) for p in row] for row in D]
    assert Es == [involution(p) for p in E]
    assert any(p != involution(p) for row in D for p in row)
    dynamics = verify_extended_consumers(full, D, E)
    print('PASS original full Yukawa and adjoint-paired time graph/energy with actual lifted dynamics', flush=True)
    Lambda0, total0 = original_total_hamiltonian(h0, D0, E0)
    Lambda, total = original_total_hamiltonian(full, D, E)
    Lambdas, _ = original_total_hamiltonian(sharp, Ds, Es)
    assert all(p == involution(p) for row in Lambda0 for p in row)
    assert Lambdas == [[involution(p) for p in row] for row in Lambda]
    print('PASS original total Hamiltonian: all eight projected constraints preserved and all four time updates equal intrinsic reduced dynamics', flush=True)
    K2 = canonical_K2_counterterm()
    K3 = actual_K3_consumer(E0, paid['source_temporal_energy_adjoint'])
    Fock = source_fock_consumer(D, E, D0, E0)
    print('PASS source Fock grading, actual Gauss coefficient extraction and nonzero original N2 complement E2', flush=True)
    print('PASS full-source canonical K2 counterterm and cancellation of the signed actual K3 adjoint defect', flush=True)
    inputs = [HERE/(name+'.json') for name in names]+[HERE/name for name in (
        'source_canonical_star_temporal_reduction.py', 'source_quantum_ordered_temporal.py',
        'source_quantum_temporal_symbol.py', 'source_scalar_temporal_form.py',
        'source_common_weyl_symbol.py', 'independent_source_coframe_live_ordering.py',
        'source_common_hamiltonian.py', 'source_quantum_grade_structure.py',
        'FockFilteredWords.lean', 'FockRaisingTensor.lean', 'FockRaising.lean')]
    record = {'root': ROOT_ID, 'source_sha256': paid['source_common_weyl_symbol']['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs},
        'scope': 'SOURCE_CANONICAL_WEYL_TEMPORAL_GRAPH_RETRACTION_AND_PROJECTED_DYNAMICS_THROUGH_FORMAL_ORDER3',
        'extended_canonical_variables': 'eta=y-y_source and the original four primary momenta pi_y; their Weyl product has eta_a star pi_b-pi_b star eta_a=i delta_ab. Retained coefficients use the original canonical100/Fock504 operator composition.',
        'source_graph_normalization': 'G_D=-sum pi_y,a D_a with no caller-supplied higher-primary generator; U_D=exp(ad_star(G_D)/i), R_D=ev_eta=pi=0 U_D, L_D=U_D^-1 incl. D(0)=0 at the original positive time column.',
        'literal_star_derivation': 'Both temporal Weyl products are expanded. ad_G/i acts as i*pi_a*(D_a star X-X star D_a)+(D_a star partial_eta_a X+partial_eta_a X star D_a)/2. Positive primary degree cannot decrease, so the projected exponential is exactly the derived Jordan recursion.',
        'source_equation': 'R_D(-partial_y H_epsilon)=0; at every order the new D coefficient enters only through the original scalar source Jacobian J0. No trace/cyclic stationary equation is substituted.',
        'H0': {'stages': stages0, 'time_coefficients': [[polynomial_json(p) for p in row] for row in D0],
            'energy_coefficients': [polynomial_json(p) for p in E0], 'every_coefficient_Hermitian': True,
            'dynamics': dynamics0, 'original_total_Hamiltonian': total0},
        'full_original_Y': {'stages': stages, 'time_coefficients': [[polynomial_json(p) for p in row] for row in D],
            'energy_coefficients': [polynomial_json(p) for p in E],
            'adjoint_branch_generated_independently_and_equals_word_adjoint': True,
            'time_graph_Hermitian_assumed': False, 'original_Y_removed_or_Yadjoint_added': False,
            'dynamics': dynamics, 'original_total_Hamiltonian': total,
            'adjoint_multiplier_branch_generated_independently': True},
        'actual_canonical_K2': K2, 'actual_K3_germ': K3, 'source_Fock_consumer': Fock,
        'comparison_scope': 'K1/K2 equality compares reduction rules applied to the same current scalar-form atoms; it does not identify the earlier scalar-square H_native with the current form.',
        'producer_meaning': 'The same source time family acquires a specified canonical graph retraction, lifted retained algebra and exact projected formal dynamics. Its degree1/2 energies preserve the original operator words; degree3 is generated by all four projected constraints and repairs the earlier specific adjoint defect.',
        'formal_scope': 'All identities are modulo epsilon^4 in the source deformation. The all-order recurrence is implemented parametrically, but the receipt tests order3; epsilon=1 summation, a closed Hilbert generator and the quantum spectrum are not inferred.',
        'source_occurrence_or_quantum_time_family_replaced': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_canonical_star_temporal_reduction.json').write_text(json.dumps(record, separators=(',', ':'))+'\n')
    print('PASS source canonical star temporal reduction', record['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
