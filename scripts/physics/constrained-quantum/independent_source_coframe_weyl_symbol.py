#!/usr/bin/env python3
"""Raw BF and literal symmetric-product audit of the coframe Weyl symbol.

The new symbol constructor is not imported. Four quadratic placements and two
linear placements differentiate actual local polynomials. Multiplication by the
original live Gauss metric is tested before and after the full source operator.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_coframe_live_ordering import (
    RawLiveCoefficients, HERE, ROOT, ROOT_ID, rational, eq, full,
    polynomial_action, current, terms, state_encode)
from independent_source_quantum_ordered_temporal import raw_coframe_family
from independent_source_temporal_coframe_pairing import at
from independent_source_gauge_legendre import bindings, decode, encode
from independent_source_gauss_quantum_current import decoded_state


def zero(value):
    assert s.cancel(s.expand(value)) == 0


def same(left, right):
    assert not terms([(1, left), (-1, right)])


def literal_half_density(cf, qpoint, word, polynomial, z):
    origin = dict.fromkeys(z, 0)
    volume0 = s.prod(qpoint[j] for j in (0, 2, 5))
    volume = s.prod(qpoint[j]+z[j] for j in (0, 2, 5))
    shifted = (volume0/volume)**s.Rational(len(word)+2, 2)*polynomial
    f0 = s.cancel(shifted.subs(origin))
    g = rational(s.Matrix([s.diff(shifted, x).subs(origin) for x in z]))
    H = rational(s.hessian(shifted, list(z)).subs(origin))
    image, _ = polynomial_action(cf, word, f0, g, H)
    return image, g, H


def weyl_readback(cf, Mh, q, ys, qpoint, timepoint, word, f, z, correction):
    """Evaluate each Weyl binomial placement, without the conversion formula."""
    origin = dict.fromkeys(z, 0)
    live = {**dict(zip(q, [v+x for v, x in zip(qpoint, z)])), **dict(zip(ys, timepoint))}
    point = {**dict(zip(q, qpoint)), **dict(zip(ys, timepoint))}
    P = lambda j, value: -s.I*s.diff(value, z[j])
    quadratic = s.S.Zero
    for (i, j), coefficient in cf['K'].todok().items():
        a = coefficient.subs(live)
        quadratic += (a*P(i, P(j, f))+P(i, a*P(j, f))+
                      P(j, a*P(i, f))+P(i, P(j, a*f))).subs(origin)/4
    mixed = []
    for j, M in enumerate(Mh):
        matrix = full(rational(M.subs(live)))
        left = current(matrix, {word: P(j, f)})
        right = current(matrix, {word: f})
        mixed.append((1, {w: s.cancel(value.subs(origin)/2) for w, value in left.items()}))
        mixed.append((1, {w: s.cancel(P(j, value).subs(origin)/2) for w, value in right.items()}))
    data = {key: at(value, point) for key, value in cf.items()}
    f0 = s.cancel(f.subs(origin))
    constant, _ = polynomial_action(data, word, f0, s.zeros(6, 1), s.zeros(6))
    return terms([(s.cancel(quadratic+correction*f0), {word: 1}), (1, constant)]+mixed), data


def generic_coefficients(raw, ys, candidate):
    e, cf = raw_coframe_family(raw, ys)
    q = raw.q
    p = s.Matrix([s.Symbol(name, real=True) for name in candidate['canonical_momenta']])
    number = s.Symbol('particle_number', integer=True, nonnegative=True)
    variables = {str(v): v for v in (*q, *ys, *p, number)}
    volume = q[0]*q[2]*q[5]
    K = cf['K']; eq(K.H, K)
    divK = rational(s.Matrix([sum(s.diff(K[i, j], q[i]) for i in range(6)) for j in range(6)]))
    quarter = s.cancel(sum(s.diff(K[i, j], q[i], q[j]) for i in range(6) for j in range(6))/4)
    zero(quarter+ys[0]/(4*volume))
    gradient = s.Matrix([s.diff(volume, x)/volume for x in q])
    D = rational(s.I*cf['drift'].T)
    t = rational(s.Matrix([s.trace(M.H-M)/(16*s.I) for M in cf['M']]))
    eq(t, K*gradient); eq(D-divK, 2*t)
    Mh = [rational((M+M.H)/2) for M in cf['M']]
    for j, M in enumerate(Mh):
        eq(M.H, M); eq(cf['M'][j], M-s.I*t[j]*s.eye(8))
    eq(sum((M.diff(q[j]) for j, M in enumerate(Mh)), s.zeros(8)), s.zeros(8))
    eq(sum((gradient[j]*M for j, M in enumerate(Mh)), s.zeros(8)), s.zeros(8))
    alpha = (number+2)/2
    delta = s.cancel(alpha*((D+number*t).T*gradient)[0]-alpha**2*(gradient.T*K*gradient)[0]+
                     alpha*sum(K[i, j]*s.diff(gradient[i], q[j]) for i in range(6) for j in range(6)))
    correction = s.cancel(delta+quarter)
    zero(delta-3*ys[0]*(number+2)*(number+4)/(16*volume))
    zero(correction-ys[0]*(3*number**2+18*number+20)/(16*volume))
    symbol = candidate['symbol']
    scalar = s.cancel((p.T*K*p)[0]+correction)
    zero(scalar-s.sympify(symbol['scalar_momentum_part'], locals=variables))
    mixed = rational(sum((M*p[j] for j, M in enumerate(Mh)), s.zeros(8)))
    eq(mixed, decode(symbol['mixed_current_spin8'], variables)); eq(mixed.H, mixed)
    onebody = rational(cf['one_body']+cf['correction'])
    eq(onebody.H, onebody); eq(onebody, decode(symbol['onebody_with_live_correction'], variables))
    # Reindex independent tensor-product matrix entries into two current slots.
    kron = rational(sum((v*s.kronecker_product(cf['J'][a], cf['J'][b])
                         for (a, b), v in cf['W'].todok().items()), s.zeros(64)))
    eq(kron.H, kron)
    slots = {}
    for (ik, jl), v in kron.todok().items():
        i, k = divmod(ik, 8); j, ell = divmod(jl, 8)
        slots[8*i+j, 8*k+ell] = v
    eq(s.SparseMatrix(64, 64, slots), decode(symbol['complete_normal_current_tensor'], variables))
    for value, key in ((quarter, 'divdivK_over4'), (delta, 'half_density_potential'),
                       (correction, 'combined_scalar_correction'), (cf['constant'], 'original_source_potential')):
        zero(value-s.sympify(symbol[key], locals=variables))
    for shift in ys[1:]:
        zero(s.diff(scalar, shift)); eq(mixed.diff(shift), s.zeros(8))
        eq(onebody.diff(shift), s.zeros(8)); eq(kron.diff(shift), s.zeros(64))
        zero(s.diff(cf['constant'], shift))
    return e, cf, p, number, variables, Mh, scalar, correction, quarter


def commutator_check(raw, ys, cf, p, Mh, scalar, variables, row, example):
    q = raw.q; L = raw.e[1:, 1:]; Li = L.inv()
    G = rational(Li.T*Li); eq(G*(L*L.T), s.eye(3))
    fG = s.cancel(G[2, 2]); zero(fG-s.sympify(row['G22'], locals=variables))
    # Original commutator is collected from the divergence operator. Its first
    # order Weyl conversion is separately tested by two literal placements.
    dg = s.Matrix([s.diff(fG, x) for x in q])
    K = cf['K']; divK = s.Matrix([sum(s.diff(K[i, j], q[i]) for i in range(6)) for j in range(6)])
    first = rational(-2*K*dg)
    scalar_zero = s.cancel(-sum(K[i, j]*s.diff(fG, q[i], q[j]) for i in range(6) for j in range(6))-(divK.T*dg)[0])
    left = s.cancel(s.I*(first.T*p)[0]+scalar_zero)
    linear_weyl = s.cancel(left-sum(s.diff(first[j], q[j]) for j in range(6))/2)
    current_zero = rational(-s.I*sum((Mh[j]*dg[j] for j in range(6)), s.zeros(8)))
    zero(left-s.sympify(row['exact_left_symbol_after_inverse_Weyl'], locals=variables))
    zero(linear_weyl-s.sympify(row['exact_star_scalar_commutator'], locals=variables))
    eq(current_zero, decode(row['exact_star_current_spin8_commutator'], variables))
    # Expand both finite star products rather than identify just their Poisson term.
    star_left, star_right = scalar*fG, fG*scalar
    for i in range(6):
        star_left -= s.I*s.diff(scalar, p[i])*dg[i]/2
        star_right += s.I*dg[i]*s.diff(scalar, p[i])/2
        for j in range(6):
            even = -s.diff(scalar, p[i], p[j])*s.diff(fG, q[i], q[j])/8
            star_left += even; star_right += even
    zero(star_left-star_right-linear_weyl)
    assert s.Poly(scalar, *p).total_degree() == 2
    assert all(s.diff(scalar, p[i], p[j], p[k]) == 0 for i in range(6) for j in range(6) for k in range(6))
    qpoint = tuple(map(s.sympify, example['q'])); timepoint = tuple(map(s.sympify, example['time']))
    word = tuple(example['input_CAR']); sub = {**dict(zip(q, qpoint)), **dict(zip(ys, timepoint))}
    data = {key: at(value, sub) for key, value in cf.items()}
    z = s.Matrix(s.symbols('commutator_increment0:6', real=True)); origin = dict.fromkeys(z, 0)
    gradient, Hessian = decode(example['gradient6']), decode(example['Hessian6'])
    polynomial = 1+(gradient.T*z)[0]+(z.T*Hessian*z)[0]/2
    live = dict(zip(q, [v+x for v, x in zip(qpoint, z)]))
    Gpoly = fG.subs(live)
    image, _, _ = literal_half_density(data, qpoint, word, polynomial, z)
    multiplied, _, _ = literal_half_density(data, qpoint, word, Gpoly*polynomial, z)
    original = terms([(1, multiplied), (-s.cancel(Gpoly.subs(origin)), image)])
    P = lambda j, a: -s.I*s.diff(a, z[j])
    weyl = s.S.Zero
    for j in range(6):
        coefficient = (s.I*first[j]).subs({**live, **dict(zip(ys, timepoint))})
        weyl += (coefficient*P(j, polynomial)+P(j, coefficient*polynomial)).subs(origin)/2
    # Scalar Weyl constant is read independently from the collected old commutator.
    scalar_constant = s.cancel(linear_weyl.subs(dict.fromkeys(p, 0)).subs(sub))
    converted = terms([(s.cancel(weyl+scalar_constant), {word: 1}),
                       (1, current(full(at(current_zero, sub)), {word: 1}))])
    same(original, converted); assert original
    source_q = (1, 0, 1, 0, 0, 1); source_time = (raw.N, 0, 0, 0)
    source_sub = {**dict(zip(q, source_q)), **dict(zip(ys, source_time))}
    source_data = {key: at(value, source_sub) for key, value in cf.items()}
    source_G = fG.subs(dict(zip(q, [v+x for v, x in zip(source_q, z)])))
    linear = z[0]
    a, _, _ = literal_half_density(source_data, source_q, (), source_G*linear, z)
    b, _, _ = literal_half_density(source_data, source_q, (), linear, z)
    germ = terms([(1, a), (-1, b)]); same(germ, {(): raw.N})
    zero(raw.N-s.sympify(row['source_linear_germ_value']))
    return {'all6q_allmomentum_original_commutator_to_Weyl': True,
            'both_star_products_expanded_through_exact_degree2': True,
            'all_third_momentum_derivatives_zero': True,
            'actual_fullCAR_operator_composition': state_encode(original),
            'independent_two_placement_inverse_Weyl': state_encode(converted),
            'actual_source_vacuum_Gauss_germ': state_encode(germ),
            'freezing_G_at_source_loses_nonzero_commutator': True}


def main():
    began = time.monotonic(); path = HERE/'source_coframe_weyl_symbol.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    paid = ('independent_source_coframe_live_ordering', 'independent_source_temporal_coframe_pairing',
            'independent_source_temporal_gauss_relations')
    for name in paid:
        row = json.loads((HERE/(name+'.json')).read_text()); count += bindings(row)
        assert row['root'] == ROOT_ID
    raw = RawLiveCoefficients()
    ys = (s.Symbol(candidate['time_parameters'][0], positive=True),
          *[s.Symbol(v, real=True) for v in candidate['time_parameters'][1:]])
    e, cf, p, number, variables, Mh, scalar, correction, quarter = generic_coefficients(raw, ys, candidate)
    print('PASS independent raw BF all-sixq/four-time Weyl quadratic/current/normal-tensor coefficients', flush=True)
    consumers = []
    assert [tuple(row['input_CAR']) for row in candidate['actual_consumers']] == [(), (144,), (144,396), (0,63,315)]
    for saved in candidate['actual_consumers']:
        qpoint = tuple(map(s.sympify, saved['q'])); timepoint = tuple(map(s.sympify, saved['time']))
        assert timepoint[0] > 0 and timepoint[0]**2 > sum(v*v for v in timepoint[1:])
        word = tuple(saved['input_CAR']); sub = {**dict(zip(raw.q, qpoint)), **dict(zip(ys, timepoint))}
        z = s.Matrix(s.symbols('weyl_increment0:6', real=True)); origin = dict.fromkeys(z, 0)
        g, H = decode(saved['gradient6']), decode(saved['Hessian6'])
        f = 1+(g.T*z)[0]+(z.T*H*z)[0]/2
        corr = s.cancel(correction.subs(number, len(word)).subs(sub))
        image, data = weyl_readback(cf, Mh, raw.q, ys, qpoint, timepoint, word, f, z, corr)
        actual, ug, uH = literal_half_density(data, qpoint, word, f, z)
        same(image, actual); same(actual, decoded_state(saved['original_U_H_U_inverse']))
        same(image, decoded_state(saved['canonical_Weyl_readback']))
        eq(ug, decode(saved['inverse_half_density_gradient6'])); eq(uH, decode(saved['inverse_half_density_Hessian6']))
        defect = {word: s.cancel(-quarter.subs(sub))}; assert defect[word] != 0
        same(defect, decoded_state(saved['omitted_divdiv_symbol_defect'])); zero(corr-s.sympify(saved['symbol_scalar_correction']))
        consumers.append({'input_CAR': list(word), 'whole_image': state_encode(image),
                          'omitted_second_derivative_defect': state_encode(defect),
                          'literal_four_and_two_placements_checked': True})
    print('PASS literal Weyl placements versus original inverse-half-density action in four CAR sectors', flush=True)
    commutator = commutator_check(raw, ys, cf, p, Mh, scalar, variables,
                                  candidate['Gauss_G_composition'], candidate['actual_consumers'][2])
    print('PASS full live-G operator composition, inverse Weyl, exact finite Moyal products and nonzero source germ', flush=True)
    files = [Path(__file__), path, HERE/'source_coframe_weyl_symbol.py',
             HERE/'independent_source_coframe_live_ordering.py', HERE/'independent_source_quantum_ordered_temporal.py',
             HERE/'independent_source_temporal_coframe_pairing.py']+[HERE/(name+'.json') for name in paid]
    result = {'verdict': 'CERTIFIED_EXACT_RAW_COFRAME_WEYL_SYMBOL_AND_LIVE_G_OPERATOR_COMPOSITION',
              'root': ROOT_ID, 'source_sha256': candidate['source_sha256'],
              'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
              'source_binding_checks': count, 'candidate_constructor_imported': False,
              'independent_method': 'Original epsilon BF inverse and primary graph; tensor-product CAR normal coefficients; literal four quadratic and two linear Weyl placements; actual inverse half-density polynomial differentiation; original two-operator composition with live Gauss G.',
              'generic_all6q_all4time_full504_coefficients': True,
              'source_divdivK_over4': str(quarter), 'complete_scalar_correction': str(correction),
              'normal_product_tensor_and_onebody_original': True,
              'every_coframe_coefficient_independent_of_time_shifts': True,
              'actual_consumers': consumers, 'live_G_composition': commutator,
              'operator_or_ordering_replaced': False,
              'full_time_secondary_reduction_or_spectrum_generated': False,
              'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
              'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_coframe_weyl_symbol.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent source coframe Weyl symbol', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
