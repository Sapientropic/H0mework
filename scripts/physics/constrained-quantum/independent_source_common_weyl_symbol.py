#!/usr/bin/env python3
"""Original Hodge/implicit-section audit of the common canonical Weyl symbol.

The common constructor and its scalar/Weyl helper are not imported. Gauge
inverse jets are solved from the original slice equations. The scalar symbol
uses its separate independent certificate; full operator images are rebuilt
from the original four densities and literal source inverse half-density jets.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_joint_form_hamiltonian import (
    RawGaussSection, RawLiveCoefficients, HERE, ROOT, ROOT_ID, bindings,
    rational, eq, decode, encode, terms, current, state_encode, decoded_state,
    zero, state_equal, raw_gauge_coefficients, whole_action, transformed_section,
    half_density_derivatives)
from independent_source_scalar_form_hamiltonian import raw_coefficients
from independent_source_quantum_ordered_temporal import raw_coframe_family
from independent_source_temporal_coframe_pairing import at
from independent_source_common_hamiltonian import raw_matter
from independent_source_full_quantum_adjoint import sparse, dual_pair


def implicit_gauge_symbol(section, point, e):
    """Every inverse derivative is a fresh linear solve of M U=I."""
    free = section.free[6:]
    V = rational(s.Matrix.hstack(*(R*point for R in section.T)))
    M = V[section.fixed, :]
    U, parameters = M.gauss_jordan_solve(s.eye(3)); assert parameters.rows == 0
    U = rational(U); eq(M*U, s.eye(3))
    pivot_gauge = s.eye(36)[:, [j-67 for j in section.fixed]]
    eg = s.eye(103)[67:, free]
    scalar_free_orbit = V[free, :]
    Avec = rational(eg-pivot_gauge*U.T*scalar_free_orbit.T)
    Ccur = rational(-pivot_gauge*U.T)
    dV, dM, dU = [], [], []
    for coordinate in free:
        derivative = rational(s.Matrix.hstack(*(R[:, coordinate] for R in section.T)))
        dm = derivative[section.fixed, :]
        du, params = M.gauss_jordan_solve(-dm*U); assert params.rows == 0
        du = rational(du); eq(M*du+dm*U, s.zeros(3))
        dV.append(derivative[free, :]); dM.append(dm); dU.append(du)
    dvec_small = [rational(-du.T*scalar_free_orbit.T-U.T*dv.T)
                  for du, dv in zip(dU, dV)]
    dvec = [rational(pivot_gauge*dv) for dv in dvec_small]
    dcur = [rational(-pivot_gauge*du.T) for du in dU]
    divergence_small = rational(sum((v[:, i] for i, v in enumerate(dvec_small)), s.zeros(3, 1)))
    divergence = pivot_gauge*divergence_small
    ddiv = s.zeros(3, 94)
    for i in range(94):
        column = s.zeros(3, 1)
        for k in range(94):
            rhs = -dM[i]*dU[k]-dM[k]*dU[i]
            if rhs.todok():
                ddu, params = M.gauss_jordan_solve(rhs); assert params.rows == 0
                ddu = rational(ddu); eq(M*ddu-rhs, s.zeros(3))
            else: ddu = s.zeros(3)
            column -= ddu.T*scalar_free_orbit[k, :].T+dU[i].T*dV[k][k, :].T+dU[k].T*dV[i][k, :].T
        ddiv[:, i] = rational(column)
    original = raw_gauge_coefficients(e, point[67:, :].reshape(3, 12), section.native)
    W, shift = original['weight'], original['shift']
    eq(W.H, W); eq(W.conjugate(), W); eq(shift.conjugate(), shift)
    zero(s.trace(W*original['ds']))
    P = rational(Avec.T*W*Avec/2)
    divP = rational((Avec.T*W*divergence+
        sum((dvec[i].T*W*Avec[:, i] for i in range(94)), s.zeros(94, 1)))/2)
    Gram = rational(pivot_gauge.T*W*pivot_gauge)
    crossed = sum((dvec_small[i][:, k].T*Gram*dvec_small[k][:, i])[0]
                  for i in range(94) for k in range(94))
    divdivP = s.cancel(((divergence.T*W*divergence)[0]+crossed+
        2*sum((Avec[:, i].T*W*pivot_gauge*ddiv[:, i])[0] for i in range(94)))/2)
    dc = s.zeros(36, 94)
    for i, ambient in enumerate(free):
        if ambient >= 67: dc[:, i] = original['ds'][:, ambient-67]
    Mcur = rational(Avec.T*W*Ccur)
    Mzero = rational(-Avec.T*W*shift)
    divMcur = rational(Ccur.T*W*divergence+
        sum((dcur[i].T*W*Avec[:, i] for i in range(94)), s.zeros(3, 1)))
    divMzero = s.cancel(-(divergence.T*W*shift)[0]-
        sum((Avec[:, i].T*W*dc[:, i])[0] for i in range(94)))
    first, second, density, _ = half_density_derivatives(section, point, 0, False)
    ell = -first[6:, :]; Hell = rational(ell*ell.T-second[6:, 6:])
    Vdensity = s.cancel((ell.T*P*ell)[0]+(divP.T*ell)[0]+
        sum(v*Hell[i, j] for (i, j), v in P.todok().items()))
    return {'original': original, 'principal': P, 'div_principal': divP,
        'divdiv_principal': divdivP, 'weyl_correction': s.cancel(divdivP/4),
        'momentum_current': Mcur, 'momentum_identity': Mzero,
        'div_momentum_current': divMcur, 'div_momentum_identity': divMzero,
        'square_current': rational(Ccur.T*W*Ccur/2), 'linear_current': rational(-Ccur.T*W*shift),
        'classical_zero': s.cancel((shift.T*W*shift)[0]/2+original['potential']),
        'half_density_potential': Vdensity, 'density': density,
        'a': Avec, 'current': Ccur, 'd_a': dvec, 'd_current': dcur,
        'implicit_inverse_derivative_rows': 94, 'implicit_inverse_second_derivative_pairs': 94*94}


def gauge_weyl_placements(symbol, charges, word, value, gradient, Hessian):
    """Four quadratic placements and two linear placements on the exact jet."""
    g, H = gradient[6:, :], Hessian[6:, 6:]
    second = -sum(v*H[i, j] for (i, j), v in symbol['principal'].todok().items())
    first = (symbol['div_principal'].T*g)[0]
    d2 = symbol['divdiv_principal']*value
    scalar = (second+(second-first)+(second-first)+(second-2*first-d2))/4
    pleft = -s.I*(symbol['momentum_identity'].T*g)[0]
    pright = pleft-s.I*symbol['div_momentum_identity']*value
    scalar += (pleft+pright)/2
    scalar += value*(symbol['classical_zero']+symbol['half_density_potential']+symbol['weyl_correction'])
    rows = [(scalar, {word: 1})]
    images = [current(Q, {word: 1}) for Q in charges]
    for a in range(3):
        left = -s.I*(symbol['momentum_current'][:, a].T*g)[0]
        right = left-s.I*symbol['div_momentum_current'][a]*value
        rows.append(((left+right)/2+value*symbol['linear_current'][a], images[a]))
    for (a, b), coefficient in symbol['square_current'].todok().items():
        rows.append((value*coefficient, current(charges[a], images[b])))
    return terms(rows)


def compare_gauge_coefficients(actual, saved):
    matrices = ('principal', 'div_principal', 'momentum_current', 'momentum_identity',
                'div_momentum_current', 'square_current', 'linear_current')
    for key in matrices:
        expected = decode(saved[key]); value = actual[key]
        if key == 'momentum_current' and expected.cols == 12:
            value = s.zeros(94, 9).row_join(value)
        elif key in ('div_momentum_current', 'linear_current') and expected.rows == 12:
            value = s.zeros(9, 1).col_join(value)
        elif key == 'square_current' and expected.rows == 12:
            value = s.diag(s.zeros(9), value)
        eq(value, expected)
    for key in ('divdiv_principal', 'weyl_correction', 'div_momentum_identity',
                'classical_zero', 'half_density_potential'):
        zero(actual[key]-s.sympify(saved[key]))


def main():
    started = time.monotonic(); path = HERE/'source_common_weyl_symbol.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    paid = ('independent_source_scalar_weyl_symbol', 'independent_source_coframe_weyl_symbol',
            'independent_source_common_temporal_form')
    for name in paid:
        receipt = json.loads((HERE/(name+'.json')).read_text()); count += bindings(receipt)
        assert receipt['root'] == ROOT_ID and receipt['verdict'].startswith('CERTIFIED_')
    section, cf_raw = RawGaussSection(), RawLiveCoefficients()
    assert section.native.hashes == candidate['source_sha256']
    row = candidate['actual_consumer']; q = tuple(map(s.sympify, row['q']))
    clock = tuple(map(s.sympify, row['time'])); assert all(clock[1:])
    x, A = decode(row['x61']), decode(row['A36'])
    point = s.Matrix(q).col_join(x).col_join(A.reshape(36, 1))
    ys = (s.Symbol('quantum_n', positive=True), *s.symbols('quantum_b1:4', real=True))
    family_e, family_cf = raw_coframe_family(cf_raw, ys)
    substitutions = {**dict(zip(cf_raw.q, q)), **dict(zip(ys, clock))}
    e = at(family_e, substitutions)
    symbol = implicit_gauge_symbol(section, point, e)
    compare_gauge_coefficients(symbol, candidate['gauge_symbol_coefficients'])
    assert symbol['weyl_correction'] and symbol['half_density_potential']
    print('PASS original BF electric inverse and all94-slice gauge symbol derivatives, currents and density terms', flush=True)

    word = tuple(row['input_CAR']); assert word == (144, 396)
    g, h = decode(row['gradient100']), decode(row['Hessian100'])
    jets, first, second, density, U = transformed_section(section, point, word, g, h, True)
    Gauss = section.Gauss_checks(point, jets)
    assert Gauss['all3_original_Gauss_values_zero'] == row['Gauss']['all3_Gauss_values_zero']
    assert Gauss['all309_first_derivatives_of_Gauss_zero'] == row['Gauss']['all309_first_derivatives_of_Gauss_zero']
    assert U > 0 and density > 0
    coframe = {key: at(value, substitutions) for key, value in family_cf.items()}
    scalar = raw_coefficients(section.native, e, x, A)
    connection = s.zeros(4, 12); connection[1:, :] = A
    matter = raw_matter(e, scalar['phi'], connection)
    M = dual_pair(rational(-s.I*matter['E_inverse']*matter['lower']))
    Y = dual_pair(rational(-s.I*matter['volume']*matter['E_inverse']*matter['Y']))
    M0 = sparse(M-Y); eq(M0.H, M0)
    operators = dict(coframe=coframe, scalar=scalar, gauge=symbol['original'], matter=M0)
    pieces, H0 = whole_action(operators, jets)
    pieces['matter_noY'] = pieces.pop('matter_without_Lorentz')
    for name, image in pieces.items():
        assert image
        state_equal(image, decoded_state(row['four_original_component_images'][name]))
        state_equal(image, decoded_state(row['four_Weyl_component_images'][name]))
    gauge_weyl = gauge_weyl_placements(symbol, section.native.Qs, word, 1, g, h)
    state_equal(gauge_weyl, pieces['gauge'])
    omitted = {word: symbol['weyl_correction']}
    state_equal(omitted, decoded_state(row['omitted_gauge_divdiv_symbol_defect']))
    Yimage = current(Y, {word: 1}); assert Yimage
    H = terms([(1, H0), (1, Yimage)])
    Hsharp = terms([(1, H0), (1, current(Y.H, {word: 1}))])
    for key, image in [('Weyl_H0', H0), ('Weyl_H', H), ('original_H', H),
                       ('original_Y', Yimage), ('Weyl_Hsharp', Hsharp)]:
        state_equal(image, decoded_state(row[key]))
    assert any(second[i, j] for i in (0, 2, 5) for j in range(6, 100))
    print('PASS literal full100 inverse half-density, original four-component images and unchanged full504 Yukawa', flush=True)

    files = [Path(__file__), path, HERE/'source_common_weyl_symbol.py',
        HERE/'independent_source_joint_form_hamiltonian.py', HERE/'independent_source_quantum_gauss_section.py',
        HERE/'independent_source_scalar_form_hamiltonian.py', HERE/'independent_source_quantum_ordered_temporal.py',
        HERE/'independent_source_common_hamiltonian.py', HERE/'independent_source_gauge_legendre.py']
    files += [HERE/(name+'.json') for name in paid]
    result = {'verdict': 'CERTIFIED_ORIGINAL_FOUR_ENERGY_CANONICAL_WEYL_SYMBOL_AND_FULL504_READBACK',
        'root': ROOT_ID, 'source_sha256': section.native.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'source_binding_checks': count, 'candidate_constructor_imported': False,
        'scalar_symbol_independently_certified_by_separate_agent': True,
        'gauge_method': 'Original native BF/Hodge electric density Hessian; exact linear solves of M U=I and both differentiated equations; all94 first derivatives and all8836 second derivative pairs; four quadratic and two linear Weyl placements.',
        'gauge_coefficients_compared': list(candidate['gauge_symbol_coefficients']),
        'actual_consumer': {'q': list(map(str, q)), 'time': list(map(str, clock)), 'input_CAR': list(word),
            'Gauss': Gauss, 'positive_source_density': str(density), 'positive_common_half_density': str(U),
            'gauge_divdivP_over4': str(symbol['weyl_correction']),
            'gauge_half_density_potential': str(symbol['half_density_potential']),
            'literal_gauge_Weyl_image': state_encode(gauge_weyl),
            'four_original_components': {k: state_encode(v) for k, v in pieces.items()},
            'H0': state_encode(H0), 'H': state_encode(H), 'Y': state_encode(Yimage), 'Hsharp': state_encode(Hsharp),
            'omitted_gauge_correction_defect': state_encode(omitted)},
        'scope': 'The four-energy symbol quantizes back to the same source form on the original residual3 chart and common positive half-density. Time remains four real parameters; the original Yukawa is retained. Neither a temporal operator root nor a spectral measure is generated.',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'independent_source_common_weyl_symbol.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent common canonical Weyl symbol', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
