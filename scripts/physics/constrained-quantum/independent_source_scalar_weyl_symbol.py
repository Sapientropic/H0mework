#!/usr/bin/env python3
"""Independent coupled-equation audit of the original scalar slice Weyl symbol.

A single affine12 system, rather than separate inverse formulas, generates the
normal and section derivatives. Its original determinant generates the measure
jet. The final image is compared with the ambient97 source form through an
independently implicit-differentiated complete CAR Gauss two-jet.
"""
from __future__ import annotations

from functools import lru_cache
import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_scalar_form_hamiltonian import (
    RawGaussSection, raw_coefficients, form_action, HERE, ROOT, ROOT_ID,
    bindings, clean, rational, eq, decode, encode, terms, current,
    state_encode, decoded_state)


def zero(value): assert s.cancel(s.expand(value)) == 0

def same(left, right): assert not terms([(1, left), (-1, right)])


def original_slice_coefficients(section, e, x, A, point):
    raw = section.native; ambient = raw_coefficients(raw, e, x, A)
    geo = section.implicit_jets(point)
    retained = [i-6 for i in section.free if i >= 6]
    pivots = [i-6 for i in section.fixed]
    assert len(retained) == 94 and retained[:61] == list(range(61))
    y = point[6:, :]
    S = clean(s.Matrix.hstack(*(T*y for T in raw.Ts)))
    B = clean(s.Matrix.vstack(*((T*y).T for T in raw.Tb)))
    D = ambient['D']; M = S[pivots, :]
    L = D.T.row_join(B[:, pivots]).col_join(s.zeros(3, 9).row_join(M.T))
    rhs = B[:, retained].col_join(S[retained, :].T)
    inverse, params = L.gauss_jordan_solve(s.eye(12)); assert params.rows == 0
    inverse = rational(inverse); eq(L*inverse, s.eye(12)); eq(inverse*L, s.eye(12))
    X = rational(inverse*rhs); eq(L*X, rhs)
    derivatives_L, derivatives_X, derivatives_M = [], [], []
    for u in retained:
        dD = clean(raw.O.T*s.Matrix.hstack(*(T*raw.R[:, u] for T in raw.rhob))) if u < 61 else s.zeros(9)
        dB = s.Matrix.vstack(*(T[:, u].T for T in raw.Tb))
        dS = s.Matrix.hstack(*(T[:, u] for T in raw.Ts)); dM = dS[pivots, :]
        dL = dD.T.row_join(dB[:, pivots]).col_join(s.zeros(3, 9).row_join(dM.T))
        drhs = dB[:, retained].col_join(dS[retained, :].T)
        dX = rational(inverse*(drhs-dL*X)); eq(L*dX+dL*X, drhs)
        derivatives_L.append(dL); derivatives_X.append(dX); derivatives_M.append(dM)
    trace_X = rational(sum((dX[:, i] for i, dX in enumerate(derivatives_X)), s.zeros(12, 1)))
    trace_derivatives = s.zeros(12, 94)
    for i, dX in enumerate(derivatives_X):
        rhs2 = derivatives_L[i]*trace_X+sum((dL*dX[:, j] for j, dL in enumerate(derivatives_L)), s.zeros(12, 1))
        col = rational(-inverse*rhs2); eq(L*col+rhs2, s.zeros(12, 1))
        trace_derivatives[:, i] = col
    E = raw.Rd.row_join(s.zeros(70, 33))
    a = rational(E-raw.O*X[:9, :])
    Z = rational(section.free_reader[6:, :]*geo['tangent'][:, 6:])
    eq(a, ambient['a']*Z.T)
    da = [rational(-raw.O*dX[:9, :]) for dX in derivatives_X]
    div_a = rational(sum((matrix[:, i] for i, matrix in enumerate(da)), s.zeros(70, 1)))
    eq(div_a, -raw.O*trace_X[:9, :])
    ddiv_a = rational(-raw.O*trace_derivatives[:9, :])
    h = 2*ambient['h00']
    principal = rational(a.T*a/h)
    divP = rational((a.T*div_a+sum((matrix.T*a[:, i] for i, matrix in enumerate(da)), s.zeros(94, 1)))/h)
    crossed = s.S.Zero
    entries = [matrix.todok() for matrix in da]
    for i, row in enumerate(entries):
        crossed += sum(value*entries[j].get((r, i), 0) for (r, j), value in row.items())
    second = s.cancel(((div_a.T*div_a)[0]+crossed+2*sum((a[:, i].T*ddiv_a[:, i])[0] for i in range(94)))/h)
    alpha = geo['a'][:, 6:]
    charges = ambient['normal'].row_join(rational(-ambient['a']*alpha.T))
    U, params = M.gauss_jordan_solve(s.eye(3)); assert params.rows == 0
    eq(M*U, s.eye(3)); eq(U*M, s.eye(3))
    dcharges = []
    for u, dM in zip(retained, derivatives_M):
        da0, dn = ambient['derivatives'][u]
        dalpha = rational(-U*dM*alpha)
        dcharges.append(dn.row_join(rational(-da0*alpha.T-ambient['a']*dalpha.T)))
    # Original orbit determinant, with its source orientation, pays the whole
    # first/second density jet by Jacobi's determinant differentiation law.
    orientation = s.sign(section.source_minor.det())
    rho = s.cancel(orientation*M.det()); assert rho > 0
    ell = s.Matrix([s.trace(U*dM)/2 for dM in derivatives_M])
    hlog = s.Matrix(94, 94, lambda i, j: -s.trace(U*derivatives_M[i]*U*derivatives_M[j])/2)
    ell, hlog = rational(ell), rational(hlog); eq(hlog, hlog.T)
    b = ambient['b']; db = ambient['db'][:, retained]
    mixed = rational(a.T*charges/ambient['h00'])
    div_mixed = rational((charges.T*div_a+sum((dc.T*a[:, i] for i, dc in enumerate(dcharges)), s.zeros(12, 1)))/ambient['h00'])
    identity = rational(-a.T*b/ambient['h00'])
    div_identity = s.cancel(-((div_a.T*b)[0]+sum((a[:, i].T*db[:, i])[0] for i in range(94)))/ambient['h00'])
    square = rational(charges.T*charges/h); linear = rational(-charges.T*b/ambient['h00'])
    potential = s.cancel((ell.T*principal*ell)[0]+(divP.T*ell)[0]+sum(v*hlog[i, j] for (i, j), v in principal.todok().items()))
    constant = s.cancel((b.T*b)[0]/h+ambient['potential'])
    return dict(ambient=ambient, point=point, a=a, charges=charges, principal=principal, divP=divP,
                second=second, mixed=mixed, div_mixed=div_mixed, identity=identity,
                div_identity=div_identity, square=square, linear=linear, potential=potential,
                constant=constant, ell=ell, hlog=hlog, rho=rho, M=M, retained=retained,
                coupled12=L, trace_derivative=trace_derivatives)


def weyl_image(data, word, g, Hessian, charge):
    """Collect independent quadratic and linear symmetric placements."""
    p, divP, second = data['principal'], data['divP'], data['second']
    g, H = g[6:, :], Hessian[6:, 6:]
    scalar = -sum(v*H[i, j] for (i, j), v in p.todok().items())-(divP.T*g)[0]-second/4
    scalar -= s.I*((data['identity'].T*g)[0]+data['div_identity']/2)
    scalar += data['constant']+data['potential']+second/4
    result = [(s.cancel(scalar), {word: 1})]
    for j in range(12):
        coefficient = s.cancel(-s.I*(data['mixed'][:, j].T*g)[0]-s.I*data['div_mixed'][j]/2+data['linear'][j])
        result.append((coefficient, charge(j, word)))
    for (i, j), v in data['square'].todok().items():
        result.extend((v*c, charge(i, w)) for w, c in charge(j, word).items())
    return terms(result)


def main():
    started = time.monotonic(); path = HERE/'source_scalar_weyl_symbol.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    paid = ('independent_source_scalar_form_hamiltonian', 'independent_source_quantum_gauss_section',
            'independent_source_gauss_section_measure', 'independent_source_scalar_temporal_form')
    for name in paid:
        record = json.loads((HERE/(name+'.json')).read_text()); count += bindings(record)
        assert record['root'] == ROOT_ID
    section = RawGaussSection(); raw = section.native
    assert raw.hashes == candidate['source_sha256']
    saved = candidate['actual_consumer']; q = tuple(map(s.sympify, saved['q']))
    clock = tuple(map(s.sympify, saved['time_column'])); x, A = decode(saved['x61']), decode(saved['A36'])
    background = json.loads((HERE.parent/'active-gauge/receipt.json').read_text())['actual_background']
    e = s.Matrix(background['coframe']).applyfunc(s.sympify)
    for i, v in zip((5, 9, 10, 13, 14, 15), q): e[i] = v
    e[:, 0] = s.Matrix(clock)
    point = s.Matrix(q).col_join(x).col_join(A.reshape(36, 1)); eq(point, decode(saved['base103']))
    data = original_slice_coefficients(section, e, x, A, point)
    eq(data['principal'], decode(saved['principal94'])); eq(data['divP'], decode(saved['div_principal94']))
    eq(data['mixed'], decode(saved['momentum_current94x12'])); eq(data['square'], decode(saved['current_square12']))
    zero(data['second']-s.sympify(saved['divdiv_principal']))
    zero(data['second']/4-s.sympify(saved['Weyl_correction']))
    zero(data['potential']-s.sympify(saved['half_density_potential']))
    assert data['second'] and data['potential']
    print('PASS original coupled12 affine system: all94 first equations and complete94x94 contracted second derivatives', flush=True)
    word = tuple(saved['input_CAR']); g, H = decode(saved['gradient100']), decode(saved['Hessian100'])
    ell = s.zeros(100, 1); ell[6:, :] = data['ell']
    hlog = s.zeros(100); hlog[6:, 6:] = data['hlog']
    ug = rational(g-ell); uH = rational(H-ell*g.T-g*ell.T+ell*ell.T-hlog)
    _, jets = section.extension_jet(point, {word: 1}, {word: ug}, {word: uH})
    gauss = section.Gauss_checks(point, jets)
    actual = terms((1, form_action(data['ambient'], w, f, dg[6:, :], h[6:, 6:])) for w, (f, dg, h) in jets.items())
    Q = raw.Qb+raw.Qs
    for matrix in Q: eq(matrix.H, matrix)
    @lru_cache(None)
    def charge(j, w): return current(Q[j], {w: 1})
    image = weyl_image(data, word, g, H, charge)
    same(actual, image); same(actual, decoded_state(saved['original_form_image']))
    same(image, decoded_state(saved['Weyl_quantized_image']))
    hidden = [w for w, (f, dg, h) in jets.items() if f == 0 and (dg.todok() or h.todok())]
    assert len(hidden) == saved['hidden_zero_value_jet_word_count'] > 0
    without_hidden = terms((1, form_action(data['ambient'], w, f, dg[6:, :], h[6:, 6:]))
                           for w, (f, dg, h) in jets.items() if f != 0)
    assert terms([(1, actual), (-1, without_hidden)])
    wrong = terms([(1, image), (-data['second']/4, {word: 1})])
    defect = terms([(1, image), (-1, wrong)]); assert defect
    same(defect, decoded_state(saved['omitted_Weyl_correction_defect']))
    print('PASS determinant-generated rho half-density, independent Gauss two-jet, raw97 form and full canonical94 Weyl image', flush=True)
    files = [Path(__file__), path, HERE/'source_scalar_weyl_symbol.py',
             HERE/'independent_source_scalar_form_hamiltonian.py', HERE/'independent_source_quantum_gauss_section.py',
             HERE/'independent_source_quantum_stabilizer.py']+[HERE/(name+'.json') for name in paid]
    result = {'verdict': 'CERTIFIED_ORIGINAL_SCALAR_CANONICAL_WEYL_SYMBOL_AND_FULL_GAUSS_FORM_READBACK',
              'root': ROOT_ID, 'source_sha256': raw.hashes,
              'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
              'source_binding_checks': count, 'candidate_constructor_imported': False,
              'independent_method': 'Original affine12 block solve joins normal D9 and orbit M3 equations; first and contracted second jets follow differentiated linear equations. Full70 principal contractions, determinant-trace density, independent implicit Gauss CAR extension and raw97 form action.',
              'coupled_original12_system': encode(data['coupled12']),
              'all94_first_differentiated_equations_checked': True,
              'all94_by94_contracted_second_derivatives_checked': True,
              'regular_chart_derivative_law': 'For the affine original L(z)X(z)=R(z), L Xi=Ri-Li X and L Xij=-Li Xj-Lj Xi; differentiating the full trace sums every retained canonical derivative. No temporal readout is treated as a canonical coordinate.',
              'original_rho_from_orbit_determinant': str(data['rho']),
              'half_density_gradient94': encode(data['ell']),
              'divdiv_principal': str(data['second']), 'Weyl_correction': str(data['second']/4),
              'half_density_potential': str(data['potential']),
              'all94_principal_and_mixed12_current_coefficients_equal': True,
              'actual_consumer': {'Gauss': gauss, 'full_original_form_image': state_encode(actual),
                  'independent_canonical_Weyl_image': state_encode(image),
                  'hidden_zero_value_jet_words': [list(w) for w in hidden],
                  'dropping_hidden_words_changes_image': True,
                  'omitted_Weyl_correction_defect': state_encode(defect)},
              'operator_or_ordering_replaced': False,
              'time_secondary_reduction_or_spectrum_generated': False,
              'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
              'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'independent_source_scalar_weyl_symbol.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent source scalar Weyl symbol', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
