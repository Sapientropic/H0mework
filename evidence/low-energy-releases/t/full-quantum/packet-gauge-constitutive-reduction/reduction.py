#!/usr/bin/env python3
"""Commute the native gauge auxiliary elimination with its true external leg.

The reduced current is differentiated directly from the eliminated density.
The comparison uses the original 289-field auxiliary rows and independently
generated primitive/B-current vertices, with eight free momentum variables.
"""
import hashlib
import itertools
import json
from pathlib import Path
import sys
import time

import sympy as s

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
BASE = FQ.parent
ROOT = HERE.parents[4]
sys.path.insert(0, str(FQ/'packet-gauge-kernel'))
import source
import ward


def read(path):
    return json.loads(path.read_text())


def matrix(record):
    return s.SparseMatrix(*record['shape'], {(i, j): s.sympify(value, locals={str(p): p for p in ward.p})
                                           for i, j, value in record['entries']})


def main():
    started = time.monotonic()
    paths = [BASE/'active-gauge/receipt.json', FQ/'packet-gauge-kinetic/receipt.json',
             FQ/'packet-gauge-constitutive-vertex/vertices.json']
    original, kinetic, vertices = map(read, paths)
    jet = source.load(BASE/'active-gauge/compute.py', 'reduction_source_jet')
    bijet = source.load(FQ/'packet-gauge-bilocal/vertices.py', 'reduction_source_bijet')
    coordinates, actions, _, data, metadata = jet.build(ROOT)
    assert coordinates.fields == original['fields']
    for path, digest in metadata['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest
    for path, digest in original['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest
    native = matrix(kinetic['native_pairing'])
    sigma, e0, a0, b0 = [data[key] for key in ['sigma', 'e0', 'a0', 'gauge_b0']]
    assert b0 == matrix(kinetic['background_B']).reshape(6, 12)
    q, J = coordinates.value, jet.Jet
    e = jet.matrix(4, 4, lambda i, j: e0[i, j]+q('coframe', i, j))
    exterior = jet.wedge(e)
    exterior0 = jet.wedge_matrix(e0)
    star = jet.multiply(jet.multiply(jet.inverse_second_jet(exterior, exterior0.inv()),
                                  jet.fixed(jet.J)), exterior)
    A = jet.matrix(4, 12, lambda mu, color: a0[mu, color]+q('gauge_A', mu, color))
    F = jet.matrix(6, 12, lambda pair, out:
        q('gauge_A', jet.PAIRS[pair][1], out, derivative=jet.PAIRS[pair][0])-
        q('gauge_A', jet.PAIRS[pair][0], out, derivative=jet.PAIRS[pair][1])+
        sum((A[jet.PAIRS[pair][0]][a]*A[jet.PAIRS[pair][1]][b]*v
             for (a, b, c), v in data['brackets'].items() if c == out), J()))
    B = jet.matrix(6, 12, lambda pair, color: b0[pair, color]+q('gauge_B', pair, color))
    constitutive_B = jet.scale(-1/sigma, jet.multiply(star, F))

    def pairing(left, right):
        return sum((native[a, b]*jet.W[i, j]*left[i][a]*right[j][b]
            for a, b, i, j in itertools.product(range(12), range(12), range(6), range(6))
            if native[a, b] and jet.W[i, j]), J())

    eliminated_density = s.Rational(1, 2)*pairing(constitutive_B, F)
    original_gauge = jet.fourier_hessian(coordinates, actions['gauge'])
    direct_reduced = jet.fourier_hessian(coordinates, eliminated_density)
    p = list(ward.p)
    r = list(s.symbols('r0:4', real=True))
    pin, pout = p, [p[i]+r[i] for i in range(4)]
    retained = [i for i, f in enumerate(coordinates.fields) if f['group'] in ['gauge_A', 'coframe']]
    auxiliary = [i for i, f in enumerate(coordinates.fields) if f['group'] == 'gauge_B']
    assert len(retained) == 64 and len(auxiliary) == 72

    def operator(table, point):
        result = s.MutableSparseMatrix(289, 289, {})
        for (i, j, powers), value in table.items():
            assert not value.imag
            result[i, j] += jet.F.to_sympy(value.real)*s.prod(t**n for t, n in zip(point, powers))
        return source.clean(result)

    H = ward.operator(original['Fourier_Jacobi_entries'], values=pin)
    Hbb = source.clean(H.extract(auxiliary, auxiliary))
    Hbb_inverse = Hbb.inv()
    assert source.clean(Hbb*Hbb_inverse) == s.eye(72)
    assert source.clean(Hbb_inverse*Hbb) == s.eye(72)

    def lift(point):
        table = ward.operator(original['Fourier_Jacobi_entries'], values=point)
        result = s.MutableSparseMatrix(289, 64, {(i, j): 1 for j, i in enumerate(retained)})
        bpart = source.clean(-Hbb_inverse*table.extract(auxiliary, retained))
        for (i, j), value in bpart.todok().items():
            result[auxiliary[i], j] = value
        assert not source.clean(table.extract(auxiliary, range(289))*result).todok()
        return s.SparseMatrix(result)

    Tin = lift(pin)
    Tminus = lift([-v for v in pin])
    original_reduced = source.clean(Tminus.T*operator(original_gauge, pin)*Tin)
    # The original operator already uses a reflected left slot, so the
    # algebraic Hessian contraction is T(-p)^T H(p) T(p).
    expected_reduced = source.clean(operator(direct_reduced, pin).extract(retained, retained))
    assert original_reduced == expected_reduced
    assert expected_reduced[:48, :48] == matrix(kinetic['constitutive_hessian'])
    print('PASS direct live-coframe reduced density and original all64 Hessian via 72 auxiliary rows', flush=True)

    def current_matrix(density, left, right):
        coefficients = bijet.density_hessian(jet, coordinates, density)
        result = s.MutableSparseMatrix(289, 289, {})
        for (i, j, a, b), value in coefficients.items():
            assert not value.imag
            result[i, j] += jet.F.to_sympy(value.real)*(left[a] if a >= 0 else 1)*(right[b] if b >= 0 else 1)
        return source.clean(result)

    left = [-v for v in pout]
    star0 = s.kronecker_product(matrix(kinetic['source_hodge']), s.eye(12))
    curvature_derivative = matrix(kinetic['curvature_derivative'])
    Bvertices = [matrix(record['Q']) for record in vertices['original_unit_auxiliary_readers']]
    Tout = lift([-v for v in pout])
    records, profiles = [], []
    for external_mu, external_color in itertools.product(range(4), range(12)):
        # The four derivative coefficients remain separate until evaluation,
        # so this is the actual weak current for an arbitrary external wave.
        ext = s.zeros(4, 12)
        ext[external_mu, external_color] = 1
        Da0 = jet.matrix(6, 12, lambda pair, out: sum((v*(
            A[jet.PAIRS[pair][0]][a]*ext[jet.PAIRS[pair][1], b]+
            ext[jet.PAIRS[pair][0], a]*A[jet.PAIRS[pair][1]][b])
            for (a, b, c), v in data['brackets'].items() if c == out), J()))
        derivatives = [jet.matrix(6, 12, lambda pair, color:
            (1 if jet.PAIRS[pair][0] == mu else 0)*ext[jet.PAIRS[pair][1], color]-
            (1 if jet.PAIRS[pair][1] == mu else 0)*ext[jet.PAIRS[pair][0], color])
            for mu in range(4)]
        primitive_current = pairing(B, Da0)
        primitive_vertex = current_matrix(primitive_current, left, pin)
        assert all(a == b == -1 for _, _, a, b in bijet.density_hessian(jet, coordinates, primitive_current))
        reduced_parts = [current_matrix(pairing(constitutive_B, d), left, pin)
                         for d in [Da0, *derivatives]]
        reduced_vertex = source.clean(reduced_parts[0]+sum((r[mu]*reduced_parts[1+mu]
            for mu in range(4)), s.zeros(289))).extract(retained, retained)
        b_ext = source.clean(-star0*curvature_derivative.subs(dict(zip(p, r)))*s.Matrix(list(ext))/sigma)
        additional = source.clean(sum((b_ext[i]*Bvertices[i] for i in range(72) if b_ext[i]), s.zeros(289)))
        joint = source.clean(primitive_vertex+additional)
        reduced_insertion = source.clean(Tout.T*joint*Tin)
        difference = source.clean(reduced_insertion-reduced_vertex)
        assert not difference.todok(), ((external_mu, external_color), list(difference.todok().items())[:2])
        omitted = source.clean(Tout.T*primitive_vertex*Tin-reduced_vertex)
        gauge_only = source.clean(omitted[:48, :48])
        coframe_entries = [(i, j, str(v)) for (i, j), v in omitted.todok().items() if i >= 48 or j >= 48]
        record = {'reader': [external_mu, external_color],
                  'reduced_external_vertex': source.encode(reduced_vertex),
                  'all_eight_variable_coefficients_equal': True,
                  'omitted_B_background_vertex_entries': len(omitted.todok()),
                  'omitted_B_gauge_entries': len(gauge_only.todok()),
                  'omitted_B_coframe_entries': len(coframe_entries)}
        if external_mu == external_color == 1:
            assert omitted.todok() and gauge_only.todok() and coframe_entries
            record['gauge_omission_witness'] = [*next(iter(gauge_only.todok())), str(next(iter(gauge_only.todok().values())))]
            record['coframe_omission_witness'] = coframe_entries[0]
            for row in vertices['profiles']:
                point = list(map(s.sympify, row['external_derivative_symbol']))
                assert source.clean(b_ext.subs(dict(zip(r, point)))) == matrix(row['B1'])
                assert source.clean(additional.subs(dict(zip(r, point)))) == matrix(row['additional_B_vertex'])
                profiles.append({'wave_sign': row['wave_sign'], 'native_constitutive_vertex_recovered': True})
        records.append(record)
        if external_color == 11:
            print('PASS all12 colors for external spacetime component', external_mu, flush=True)
    print('PASS all48 eight-variable external insertions commute with source auxiliary elimination', flush=True)

    result = {
        'scope': 'STRIKE_ORIGINAL_CONSTITUTIVE_GAUGE_ELIMINATION_COMMUTES_WITH_LIVE_COFRAME_EXTERNAL_INSERTION',
        'source_sha256': metadata['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'retained_original_fields': retained, 'auxiliary_original_fields': auxiliary,
        'free_momenta': {'incoming': list(map(str, pin)), 'external': list(map(str, r)), 'outgoing': list(map(str, pout))},
        'Hbb_two_sided_inverse': True, 'all64_live_coframe_reduced_density_Hessian': True,
        'fixed_coframe48_source_kinetic_recovered': True,
        'reduced_gauge_Hessian': source.encode(expected_reduced),
        'readers': records, 'reader_count': len(records),
        'all_momentum_coefficients_equal': True,
        'identity': 'D_a Hess(S_eliminated)(pout,pin) = T(-pout)^T [Q_A(-pout,pin)+sum_i b_ext_i Q_Bi] T(pin)',
        'source_producer': 'S_eliminated=-W(star_e F,F)/(2sigma); its current -W(star_e F,D_A a)/sigma is differentiated independently',
        'actual_profile_consumers': profiles,
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'reduction.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS all64 source consumer and constitutive controls', result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
