#!/usr/bin/env python3
"""Original gauge-auxiliary density vertices and constitutive external legs."""
import hashlib
import gzip
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
import source as primitive
import ward


def read(path):
    return json.loads(path.read_text())


def matrix(record, symbols=None):
    return s.SparseMatrix(*record['shape'], {(i, j): s.sympify(value, locals=symbols or {})
                                          for i, j, value in record['entries']})


def main():
    started = time.monotonic()
    actual_path = BASE/'active-gauge/receipt.json'
    primitive_path = FQ/'packet-gauge-kernel/source.json'
    kinetic_path = FQ/'packet-gauge-kinetic/receipt.json'
    causal_path = FQ/'packet-gauge-causal/source.json'
    actual, data, kinetic, causal = map(read, [actual_path, primitive_path, kinetic_path, causal_path])
    for path, digest in actual['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest
    jet = primitive.load(BASE/'active-gauge/compute.py', 'constitutive_vertex_jet')
    coordinates = jet.Coordinates()
    for group, shape in [('scalar_J', (9,)), ('gauge_A', (4, 12)), ('coframe', (4, 4)),
                         ('primal_H', (2, 4, 3)), ('dual_H', (2, 4, 3)), ('Lorentz', (4, 6)),
                         ('gravity_B', (6, 6)), ('multiplier', (6, 6)), ('gauge_B', (6, 12))]:
        coordinates.group(group, shape)
    assert coordinates.fields == actual['fields']
    idx = {(row['group'], tuple(row['coordinate'])): i for i, row in enumerate(actual['fields'])}
    generators = list(map(matrix, data['fundamental']))
    trace_gram = s.Matrix(12, 12, lambda i, j: s.re(-s.trace(generators[i]*generators[j])))
    gram = matrix(kinetic['native_pairing'])
    assert gram[11, 11] == 1 and trace_gram[11, 11] == 2
    inverse_gram = trace_gram.inv()
    brackets = {}
    for a, b in itertools.product(range(12), repeat=2):
        commutator = generators[a]*generators[b]-generators[b]*generators[a]
        coefficients = inverse_gram*s.Matrix([s.re(-s.trace(g*commutator)) for g in generators])
        assert sum((coefficients[c]*generators[c] for c in range(12)), s.zeros(7)) == commutator
        for c, value in enumerate(coefficients):
            if value:
                brackets[a, b, c] = value
    sigma = s.sympify(actual['source_coupling'])
    coframe = s.Matrix(actual['actual_background']['coframe']).applyfunc(s.sympify)
    abar = s.Matrix(actual['actual_background']['gauge_connection']).applyfunc(s.sympify)
    b0 = matrix(kinetic['background_B']).reshape(6, 12)
    q = coordinates.value
    e = jet.matrix(4, 4, lambda i, j: coframe[i, j]+q('coframe', i, j))
    exterior = jet.wedge(e)
    exterior0 = s.Matrix(6, 6, lambda i, j:
        coframe[jet.PAIRS[i][0], jet.PAIRS[j][0]]*coframe[jet.PAIRS[i][1], jet.PAIRS[j][1]]-
        coframe[jet.PAIRS[i][0], jet.PAIRS[j][1]]*coframe[jet.PAIRS[i][1], jet.PAIRS[j][0]])
    hodge = jet.multiply(jet.multiply(jet.inverse_second_jet(exterior, exterior0.inv()), jet.fixed(jet.J)), exterior)
    hodge0 = s.Matrix(6, 6, lambda i, j: jet.F.to_sympy(hodge[i][j].terms.get((), jet.ZERO).real))
    assert hodge0 == matrix(kinetic['source_hodge'])
    connection = jet.matrix(4, 12, lambda mu, c: abar[mu, c]+q('gauge_A', mu, c))
    curvature = jet.matrix(6, 12, lambda pair, c:
        q('gauge_A', jet.PAIRS[pair][1], c, derivative=jet.PAIRS[pair][0])-
        q('gauge_A', jet.PAIRS[pair][0], c, derivative=jet.PAIRS[pair][1])+
        sum((connection[jet.PAIRS[pair][0]][a]*connection[jet.PAIRS[pair][1]][b]*value
             for (a, b, out), value in brackets.items() if out == c), jet.Jet()))
    B = jet.matrix(6, 12, lambda pair, c: b0[pair, c]+q('gauge_B', pair, c))
    residual = jet.add(curvature, jet.scale(-sigma, jet.multiply(hodge, B)))
    native_rows = {}
    for i, j, powers, text in actual['Fourier_Jacobi_entries']:
        if actual['fields'][i]['group'] == 'gauge_B':
            native_rows[i, j, tuple(powers)] = s.sympify(text)
    readers = []
    matrices = []
    coframe_fields = set(coordinates.groups['coframe'].values())
    mixed_count = 0
    for pair in range(6):
        for color in range(12):
            density = jet.Jet()
            for j, b in itertools.product(range(6), range(12)):
                if jet.W[pair, j] and gram[color, b]:
                    density += jet.W[pair, j]*gram[color, b]*residual[j][b]
            assert not density.terms.get((), jet.ZERO)
            row = idx['gauge_B', (pair, color)]
            first = {}
            for key, value in density.terms.items():
                if len(key) != 1:
                    continue
                field, derivative = coordinates.jets[key[0]]
                powers = [0]*4
                if derivative >= 0:
                    powers[derivative] = 1
                assert not value.imag
                first[field, tuple(powers)] = jet.F.to_sympy(value.real)
            expected = {(j, powers): value for (i, j, powers), value in native_rows.items() if i == row}
            assert first == expected
            hessian = jet.fourier_hessian(coordinates, density)
            assert all(not any(power) and not value.imag for (i, j, power), value in hessian.items())
            Q = s.SparseMatrix(289, 289, {(i, j): jet.F.to_sympy(value.real)
                                         for (i, j, _), value in hessian.items()})
            assert Q == Q.T
            mixed_count += sum(i in coframe_fields or j in coframe_fields for i, j in Q.todok())
            matrices.append(Q)
            readers.append({'auxiliary': [pair, color], 'original_field': row, 'Q': primitive.encode(Q)})
    print('PASS all72 original B-current rows and their full live-coframe quadratic vertices', flush=True)

    p = ward.p
    derivative = matrix(kinetic['curvature_derivative'], {str(v): v for v in p})
    star = s.kronecker_product(matrix(kinetic['source_hodge']), s.eye(12))
    direction = s.zeros(48, 1)
    direction[12+1] = 1
    incoming = list(map(s.sympify, causal['physical_momentum']))
    external = [k/2 for k in incoming]
    profiles = []
    for sign in [0, 1, -1]:
        point = [s.Integer(0), *[sign*s.I*k for k in external]]
        F1 = primitive.clean(derivative.subs(dict(zip(p, point)))*direction)
        B1 = primitive.clean(-star*F1/sigma)
        assert primitive.clean(F1-sigma*star*B1) == s.zeros(72, 1)
        full_direction = s.zeros(289, 1)
        full_direction[idx['gauge_A', (1, 1)]] = 1
        for pair, color in itertools.product(range(6), range(12)):
            full_direction[idx['gauge_B', (pair, color)]] = B1[12*pair+color]
        extra = primitive.clean(sum((B1[i]*Q for i, Q in enumerate(matrices) if B1[i]), s.zeros(289)))
        assert extra.todok()
        H = ward.operator(actual['Fourier_Jacobi_entries'], values=point)
        E1 = primitive.clean(H*full_direction)
        B_rows = [idx['gauge_B', (pair, color)] for pair, color in itertools.product(range(6), range(12))]
        assert E1.extract(B_rows, [0]) == s.zeros(72, 1)
        primitive_direction = s.zeros(289, 1)
        primitive_direction[idx['gauge_A', (1, 1)]] = 1
        unprepared = primitive.clean(H*primitive_direction)
        assert unprepared.extract(B_rows, [0]).todok()
        profiles.append({'wave_sign': sign, 'external_derivative_symbol': list(map(str, point)),
            'B1': primitive.encode(B1), 'complete_background_direction': primitive.encode(full_direction),
            'additional_B_vertex': primitive.encode(extra), 'reconstituted_E1': primitive.encode(E1),
            'all72_auxiliary_background_equations_preserved': True,
            'fixed_B_background_auxiliary_residual_nonzero': True,
            'additional_coframe_entries': sum(i in coframe_fields or j in coframe_fields for i, j in extra.todok())})
    plus, minus = profiles[1:]
    assert primitive.clean(matrix(minus['B1'])-matrix(plus['B1']).conjugate()) == s.zeros(72, 1)
    assert primitive.clean(matrix(minus['additional_B_vertex'])-matrix(plus['additional_B_vertex']).conjugate()) == s.zeros(289)
    # Test the actual prepared theta column, not just a nonzero vertex matrix.
    sys.path.insert(0, str(FQ/'packet-gauge-bilocal'))
    import hermitian as exact
    transfer_path = FQ/'packet-gauge-causal/transfer.json.gz'
    transfer = json.loads(gzip.decompress(transfer_path.read_bytes()))
    x = s.symbols('x', real=True)
    X = exact.matrix(289, 6, [(i, j, exact.scalar(s.sympify(value, locals={'x': x}).subs(x, 6*(1-s.I))))
                             for i, j, value in transfer['X0']['entries']])
    L = exact.stored_matrix(causal['L'])
    kept = [i for i in range(289) if i not in causal['removed']]
    factor = exact.polynomial(s.sympify(transfer['Fhat'], locals={'U': exact.U}))
    for profile in profiles:
        Vb = exact.stored_matrix(profile['additional_B_vertex'])
        force = L.transpose().matmul(Vb).matmul(X).extract(kept, range(6))
        assert not force.is_zero_matrix
        witnesses = []
        entries = force.to_dok()
        for row in sorted({i for i, _ in entries}):
            value = exact.POLY.from_dict({(j,): entries[row, j] for j in range(6) if (row, j) in entries})
            if value.gcd(factor).degree() == 0:
                witnesses.append({'original_axis_field': kept[row], 'numerator': exact.encode_poly(value)})
                break
        assert witnesses
        profile['actual_theta_retained_force_nonzero_rows'] = len({i for i, _ in entries})
        profile['actual_theta_force_witness'] = witnesses[0]
        profile['witness_frequency'] = 'lambda=6*(6*sqrt(15)/25)*(1-I); x=6*(1-I)'
    print('PASS actual theta source sees the additional constitutive vertices in retained source rows', flush=True)
    result = {'scope': 'STRIKE_ORIGINAL_LIVE_COFRAME_GAUGE_AUXILIARY_VERTICES_AND_CONSTITUTIVE_EXTERNAL_DIRECTION',
        'source_sha256': actual['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                         for path in [actual_path, primitive_path, kinetic_path, causal_path, transfer_path]},
        'original_unit_auxiliary_readers': readers,
        'auxiliary_reader_count': 72, 'all72_first_rows_match_original_H289': True,
        'quadratic_vertex_entries': sum(len(Q.todok()) for Q in matrices),
        'live_coframe_vertex_entries': mixed_count, 'profiles': profiles,
        'exact_background_curve': 'A_epsilon=Abar+epsilon a; B_epsilon=-star_e F(A_epsilon)/sigma=Bbar+epsilon B1, since a has only dx1 component and [a,a]=0.',
        'nonconstant_profiles': 'The two complex Fourier components combine with coefficient1/2 each into the actual real cosine family.',
        'vertex_composition': 'V_reconstituted(pout,pin)=Q_A1S01(-pout,pin)+additional_B_vertex(q); the latter has no fluctuation derivative slots.',
        'physical_scope': 'Original constitutive background path and full density vertices; shifted Noether response and kinetic matching are direct consumers.',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'vertices.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source constitutive profiles, complete auxiliary residuals, and real cosine pairing', result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
