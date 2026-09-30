#!/usr/bin/env python3
"""Literal incoming/outgoing source insertion for the two spatial propagation legs."""
import hashlib
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
import propagation as native

k = s.symbols('k1:4', real=True)
d = s.symbols('d1:4', real=True)
clean, encode = native.clean, native.encode


def read(path):
    return json.loads(path.read_bytes())


def matrix(record):
    return native.matrix(record, {str(v): v for v in [*native.ward.p, *k, *d]})


def evaluate(entries, left, right):
    value = s.MutableSparseMatrix(289, 289, {})
    for i, j, a, b, text in entries:
        value[i, j] += s.sympify(text)*(left[a] if a >= 0 else 1)*(right[b] if b >= 0 else 1)
    return clean(value)


def main(return_native=False):
    start = time.monotonic()
    paths = [BASE/'active-gauge/receipt.json', FQ/'packet-gauge-kernel/source.json',
             FQ/'packet-gauge-kernel/ward.json', FQ/'packet-gauge-bilocal/vertices.json',
             FQ/'packet-gauge-constitutive-vertex/vertices.json', FQ/'packet-gauge-kinetic/receipt.json']
    actual, primitive, ward, vertices, auxiliary, kinetic = map(read, paths)
    for path, expected in actual['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == expected
    N = s.sympify(actual['source_lapse'])
    c = s.expand(N*s.sqrt(2))
    z = s.expand(6*c*(1-s.I))
    pin = [z, *[-s.I*v for v in k]]
    pout = [z, *[-s.I*(v-w) for v, w in zip(k, d)]]
    pe = [s.Integer(0), *[s.I*v for v in d]]
    H = lambda p: native.ward.operator(actual['Fourier_Jacobi_entries'], values=p)
    Kformal = matrix(ward['K0'])
    K = lambda p: clean(Kformal.subs(dict(zip(native.ward.p, p))))
    idx = {(f['group'], tuple(f['coordinate'])): i for i, f in enumerate(actual['fields'])}
    gen = list(map(matrix, primitive['fundamental']))
    gram = s.Matrix(12, 12, lambda i, j: s.re(-s.trace(gen[i]*gen[j])))
    gi = gram.inv()
    adjoint = [s.Matrix.hstack(*(gi*s.Matrix([s.re(-s.trace(t*(gen[a]*gen[b]-gen[b]*gen[a])))
                  for t in gen]) for b in range(12))) for a in range(12)]
    original = native.source.load(BASE/'active-gauge/compute.py', 'propagation_curvature_original_action')
    actions = []
    for g in range(12):
        M = s.MutableSparseMatrix(289, 289, {})
        for group, count in [('gauge_A', 4), ('gauge_B', 6)]:
            for mu in range(count):
                for (i, j), value in s.SparseMatrix(adjoint[g]).todok().items():
                    M[idx[group, (mu, i)], idx[group, (mu, j)]] = value
        internal = s.kronecker_product(s.eye(4), gen[g][:3, :3]+gen[g][5, 5]*s.eye(3))
        for group, action in [('primal_H', internal), ('dual_H', -internal.T)]:
            for (i, j), value in s.SparseMatrix(original.active.realify(action)).todok().items():
                M[idx[group, (i//12, (i % 12)//3, i % 3)], idx[group, (j//12, (j % 12)//3, j % 3)]] = value
        actions.append(s.SparseMatrix(M))
    lorentz = []
    for a, b in original.PAIRS:
        M = s.MutableSparseMatrix(289, 289, {})
        tangent = s.zeros(4)
        tangent[a, b], tangent[b, a] = original.ETA[a, a], -original.ETA[b, b]
        for mu in range(4):
            for (i, j), value in s.SparseMatrix(tangent).todok().items():
                M[idx['coframe', (i, mu)], idx['coframe', (j, mu)]] = value
        spin = s.kronecker_product(original.GAMMA[a]*original.GAMMA[b]/2, s.eye(3))
        for group, action in [('primal_H', spin), ('dual_H', -spin.T)]:
            for (i, j), value in s.SparseMatrix(original.active.realify(action)).todok().items():
                M[idx[group, (i//12, (i % 12)//3, i % 3)], idx[group, (j//12, (j % 12)//3, j % 3)]] = value
        lorentz.append(s.SparseMatrix(M))
    color = s.zeros(12, 3)
    color[1, 0] = color[0, 1] = color[6, 2] = s.Rational(1, 2)
    color[7, 2] = -s.Rational(1, 2)
    curvature = matrix(kinetic['curvature_derivative'])
    star = s.kronecker_product(matrix(kinetic['source_hodge']), s.eye(12))
    sigma = s.sympify(actual['source_coupling'])
    external48 = s.zeros(48, 1)
    external48[13] = 1
    F1 = clean(curvature.subs(dict(zip(native.ward.p, pe)))*external48)
    B1 = clean(-star*F1/sigma)
    assert clean(F1-sigma*star*B1) == s.zeros(72, 1)
    direction = s.MutableSparseMatrix(289, 1, {(idx['gauge_A', (1, 1)], 0): 1})
    extra = s.zeros(289)
    QB = []
    for row in auxiliary['original_unit_auxiliary_readers']:
        pair, g = row['auxiliary']
        value = B1[12*pair+g, 0]
        direction[row['original_field'], 0] = value
        item = matrix(row['Q'])
        extra += value*item
        QB.append(item)
    selected = next(row for row in vertices['readers'] if row['reader'] == [1, 1])
    V = clean(evaluate(selected['Q0_bijet'], [-v for v in pout], pin)+extra)
    E1 = clean(H(pe)*direction)
    assert all(E1[i, 0] == 0 for i, field in enumerate(actual['fields'])
               if field['group'] in ['scalar_J', 'gauge_B', 'Lorentz', 'gravity_B', 'multiplier'])
    Tg1 = clean(s.SparseMatrix.hstack(*(action*direction for action in actions)))
    Cg = clean(s.SparseMatrix.hstack(*(action.T*E1 for action in actions)))
    K1 = clean((Tg1*color).row_join(s.SparseMatrix.hstack(*(action*direction for action in lorentz))))
    C1 = clean((Cg*color).row_join(s.SparseMatrix.hstack(*(action.T*E1 for action in lorentz))))
    assert clean(V*K(pin)+H(pout)*K1+C1) == s.zeros(289, 9)
    assert clean(K([-v for v in pout]).T*V+K1.T*H(pin)+C1.T) == s.zeros(9, 289)
    assert clean(V*native.ward.operator(actual['source_primitive_gauge_tangent'], cols=12, values=pin)
                 +H(pout)*Tg1+Cg) == s.zeros(289, 12)
    # The observable reads the output momentum. Its auxiliary reader uses
    # the real weak variation (-conj(z)-z,0), not the insertion momentum.
    weak = [-s.conjugate(z)-z, s.Integer(0), s.Integer(0), s.Integer(0)]
    b_reader = clean(-star*curvature.subs(dict(zip(native.ward.p, weak)))*external48/sigma)
    Q = evaluate(selected['Q0_bijet'], list(map(s.conjugate, pout)), pout)
    Q = clean(Q+sum((b_reader[j, 0]*value for j, value in enumerate(QB)), s.zeros(289)))
    assert Q == Q.H
    if return_native:
        return {'actual': actual, 'vertices': vertices, 'auxiliary': auxiliary,
                'kinetic': kinetic, 'Kformal': Kformal, 'gauge_actions': actions,
                'lorentz_actions': lorentz, 'color': color, 'curvature': curvature,
                'star': star, 'sigma': sigma, 'QB': QB, 'index': idx,
                'N': N, 'c': c, 'z': z}
    result = {'scope': 'ACTUAL_FIXED_INCOMING_VARIABLE_SOURCE_FOR_BOTH_SPATIAL_PROPAGATION_LEGS',
              'source_sha256': actual['source_sha256'],
              'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
              'physical_frequency': str(z), 'physical_incoming': list(map(str, k)),
              'physical_outgoing': [str(v-w) for v, w in zip(k, d)],
              'physical_p_in': list(map(str, pin)), 'physical_p_out': list(map(str, pout)),
              'physical_p_external': list(map(str, pe)), 'weak_reader': list(map(str, weak)),
              'source_polynomial': {name: encode(clean(value)) for name, value in
                  [('V', V), ('K1', K1), ('C1', C1), ('E1', E1), ('B1', B1),
                   ('complete_direction', direction), ('Q', Q), ('b_reader', b_reader)]},
              'all_six_variable_Ward_identities': True, 'all12_original_gauge_directions': True,
              'actual_native_reader_Hermitian': True,
              'seconds': round(time.monotonic()-start, 3)}
    (HERE/'source.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS six physical variables, native constitutive insertion, both Ward legs and actual output reader',
          result['seconds'], flush=True)


if __name__ == '__main__':
    main()
