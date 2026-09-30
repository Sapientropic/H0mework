#!/usr/bin/env python3
"""All nine native source/reader channels and true radial/external quadratic jets."""
import importlib.util
import json
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('propagation_axis_origin', HERE/'origin.py')
alg = importlib.util.module_from_spec(spec)
spec.loader.exec_module(alg)
source, h, K, FQ, BASE = alg.source, alg.h, alg.K, alg.FQ, alg.BASE
r = s.Symbol('r', real=True)
delta = source.d
variables = [r, *delta]
indices = sorted([a for a in __import__('itertools').product(range(3), repeat=4) if sum(a) <= 2], key=lambda a: (sum(a), a))
zero = (0,)*4
# Reuse the exact derivative product engine with the current four variables.
alg.variables, alg.indices, alg.zero = variables, indices, zero
jet, multiply, solve = alg.jet, alg.multiply, alg.solve
empty, eye, finite = alg.empty, alg.eye, alg.finite


def main():
    began = time.monotonic()
    native = source.main(return_native=True)
    actual = native['actual']
    quotient = source.read(BASE/'active-gauge/quotient.json')
    catalog = source.read(BASE/'active-gauge/propagation.json')
    global_data = source.read(FQ/'packet-gauge-global-transfer/source.json')
    N, z = native['N'], native['z']
    pin = [z, s.Integer(0), s.Integer(0), -s.I*r]
    pout = [z, s.I*delta[0], s.I*delta[1], -s.I*(r-delta[2])]
    pe = [s.Integer(0), *[s.I*v for v in delta]]
    Hraw = source.native.ward.operator(actual['Fourier_Jacobi_entries'], values=pout)
    H = jet(Hraw)
    Kminus = source.clean(native['Kformal'].subs(dict(zip(source.native.ward.p, [-v for v in pout]))))
    Kplus_in = source.clean(native['Kformal'].subs(dict(zip(source.native.ward.p, pin))))
    incoming = alg.global_origin_columns(global_data, z)
    to_axis = {source.k[0]: 0, source.k[1]: 0, source.k[2]: r}
    X = jet(incoming['X'].subs(to_axis, simultaneous=True))
    I = jet(incoming['I'].subs(to_axis, simultaneous=True))
    Xout = jet(incoming['X'].subs({source.k[0]: -delta[0], source.k[1]: -delta[1], source.k[2]: r-delta[2]}, simultaneous=True))
    readers = {tuple(v['reader']): v for v in native['vertices']['readers']}
    basis = [(mu, color, terms) for mu in range(1, 4)
             for color, terms in [('S01', [(1, 1)]), ('A01', [(0, 1)]), ('Cartan01', [(6, 1), (7, -1)])]]
    rhs_columns, torque_columns, Qjets, native_profiles = [], [], [], []
    raw_Q = []
    weak = [-s.conjugate(z)-z, 0, 0, 0]
    for mu, name, terms in basis:
        ext = s.zeros(48, 1)
        for a, coefficient in terms: ext[12*mu+a] = coefficient
        Fb = source.clean(native['curvature'].subs(dict(zip(source.native.ward.p, pe)))*ext)
        Bb = source.clean(-native['star']*Fb/native['sigma'])
        direction = s.zeros(289, 1)
        direction[9:57, :] = ext
        extra = s.zeros(289)
        for row, Q in zip(native['auxiliary']['original_unit_auxiliary_readers'], native['QB']):
            pair, a = row['auxiliary']
            coefficient = Bb[12*pair+a]
            direction[row['original_field']] = coefficient
            extra += coefficient*Q
        V = extra+sum((coefficient*source.evaluate(readers[mu, a]['Q0_bijet'], [-v for v in pout], pin)
                       for a, coefficient in terms), s.zeros(289))
        V = source.clean(V)
        E = source.clean(source.native.ward.operator(actual['Fourier_Jacobi_entries'], values=pe)*direction)
        K1 = source.clean((s.SparseMatrix.hstack(*(A*direction for A in native['gauge_actions']))*native['color']).row_join(
            s.SparseMatrix.hstack(*(A*direction for A in native['lorentz_actions']))))
        C1 = source.clean((s.SparseMatrix.hstack(*(A.T*E for A in native['gauge_actions']))*native['color']).row_join(
            s.SparseMatrix.hstack(*(A.T*E for A in native['lorentz_actions']))))
        assert source.clean(V*Kplus_in+Hraw*K1+C1) == s.zeros(289, 9)
        inserted = multiply(jet(V), X)
        ca = multiply({a: v.transpose() for a, v in jet(K1).items()}, I)
        cb = multiply({a: v.transpose() for a, v in jet(C1).items()}, X)
        rhs_columns.append(inserted)
        torque_columns.append({a: -ca[a]-cb[a] for a in indices})
        bb = source.clean(-native['star']*native['curvature'].subs(dict(zip(source.native.ward.p, weak)))*ext/native['sigma'])
        Q = sum((coefficient*source.evaluate(readers[mu, a]['Q0_bijet'], list(map(s.conjugate, pout)), pout)
                 for a, coefficient in terms), s.zeros(289))
        Q = source.clean(Q+sum((bb[j]*v for j, v in enumerate(native['QB'])), s.zeros(289)))
        assert Q == Q.H
        Qjets.append(jet(Q)); raw_Q.append(Q)
        native_profiles.append({'direction': [mu, name], 'V': source.encode(V),
            'K1': source.encode(K1), 'C1': source.encode(C1), 'Q': source.encode(Q),
            'B1': source.encode(Bb), 'E1': source.encode(E)})
    external = {a: rhs_columns[0][a].hstack(*(row[a] for row in rhs_columns[1:])) for a in indices}
    torque = {a: torque_columns[0][a].hstack(*(row[a] for row in torque_columns[1:])) for a in indices}
    removed = quotient['fixed_section_removed_original_fields']
    minor = {a: v.extract(removed, range(9)).transpose() for a, v in jet(Kminus).items()}
    charge = solve(minor, minor[zero].inv(), torque)
    I1 = {a: h.matrix(289, 9, [(removed[i], j, v) for (i, j), v in value.to_dok().items()]) for a, value in charge.items()}
    rhs = {a: I1[a]-external[a] for a in indices}
    current, fields, steps = H, list(range(289)), []
    print('PASS all nine actual source directions, native weak readers and15 Noether source jets', flush=True)
    for step in actual['algebraic_Schur_steps']:
        eliminated = step['eliminated_fields']
        retained = [i for i in fields if i not in eliminated]
        erows, krows = [[fields.index(i) for i in ids] for ids in [eliminated, retained]]
        inv = h.matrix(len(eliminated), len(eliminated), [(eliminated.index(i), eliminated.index(j), h.number(v))
                        for i, j, v in step['algebraic_block_inverse']])
        assert current[zero].extract(erows, erows).matmul(inv) == eye(len(eliminated))
        assert all(current[a].extract(erows, erows).is_zero_matrix for a in indices if a != zero)
        particular = {a: inv.matmul(rhs[a].extract(erows, range(9))) for a in indices}
        back = {a: -inv.matmul(current[a].extract(erows, krows)) for a in indices}
        left = {a: current[a].extract(krows, erows) for a in indices}
        update, correction = multiply(left, back), multiply(left, particular)
        rhs = {a: rhs[a].extract(krows, range(9))-correction[a] for a in indices}
        current = {a: current[a].extract(krows, krows)+update[a] for a in indices}
        steps.append((eliminated, retained, particular, back)); fields = retained
    keep = [i for i in range(121) if i not in removed]
    scale = dict(zip(quotient['retained_original_fields'], map(s.sympify, catalog['constant_diagonal_field_scaling'])))
    D = s.diag(*[1 if i < 9 else scale[i] for i in keep])
    operator = {a: value.extract(keep, keep) for a, value in current.items()}
    inverse, blocks = source.native.rational_inverse(source.clean(D*operator[zero].to_Matrix()*D/N))
    true_inverse = finite(source.clean(D*inverse*D/N))
    assert operator[zero].matmul(true_inverse) == true_inverse.matmul(operator[zero]) == eye(112)
    section = solve(operator, true_inverse, {a: value.extract(keep, range(9)) for a, value in rhs.items()})
    vectors = {a: h.matrix(289, 9, [(keep[i], j, value) for (i, j), value in section[a].to_dok().items()]) for a in indices}
    for eliminated, retained, particular, back in reversed(steps):
        correction = multiply(back, {a: value.extract(retained, range(9)) for a, value in vectors.items()})
        vectors = {a: vectors[a]+h.matrix(289, 9, [(eliminated[i], j, value) for (i, j), value in
                      (particular[a]+correction[a]).to_dok().items()]) for a in indices}
    residual = multiply(H, vectors)
    assert all((residual[a]+external[a]-I1[a]).is_zero_matrix for a in indices)
    assert all(v.extract(removed, range(9)).is_zero_matrix for v in vectors.values())
    left = {a: h.conjugate_matrix(value).transpose() for a, value in Xout.items()}
    by_reader = [multiply(multiply(left, Q), vectors) for Q in Qjets]
    tensors = {a: h.matrix(9, 9, [(b, j, value) for b, row in enumerate(by_reader)
                     for (i, j), value in row[a].to_dok().items()]) for a in indices}
    v = s.symbols('v1:4', real=True)
    weights = s.Matrix([v[i]*v[j] for i in range(3) for j in range(3)])
    contracted = {a: s.expand((weights.T*M.to_Matrix()*weights)[0]) for a, M in tensors.items()}
    origin = source.read(HERE/'origin.json')
    first = {tuple(a): s.sympify(value) for a, value in origin['source_and_frames'][0]['fixed_frame_scalar_jet']}
    for a in indices:
        full = (0, 0, a[0], *a[1:])
        assert s.expand(contracted[a].subs({v[0]: 1, v[1]: 0, v[2]: 0})-first.get(full, 0)) == 0
    report = {'scope': 'ALL_NINE_NATIVE_AXIS_SOURCE_READER_JETS_FOR_THE_ORIGINAL_PAIRED_FRAME',
              'physical_frequency': str(z), 'physical_variables': list(map(str, variables)),
              'source_basis': [[mu, name] for mu, name, terms in basis],
              'all15_original289_equations_for_each_of9_sources': True,
              'actual112_inverse_blocks': blocks, 'all_removed9_source_protocol_preserved': True,
              'scalar_tensor': [[list(a), source.encode(M.to_Matrix())] for a, M in tensors.items()],
              'rank_one_original_probe_contraction': [[list(a), str(value)] for a, value in contracted.items() if value],
              'zero_first_jets_on_all_rank_one_probes': all(value == 0 for a, value in contracted.items() if sum(a) == 1),
              'origin_selected_consumer': True, 'seconds': round(time.monotonic()-began, 3)}
    (HERE/'axis.json').write_text(json.dumps(report, separators=(',', ':'))+'\n')
    exact = {'scope': 'ACTUAL_NINE_PROFILE_AXIS_POLYNOMIALS_BEFORE_ANY_SOURCE_ROOT_OR_RADIAL_TRUNCATION',
        'physical_frequency': str(z), 'variables': list(map(str, variables)),
        'physical_p_in': list(map(str, pin)), 'physical_p_out': list(map(str, pout)),
        'original_Kminus': source.encode(Kminus), 'profiles': native_profiles,
        'all_original_Ward_polynomial_identities': True, 'source_sha256': actual['source_sha256']}
    (HERE/'axis-source.json').write_text(json.dumps(exact, separators=(',', ':'))+'\n')
    print('PASS actual81 reader/source tensors and complete radial/external two-jet', report['seconds'], flush=True)


if __name__ == '__main__': main()
