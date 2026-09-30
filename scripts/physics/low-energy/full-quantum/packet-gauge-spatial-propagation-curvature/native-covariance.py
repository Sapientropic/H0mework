#!/usr/bin/env python3
"""Original full native bi-jet covariance and the actual rank-one world probe."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
FQ, BASE, ROOT = HERE.parent, HERE.parent.parent, HERE.parents[4]
spec = importlib.util.spec_from_file_location('native_bijet_covariance_source', HERE/'source.py')
source = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = source
spec.loader.exec_module(source)
clean, encode = source.clean, source.encode
left = s.symbols('ell0:4', real=True)
right = s.symbols('r0:4', real=True)


def build():
    native = source.main(return_native=True)
    profiles = [(mu, label, terms) for mu in range(1, 4) for label, terms in
                [('S01', [(1, 1)]), ('A01', [(0, 1)]), ('Cartan01', [(6, 1), (7, -1)])]]
    index = native['index']
    E = s.MutableSparseMatrix(289, 9, {})
    pivots = []
    for column, (mu, label, terms) in enumerate(profiles):
        pivots.append(index['gauge_A', (mu, terms[0][0])])
        for color, weight in terms: E[index['gauge_A', (mu, color)], column] = weight
    bare = {tuple(row['reader']): row['Q0_bijet'] for row in native['vertices']['readers']}
    external = [-a-b for a, b in zip(left, right)]
    D = native['curvature'].subs(dict(zip(source.native.ward.p, external)))
    allQ, allB, allBare = [], [], []
    for column, (mu, label, terms) in enumerate(profiles):
        bareQ = clean(sum((weight*source.evaluate(bare[mu, color], left, right) for color, weight in terms), s.zeros(289)))
        b72 = clean(-native['star']*D*E[9:57, column]/native['sigma'])
        B = s.MutableSparseMatrix(289, 1, {})
        Q = bareQ.copy()
        for row, value, QB in zip(native['auxiliary']['original_unit_auxiliary_readers'], b72, native['QB']):
            if value:
                B[row['original_field'], 0] = value
                Q += value*QB
        allQ.append(clean(Q)); allB.append(clean(B)); allBare.append(bareQ)
    return {'native': native, 'profiles': profiles, 'basis': s.SparseMatrix(E), 'pivots': pivots,
            'Q': allQ, 'B': allB, 'bare': allBare, 'left': left, 'right': right}


def main():
    started = time.monotonic()
    data = build()
    native, profiles, E = data['native'], data['profiles'], data['basis']
    allQ, allB = data['Q'], data['B']
    generator_path = BASE/'active-gauge/rotation/generators.json'
    finite_path = BASE/'active-gauge/rotation/finite.json'
    circles_path = FQ/'packet-field/circle-data.json'
    generators, finite, circles = map(source.read, [generator_path, finite_path, circles_path])
    whole_swap = dict(zip(left, right)) | dict(zip(right, left))
    for column, Q in enumerate(allQ):
        assert not clean(Q-Q.xreplace(whole_swap).T).todok(), ('source Hessian slot exchange', column)
        assert not clean(s.conjugate(Q)-Q).todok(), ('actual real coefficient density', column)
    checks = []
    for axis, generator in enumerate(generators['generators']):
        J = s.SparseMatrix(289, 289, {(i, j): s.sympify(value) for i, j, value in generator['field_generator']})
        Rgen = s.Matrix(generator['spatial_matrix']).applyfunc(s.sympify)
        assert Rgen.T+Rgen == s.zeros(4)
        spatial = Rgen[1:4, 1:4]
        profile_action = clean(J*E).extract(data['pivots'], range(9))
        assert not clean(J*E-E*profile_action).todok()
        expected = -s.kronecker_product(spatial, s.eye(3))-s.kronecker_product(s.eye(3), spatial)
        assert profile_action == expected
        momentum_rates = list(Rgen.T*s.Matrix(left))+list(Rgen.T*s.Matrix(right))
        def derivative(M):
            return clean(sum((M.diff(variable)*rate for variable, rate in zip([*left, *right], momentum_rates)), s.zeros(*M.shape)))
        for column, (Q, B) in enumerate(zip(allQ, allB)):
            Qprofile = sum((profile_action[row, column]*allQ[row] for row in range(9) if profile_action[row, column]), s.zeros(289))
            Bprofile = sum((profile_action[row, column]*allB[row] for row in range(9) if profile_action[row, column]), s.zeros(289, 1))
            defect = clean(J.T*Q+Q*J+derivative(Q)+Qprofile)
            bdefect = clean(derivative(B)+Bprofile-J*B)
            assert not defect.todok(), ('full native bi-jet', axis, column, list(defect.todok().items())[:1])
            assert not bdefect.todok(), ('true constitutive graph', axis, column, list(bdefect.todok().items())[:1])
        checks.append({'axis': axis, 'all_nine_whole289_native_bijet_identities': True,
                       'all_eight_independent_left_right_momentum_variables': True,
                       'actual_constitutive_graph_intertwining': True,
                       'actual_profile_generator': encode(profile_action)})
        print('PASS original full native bi-jet and joint insertion rotation axis', axis, flush=True)

    # Literal source circle coefficients pay the exact finite action and its
    # normalization. This is independent of specializing the momentum slots.
    circle_records = []
    spatial_coefficients = []
    for axis, (generator, field_circle, rotation) in enumerate(zip(generators['generators'], circles['circles'], finite['certificates'])):
        J = s.SparseMatrix(289, 289, {(i, j): s.sympify(value) for i, j, value in generator['field_generator']})
        Rgen = s.Matrix(generator['spatial_matrix']).applyfunc(s.sympify)
        C = [source.matrix(record) for record in field_circle['coefficients']]
        P = [s.MutableSparseMatrix(4, 4, {}) for _ in range(5)]
        for i, j, coefficients in rotation['spatial_numerator']:
            for n, value in enumerate(coefficients): P[n][i, j] = s.sympify(value)
        spatial_coefficients.append([s.SparseMatrix(value[1:4, 1:4]) for value in P])
        assert C[0] == s.eye(289) and P[0] == s.eye(4)
        for n in range(10):
            above = C[n+1] if n+1 < 9 else s.zeros(289)
            below = C[n-1] if n else s.zeros(289)
            current = C[n] if n < 9 else s.zeros(289)
            assert not clean((n+1)*above+(n-9)*below-4*J*current).todok()
        for n in range(6):
            above = P[n+1] if n+1 < 5 else s.zeros(4)
            below = P[n-1] if n else s.zeros(4)
            current = P[n] if n < 5 else s.zeros(4)
            assert not clean((n+1)*above+(n-5)*below-4*Rgen*current).todok()
        for n in range(9):
            tensor = sum((s.kronecker_product(P[i][1:4, 1:4], P[n-i][1:4, 1:4])
                          for i in range(5) if 0 <= n-i < 5), s.zeros(9))
            assert not clean((-1)**n*C[n]*E-E*tensor).todok()
        circle_records.append({'axis': axis, 'whole_field_and_spatial_circle_ODE': True,
                               'all_inverse_profile_coefficients': True,
                               'literal_finite_profile_identity': 'L_axis(-t) E9 = E9 (R_axis(t) tensor R_axis(t))'})
    c = native['c']
    assert s.expand(c-6*s.sqrt(15)/25) == 0 and native['sigma'] == s.Rational(1, 2)
    colors = s.zeros(12, 3); colors[1, 0] = colors[0, 1] = colors[6, 2] = 1; colors[7, 2] = -1
    gram = source.matrix(native['kinetic']['native_pairing'])
    assert clean(colors.T*gram*colors) == 2*s.eye(3)
    assert colors == 2*native['color']

    # A non-axis source point consumes the actual word order, the unhalved
    # Cartan basis and the complete whole-field inverse action.
    ty, tz = s.Rational(1, 5), s.Rational(1, 3)
    def circle_value(axis, t):
        field = sum((t**n*source.matrix(record) for n, record in enumerate(circles['circles'][axis]['coefficients'])), s.zeros(289))/(1+t*t)**4
        spatial = sum((t**n*C for n, C in enumerate(spatial_coefficients[axis])), s.zeros(3))/(1+t*t)**2
        return clean(field), clean(spatial)
    Lyinv, Ryinv = circle_value(1, -ty)
    Lzinv, Rzinv = circle_value(2, -tz)
    Ry, Rz = Ryinv.T, Rzinv.T
    direction = E[:, 0]
    actual = clean(Lyinv*Lzinv*direction)
    R = clean(Ry*Rz)
    v = R[:, 0]
    weights = s.kronecker_product(v, v)
    assert not clean(actual-E*weights).todok()
    assert s.expand((v.T*v)[0]-1) == 0
    reversed_v = (Rz*Ry)[:, 0]
    reversed_difference = clean(actual-E*s.kronecker_product(reversed_v, reversed_v))
    assert reversed_difference.todok()
    halfE = E.copy()
    for j in [2, 5, 8]: halfE[:, j] = halfE[:, j]/2
    half_difference = clean(actual-halfE*weights)
    assert half_difference.todok()
    wave = [native['z'], s.I/3, 2*s.I/5, 4*s.I/7]
    native_sub = dict(zip(left, list(map(s.conjugate, wave)))) | dict(zip(right, wave))
    opposite_sub = dict(zip(left, [-v for v in wave])) | dict(zip(right, wave))
    native_vs_opposite = []
    omitted_bg = []
    for j, Q in enumerate(allQ):
        native_Q = clean(Q.subs(native_sub, simultaneous=True))
        assert native_Q == native_Q.H
        native_vs_opposite.append(len(clean(native_Q-Q.subs(opposite_sub, simultaneous=True)).todok()))
        omitted_bg.append(len(clean(native_Q-data['bare'][j].subs(native_sub, simultaneous=True)).todok()))
    assert all(native_vs_opposite) and all(omitted_bg)
    paths = [HERE/'source.py', generator_path, finite_path, circles_path,
             FQ/'packet-gauge-bilocal/vertices.json', FQ/'packet-gauge-constitutive-vertex/vertices.json',
             FQ/'packet-gauge-kinetic/receipt.json']
    result = {'scope': 'ORIGINAL_NATIVE_DOUBLE_JET_CURRENT_AND_JOINT_INSERTION_FINITE_ROTATION',
              'source_sha256': native['actual']['source_sha256'],
              'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
              'independent_formal_slots': list(map(str, [*left, *right])),
              'source_profiles': [[mu, label, terms] for mu, label, terms in profiles],
              'native_definition': 'Q_a(ell,r)=bare_bijet_a(ell,r)+sum[-star D_A(-ell-r)a/sigma]_j QB_j',
              'Lie_identity': 'J^T Q_a+Q_a J+d_(S^T ell,S^T r) Q_a+Q_(J a)=0, S is the actual infinitesimal spatial generator',
              'finite_identity': 'L(t)^T Q_(L(t)a)(R(t)^T ell,R(t)^T r) L(t)=Q_a(ell,r)',
              'constitutive_identity': 'B_(L(t)a)(R(t)^T ell,R(t)^T r)=L(t)B_a(ell,r)',
              'joint_insertion_specialization': 'ell=-pout,r=pin gives V_a(pout,pin) with genuine b_a(pout-pin); both time components may be independent.',
              'native_reader_specialization': 'ell=conj(pout),r=pout gives the actual Hermitian current, weak reader=-conj(pout)-pout.',
              'checks': checks, 'circle_checks': circle_records,
              'native_pairing_on_unhalved_color_triple': '2 I3; [S01,A01,D0-2-D1-2]=2 original sourceColor generators',
              'whole_word_probe': 'L=Lz(tz)Ly(ty); Rsp=Ry(ty)Rz(tz); L^-1(A1 S01)=E9 vec(v v^T), v=Rsp e1',
              'all_parameter_probe_identity_from_literal_coefficients': True,
              'actual_nonaxis_probe_v': list(map(str, v)), 'physical_external_transfer': 'd_axis=Rsp d_world',
              'controls': {'wrong_Rz_Ry_order_nonzero_fields': len(reversed_difference.todok()),
                           'halved_Cartan_wrong_fields': len(half_difference.todok()),
                           'native_vs_opposite_nonzero_matrix_entries_by_profile': native_vs_opposite,
                           'omitted_true_Bg_reader_nonzero_entries_by_profile': omitted_bg},
              'all_full289_scalar_and_independent_dual_slots_retained': True,
              'literal_native_bijet_entries_by_profile': [len(Q.todok()) for Q in allQ],
              'coefficient_reality_and_exact_slot_exchange': True,
              'no_Hessian_quadratic_in_place_of_density_bijet': True,
              'seconds': round(time.monotonic()-started, 3)}
    (HERE/'native-covariance.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS full native source covariance, original profile normalization and whole-word probe', result['seconds'], flush=True)


if __name__ == '__main__': main()
