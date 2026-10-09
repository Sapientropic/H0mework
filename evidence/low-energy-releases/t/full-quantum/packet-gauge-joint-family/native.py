#!/usr/bin/env python3
"""Literal finite A/B path, live Hodge Hessian and its off-shell Ward source."""
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
import propagation as original

clean, encode = original.clean, original.encode


def read(path):
    return json.loads(path.read_text())


def matrix(record):
    return original.matrix(record, {str(v): v for v in original.ward.p})


def main():
    started = time.monotonic()
    paths = [BASE/'active-gauge/receipt.json', FQ/'packet-gauge-kernel/source.json',
        FQ/'packet-gauge-kernel/ward.json', FQ/'packet-gauge-kinetic/receipt.json',
        FQ/'packet-gauge-constitutive-vertex/vertices.json',
        FQ/'packet-gauge-causal/source.json', FQ/'packet-gauge-joint-momentum-jet/source.json']
    actual, primitive, ward, kinetic, vertices, frame, jet_source = map(read, paths)
    for name, digest in actual['source_sha256'].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest
    native_path = BASE/'active-gauge/compute.py'
    jet = original.source.load(native_path, 'joint_family_native_jet')
    coord = jet.Coordinates()
    for group, shape in [('scalar_J', (9,)), ('gauge_A', (4, 12)), ('coframe', (4, 4)),
            ('primal_H', (2, 4, 3)), ('dual_H', (2, 4, 3)), ('Lorentz', (4, 6)),
            ('gravity_B', (6, 6)), ('multiplier', (6, 6)), ('gauge_B', (6, 12))]:
        coord.group(group, shape)
    assert coord.fields == actual['fields']
    index = {(record['group'], tuple(record['coordinate'])): i for i, record in enumerate(actual['fields'])}
    value = coord.value
    generators = list(map(matrix, primitive['fundamental']))
    tracegram = s.Matrix(12, 12, lambda i, j: s.re(-s.trace(generators[i]*generators[j])))
    gram = matrix(kinetic['native_pairing'])
    assert gram[11, 11] == 1 and tracegram[11, 11] == 2
    gi = tracegram.inv()
    brackets = {}
    adjoint = []
    for g in range(12):
        columns = []
        for h in range(12):
            bracket = generators[g]*generators[h]-generators[h]*generators[g]
            co = gi*s.Matrix([s.re(-s.trace(T*bracket)) for T in generators])
            assert sum((co[k]*generators[k] for k in range(12)), s.zeros(7)) == bracket
            columns.append(co)
            for k, v in enumerate(co):
                if v:
                    brackets[g, h, k] = v
        adjoint.append(s.Matrix.hstack(*columns))
    N, sigma = map(s.sympify, [actual['source_lapse'], actual['source_coupling']])
    coframe = s.Matrix(actual['actual_background']['coframe']).applyfunc(s.sympify)
    abar = matrix(primitive['gauge_background'])
    Bbar = matrix(primitive['gauge_auxiliary_background'])
    e = jet.matrix(4, 4, lambda i, j: coframe[i, j]+value('coframe', i, j))
    exterior = jet.wedge(e)
    exterior0 = s.Matrix(6, 6, lambda i, j:
        coframe[jet.PAIRS[i][0], jet.PAIRS[j][0]]*coframe[jet.PAIRS[i][1], jet.PAIRS[j][1]]-
        coframe[jet.PAIRS[i][0], jet.PAIRS[j][1]]*coframe[jet.PAIRS[i][1], jet.PAIRS[j][0]])
    hodge = jet.multiply(jet.multiply(jet.inverse_second_jet(exterior, exterior0.inv()), jet.fixed(jet.J)), exterior)
    A = jet.matrix(4, 12, lambda mu, color: abar[mu, color]+value('gauge_A', mu, color))
    B = jet.matrix(6, 12, lambda pair, color: Bbar[pair, color]+value('gauge_B', pair, color))
    F = jet.matrix(6, 12, lambda pair, color:
        value('gauge_A', jet.PAIRS[pair][1], color, derivative=jet.PAIRS[pair][0])-
        value('gauge_A', jet.PAIRS[pair][0], color, derivative=jet.PAIRS[pair][1])+
        sum((A[jet.PAIRS[pair][0]][a]*A[jet.PAIRS[pair][1]][b]*v
             for (a, b, out), v in brackets.items() if out == color), jet.Jet()))
    F1 = jet.matrix(6, 12, lambda pair, color:
        sum((v*A[jet.PAIRS[pair][1]][b] for (a, b, out), v in brackets.items()
             if jet.PAIRS[pair][0] == 1 and a == 1 and out == color), jet.Jet())+
        sum((v*A[jet.PAIRS[pair][0]][a] for (a, b, out), v in brackets.items()
             if jet.PAIRS[pair][1] == 1 and b == 1 and out == color), jet.Jet()))
    f1 = s.Matrix(6, 12, lambda i, j: jet.F.to_sympy(F1[i][j].terms.get((), jet.ZERO).real))
    star0 = matrix(kinetic['source_hodge'])
    background_B1 = clean(-star0*f1/sigma)
    assert clean(f1-sigma*star0*background_B1) == s.zeros(6, 12)
    profile = next(row for row in vertices['profiles'] if row['wave_sign'] == 0)
    assert background_B1.reshape(72, 1) == matrix(profile['B1'])
    direction = s.zeros(289, 1)
    direction[index['gauge_A', (1, 1)], 0] = 1
    for pair, color in itertools.product(range(6), range(12)):
        direction[index['gauge_B', (pair, color)], 0] = background_B1[pair, color]
    assert direction == matrix(profile['complete_background_direction'])

    def pairing(left, right):
        result = jet.Jet()
        for i, j, a, b in itertools.product(range(6), range(6), range(12), range(12)):
            if jet.W[i, j] and gram[a, b]:
                result += jet.W[i, j]*gram[a, b]*left[i][a]*right[j][b]
        return result

    bj = jet.fixed(background_B1)
    starB, starb = jet.multiply(hodge, B), jet.multiply(hodge, bj)
    assert pairing(B, starb).terms == pairing(bj, starB).terms
    extra1 = pairing(bj, F)-sigma*pairing(bj, starB)
    extra2 = pairing(bj, F1)-sigma*s.Rational(1, 2)*pairing(bj, starb)
    Hextra1 = jet.fourier_hessian(coord, extra1)
    Hextra2 = jet.fourier_hessian(coord, extra2)
    Hpure2 = jet.fourier_hessian(coord, (-sigma/2)*pairing(bj, starb))
    assert Hextra2 == Hpure2
    assert not jet.fourier_hessian(coord, pairing(bj, F1))
    # The finite gauge action itself, evaluated before its field Hessian,
    # has these exact epsilon coefficients. F(A+epsilon a) has no epsilon²
    # because this actual a has only one world one-form component.
    gauge0 = pairing(B, F)-sigma*s.Rational(1, 2)*pairing(B, starB)
    gauge1 = pairing(B, F1)+extra1
    for eps in [s.Rational(7, 9), -s.Rational(3, 5)]:
        Ae = jet.add(A, jet.scale(eps, jet.fixed(s.Matrix(4, 12, lambda i, j: int(i == 1 and j == 1)))))
        Fe = jet.matrix(6, 12, lambda pair, color:
            value('gauge_A', jet.PAIRS[pair][1], color, derivative=jet.PAIRS[pair][0])-
            value('gauge_A', jet.PAIRS[pair][0], color, derivative=jet.PAIRS[pair][1])+
            sum((Ae[jet.PAIRS[pair][0]][a]*Ae[jet.PAIRS[pair][1]][b]*v
                 for (a, b, out), v in brackets.items() if out == color), jet.Jet()))
        assert all(Fe[i][j].terms == (F[i][j]+eps*F1[i][j]).terms for i in range(6) for j in range(12))
        Be = jet.add(B, jet.scale(eps, bj))
        finite = pairing(Be, Fe)-sigma*s.Rational(1, 2)*pairing(Be, jet.multiply(hodge, Be))
        assert not (finite-gauge0-eps*gauge1-eps**2*extra2).terms
    assert all(not any(power) and not coeff.imag for (i, j, power), coeff in Hextra1.items())
    assert all(not any(power) and not coeff.imag for (i, j, power), coeff in Hextra2.items())
    extra_matrix1 = s.SparseMatrix(289, 289, {(i, j): jet.F.to_sympy(v.real)
        for (i, j, _), v in Hextra1.items()})
    extra_matrix2 = s.SparseMatrix(289, 289, {(i, j): jet.F.to_sympy(v.real)
        for (i, j, _), v in Hextra2.items()})
    summation = clean(sum((background_B1[row['auxiliary'][0], row['auxiliary'][1]]*matrix(row['Q'])
        for row in vertices['original_unit_auxiliary_readers']), s.zeros(289)))
    assert extra_matrix1 == summation == matrix(profile['additional_B_vertex'])
    assert all(actual['fields'][i]['group'] == actual['fields'][j]['group'] == 'coframe'
        for i, j in extra_matrix2.todok())
    p = original.ward.p
    H0 = original.ward.operator(actual['Fourier_Jacobi_entries'])
    H1 = clean(original.ward.operator(primitive['H1'])+extra_matrix1)
    H2 = clean(original.ward.operator(primitive['H2'])+extra_matrix2)

    def euler(density):
        E = s.zeros(289, 1)
        for key, number in density.terms.items():
            if len(key) == 1:
                field, derivative = coord.jets[key[0]]
                if derivative < 0:
                    assert not number.imag
                    E[field, 0] += jet.F.to_sympy(number.real)
        return clean(E)

    E1 = clean(matrix(primitive['E1'])+euler(extra1))
    E2 = euler(extra2)
    assert E1 == matrix(profile['reconstituted_E1'])
    assert clean(H0.subs(dict(zip(p, [0]*4)))*direction-E1) == s.zeros(289, 1)
    bg = [index['gauge_B', (i, j)] for i in range(6) for j in range(12)]
    assert E1.extract(bg, [0]) == E2.extract(bg, [0]) == s.zeros(72, 1)
    assert E2.todok()
    assert E1[:9, :] == E2[:9, :] == s.zeros(9, 1)

    actions = []
    for g in range(12):
        M = s.MutableSparseMatrix(289, 289, {})
        for group, count in [('gauge_A', 4), ('gauge_B', 6)]:
            for mu in range(count):
                for (i, j), v in s.SparseMatrix(adjoint[g]).todok().items():
                    M[index[group, (mu, i)], index[group, (mu, j)]] = v
        internal = s.kronecker_product(s.eye(4), generators[g][:3, :3]+generators[g][5, 5]*s.eye(3))
        for group, action in [('primal_H', internal), ('dual_H', -internal.T)]:
            for (i, j), v in s.SparseMatrix(jet.active.realify(action)).todok().items():
                M[index[group, (i//12, i%12//3, i%3)], index[group, (j//12, j%12//3, j%3)]] = v
        actions.append(s.SparseMatrix(M))
    lorentz = []
    for i, j in jet.PAIRS:
        M = s.MutableSparseMatrix(289, 289, {})
        L = s.zeros(4)
        L[i, j], L[j, i] = jet.ETA[i, i], -jet.ETA[j, j]
        for mu in range(4):
            for (a, b), v in s.SparseMatrix(L).todok().items():
                M[index['coframe', (a, mu)], index['coframe', (b, mu)]] = v
        internal = s.kronecker_product(jet.GAMMA[i]*jet.GAMMA[j]/2, s.eye(3))
        for group, action in [('primal_H', internal), ('dual_H', -internal.T)]:
            for (a, b), v in s.SparseMatrix(jet.active.realify(action)).todok().items():
                M[index[group, (a//12, a%12//3, a%3)], index[group, (b//12, b%12//3, b%3)]] = v
        lorentz.append(s.SparseMatrix(M))
    color = s.zeros(12, 3)
    color[1, 0] = color[0, 1] = s.Rational(1, 2)
    color[6, 2], color[7, 2] = s.Rational(1, 2), -s.Rational(1, 2)
    K0 = matrix(ward['K0'])
    Tg = original.ward.operator(actual['source_primitive_gauge_tangent'], cols=12)
    Tg1 = clean(s.SparseMatrix.hstack(*(M*direction for M in actions)))
    K1 = clean((Tg1*color).row_join(s.SparseMatrix.hstack(*(M*direction for M in lorentz))))
    contacts = []
    for E in [E1, E2]:
        for group in ['scalar_J', 'Lorentz', 'gravity_B', 'multiplier', 'gauge_B']:
            assert all(E[i, 0] == 0 for i, record in enumerate(actual['fields']) if record['group'] == group)
        Cg = clean(s.SparseMatrix.hstack(*(M.T*E for M in actions)))
        contacts.append(clean((Cg*color).row_join(s.SparseMatrix.hstack(*(M.T*E for M in lorentz)))))
    C1, C2 = contacts
    assert clean(H1*K0+H0*K1+C1) == s.zeros(289, 9)
    assert clean(H2*K0+H1*K1+C2) == s.zeros(289, 9)
    assert clean(H2*K1) == s.zeros(289, 9)
    for degree, E in enumerate([E1, E2], 1):
        Cg = clean(s.SparseMatrix.hstack(*(M.T*E for M in actions)))
        residual = H1*Tg+H0*Tg1 if degree == 1 else H2*Tg+H1*Tg1
        assert clean(residual+Cg) == s.zeros(289, 12)
    assert clean(H2*Tg1) == s.zeros(289, 12)
    for Hj in [H0, H1, H2]:
        assert clean(Hj.subs({v: -v for v in p}).T-Hj) == s.zeros(289)

    # The prior joint-momentum family labels external s. Its value s=0
    # must equal this background-amplitude first derivative.
    ss = s.Symbol('s', real=True)
    fixed_p = [s.sympify(t) for t in jet_source['physical_p_in']]
    for name, M in [('V', H1.subs(dict(zip(p, fixed_p)))), ('K1', K1), ('C1', C1), ('E1', E1)]:
        prior = original.matrix(jet_source['source_polynomial'][name], {'s': ss})
        assert clean(M-prior.subs(ss, 0)) == s.zeros(*M.shape), name
    print('PASS literal all-parameter gauge action, live-Hodge H2 and E2, full polynomial Ward, joint s0', flush=True)
    result = {'scope': 'STRIKE_ORIGINAL_CONSTITUTIVE_CONSTANT_A_B_FINITE_PARAMETER_ACTION',
        'source_sha256': actual['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in paths+[native_path]},
        'H1': encode(H1), 'H2': encode(H2), 'additional_H1': encode(extra_matrix1),
        'additional_H2': encode(extra_matrix2), 'E1': encode(E1), 'E2': encode(E2),
        'K0': encode(K0), 'K1': encode(K1), 'C1': encode(C1), 'C2': encode(C2),
        'background_direction': encode(direction), 'B1': encode(background_B1.reshape(72, 1)),
        'parameter_family': 'Aepsilon=Abar+epsilon dx1 S01; Bepsilon=Bbar+epsilon b0; original coframe fixed only in background path',
        'finite_action_identity': 'Gauge change =epsilon[W(B,D_Aa)+W(b,F)-sigma W(b,star_e B)]+epsilon^2[W(b,D_Aa)-sigma W(b,star_e b)/2]; no higher epsilon coefficient since [a,a]=0.',
        'Hessian_identity': 'H1=old_full_H1+sum b_i Q_Bi; H2=old_scalar_H2+Hess[-sigma W(b,star_e b)/2]',
        'Euler_identity': 'Eepsilon=epsilon E1+epsilon^2 E2; W(b,D_Aa) contributes true gauge_A E2 despite zero field Hessian',
        'Ward_identity': '(H0+epsilon H1+epsilon^2 H2)(K0+epsilon K1)=-epsilon C1-epsilon^2 C2; full9 and primitive12',
        'original_joint_first_insertion_s0_readback': True,
        'nonzero_counts': {'H1': len(H1.todok()), 'H2': len(H2.todok()),
            'additional_H2': len(extra_matrix2.todok()), 'E1': len(E1.todok()), 'E2': len(E2.todok()),
            'K1': len(K1.todok()), 'C1': len(C1.todok()), 'C2': len(C2.todok())},
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'native.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS native finite joint path', result['nonzero_counts'], result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
