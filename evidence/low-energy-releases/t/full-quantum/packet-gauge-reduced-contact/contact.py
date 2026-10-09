#!/usr/bin/env python3
"""Actual native reader contact, including both source constitutive lifts."""
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


def decode(record):
    return s.SparseMatrix(*record['shape'], {(i, j): s.sympify(v) for i, j, v in record['entries']})


def main():
    began = time.monotonic()
    paths = [BASE/'active-gauge/receipt.json', FQ/'packet-gauge-constitutive-vertex/vertices.json',
             FQ/'packet-gauge-kinetic/receipt.json', FQ/'packet-gauge-bilocal/vertices.json']
    original, bvertices, kinetic, scalar_vertices = [json.loads(p.read_text()) for p in paths]
    jet = source.load(BASE/'active-gauge/compute.py', 'contact_native_jet')
    bijet = source.load(FQ/'packet-gauge-bilocal/vertices.py', 'contact_native_bijet')
    coordinates, _, _, data, provenance = jet.build(ROOT)
    assert coordinates.fields == original['fields']
    e0, A0, B0, sigma = [data[k] for k in ['e0', 'a0', 'gauge_b0', 'sigma']]
    native = decode(kinetic['native_pairing'])
    e = jet.matrix(4, 4, lambda i, j: e0[i, j]+coordinates.value('coframe', i, j))
    exterior = jet.wedge(e)
    star = jet.multiply(jet.multiply(jet.inverse_second_jet(exterior, jet.wedge_matrix(e0).inv()),
                                   jet.fixed(jet.J)), exterior)
    star0 = decode(kinetic['source_hodge'])
    A = jet.matrix(4, 12, lambda mu, c: A0[mu, c]+coordinates.value('gauge_A', mu, c))
    B = jet.matrix(6, 12, lambda i, c: B0[i, c]+coordinates.value('gauge_B', i, c))
    F = jet.matrix(6, 12, lambda pair, out:
        coordinates.value('gauge_A', jet.PAIRS[pair][1], out, derivative=jet.PAIRS[pair][0])-
        coordinates.value('gauge_A', jet.PAIRS[pair][0], out, derivative=jet.PAIRS[pair][1])+
        sum((A[jet.PAIRS[pair][0]][a]*A[jet.PAIRS[pair][1]][b]*v
             for (a, b, c), v in data['brackets'].items() if c == out), jet.Jet()))

    def pairing(left, right):
        return sum((native[a, b]*jet.W[i, j]*left[i][a]*right[j][b]
            for a, b, i, j in itertools.product(range(12), range(12), range(6), range(6))
            if native[a, b] and jet.W[i, j]), jet.Jet())

    def external(mu, color):
        ext = s.zeros(4, 12)
        ext[mu, color] = 1
        value = jet.matrix(6, 12, lambda pair, out: sum((v*(
            A[jet.PAIRS[pair][0]][a]*ext[jet.PAIRS[pair][1], b]+
            ext[jet.PAIRS[pair][0], a]*A[jet.PAIRS[pair][1]][b])
            for (a, b, c), v in data['brackets'].items() if c == out), jet.Jet()))
        derivative = [jet.matrix(6, 12, lambda pair, c:
            (1 if jet.PAIRS[pair][0] == j else 0)*ext[jet.PAIRS[pair][1], c]-
            (1 if jet.PAIRS[pair][1] == j else 0)*ext[jet.PAIRS[pair][0], c]) for j in range(4)]
        return ext, [value, *derivative]

    def constant(jets):
        return s.Matrix(6, 12, lambda i, j: jet.F.to_sympy(jets[i][j].terms.get((), jet.ZERO).real))

    p = list(ward.p)
    q = list(s.symbols('q0:4', real=True))
    r = list(s.symbols('r0:4', real=True))
    left = [-p[i]-q[i]-r[i] for i in range(4)]
    qweights, rweights = [s.Integer(1), *q], [s.Integer(1), *r]
    retained = [i for i, f in enumerate(coordinates.fields) if f['group'] in ['gauge_A', 'coframe']]
    bg = [i for i, f in enumerate(coordinates.fields) if f['group'] == 'gauge_B']
    QB = [decode(row['Q']) for row in bvertices['original_unit_auxiliary_readers']]
    Hbb = ward.operator(original['Fourier_Jacobi_entries'], values=p).extract(bg, bg)
    Hbb_inverse = Hbb.inv()
    assert source.clean(Hbb*Hbb_inverse) == s.eye(72)
    assert source.clean(Hbb_inverse*Hbb) == s.eye(72)

    def lift(point):
        H = ward.operator(original['Fourier_Jacobi_entries'], values=point)
        result = s.MutableSparseMatrix(289, 64, {(i, j): 1 for j, i in enumerate(retained)})
        bottom = source.clean(-Hbb_inverse*H.extract(bg, retained))
        for (i, j), value in bottom.todok().items():
            result[bg[i], j] = value
        assert not source.clean(H.extract(bg, range(289))*result).todok()
        return s.SparseMatrix(result)

    Tr, Tl = lift(p), lift(left)

    def hessian(density):
        result = s.MutableSparseMatrix(289, 289, {})
        for (i, j, a, b), value in bijet.density_hessian(jet, coordinates, density).items():
            assert not value.imag
            result[i, j] += jet.F.to_sympy(value.real)*(left[a] if a >= 0 else 1)*(p[b] if b >= 0 else 1)
        return source.clean(result)

    a, Da = external(1, 1)
    ba = [source.clean(-star0*constant(v)/sigma) for v in Da]
    Ta = s.MutableSparseMatrix(289, 64, {})
    for weight, d in zip(qweights, Da):
        variation = jet.scale(-1/sigma, jet.multiply(star, d))
        for pair, color in itertools.product(range(6), range(12)):
            for key, value in variation[pair][color].terms.items():
                if len(key) != 1:
                    continue
                field, derivative = coordinates.jets[key[0]]
                assert derivative == -1 and field in retained and not value.imag
                Ta[bg[12*pair+color], retained.index(field)] += weight*jet.F.to_sympy(value.real)
    Ta = source.clean(Ta)
    all_ba = source.clean(sum((w*m for w, m in zip(qweights, ba)), s.zeros(6, 12)))
    rows = []
    source_scalar = {tuple(row['reader']): row['Q1_bijet'] for row in scalar_vertices['readers']}
    for mu, color in itertools.product(range(4), range(12)):
        b, Db = external(mu, color)
        bb = [source.clean(-star0*constant(v)/sigma) for v in Db]
        all_bb = source.clean(sum((w*m for w, m in zip(rweights, bb)), s.zeros(6, 12)))
        Fab = s.Matrix(6, 12, lambda pair, out: sum(v*(
            a[jet.PAIRS[pair][0], aa]*b[jet.PAIRS[pair][1], ab]+
            b[jet.PAIRS[pair][0], aa]*a[jet.PAIRS[pair][1], ab])
            for (aa, ab, c), v in data['brackets'].items() if c == out))
        delta_bb = source.clean(-star0*Fab/sigma)
        base = hessian(pairing(B, Db[0]))
        eff = source.clean(base+sum((all_bb[i//12, i % 12]*QB[i] for i in range(72)
                                     if all_bb[i//12, i % 12]), s.zeros(289)))
        contact = sum((delta_bb[i//12, i % 12]*QB[i] for i in range(72)
                       if delta_bb[i//12, i % 12]), s.zeros(289))
        direct = hessian((-1/sigma)*pairing(jet.multiply(star, F), jet.fixed(Fab)))
        for i, j in itertools.product(range(5), repeat=2):
            if not any(Da[i][a][b] for a in range(6) for b in range(12)) or not any(Db[j][a][b] for a in range(6) for b in range(12)):
                continue
            weight = qweights[i]*rweights[j]
            direct += weight*hessian((-1/sigma)*pairing(jet.multiply(star, Da[i]), Db[j]))
            contact += weight*hessian((-sigma)*pairing(jet.fixed(bb[j]), jet.multiply(star, jet.fixed(ba[i]))))
        contact, direct = source.clean(contact), source.clean(direct.extract(retained, retained))
        term0 = source.clean(Tl.T*contact*Tr)
        termL = source.clean(Ta.T*eff*Tr)
        termR = source.clean(Tl.T*eff*Ta)
        difference = source.clean(direct-term0-termL-termR)
        assert not difference.todok(), ((mu, color), list(difference.todok().items())[:2])
        scalar = bijet.evaluate(source_scalar[mu, color], left, p)
        assert not scalar.extract(retained, retained).todok()
        complete = source.clean(contact+scalar)
        rows.append({'reader': [mu, color], 'native_contact_gauge': source.encode(contact),
                     'native_contact_complete': source.encode(complete),
                     'source_scalar_contact_entries': len(scalar.todok()),
                     'direct_reduced_fourth_variation_entries': len(direct.todok()),
                     'all12_variable_coefficients_equal': True,
                     'dropping_reader_contact_nonzero_entries': len(term0.todok()),
                     'dropping_both_lift_variations_nonzero_entries': len(source.clean(termL+termR).todok())})
        if color == 11:
            print('PASS native mixed fourth variation all12 colors at reader component', mu, flush=True)
    result = {'scope': 'STRIKE_ORIGINAL_NATIVE_READER_CONTACT_AND_FULL48_MIXED_FOURTH_VARIATION',
        'source_sha256': provenance['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'external_input': [1, 1], 'input_derivatives': list(map(str, q)), 'reader_derivatives': list(map(str, r)),
        'right_field_derivatives': list(map(str, p)), 'left_field_derivatives': list(map(str, left)),
        'original_retained_fields': retained,
        'constitutive_lift_input_variation': source.encode(Ta),
        'source_input_B_variation': source.encode(all_ba),
        'contact_identity': "Qeff_b'[a+b_a] = sum(delta_a b_b)_i QB_i + Hess[-sigma W(b_b,star_e b_a)] + original_scalar_Qprime",
        'direct_source_density': 'D_a D_b Sred = -W(star D_A a,D_A b)/sigma -W(star F,D_A^2F[a,b])/sigma',
        'whole_commuting_identity': "D_R^2 D_a D_b Sred = T(left)^T Qeff_b' T(right) + T_a^T Qeff_b T(right) + T(left)^T Qeff_b T_a",
        'all48_all12_free_momentum_identity': True, 'reader_count': len(rows), 'readers': rows,
        'source_scalar_contacts_retained': sum(row['source_scalar_contact_entries'] for row in rows),
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'contact.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS full48 native contacts and source fourth-variation consumer', result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
