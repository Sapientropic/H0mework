#!/usr/bin/env python3
"""All48 native local-Euler readers on the same finite constitutive path."""
from fractions import Fraction
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


def matrix(record, symbols=None):
    return original.matrix(record, symbols)


def bound(value):
    rest = s.expand(value)
    total = Fraction(0)
    for radical, upper in [(s.sqrt(30), 6), (s.sqrt(15), 4), (s.sqrt(2), Fraction(3, 2))]:
        coefficient = rest.coeff(radical)
        rest = s.expand(rest-radical*coefficient)
        assert s.re(coefficient).is_Rational and s.im(coefficient).is_Rational
        total += upper*(abs(Fraction(str(s.re(coefficient))))+abs(Fraction(str(s.im(coefficient)))))
    assert s.re(rest).is_Rational and s.im(rest).is_Rational
    return total+abs(Fraction(str(s.re(rest))))+abs(Fraction(str(s.im(rest))))


def main():
    began = time.monotonic()
    paths = [HERE/'native.json', BASE/'active-gauge/receipt.json',
        FQ/'packet-gauge-kinetic/receipt.json', FQ/'packet-gauge-constitutive-vertex/vertices.json',
        FQ/'packet-gauge-bilocal/vertices.json', FQ/'packet-gauge-reduced-contact/contact.json',
        FQ/'packet-gauge-causal/source.json', FQ/'packet-gauge-kernel/source.json']
    native, actual, kinetic, bvertices, weak, contact, frame, primitive = map(read, paths)
    jet = original.source.load(BASE/'active-gauge/compute.py', 'joint_family_reader_jet')
    coords = jet.Coordinates()
    for group, shape in [('scalar_J', (9,)), ('gauge_A', (4, 12)), ('coframe', (4, 4)),
            ('primal_H', (2, 4, 3)), ('dual_H', (2, 4, 3)), ('Lorentz', (4, 6)),
            ('gravity_B', (6, 6)), ('multiplier', (6, 6)), ('gauge_B', (6, 12))]:
        coords.group(group, shape)
    assert coords.fields == actual['fields']
    e0 = s.Matrix(actual['actual_background']['coframe']).applyfunc(s.sympify)
    e = jet.matrix(4, 4, lambda i, j: e0[i, j]+coords.value('coframe', i, j))
    exterior0 = s.Matrix(6, 6, lambda i, j:
        e0[jet.PAIRS[i][0], jet.PAIRS[j][0]]*e0[jet.PAIRS[i][1], jet.PAIRS[j][1]]-
        e0[jet.PAIRS[i][0], jet.PAIRS[j][1]]*e0[jet.PAIRS[i][1], jet.PAIRS[j][0]])
    exterior = jet.wedge(e)
    star = jet.multiply(jet.multiply(jet.inverse_second_jet(exterior, exterior0.inv()), jet.fixed(jet.J)), exterior)
    star0 = matrix(kinetic['source_hodge'])
    gram = matrix(kinetic['native_pairing'])
    sigma = s.sympify(actual['source_coupling'])
    ba = matrix(native['B1']).reshape(6, 12)
    starba = jet.multiply(star, jet.fixed(ba))
    def pairing(A, B):
        return sum((jet.W[i, j]*gram[a, b]*A[i][a]*B[j][b]
            for i, j, a, b in itertools.product(range(6), range(6), range(12), range(12))
            if jet.W[i, j] and gram[a, b]), jet.Jet())
    def hessian(density):
        terms = jet.fourier_hessian(coords, density)
        assert all(not any(power) and not value.imag for (i, j, power), value in terms.items())
        return s.SparseMatrix(289, 289, {(i, j): jet.F.to_sympy(value.real)
            for (i, j, _), value in terms.items()})
    QB, QB1 = [], []
    for row in bvertices['original_unit_auxiliary_readers']:
        pair, color = row['auxiliary']
        unit = s.zeros(6, 12)
        unit[pair, color] = 1
        QB.append(matrix(row['Q']))
        QB1.append(hessian((-sigma)*pairing(jet.fixed(unit), starba)))
    twice_h2 = clean(sum((ba[i//12, i % 12]*M for i, M in enumerate(QB1)), s.zeros(289)))
    assert twice_h2 == 2*matrix(native['additional_H2'])
    gen = list(map(matrix, primitive['fundamental']))
    tracegram = s.Matrix(12, 12, lambda i, j: s.re(-s.trace(gen[i]*gen[j])))
    gi = tracegram.inv()
    commutator = [gi*s.Matrix([s.re(-s.trace(T*(gen[1]*G-G*gen[1]))) for T in gen]) for G in gen]
    # The external background is a=dx1 S01. The derivative below is the
    # actual D_(A+epsilon a) reader, with no extra amplitude normalization.
    delta = []
    for mu, color in itertools.product(range(4), range(12)):
        Fab = s.Matrix(6, 12, lambda pair, j:
            int(jet.PAIRS[pair] == (1, mu))*commutator[color][j]-
            int(jet.PAIRS[pair] == (mu, 1))*commutator[color][j])
        delta.append(clean(-star0*Fab/sigma))
    p = original.ward.p
    derivative = matrix(kinetic['curvature_derivative'], {str(v): v for v in p})
    l = s.symbols('l0:4', real=True)
    r = s.symbols('t0:4', real=True)
    qinput = s.symbols('q0:4', real=True)
    reader = s.symbols('r0:4', real=True)
    def bilocal(entries):
        M = s.MutableSparseMatrix(289, 289, {})
        for i, j, a, b, text in entries:
            M[i, j] += s.sympify(text)*(l[a] if a >= 0 else 1)*(r[b] if b >= 0 else 1)
        return clean(M)
    names = {str(v): v for v in [*p, *qinput, *reader]}
    contact_by_reader = {tuple(row['reader']): row for row in contact['readers']}
    spatial = [s.sympify(value) for value in frame['physical_momentum']]
    spatial_sub = {**{l[j+1]: -s.I*spatial[j] for j in range(3)},
                   **{r[j+1]: s.I*spatial[j] for j in range(3)}}
    records = []
    for j, row in enumerate(weak['readers']):
        mu, color = row['reader']
        assert j == mu*12+color
        a = s.zeros(48, 1)
        a[j, 0] = 1
        b0 = clean(-s.kronecker_product(star0, s.eye(12))*
            derivative.subs({p[k]: -l[k]-r[k] for k in range(4)})*a/sigma)
        db = delta[j].reshape(72, 1)
        Q0 = clean(bilocal(row['Q0_bijet'])+sum((b0[i]*QB[i] for i in range(72)), s.zeros(289)))
        Q1 = clean(bilocal(row['Q1_bijet'])+sum((db[i]*QB[i]+b0[i]*QB1[i] for i in range(72)), s.zeros(289)))
        Q2 = clean(sum((db[i]*QB1[i] for i in range(72)), s.zeros(289)))
        assert Q2 == hessian((-sigma)*pairing(jet.fixed(delta[j]), starba))
        old = matrix(contact_by_reader[mu, color]['native_contact_complete'], names)
        old = clean(old.subs({**{p[k]: r[k] for k in range(4)}, **{qinput[k]: 0 for k in range(4)},
            **{reader[k]: -l[k]-r[k] for k in range(4)}}, simultaneous=True))
        assert Q1 == old, (mu, color)
        source_bounds = []
        for M in [Q0, Q1, Q2]:
            values = clean(M.subs(spatial_sub))
            total = Fraction(0)
            for value in values.todok().values():
                for powers, coefficient in s.Poly(value, l[0], r[0]).terms():
                    assert all(power <= 1 for power in powers)
                    total += bound(coefficient)/2
            source_bounds.append(str(total))
        records.append({'reader': row['reader'], 'Q2': encode(Q2),
            'Q0_entries': len(Q0.todok()), 'Q1_entries': len(Q1.todok()), 'Q2_entries': len(Q2.todok()),
            'Q1_matches_original_reduced_fourth_variation': True,
            'source_value_timejet_bilinear_bounds': source_bounds})
    assert not records[13]['Q2']['entries']
    assert any(record['Q2']['entries'] for record in records)
    result = {'scope': 'STRIKE_ALL48_FINITE_CONSTITUTIVE_READER_QUADRATIC_PARAMETER_COEFFICIENTS',
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'source_sha256': native['source_sha256'],
        'QB_derivative': list(map(encode, QB1)),
        'reader_family': 'Qeff(epsilon)=Q0+epsilon Q1+epsilon² Q2; b_reader(epsilon)=b0+epsilon db, QB(epsilon)=QB0+epsilon QB1; original scalar contact affine',
        'Q2_identity': 'Q2=Hess[-sigma W(db_reader,star_e b_a)]',
        'weak_reader': 'external=-(left+right); background input momentum0, original two field momenta retained',
        'all48_Q1_matches_original_mixed_fourth_variation': True,
        'physical_spatial_pair': list(map(str, spatial)),
        'bounds_meaning': 'For original density half Q, V_j=sum absolute source coefficients/2 on two field/value-timejet vectors; no constant-current or linear-field term added',
        'readers': records, 'nonzero_Q2_readers': sum(bool(record['Q2']['entries']) for record in records),
        'selected_Q2_zero_from_source': True, 'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'readers.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS all48 exact quadratic native reader families; Q2 nonzero', result['nonzero_Q2_readers'], result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
