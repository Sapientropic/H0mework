#!/usr/bin/env python3
"""Generate frame-free field and covector numerators from the original pole pair."""
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
u, q, U, T = s.symbols('u q U T', real=True)
kx, ky, kz, nx, ny, nz = s.symbols('kx ky kz nx ny nz', real=True)


def read(path): return json.loads(path.read_bytes())
def clean(M): return s.SparseMatrix(M).applyfunc(s.expand)
def zero(M): assert not clean(M).todok(), list(clean(M).todok().items())[:2]
def matrix(rec):
    return s.SparseMatrix(*rec['shape'], {(i, j): s.sympify(v, locals={'u': u, 'q': q}) for i, j, v in rec['entries']})
def encode(M):
    return {'shape': list(M.shape), 'entries': [[i, j, str(v)] for (i, j), v in sorted(clean(M).todok().items())]}
def even(value):
    poly = s.Poly(s.expand(value), u, q)
    assert all(a % 2 == b % 2 == 0 for (a, b), _ in poly.terms())
    return s.expand(sum(c*U**(a//2)*T**(b//2) for (a, b), c in poly.terms()))


def main():
    started = time.monotonic()
    paths = [BASE/'active-gauge/receipt.json', FQ/'light-modes/field-receipt.json',
             FQ/'packet-field/pole-source.json', FQ/'packet-field/circle-data.json',
             BASE/'active-gauge/rotation/generators.json', FQ/'packet-seed-regularity/receipt.json',
             FQ/'packet-field/field-data.json']
    actual, light, pole, circles, generators, seed, field = map(read, paths)
    for path, digest in actual['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    V = matrix(light['axial_original289_pole_leg'])
    factor = s.Poly(s.sympify(light['axial_source_factor'], locals={'u': u, 'q': q}), u, q, domain=s.QQ)
    cf = factor.coeff_monomial(u*u)
    c = s.simplify(s.sqrt(2)*s.sympify(actual['source_lapse']))
    axial = {name: matrix(pole[key]) for name, key in [
        ('A', 'pair_numerator_linear'), ('B', 'pair_numerator_constant'), ('Z', 'source_projection_numerator')]}
    zero(axial['A']+c/cf*(V-V.subs(u, -u)).applyfunc(lambda a: s.cancel(a/(2*u))))
    zero(axial['B']+c*c/cf*(V+V.subs(u, -u))/2)
    G = [s.SparseMatrix(289, 289, {(i, j): s.sympify(v) for i, j, v in row['field_generator']})
         for row in generators['generators']]
    spatial = [s.Matrix([[s.sympify(v) for v in row] for row in item['spatial_matrix']])
               for item in generators['generators']]
    C = [[matrix(v) for v in item['coefficients']] for item in circles['circles']]
    eye, empty = s.eye(289), s.zeros(289)
    representations = {'field': (G, C), 'source_covector': ([-g.T for g in G],
                         [[(-1)**degree*v.T for degree, v in enumerate(axis)] for axis in C])}
    ode = []
    for name, (action, coefficients) in representations.items():
        for axis in range(3):
            assert coefficients[axis][0] == eye
            for n in range(10):
                above = coefficients[axis][n+1] if n+1 < 9 else empty
                below = coefficients[axis][n-1] if n else empty
                current = coefficients[axis][n] if n < 9 else empty
                zero((n+1)*above+(n-9)*below-4*action[axis]*current)
            ode.append({'representation': name, 'axis': axis, 'all_circle_ODE_coefficients': True})
    print('PASS actual field L and source L^-T all-parameter native circle equations', flush=True)
    result = {}
    for name in ['A', 'B', 'Z']:
        role = 'source_covector' if name == 'Z' else 'field'
        action, coefficients = representations[role]
        original = axial[name]
        flip = sum(coefficients[1], empty)/16
        zero(flip*original-original.subs(q, -q))
        for d, coefficient in enumerate(coefficients[2]):
            weight = s.binomial(4, d//2) if d % 2 == 0 else 0
            zero(coefficient*original-weight*original)
        casimir = clean(-sum((g*g for g in action), empty))
        zero(casimir*(casimir-2*eye)*(casimir-6*eye)*original)
        projectors = [(casimir-2*eye)*(casimir-6*eye)/12,
                      -casimir*(casimir-6*eye)/8, casimir*(casimir-2*eye)/24]
        pieces, radial, decomp = [], [], []
        for j, projector in enumerate(projectors):
            part = clean(projector*original)
            zero((casimir-j*(j+1)*eye)*part)
            zero(action[2]*part)
            entries, terms = {}, 0
            for (i, _), value in part.todok().items():
                poly = s.Poly(value, u, q)
                assert all(a % 2 == 0 and b >= j and (b-j) % 2 == 0 for (a, b), _ in poly.terms())
                entries[i, 0] = s.expand(sum(v*U**(a//2)*T**((b-j)//2) for (a, b), v in poly.terms()))
                terms += len(poly.terms())
            reduced = s.SparseMatrix(289, 1, entries)
            zero(q**j*reduced.subs({U: u*u, T: q*q})-part)
            pieces.append(part); radial.append(reduced)
            decomp.append({'j': j, 'actual_Casimir_eigenvalue': j*(j+1), 'weight_zero': True,
                           'original_nonzero_rows': len(part.todok()), 'terms': terms,
                           'exact_q_divisor': j, 'radial_polynomial': encode(reduced)})
        zero(sum(pieces, s.zeros(289, 1))-original)
        b0, b1, b2 = radial
        c2 = clean((action[1]*action[1]*b2+3*b2)/2)
        e2 = clean(action[2]*c2)
        t1 = clean(nz*b1+nx*action[1]*b1-ny*action[0]*b1)
        t2 = clean((2*nz*nz-nx*nx-ny*ny)*b2/2+nx*nz*action[1]*b2-
                   ny*nz*action[0]*b2+(nx*nx-ny*ny)*c2+nx*ny*e2)
        zero(t1.subs({nx: 0, ny: 0, nz: 1})-b1)
        zero(t2.subs({nx: 0, ny: 0, nz: 1})-b2)
        zero(sum((t2.diff(v, 2) for v in [nx, ny, nz]), s.zeros(289, 1)))
        for axis in range(3):
            tangent = spatial[axis].extract([1, 2, 3], [1, 2, 3]).T*s.Matrix([nx, ny, nz])
            for tensor in [b0, t1, t2]:
                zero(sum((tangent[i]*tensor.diff(v) for i, v in enumerate([nx, ny, nz])), s.zeros(289, 1))
                     -action[axis]*tensor)
        global_column = clean(b0-(kz*b1+kx*action[1]*b1-ky*action[0]*b1)/s.sqrt(2)
                   +(2*kz*kz-kx*kx-ky*ky)*b2/4+kx*kz*action[1]*b2/2-
                   ky*kz*action[0]*b2/2+(kx*kx-ky*ky)*c2/2+kx*ky*e2/2)
        zero(global_column.subs({kx: 0, ky: 0, kz: s.sqrt(2)*q, U: u*u, T: q*q})-original.subs(q, -q))
        zero(s.conjugate(global_column)-global_column.subs({kx: -kx, ky: -ky, kz: -kz}, simultaneous=True))
        origin = clean(global_column.subs({kx: 0, ky: 0, kz: 0, U: 0, T: 0}))
        zero(origin-original.subs({u: 0, q: 0}))
        for g in action: zero(g*origin)
        if name == 'A':
            prior = s.SparseMatrix(289, 1, {(r['index'], 0): s.sympify(r['numerator'], locals={str(v): v for v in [kx, ky, kz, U, T]}) for r in seed['fields']})
            zero(global_column-prior)
        result[name] = {'variance': role, 'axial_source': encode(original), 'decomposition': decomp,
                        'nine_entire_generator_identities': True, 'reflection_and_nine_z_stabilizer_coefficients': True,
                        'global_numerator': encode(global_column), 'origin': encode(origin),
                        'Fourier_reality': True, 'actual_same_source_circle_transport': True}
        print('PASS', name, role, 'source decomposition', [(d['j'], d['original_nonzero_rows']) for d in decomp],
              'global rows', len(global_column.todok()), 'origin', len(origin.todok()), flush=True)
    Fhat = even(factor.as_expr())
    Dhat = even(s.sympify(pole['factor_D'], locals={'u': u, 'q': q}))
    assert s.expand(s.diff(Fhat, U)/cf-Dhat) == 0
    assert Dhat.subs({U: 0, T: 0}) == 1
    injection = s.SparseMatrix(289, 1, {(57, 0): -2*s.sympify(actual['source_lapse'])})
    for g in representations['source_covector'][0]: zero(g*injection)
    output = {'scope': 'STRIKE_ORIGINAL_FULL289_FRAME_FREE_THETA_FIELD_AND_PROJECTED_SOURCE',
              'source_sha256': actual['source_sha256'],
              'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
              'physical_clock': str(c), 'source_coefficient': str(cf),
              'variables': ['kx', 'ky', 'kz', 'U', 'T'], 'physical_radial_variable': 'T=|k|^2/2',
              'same_source_root': 'U=T*sourceRoot.axialPhase.root(T)',
              'complete_Fhat': str(Fhat), 'denominator_D': str(Dhat),
              'original_negative_g00_injection': encode(injection),
              'source_root_control': seed['source_root_control'],
              'source_root_remainder': field['root']['root_remainder'],
              'native_circle_ODE': ode, 'columns': result,
              'actual_transfer': '(lambda*A_global+B_global)/(D*(lambda^2-c^2*U))',
              'actual_source': 'Z_global/D; transported original source covector, not H times a supplied field',
              'physical_spatial_Fourier_symbol': '[lambda,-I*kx,-I*ky,-I*kz]',
              'reflection': 'All columns already use the original ell(-k) pair; source variance is L^-T',
              'seconds': round(time.monotonic()-started, 3)}
    (HERE/'source.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS global source construction', output['seconds'], flush=True)


if __name__ == '__main__': main()
