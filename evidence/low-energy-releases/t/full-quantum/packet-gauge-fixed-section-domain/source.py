#!/usr/bin/env python3
"""Generate the actual fixed incoming section's all-momentum determinant law."""
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
sys.path.insert(0, str(BASE/'active-gauge/rotation'))
import finite

p = s.symbols('p0:4', real=True)
t = s.Symbol('t', real=True)
x = s.Symbol('x', real=True)
k = s.symbols('k1:4', real=True)


def read(path):
    return json.loads(path.read_bytes())


def clean(M):
    return s.SparseMatrix(M.rows, M.cols, {ij: v for ij, raw in s.SparseMatrix(M).todok().items()
                                         if (v := s.expand(raw)) != 0})


def encode(M):
    return {'shape': list(M.shape), 'entries': [[i, j, str(v)] for (i, j), v in sorted(M.todok().items())]}


def matrix(record, names=None):
    return s.SparseMatrix(*record['shape'], {(i, j): s.sympify(v, locals=names or {str(a): a for a in p})
                                            for i, j, v in record['entries']})


def operator(entries, size=121):
    out = s.MutableSparseMatrix(size, size, {})
    for i, j, powers, raw in entries:
        out[i, j] += s.sympify(raw)*s.prod(a**n for a, n in zip(p, powers))
    return clean(out)


def polynomial_matrix(entries, size):
    return s.SparseMatrix(size, size, {(i, j): sum(v*t**n for n, v in enumerate(poly))
                                     for i, j, poly in entries if i < size and j < size})


def main():
    began = time.monotonic()
    paths = [BASE/'active-gauge/receipt.json', BASE/'active-gauge/quotient.json',
             BASE/'active-gauge/rotation/finite.json', BASE/'active-gauge/rotation/generators.json',
             FQ/'packet-gauge-kernel/ward.json', FQ/'packet-gauge-momentum-domain/source.json']
    raw, quotient, rotations, generators, ward, axial = map(read, paths)
    for name, expected in raw['source_sha256'].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == expected
    H = operator(raw['primitive_121_Fourier_Jacobi_entries'])
    K = matrix(ward['K0'])[:121, :]
    Km = K.subs(dict(zip(p, [-a for a in p])))
    assert clean(H*K) == s.zeros(121, 9)
    assert clean(Km.T*H) == s.zeros(9, 121)
    assert clean(H.T-H.subs(dict(zip(p, [-a for a in p])))) == s.zeros(121)
    removed = quotient['fixed_section_removed_original_fields']
    keep = [i for i in range(121) if i not in removed]
    assert keep == axial['keep112']
    minor = K.extract(removed, range(9))
    delta = s.factor(minor.det())
    delta0 = 27*s.sqrt(2)/500
    assert s.expand(delta-delta0*(1+25*p[1]**2/18)) == 0
    assert minor.subs(dict.fromkeys(p, 0)).det() == delta0
    origin = K.subs(dict.fromkeys(p, 0))
    origin_inverse = minor.subs(dict.fromkeys(p, 0)).inv(method='DM')
    d = 1+t*t
    _, coefficients = finite.source_integer_coefficients(
        {'Fourier_Jacobi_entries': raw['primitive_121_Fourier_Jacobi_entries']})
    circle_receipts = []
    for entry, gen in zip(rotations['certificates'], generators['generators']):
        axis = entry['axis']
        D = s.Integer(entry['field_constant_denominator'])
        full = {(i, j): tuple(v) for i, j, v in entry['field_numerator']}
        assert all((i < 121) == (j < 121) for i, j in full)
        field = {ij: value for ij, value in full.items() if ij[0] < 121}
        spatial = {(i, j): tuple(v) for i, j, v in entry['spatial_numerator']}
        slots = finite.finite_congruence(coefficients, spatial, D, field)
        Ln = polynomial_matrix(entry['field_numerator'], 121)
        Rn = polynomial_matrix(entry['spatial_numerator'], 4)
        J = s.SparseMatrix(121, 121, {(i, j): s.sympify(v) for i, j, v in gen['field_generator']
                                     if i < 121 and j < 121})
        assert J.trace() == 0
        assert Ln.subs(t, 0) == D*s.eye(121)
        assert clean(d*Ln.diff(t)-8*t*Ln-4*J*Ln) == s.zeros(121)
        # The original K basis, including its Lorentz ordering, fixes U.
        Un = (origin_inverse*(Ln*origin).extract(removed, range(9))/(D*d*d)).applyfunc(s.cancel)
        assert all(s.Poly(v, t).degree() <= 4 for v in Un.todok().values())
        rotated_p = Rn.T*s.Matrix(p)
        Kn = clean(d*d*origin + sum((K.diff(a)*v for a, v in zip(p, rotated_p)), s.zeros(121, 9)))
        assert clean(Ln*K-D*Kn*Un) == s.zeros(121, 9)
        assert s.expand(Un.det()-d**18) == 0
        assert Un.subs(t, 0) == s.eye(9)
        circle_receipts.append({'axis': axis, 'primitive121_congruence_zero_slots': slots,
            'original_K_intertwining_all_p_and_t': True, 'parameter_numerator': encode(s.SparseMatrix(Un)),
            'parameter_denominator': '(1+t^2)^2', 'parameter_determinant': '1',
            'field_trace_generator': '0', 'field_ODE_all_coefficients_zero': True,
            'field121_determinant': '1'})
        print('PASS native circle', axis, ': full121 congruence, original K covariance and both determinant laws', flush=True)
    N = s.sympify(raw['source_lapse'])
    c = s.sqrt(2)*N
    M = H.extract(keep, keep)
    Dscale = matrix(axial['scales112'], {'x': x})
    A = clean((Dscale*M*Dscale/N).subs(dict(zip(p, [c*x, *[s.I*a for a in k]]))))
    assert clean(A.subs({k[0]: 0, k[1]: 0, k[2]: s.sqrt(2)*s.Symbol('q', real=True)})
                 - matrix(axial['normalized112'], {'x': x, 'q': s.Symbol('q', real=True)})) == s.zeros(112)
    for value in A.todok().values():
        assert s.Poly(value, x, *k, extension=[s.sqrt(2), s.sqrt(15), s.I]).degree(x) <= 2
    output = {'scope': 'ORIGINAL_FIXED_SECTION_ALL_MOMENTUM_DETERMINANT_TRANSPORT',
        'source_sha256': raw['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'removed': removed, 'keep112': keep, 'original_K121': encode(s.SparseMatrix(K)),
        'original_minor': encode(s.SparseMatrix(minor)), 'minor_determinant': str(delta),
        'minor_axis_determinant': str(delta0), 'both_original_null_identities': True,
        'circles': circle_receipts, 'scales112': encode(Dscale), 'normalized112': encode(A),
        'normalized_variables': [str(x), *map(str, k)], 'physical_clock': str(c),
        'determinant_ratio': '(1-25*k1^2/18)^2',
        'determinant_argument': 'Original basis [K,P], det L121=det U9=1, and actual projection I-K(RK)^(-1)R. No replacement output section.',
        'frequency_degree': 126, 'new_Lean_declarations': 0, 'controller_advance': False,
        'seconds': round(time.monotonic()-began, 3)}
    (HERE/'source.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS fixed-section source and exact axial readback', output['seconds'], flush=True)


if __name__ == '__main__':
    main()
