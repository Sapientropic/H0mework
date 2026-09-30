#!/usr/bin/env python3
"""True radial-sign readback and a complete nonzero-momentum source consumer."""
import gzip
import importlib.util
import json
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('propagation_consumer_origin', HERE/'origin.py')
alg = importlib.util.module_from_spec(spec); spec.loader.exec_module(alg)
source, h, K = alg.source, alg.h, alg.K
q, x, U = s.symbols('q x U', real=True)


def read(path):
    raw = path.read_bytes()
    return json.loads(gzip.decompress(raw) if path.suffix == '.gz' else raw)


def main():
    started = time.monotonic()
    kernel = read(HERE/'kernel.json')
    radial = read(HERE/'radial-inverse.json.gz')
    old = read(source.FQ/'packet-gauge-momentum-domain/source.json')
    actual = read(source.BASE/'active-gauge/receipt.json')
    alpha = [tuple(a) for a, rec in kernel['normalized_operator_jets']]
    zero = (0, 0, 0)
    def matrix(record): return source.native.matrix(record, {'q': q, 'x': x, 'U': U})
    operators = {tuple(a): matrix(rec) for a, rec in kernel['normalized_operator_jets']}
    old_A = matrix(old['normalized112']).subs(x, 6*(1-s.I))
    assert source.clean(operators[zero]-old_A.subs(q, -q)) == s.zeros(112)
    point = s.Rational(1, 262144)
    P, derivative = s.MutableSparseMatrix(112, 112, {}), s.MutableSparseMatrix(112, 112, {})
    for block in radial['blocks']:
        rows = block['indices']
        den = s.sympify(block['denominator'], locals={'q': q})
        d0, d1 = [s.expand(value.subs(q, -point)) for value in [den, s.diff(den, q)]]
        for i, j, text in block['numerator']:
            num = s.sympify(text, locals={'q': q})
            n0, n1 = [s.expand(value.subs(q, -point)) for value in [num, s.diff(num, q)]]
            P[rows[i], rows[j]] = s.cancel(n0/d0)
            derivative[rows[i], rows[j]] = s.cancel(-(n1*d0-n0*d1)/d0**2)
    P, derivative = alg.finite(source.clean(P)), alg.finite(source.clean(derivative))
    M, Mp = [alg.finite(source.clean(value.subs(q, point))) for value in [operators[zero], operators[zero].diff(q)]]
    assert M.matmul(P) == P.matmul(M) == alg.eye(112)
    assert (Mp.matmul(P)+M.matmul(derivative)).is_zero_matrix
    assert not (Mp.matmul(P)-M.matmul(derivative)).is_zero_matrix
    print('PASS actual negative-phase whole-q identity and odd derivative sign', flush=True)
    Fhat = s.Poly(s.sympify(kernel['same_complete_Fhat'], locals={'q': q, 'U': U}).subs(q, point), U, domain=s.QQ)
    degree = Fhat.degree()
    denominator = s.Poly(s.sympify(kernel['same_source_common_denominator'], locals={'q': q, 'U': U}).subs(q, point), U, extension=[s.sqrt(2), s.sqrt(15), s.I])
    assert denominator.gcd(Fhat).degree() == 0
    def constant(record): return alg.finite(source.clean(matrix(record).subs(q, point)))
    def polynomial_columns(record):
        M = source.clean(matrix(record).subs(q, point))
        terms = []
        for (i, j), value in M.todok().items():
            for (n,), coefficient in s.Poly(value, U, extension=[s.sqrt(2), s.sqrt(15), s.I]).rem(Fhat).terms():
                if coefficient: terms.append((i, degree*j+n, h.scalar(coefficient)))
        return h.matrix(M.rows, degree*M.cols, terms)
    op = {a: alg.finite(source.clean(M.subs(q, point))) for a, M in operators.items()}
    force = {tuple(a): polynomial_columns(rec) for a, rec in kernel['normalized_force_jets']}
    alg.indices, alg.zero = alpha, zero
    y = alg.solve(op, P, force)
    D = h.stored_matrix(kernel['actual_normalization_D']); keep = kernel['keep112']
    physical = {a: D.matmul(value) for a, value in y.items()}
    fields = {a: h.matrix(289, 9*degree, [(keep[i], j, value) for (i, j), value in v.to_dok().items()]) for a, v in physical.items()}
    for step in reversed(kernel['auxiliary_backwrites']):
        back = {tuple(a): constant(rec) for a, rec in step['back']}
        part = {tuple(a): polynomial_columns(rec) for a, rec in step['particular']}
        values = {a: value.extract(step['retained'], range(9*degree)) for a, value in fields.items()}
        new = alg.multiply(back, values)
        fields = {a: fields[a]+h.matrix(289, 9*degree, [(step['eliminated'][i], j, value)
                  for (i, j), value in (part[a]+new[a]).to_dok().items()]) for a in alpha}
    e = source.d
    z = s.sympify(kernel['physical_frequency'])
    H = source.native.ward.operator(actual['Fourier_Jacobi_entries'], values=[z, s.I*s.sqrt(2)*e[0],
        s.I*s.sqrt(2)*e[1], -s.I*s.sqrt(2)*(point-e[2])])
    alg.variables = list(e)
    Hjets = alg.jet(H)
    rhs = {tuple(a): polynomial_columns(rec) for a, rec in kernel['original_rhs_jets']}
    residual = alg.multiply(Hjets, fields)
    assert all((residual[a]-rhs[a]).is_zero_matrix for a in alpha)
    assert all(v.extract(kernel['removed'], range(9*degree)).is_zero_matrix for v in fields.values())
    result = {'scope': 'WHOLE_NEGATIVE_PHASE_FAMILY_AND_TRUE_NONZERO_SOURCE_CURRENT_CONSUMER',
              'radial_identity': 'A_current(q)=A_old(-q); P_current(q)=P_old(-q)',
              'physical_input_k': 'sqrt2/262144*e3', 'all112_both_inverses': True,
              'true_odd_radial_derivative_sign': True, 'wrong_odd_sign_nonzero': True,
              'same_complete_theta_polynomial_degree': degree, 'same_source_denominator_coprime': True,
              'all10_by9_by289_original_equations_on_complete_F': True,
              'original_Noether_and_removed9_preserved': True,
              'full168_auxiliary_backwrite': True, 'new_Lean_declarations': 0,
              'seconds': round(time.monotonic()-started, 3)}
    (HERE/'consumer.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS actual full289 source consumer for all profiles and external jets', result['seconds'], flush=True)


if __name__ == '__main__': main()
