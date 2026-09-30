#!/usr/bin/env python3
"""Full289 source equations for the independently transported field/covector pair."""
from functools import lru_cache
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time
import sympy as s
from sympy.polys.rings import ring

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
BASE = FQ.parent
ROOT = HERE.parents[4]
FIELD = s.QQ.algebraic_field(s.sqrt(2), s.sqrt(15), s.I)
R, rz, rx, ry, rU, rT, rl = ring('kz,kx,ky,U,T,lam', FIELD)
kz, kx, ky, U, T = s.symbols('kz kx ky U T', real=True)
lam = s.Symbol('lam')
symbols = [kz, kx, ky, U, T, lam]
locals_ = {str(v): v for v in symbols}


def read(path): return json.loads(path.read_bytes())
@lru_cache(None)
def scalar(value):
    value = s.sympify(value)
    if value.is_Rational: return FIELD.convert(value)
    if value.is_Add: return sum((scalar(v) for v in value.args), FIELD.zero)
    if value.is_Mul:
        out = FIELD.one
        for v in value.args: out *= scalar(v)
        return out
    if value.is_Pow and value.exp.is_Integer: return scalar(value.base)**int(value.exp)
    return FIELD.from_sympy(value)
def poly(text):
    expr = s.sympify(text, locals=locals_)
    return R.from_dict({m: scalar(v) for m, v in s.Poly(expr, *symbols, domain=s.EX).terms() if v})
def column(record):
    out = [R.zero for _ in range(289)]
    for i, _, value in record['entries']: out[i] = poly(value)
    return out
def add(*columns): return [sum((v[i] for v in columns), R.zero) for i in range(289)]
def scaled(q, col): return [q*v for v in col]


def main():
    started = time.monotonic()
    paths = [HERE/'source.json', BASE/'active-gauge/receipt.json',
             FQ/'packet-gauge-joint-momentum-jet/jets.json.gz']
    source, actual = map(read, paths[:2])
    jets = json.loads(gzip.decompress(paths[2].read_bytes()))
    A, B, Z = [column(source['columns'][name]['global_numerator']) for name in ['A', 'B', 'Z']]
    Fhat, D = poly(source['complete_Fhat']), poly(source['denominator_D'])
    c2 = R.ground_new(scalar(s.sympify(source['physical_clock'])**2))
    ratio = R.ground_new(scalar(s.sympify(source['physical_clock'])**2/s.sympify(source['source_coefficient'])))
    j = column(source['original_negative_g00_injection'])
    relation = rz*rz+rx*rx+ry*ry-2*rT
    def reduce(v): return v.rem(relation)
    def assert_zero(col):
        failures = [i for i, v in enumerate(col) if reduce(v)]
        assert not failures, failures[:8]
    def operator(sign):
        p = [rl, sign*R.ground_new(scalar(s.I))*rx,
             sign*R.ground_new(scalar(s.I))*ry, sign*R.ground_new(scalar(s.I))*rz]
        parts = [[] for _ in range(3)]
        for i, j, powers, coefficient in actual['Fourier_Jacobi_entries']:
            assert powers[0] <= 2
            value = R.ground_new(scalar(s.sympify(coefficient)))
            for component, exponent in zip(p[1:], powers[1:]): value *= component**exponent
            parts[powers[0]].append((i, j, value))
        return parts
    def apply(entries, col):
        result = [R.zero for _ in range(289)]
        for i, j, value in entries: result[i] += value*col[j]
        return result
    H0, H1, H2 = operator(-1)
    assert_zero(apply(H2, A)); assert_zero(apply(H2, B))
    assert_zero(add(apply(H1, A), scaled(-R.one, Z)))
    assert_zero(add(apply(H0, A), apply(H1, B)))
    assert_zero(add(apply(H0, B), scaled(c2*rU, Z), scaled(ratio*Fhat, j)))
    numerator = add(scaled(rl, A), B)
    response = add(apply(H0, numerator), scaled(rl, apply(H1, numerator)), scaled(rl*rl, apply(H2, numerator)))
    residual = add(response, scaled(-(rl*rl-c2*rU), Z), scaled(ratio*Fhat, j))
    assert_zero(residual)
    print('PASS all physical lambda/k/U/T original289 identities before the full-F root restriction', flush=True)

    wrong_parts = operator(1)
    wrong = add(*(scaled(rl**i, apply(H, numerator)) for i, H in enumerate(wrong_parts)),
                scaled(-(rl*rl-c2*rU), Z), scaled(ratio*Fhat, j))
    wrong_rows = [i for i, value in enumerate(wrong) if reduce(value).rem(Fhat)]
    assert wrong_rows
    source_origin = [value.evaluate([(rz, FIELD.zero), (rx, FIELD.zero), (ry, FIELD.zero),
                                     (rU, FIELD.zero), (rT, FIELD.zero), (rl, FIELD.zero)]) for value in Z]
    assert any(source_origin[i]+scalar(s.sympify(v)) != FIELD.zero
               for i, _, v in source['original_negative_g00_injection']['entries'])
    print('PASS wrong spatial Fourier sign and complete-g00-source replacement controls', flush=True)

    # The legacy positive physical momentum column equals this reflected formula at k=-kin.
    kin = list(map(s.sympify, jets['physical_k_in']))
    frequency = s.sympify(jets['physical_lambda'])
    rho2 = s.expand(sum(v*v for v in kin)/2)
    subst = {kx: -kin[0], ky: -kin[1], kz: -kin[2], T: rho2, lam: frequency}
    P, pu = ring('U', FIELD)
    def univariate(expr):
        return P.from_dict({power: scalar(coefficient) for power, coefficient in s.Poly(s.expand(expr), U).terms() if coefficient})
    sourcefactor = univariate(s.sympify(source['complete_Fhat'], locals=locals_).subs(T, rho2))
    def evalcolumn(values): return [univariate(v.as_expr(*symbols).subs(subst)).rem(sourcefactor) for v in values]
    def frozen(record):
        out = [P.zero for _ in range(289)]
        for i, power, value in record['entries']: out[i] += scalar(s.sympify(value))*pu**power
        return [v.rem(sourcefactor) for v in out]
    assert evalcolumn(numerator) == frozen(jets['X0_numerator_coefficients'])
    assert evalcolumn(scaled(rl*rl-c2*rU, Z)) == frozen(jets['I0_numerator_coefficients'])
    den = s.sympify(source['denominator_D'], locals=locals_)*(lam*lam-s.sympify(source['physical_clock'])**2*U)
    assert univariate(den.subs(subst)) == univariate(s.sympify(jets['common_incoming_theta_denominator'], locals={'U': U}))
    print('PASS same original incoming U, exact physical clock and frozen nonaxis causal column/source', flush=True)
    output = {'scope': 'STRIKE_ORIGINAL_FULL289_GLOBAL_THETA_EQUATION_AND_CAUSAL_INITIAL_SOURCE',
              'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
              'exact_identity': 'H(lambda,-ik)*(lambda*A+B)=(lambda^2-c^2*U)*Z-(c^2/cF)*Fhat(U,T)*j_g00 modulo 2T-|k|^2',
              'independent_lambda_U_T': True, 'all289_rows': True,
              'time_coefficients': {'H2A_zero': True, 'H2B_zero': True, 'H1A_equals_Z': True,
                                    'H0A_plus_H1B_zero': True, 'H0B_plus_c2U_Z_equals_minus_fullF_source': True},
              'actual_source_precedes_equation': True,
              'wrong_Fourier_sign_fullF_nonzero_rows': wrong_rows,
              'source_not_complete_negative_g00': True,
              'frozen_causal_consumer': {'formula_argument': '-original_kin', 'all289_X0_and_I0': True,
                                          'same_denominator_and_original_incoming_root': True},
              'retarded_kernel': '[A*cosh(c*sqrt(U)*t)+B*sinh(c*sqrt(U)*t)/(c*sqrt(U))]/D for t>=0, zero for t<0; sinh term extends as t at U=0',
              'initial_kernel': 'A/D', 'initial_kernel_derivative': 'B/D',
              'true_distributional_source': 'H(partial_t,-ik)K_theta=(Z/D)*delta_0; H2K_theta=0, source and mixed-order contacts paid',
              'seconds': round(time.monotonic()-started, 3)}
    (HERE/'equations.json').write_text(json.dumps(output, indent=2)+'\n')
    print('PASS global original equations and actual consumer', output['seconds'], flush=True)


if __name__ == '__main__': main()
