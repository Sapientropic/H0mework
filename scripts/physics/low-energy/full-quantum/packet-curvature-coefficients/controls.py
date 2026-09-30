#!/usr/bin/env python3
"""Actual-root consumer against the independently certified native-circle jet.

The seed contraction is evaluated in the complete even source-factor quotient.
The comparison comes from the other construction's four signed, moving-pole
vertices, including its radial root and own-residue derivative.
"""
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
FQ = HERE.parent
u, q, U, T, r = s.symbols('u q U T r', real=True)


def read(path):
    return json.loads(path.read_text())


def main():
    started = time.monotonic()
    receipt = read(HERE/'receipt.json')
    taylor_path = FQ/'packet-current-taylor/symbolic.json'
    taylor = read(taylor_path)
    assert receipt['source_sha256'] == taylor['source_sha256']
    for path, digest in receipt['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest
    sample = s.Rational(1, 262144)
    F = s.Poly(s.sympify(taylor['root_motion']['F'], locals={'u':u, 'q':q}), u, q)
    assert all(a % 2 == 0 and b % 2 == 0 for (a,b), _ in F.terms())
    Fhat = s.Poly(sum(c*U**(a//2)*T**(b//2) for (a,b),c in F.terms()), U, T)
    cf = F.coeff_monomial(u**2)
    f = s.Poly(Fhat.as_expr()/cf, U, T)
    D = f.diff(U)
    point = s.Poly(Fhat.as_expr().subs(T, sample**2), U, domain=s.QQ)
    Fr = s.Poly(point.as_expr().subs(U, sample**2*r), r, domain=s.QQ)
    assert Fr.count_roots(s.Rational(3,4), s.Rational(4,5)) == 1
    assert s.gcd(point, point.diff()).degree() == 0
    isolated = [(a,b) for ((a,b),m) in Fr.intervals(eps=s.Rational(1,2**160))
                if s.Rational(3,4) < a < b < s.Rational(4,5) and m == 1]
    assert len(isolated) == 1
    lo, hi = isolated[0]

    from sympy.polys.rings import ring
    K = s.QQ.algebraic_field(s.sqrt(2), s.sqrt(15), s.I)
    R, x = ring((U,), K)
    basis_expr = list(map(s.sympify, receipt['coefficient_basis']))
    basis = [K.from_sympy(c) for c in basis_expr]

    @lru_cache(None)
    def number(value):
        value = s.expand(value)
        if value.is_Add:
            return sum((number(c) for c in value.args), K.zero)
        rational, radical = value.as_coeff_Mul()
        return K.convert(rational)*basis[basis_expr.index(radical)]

    def poly(expression):
        return R.from_dict({powers:number(c) for powers,c in s.Poly(s.expand(expression), U).terms()})

    modulus = poly(point.as_expr())
    zero, one = R.zero, R.one

    def red(value):
        return value % modulus

    def substitute(polynomial):
        return poly(polynomial.as_expr().subs(T, sample**2))

    Dpoint = s.Poly(D.as_expr().subs(T, sample**2), U, domain=s.QQ)
    inverseD = poly(s.invert(Dpoint, point).as_expr())
    slope = red(-substitute(f.diff(T))*inverseD)
    curvature = red(-(substitute(f.diff(T).diff(T)) +
                      2*substitute(f.diff(U).diff(T))*slope +
                      substitute(f.diff(U).diff(U))*slope*slope)*inverseD)
    s0 = s.Rational(receipt['root']['s0'])
    actual = [zero, zero, R.ground_new(number(s.sqrt(2)*sample)), x,
              R.ground_new(K.convert(sample**2)), slope-R.ground_new(K.convert(s0)), curvature]

    def evaluate(record, assignments=actual):
        max_powers = [max(powers[i] for powers,_ in record['numerator']) for i in range(7)]
        powers = []
        for value, maximum in zip(assignments, max_powers):
            row = [one]
            for _ in range(maximum):
                row.append(red(row[-1]*value))
            powers.append(row)
        result = zero
        for exponents, pieces in record['numerator']:
            if any(assignments[i] == zero and power for i,power in enumerate(exponents)):
                continue
            coefficient = sum((K.convert(s.Rational(c))*basis[i] for i,c in pieces), K.zero)
            term = R.ground_new(coefficient)
            for axis, power in enumerate(exponents):
                term = red(term*powers[axis][power])
            result += term
        return red(result*inverseD**record['denominator_power'])

    def even(expression):
        source = s.Poly(s.expand(expression), u)
        assert all(power % 2 == 0 for (power,),_ in source.terms())
        return sum(c*U**(power//2) for (power,),c in source.terms())

    def rational_value(expression):
        # All tested native contractions have the common real sqrt(15) factor.
        numerator, denominator = s.fraction(s.cancel(expression/s.sqrt(15)))
        numerator = s.Poly(even(numerator.subs(q,sample)), U, domain=s.QQ)
        denominator = s.Poly(even(denominator.subs(q,sample)), U, domain=s.QQ)
        assert s.gcd(denominator,point).degree() == 0
        return red(R.ground_new(number(s.sqrt(15)))*poly(numerator.as_expr())*
                   poly(s.invert(denominator,point).as_expr()))

    same = taylor['pairings'][0]
    opposite = taylor['pairings'][1]
    parse = lambda value:s.sympify(value, locals={'u':u,'q':q})
    Csame, Copp = map(lambda rec:parse(rec['quadratic_coefficient']), [same,opposite])
    clock = parse(taylor['root_motion']['physical_clock'])
    alpha_reference = 2*clock**2*(parse(same['raw_contractions']['Q'])-
                                 parse(opposite['raw_contractions']['Q']))/F.diff(u).as_expr()**2
    tensors = receipt['tensor_polynomials']
    alpha = evaluate(tensors['alpha'])
    beta = evaluate(tensors['beta'][0])
    delta = evaluate(tensors['delta'][0])
    assert alpha == rational_value(alpha_reference)
    assert beta == zero
    assert delta == rational_value(4*(Csame+Copp))
    print('PASS new true-root alpha and delta00 against all four moving-pole vertices',flush=True)

    # At this axis the transverse second derivative still sees the true radial
    # slope. Its removal is distinct from deleting the entire radial motion.
    frozen = list(actual)
    frozen[5] = zero
    wrong_frozen = delta-evaluate(tensors['delta'][0], frozen)
    wrong_half = delta-rational_value(2*(Csame+Copp))
    wrong_sync = delta-rational_value(8*19*s.sqrt(15)/15625)

    def gcd_nonzero(polynomial):
        assert polynomial != zero
        # Scalar results here are real sqrt(15) times rational polynomials.
        rational = s.Poly(s.expand(polynomial.as_expr()/s.sqrt(15)), U, domain=s.QQ)
        degree = s.gcd(rational,point).degree()
        assert degree == 0
        return degree

    controls = {name:{'nonzero_on_every_complete_factor_root':True,
                      'gcd_degree':gcd_nonzero(value)}
                for name,value in [('frozen_source_slope_s0',wrong_frozen),
                                   ('omit_second_derivative_factor2',wrong_half),
                                   ('replace_by_synchronous_path',wrong_sync)]}
    print('PASS slope, Taylor-factor and synchronous-path negative controls',flush=True)
    output = {
        'scope':'STRIKE_ACTUAL_SOURCE_CONSUMER_OF_CURVATURE_TENSOR',
        'source_sha256':receipt['source_sha256'],
        'input_sha256':{str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest()
                        for path in [HERE/'receipt.json',taylor_path]},
        'q':str(sample),'physical_k':['0','0',str(s.sqrt(2)*sample)],'direction':['1','0','0'],
        'actual_theta_root':{'radial_window':['3/4','4/5'],'sturm_count':1,
                             'refined_radial_interval':[str(lo),str(hi)],
                             'complete_factor_simple':True},
        'identities_mod_complete_source_factor':{
            'alpha_equals_sum_all_four_native_pole_contractions':True,
            'beta_e1_zero_at_axis':True,
            'delta_e1_equals_4_times_same_plus_opposite_C2':True},
        'negative_controls':controls,
        'complex_tensor_preserved':{
            'beta_imaginary_monomials':[v['imaginary_monomials'] for v in tensors['beta']],
            'delta_imaginary_monomials':[
                {'axes':v['axes'],'count':v['imaginary_monomials']} for v in tensors['delta']]},
        'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'controls.json').write_text(json.dumps(output,indent=2)+'\n')
    print('PASS curvature coefficients direct source consumer',output['elapsed_seconds'],flush=True)


if __name__ == '__main__':
    main()
