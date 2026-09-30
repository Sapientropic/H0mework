#!/usr/bin/env python3
"""Actual native contact, true packet jets and whole-ball reader curvature bound."""
from fractions import Fraction as F
from functools import lru_cache
from math import comb
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
ROOT = HERE.parents[4]
sys.path.insert(0, str(FQ/'packet-band-kernel'))
from intervals import Box, pi_box


def read(path):
    return json.loads(path.read_bytes())


@lru_cache(None)
def coefficient_bound(expression):
    value = s.expand(expression)
    bound = F(0)
    for part in [s.expand(s.re(value)), s.expand(s.im(value))]:
        for radical, upper in [(s.sqrt(30), F(6)), (s.sqrt(15), F(4)), (s.sqrt(2), F(3, 2))]:
            coefficient = part.coeff(radical)
            assert coefficient.is_Rational, coefficient
            bound += abs(F(str(coefficient)))*upper
            part = s.expand(part-coefficient*radical)
        assert part.is_Rational, part
        bound += abs(F(str(part)))
    return bound


def jet_product(a, b):
    return [sum(F(comb(n, j))*a[j]*b[n-j] for j in range(n+1)) for n in range(4)]


def jet_power(a, degree):
    result = [F(1), F(0), F(0), F(0)]
    for _ in range(degree):
        result = jet_product(result, a)
    return result


def main():
    began = time.monotonic()
    paths = [FQ/'packet-gauge-global-transfer/source.json', FQ/'packet-gauge-global-transfer/jets.json',
        FQ/'packet-gauge-reduced-contact/contact.json', FQ/'packet-gauge-probe-moments/integrals.json',
        FQ/'packet-gauge-probe-laplace/bounds.json', FQ.parent/'active-gauge/receipt.json',
        FQ/'packet-band-kernel/intervals.py']
    source, global_jets, contact, moments, probe, raw = [read(p) for p in paths[:-1]]
    for artifact in [source, contact, moments]:
        for path, digest in artifact['source_sha256'].items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest
    k = s.symbols('kx ky kz', real=True)
    U, T = s.symbols('U T', real=True)
    variables = (*k, U, T)
    names = dict(zip(map(str, variables), variables))
    c = s.sympify(source['physical_clock'])
    lam = s.expand(6*c*(1-s.I))
    assert s.expand(s.sympify(moments['physical_frequency'])-lam) == 0
    assert s.re(lam) > 5
    eps = F(source['source_root_control']['epsilon'])
    radius_box = Box(2).sqrt()*eps
    radius = radius_box.hi
    assert radius < F(1, 20000)
    tmax = eps*eps
    CF = [i for i, v in enumerate(raw['fields']) if v['group'] == 'coframe']
    scalar = [i for i, v in enumerate(raw['fields']) if v['group'] == 'scalar_J']
    columns = {}
    for kind in ['A', 'B']:
        columns[kind] = {i: s.Poly(s.sympify(v, locals=names), *variables)
            for i, _, v in source['columns'][kind]['global_numerator']['entries']}
        assert all(i not in columns[kind] for i in scalar)
    active = [i for i in CF if i in columns['A'] or i in columns['B']]
    selected = next(v for v in contact['readers'] if v['reader'] == [1, 1])
    q = s.symbols('q0:4', real=True)
    r = s.symbols('r0:4', real=True)
    p = s.symbols('p0:4', real=True)
    delta = s.symbols('d1:4', real=True)
    substitution = {q[0]: 0, r[0]: -s.conjugate(lam)-lam, p[0]: lam}
    substitution |= {q[j+1]: s.I*delta[j] for j in range(3)}
    substitution |= {r[j+1]: 0 for j in range(3)}
    substitution |= {p[j+1]: -s.I*(k[j]+delta[j]) for j in range(3)}
    Q = s.zeros(len(active))
    for i, j, value in selected['native_contact_complete']['entries']:
        assert (i in CF and j in CF) or (i in scalar and j in scalar)
        if i in active and j in active:
            Q[active.index(i), active.index(j)] = s.expand(s.sympify(value,
                locals={str(v): v for v in [*p, *q, *r]}).subs(substitution))
    assert Q == Q.T and all(not value.has(*k) for value in Q)
    assert max(s.Poly(value, *delta).total_degree() for value in Q if value) == 1
    Q0 = Q.subs(dict.fromkeys(delta, 0))
    Qj = [Q.diff(v) for v in delta]
    assert Q0 == Q0.H and all(v.H == -v for v in Qj)
    assert Q == Q0+sum((delta[j]*Qj[j] for j in range(3)), s.zeros(len(active)))
    def matrix_norm(M):
        return max(sum(coefficient_bound(M[i, j]) for j in range(M.cols)) for i in range(M.rows))
    q0_bound = matrix_norm(Q0)
    q1_bound = Box(sum(matrix_norm(value)**2 for value in Qj)).sqrt().hi
    print('PASS actual affine native coframe contact, scalar zero and source adjoint relations', flush=True)

    Fbar = s.Poly(s.sympify(source['complete_Fhat'], locals=names)/s.sympify(source['source_coefficient']), U, T)
    D = s.Poly(s.sympify(source['denominator_D'], locals=names), U, T)
    assert Fbar.diff(U) == D
    def radial_bound(P, omit_constant=False):
        return sum(abs(F(str(v)))*tmax**sum(a) for a, v in P.terms()
                   if not omit_constant or sum(a))
    Derror = radial_bound(D, True)
    assert D.nth(0, 0) == 1 and Derror < F(1, 40)
    Dlower = 1-Derror
    derivative = lambda i, j: radial_bound(Fbar.diff((U, i)).diff((T, j)))
    u1 = derivative(0, 1)/Dlower
    u2 = (derivative(0, 2)+2*derivative(1, 1)*u1+derivative(2, 0)*u1*u1)/Dlower
    u3 = (derivative(0, 3)+3*derivative(1, 2)*u1+3*derivative(2, 1)*u1*u1+
          derivative(3, 0)*u1**3+3*(derivative(1, 1)+derivative(2, 0)*u1)*u2)/Dlower
    r0 = s.sympify(global_jets['root_first_at0'])
    assert r0 == -Fbar.diff(T).nth(0, 0)/D.nth(0, 0)
    source_vars = [[radius, F(1), F(0), F(0)] for _ in k]+[
        [tmax, u1*radius, u1+u2*radius**2, 3*u2*radius+u3*radius**3],
        [tmax, radius, F(1), F(0)]]
    def polynomial_jet(P):
        values = [F(0)]*4
        for powers, value in P.terms():
            term = [coefficient_bound(value), F(0), F(0), F(0)]
            for j, degree in enumerate(powers):
                term = jet_product(term, jet_power(source_vars[j], degree))
            values = [a+b for a, b in zip(values, term)]
        return values
    denominator = s.Poly(D.as_expr()*(lam**2-c*c*U), *variables)
    den_bound = polynomial_jet(denominator)
    inv_bound = [1/(Dlower*F(str(s.expand(s.conjugate(lam)*lam))))]
    for n in range(1, 4):
        inv_bound.append(inv_bound[0]*sum(F(comb(n, j))*den_bound[j]*inv_bound[n-j] for j in range(1, n+1)))
    values, raw_bounds, leading = [], [], []
    tpoly = sum(v*v for v in k)/2
    zero_poly = s.Poly(0, *variables)
    for i in active:
        P = lam*columns['A'].get(i, zero_poly)+columns['B'].get(i, zero_poly)
        assert P.nth(0, 0, 0, 0, 0) == 0
        values.append(P)
        raw_bounds.append(jet_product(polynomial_jet(P), inv_bound))
        low = sum(value*s.prod(k[j]**powers[j] for j in range(3))*r0**powers[3]*tpoly**sum(powers[3:])
                  for powers, value in P.terms() if sum(powers[:3])+2*sum(powers[3:]) <= 2)
        leading.append(s.expand(low/(lam*lam)))
    f3 = Box(sum(b[3]**2 for b in raw_bounds)).sqrt().hi
    first = s.Matrix([[s.diff(v, kj).subs(dict.fromkeys(k, 0)) for kj in k] for v in leading])
    first_gram = (first.H*first).applyfunc(s.simplify)
    f1_origin = Box(matrix_norm(first_gram)).sqrt().hi
    second = s.Matrix([[s.diff(v, ki, kj).subs(dict.fromkeys(k, 0)) for ki in k for kj in k] for v in leading])
    f2_origin = Box(sum(coefficient_bound(v)**2 for v in second)).sqrt().hi
    f2 = f2_origin+f3*radius
    f1 = f1_origin+f2_origin*radius+f3*radius**2/2
    f0 = f1_origin*radius+f2_origin*radius**2/2+f3*radius**3/6
    print('PASS same full implicit root third-derivative bounds and actual coframe origin jets', flush=True)

    gram = {v['name']: v for v in moments['all_two_probe_Gram_jets']}
    g0 = Box(*gram['N0_right_base']['raw']['real']['rational'])
    gm = Box(*gram['N0_mixed_00']['raw']['real']['rational'])
    assert g0.lo > 0 and gm.lo > 0
    for i in range(3):
        assert gram[f'N0_mixed_{i}{i}']['raw'] == gram['N0_mixed_00']['raw']
        for j in range(3):
            if i != j:
                assert all(F(v) == 0 for part in ['real', 'imaginary']
                    for v in gram[f'N0_mixed_{i}{j}']['raw'][part]['rational'])
    b0_origin, b1_origin = g0.sqrt().hi, gm.sqrt().hi
    b2, b3 = [F(probe['derivative_bounds'][j]['eta_ge5_probe_ball_B_bound']) for j in [2, 3]]
    b1 = b1_origin+b2*radius
    b0 = b0_origin+b1_origin*radius+b2*radius**2/2
    A1 = f1_origin*b0_origin
    A2origin = f2_origin*b0_origin+2*f1_origin*b1_origin
    A2 = f2*b0+2*f1*b1+f0*b2
    A3 = f3*b0+3*f2*b1+3*f1*b2+f0*b3
    # Exact sphere flux removes mixed first derivatives. Odd affine-origin
    # terms integrate to zero; Taylor remainders give a genuine O(|k|²) bound.
    coefficient = q0_bound*(A2*A2origin/2+A1*A3+A2*A3*radius/2)/4
    coefficient += q1_bound*(3*A1*A2/2+A2*A2*radius/2)/2
    ball_second = radius_box**5/(10*pi_box()**2)
    quadratic_bound = ball_second*coefficient
    # The cusp is retained. This bound uses the actual contact and the same
    # initial source slope; it does not silently replace the lens by a ball.
    amplitude = A1*radius+A2*radius*radius/2
    cusp_bound = q0_bound*amplitude*amplitude*(radius_box**2/(4*pi_box()**2))/4
    constant_bound = q0_bound*amplitude*amplitude*(radius_box**3/(6*pi_box()**2))/2
    leading_tensor = (first.H*Q0*first).applyfunc(s.simplify)
    assert leading_tensor == leading_tensor.T and all(s.im(v) == 0 for v in leading_tensor)
    assert leading_tensor != s.zeros(3)
    cusp_remainder = q0_bound*(A1*A2*radius**3+A2*A2*radius**4/4)*(radius_box**2/(16*pi_box()**2))
    constant_remainder = q0_bound*(A1*A2+A2*A2*radius/4)*(radius_box**6/(24*pi_box()**2))
    print('SOURCE f1/f2/f3',float(f1_origin),float(f2_origin),float(f3),'Q',float(q0_bound),float(q1_bound),flush=True)
    print('SOURCE A1/A2/A3',float(A1),float(A2),float(A3),flush=True)
    print('PASS whole-ball native reader quadratic coefficient bound',quadratic_bound.decimals(),flush=True)
    def encode(M):
        return {'shape':list(M.shape),'entries':[[i,j,str(v)] for (i,j),v in s.SparseMatrix(M).todok().items()]}
    result = {'scope':'STRIKE_ACTUAL_NATIVE_READER_CONTACT_ONE_SIDED_SPATIAL_CURVATURE',
        'source_sha256':source['source_sha256'],
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'physical_frequency':str(lam),'weak_reader':[str(-12*c),'0','0','0'],
        'physical_band_radius':str(s.sqrt(2)*s.Rational(str(eps))),
        'active_original_coframe_fields':active,'actual_scalar_columns_zero':True,
        'Q0':encode(Q0),'Q_physical_external_derivatives':list(map(encode,Qj)),
        'Q0_selfadjoint_and_Qj_skewadjoint':True,'actual_contact_degree_one':True,
        'coframe_first_jet':encode(first),'coframe_first_Gram':encode(first_gram),'coframe_second_jet':encode(second),
        'actual_leading_native_tensor':encode(leading_tensor),
        'same_root_bounds':{'D_error':str(Derror),'U_first':str(u1),'U_second':str(u2),'U_third':str(u3)},
        'source_F_bounds':{'F1_origin':str(f1_origin),'F2_origin':str(f2_origin),'F3_global':str(f3)},
        'actual_full_time_packet_Gram':{'raw_base':g0.record(),'raw_mixed_diagonal':gm.record()},
        'packet_vector_bounds':list(map(str,[b0,b1,b2,b3])),
        'actual_A_equals_F_tensor_packet_bounds':{'A1_origin':str(A1),'A2_origin':str(A2origin),'A2_global':str(A2),'A3_global':str(A3)},
        'exact_quadratic_integrand':'1/4 Re< A,Q0 Dn²A > + 1/2 Re< A,Qn DnA >, after actual body plus surface flux; odd origin terms integrate to zero',
        'quadratic_integrand_after_odd_subtraction_bound':str(coefficient),
        'original_ball_second_radial_moment':ball_second.record(),
        'absolute_q_squared_coefficient_bound':quadratic_bound.record(),
        'absolute_one_sided_cusp_coefficient_bound':cusp_bound.record(),
        'absolute_constant_bound':constant_bound.record(),
        'leading_cusp':'-G0*B^4/(64*pi²)*(trace(T)+n^transpose*T*n), T=F1^adjoint*Q0*F1',
        'leading_constant':'G0*B^5/(60*pi²)*trace(T)',
        'absolute_cusp_minus_leading_bound':cusp_remainder.record(),
        'absolute_constant_minus_leading_bound':constant_remainder.record(),
        'normalization':'two cosine branches each1/4; q² coefficient, not Hessian; original physical d³k/(2pi)³ and R=B lens',
        'new_Lean_declarations':0,'elapsed_seconds':round(time.monotonic()-began,3)}
    (HERE/'bounds.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS source bounds',result['elapsed_seconds'],flush=True)


if __name__=='__main__':
    main()
