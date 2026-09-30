#!/usr/bin/env python3
"""Actual origin tensor, indispensable surface flux and original window readback."""
from fractions import Fraction as F
import hashlib
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


def main():
    began = time.monotonic()
    path = HERE/'bounds.json'
    data = read(path)
    record = data['actual_leading_native_tensor']
    T = s.SparseMatrix(*record['shape'], {(i,j):s.sympify(v) for i,j,v in record['entries']})
    tau = s.simplify(-T[1,1])
    assert T == s.diag(-2*tau,-tau,-tau) and tau > 0
    k = s.Matrix(s.symbols('k1:4',real=True))
    n = s.Matrix(s.symbols('n1:4',real=True))
    t,G = s.symbols('t G',real=True)
    affine = s.expand(G*((k-t*n/2).T*T*(k+t*n/2))[0])
    body = s.diff(affine,t,2).subs(t,0)/4
    baseline = affine.subs(t,0)
    flux = sum(n[i]*n[j]*s.diff(baseline,k[i],k[j]) for i in range(3) for j in range(3))/16
    assert s.expand(body+flux) == 0 and body != 0
    # The spherical |n.normal| tensor follows from these two exact polar
    # integrals and ordinary rotation invariance of the integration measure.
    v=s.Symbol('v',real=True)
    parallel=4*s.pi*s.integrate(v**3,(v,0,1))
    transverse=2*s.pi*s.integrate(v*(1-v*v),(v,0,1))
    assert parallel == s.pi and transverse == s.pi/2
    trace_formula=s.expand(s.trace(T)+(n.T*T*n)[0])
    assert s.expand(trace_formula+tau*(5+n[0]**2)-tau*(1-sum(a*a for a in n))) == 0

    g0=Box(*data['actual_full_time_packet_Gram']['raw_base']['rational'])
    b=s.sympify(data['physical_band_radius'])
    eps=s.simplify(b/s.sqrt(2))
    assert eps.is_Rational
    B=Box(2).sqrt()*F(str(eps))
    tau_scalar=s.simplify(tau/s.sqrt(30))
    assert tau_scalar.is_Rational
    tau_box=Box(30).sqrt()*F(str(tau_scalar))
    pi=pi_box()
    leading_cusp=g0*B**4*tau_box*Box(5,6)/(64*pi**2)
    cusp_error=Box(*data['absolute_cusp_minus_leading_bound']['rational']).hi
    actual_cusp=leading_cusp.grow(cusp_error)
    assert actual_cusp.lo > 0
    leading_constant=-g0*B**5*tau_box/(15*pi**2)
    constant_error=Box(*data['absolute_constant_minus_leading_bound']['rational']).hi
    actual_constant=leading_constant.grow(constant_error)
    assert actual_constant.hi < 0
    bound=Box(*data['absolute_q_squared_coefficient_bound']['rational']).hi
    assert bound < F(369,10**28)
    # A completed third summand of the original five-term response. The two
    # source legs have a Hessian, so their Taylor coefficient is divided by2.
    source_path=FQ/'packet-gauge-spatial-source-curvature/receipt.json'
    source=read(source_path)
    assert s.expand(s.sympify(source['physical_frequency'])-s.sympify(data['physical_frequency'])) == 0
    source_coefficient=Box(*source['whole_ball_current_source_Hessian']['rational'])/2
    three_terms=source_coefficient.grow(bound)
    assert three_terms.hi < 0
    dominance=(-source_coefficient.hi)/bound
    assert dominance > 7000
    omitted_flux=g0*tau_box*(B**3/(6*pi**2))/4
    assert omitted_flux.lo > bound*1000000
    result={'scope':'STRIKE_SOURCE_READER_LENS_BODY_FLUX_AND_THREE_SUMMAND_SPATIAL_CONSUMER',
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [path,source_path]},
        'actual_origin_tensor':'-tau*diag(2,1,1)', 'tau':str(tau),
        'actual_affine_body':str(s.expand(body)),'actual_affine_flux':str(s.expand(flux)),
        'actual_affine_q_squared_cancellation':True,
        'spherical_cusp_tensor':'pi/2*(Id+n*n^transpose)',
        'whole_ball_one_sided_expansion':'I_contact(s*n)=I0+I1(n)*s+I2(n)*s²+o(s²), s->0+; I1 gives the |q| cusp',
        'source_leading_cusp':'G0*B^4*tau/(64*pi²)*(5+n1²)',
        'all_unit_directions_actual_cusp':actual_cusp.record(),
        'actual_constant':actual_constant.record(),
        'all_unit_directions_abs_q_squared_coefficient_upper':str(bound),
        'source_legs_plus_reader_contact_q_squared_coefficient':three_terms.record(),
        'source_coefficient_over_reader_bound_lower':str(dominance),
        'actual_affine_drop_flux_e1_coefficient':omitted_flux.record(),
        'remaining_terms':'Two field-propagation legs remain separate; this is exactly three of the five native spatial-response summands.',
        'source_state':'Same uncentered fixed prepared packet; true full-time Gram G0 and mixed derivative norm, no t0 substitution or re-preparation.',
        'new_Lean_declarations':0,'elapsed_seconds':round(time.monotonic()-began,3)}
    (HERE/'shape.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS actual nonzero cusp, body/flux cancellation, whole-ball reader bound and negative three-summand coefficient',result['elapsed_seconds'],flush=True)
    print('cusp',actual_cusp.decimals(),'constant',actual_constant.decimals(),'three_terms',three_terms.decimals(),flush=True)


if __name__=='__main__':
    main()
