#!/usr/bin/env python3
"""Source-generated complex-ray contour majorants in the original physical clock."""
import hashlib
import json
import math
from pathlib import Path
import time
import sympy as s
import algebra as alg

HERE=Path(__file__).resolve().parent;FQ=HERE.parent
x,U=alg.x,alg.U
ray,a=s.symbols('s a',real=True)
rho=s.Rational(1,131072)
c=6*s.sqrt(15)/25


def matrix(record):
    return alg.old.matrix(record,{'x':x,'s':ray,'U':U})


def bound(M,entry=False):
    rows=[s.S(0)]*M.rows
    maximum=s.S(0)
    for (i,j),value in M.todok().items():
        remaining=s.expand(value.subs(ray,s.sqrt(2)*a));parts=[]
        for radical in alg.radicals[1:]:
            coef=remaining.coeff(radical);parts.append(coef);remaining-=radical*coef
        parts=[s.expand(remaining),*parts]
        absolute=s.S(0)
        for weight,part in zip([1,2,4,6],parts):
            for (m,n),coef in s.Poly(part,x,a,domain=s.QQ_I).terms():
                absolute+=weight*(abs(s.re(coef))+abs(s.im(coef)))*5**m*rho**n
        rows[i]+=absolute;maximum=max(maximum,absolute)
    return maximum if entry else max(rows)


def main():
    started=time.monotonic()
    paths=[HERE/'full-maps.json',HERE/'maps.json',HERE/'proper.json',HERE/'transfer.json',
           FQ/'packet-gauge-momentum-domain/source.json',FQ/'packet-gauge-momentum-domain/domain.json']
    full,maps,proper,transfer,source,domain=map(alg.read,paths)
    assert proper['full_source_family_strictly_proper']
    assert proper['all289_nonpositive_Laurent_powers']==[]
    assert transfer['determinant_frequency_degree']==126
    R=s.Rational(source['q_radius'])
    assert 2*rho<R and 5*c<5
    assert s.Rational(4,5)*rho*rho<1
    # Coefficient triangle estimates use only |q|, so the same paid margin
    # also holds for complex q. It is not a real-axis spectral inference.
    margins=[]
    for record in domain['all_native_factor_margins']:
        p=s.Poly(s.sympify(record['polynomial'],locals={'x':x,'q':a}),x,a,domain=s.QQ)
        degree=record['x_degree']
        leading=s.S(0);tail=s.S(0)
        for (m,n),coef in p.terms():
            if m==degree:
                if n==0:leading+=abs(coef)
                else:leading-=abs(coef)*R**n
            else:tail+=abs(coef)*5**m*R**n
        margin=leading*5**degree-tail
        assert leading>0 and margin==s.Rational(record['strict_circle_margin']) and margin>0
        margins.append(str(margin))
    determinant_lower=s.Rational(domain['normalized112_circle_abs_x5_determinant_lower'])/abs(s.Rational(domain['scalar_G9_over_N_determinant']))
    assert determinant_lower>0
    b=bound(matrix(full['normalized103']),entry=True)
    force=bound(matrix(full['force']))
    part=bound(matrix(full['part']))
    lift=bound(matrix(full['lift']))
    frame=bound(matrix(maps['Frame']))
    assert all(v>0 for v in [b,force,lift,frame])
    inverse=s.factorial(103)*b**102/determinant_lower
    # D(U) remains the actual incoming source value, not a supplied constant.
    D=s.Poly(s.sympify(full['D'],locals={'U':U}),U,domain=s.QQ)
    F=s.Poly(s.sympify(full['Fhat'],locals={'U':U}),U,domain=s.QQ)
    assert D.gcd(F).degree()==0
    prefactor=s.factor(frame*(part+lift*inverse*force)/(s.Rational(108,125)*24))
    assert prefactor>0
    result={'scope':'STRIKE_ACTUAL_COMPLEX_RAY_CONTOUR_AND_PHYSICAL_TIME_KERNEL_BOUNDS',
      'input_sha256':{str(p.relative_to(alg.old.source.ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
      'complex_parameter_disk':'|a|<=rho, physical s=sqrt2*a; |q_out|=|rho+a|<=2rho<R',
      'rho':str(rho),'complex_axial_q_radius':str(R),'all32_complex_coefficient_margins_positive':True,
      'normalized103_circle_determinant_lower':str(determinant_lower),
      'actual_source_bounds':{'matrix_max_entry':str(b),'force_row_sum':str(force),
          'part_row_sum':str(part),'lift_row_sum':str(lift),'Frame_row_sum':str(frame)},
      'inverse_bound_expression':'103! * matrix_max_entry^102 / normalized103_circle_determinant_lower',
      'source_circle_bound_numerator':str(prefactor),
      'source_circle_bound':'C=source_circle_bound_numerator / abs(D(U)), D and U from the original incoming source',
      'incoming_D':str(D.as_expr()),'incoming_D_nonzero_from_full_factor':True,
      'contour_kernel':'chi(s,t)=c/(2*pi*i) integral_{|z|=5,CCW} exp(c*z*t) X1(s,c*z) dz, t>=0; zero past',
      'physical_parameter_derivative_circle_bounds':['C','C/(sqrt(2)*rho)','C/rho^2'],
      'physical_time_derivative_bound':'||d_t^r d_s^j chi(0,t)||_infty <= (5*c)^(r+1) * j! * C/(sqrt2*rho)^j * exp(5*c*t)',
      'weighted_L1_bound':'For eta>=5: integral_0^infty exp(-eta*t)||d_t^r d_s^j chi(0,t)|| dt <= (5*c)^(r+1)*j!*C/((sqrt2*rho)^j*(eta-5*c))',
      'true_physical_clock_gap':str(5-5*c),
      'Laplace_identity':'integral_0^infty exp(-lambda*t) d_s^j chi(0,t) dt = X1_j(lambda), Re(lambda)>=5, j=0,1,2',
      'strong_parameter_identity':'Holomorphic original inverse on the closed complex parameter disk and contour gives actual s derivatives under the finite contour, time integral and local Volterra convolution.',
      'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'time.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS actual complex source disk, contour bounds, and original physical-clock gap',result['elapsed_seconds'],flush=True)


if __name__=='__main__':main()
