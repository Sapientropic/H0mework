#!/usr/bin/env python3
"""Uniform original pole disk and actual inverse ray derivatives, including0."""
from fractions import Fraction as F
from math import factorial
import hashlib
import json
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent
x,q=s.symbols('x q',real=True)
point=6*(1-s.I)
N=3*s.sqrt(30)/25;c=N*s.sqrt(2)
radicals=[s.Integer(1),s.sqrt(2),s.sqrt(15),s.sqrt(30)]
radical_bounds=[F(1),F(10,7),F(31,8),F(11,2)]


def rational(v):
    assert v.is_Rational,v
    return F(int(s.numer(v)),int(s.denom(v)))


def number_bound(v):
    remaining=s.expand(v);coeff=[s.Integer(0)]*4
    for j in range(3,0,-1):
        coeff[j]=remaining.coeff(radicals[j]);remaining=s.expand(remaining-radicals[j]*coeff[j])
    coeff[0]=remaining
    assert s.expand(v-sum(a*b for a,b in zip(radicals,coeff)))==0
    return sum((abs(rational(s.re(v)))+abs(rational(s.im(v))))*b for v,b in zip(coeff,radical_bounds))


def matrix(record):
    return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(v,locals={'x':x,'q':q}) for i,j,v in record['entries']})


def main():
    began=time.monotonic()
    src=json.loads((HERE/'source.json').read_text())
    R=F(src['q_radius']);assert R==F(1,32768)
    margins=[];lower=F(1);frequency_degree=0
    for block in src['all_source_factors']:
        lower*=abs(F(block['constant']))
        for factor in block['factors']:
            P=s.Poly(s.sympify(factor['polynomial'],locals={'x':x,'q':q}),x,q,domain=s.QQ)
            degree=P.degree(x)
            constant=next((rational(v) for (i,j),v in P.terms() if i==degree and j==0),F(0))
            perturb=sum(abs(rational(v))*R**j for (i,j),v in P.terms() if i==degree and j>0)
            leading=abs(constant)-perturb
            tail=sum(abs(rational(v))*F(5)**i*R**j for (i,j),v in P.terms() if i<degree)
            margin=leading*F(5)**degree-tail
            assert leading>0 and margin>0,(factor,margin)
            lower*=margin**factor['multiplicity'];frequency_degree+=degree*factor['multiplicity']
            margins.append({'polynomial':factor['polynomial'],'multiplicity':factor['multiplicity'],
                'x_degree':degree,'leading_uniform_lower':str(leading),'lower_terms_uniform_abs_bound_at_5':str(tail),
                'strict_circle_margin':str(margin)})
    G=matrix(src['scalar_G9'])/N
    gdet=s.simplify(G.det());gabs=abs(rational(gdet));assert gabs>0
    lower*=gabs
    assert frequency_degree==126
    # For every |x|>=5, each margin grows by at least (|x|/5)^degree.
    # The actual point has |x|²=72>64, so the rational lower radius8 is valid.
    assert s.expand(s.conjugate(point)*point)==72
    point_lower=lower*F(8,5)**frequency_degree
    assert point_lower>0 and F(108,125)<1 and 36*F(108,125)>25
    print('PASS all-q factor bounds, full112 including q=0, |x poles|<5',flush=True)
    A=matrix(src['normalized112'])
    at=A.subs(x,point).applyfunc(s.expand)
    derivatives=[at,at.diff(q),at.diff(q,2)]
    row_bounds=[];entry0=F(0)
    for order,derivative in enumerate(derivatives):
        rows=[F(0)]*112
        for (i,j),value in s.SparseMatrix(derivative).todok().items():
            amount=sum((abs(rational(s.re(v)))+abs(rational(s.im(v))))*R**power
                       for (power,),v in s.Poly(value,q,domain=s.QQ_I).terms())
            rows[i]+=amount
            if order==0:entry0=max(entry0,amount)
        row_bounds.append(max(rows))
    # Two explicit cofactor estimates; take the stronger generated bound.
    leibniz=F(factorial(112))*entry0**111/point_lower
    hadamard=F(112)*F(111)**56*entry0**111/point_lower
    inverse=min(leibniz,hadamard)
    first=inverse**2*row_bounds[1]
    second=2*inverse**3*row_bounds[1]**2+inverse**2*row_bounds[2]
    assert min(inverse,first,second)>0
    D=matrix(src['scales112'])
    scale=max(number_bound(D[i,i]) for i in range(112))
    physical_factor=scale**2*number_bound(1/N)
    actual=[physical_factor*v for v in [inverse,first,second]]
    # A fixed source circle frame is independent of q.  Its all-angle bounds
    # therefore only conjugate the same derivatives; no frame derivative enters.
    circle={z['axis']:F(z['uniform_infinity_norm_for_abs_parameter_le1']) for z in src['native_rotation_checks']}
    common_frame=circle[1]*circle[2]
    result={'scope':'STRIKE_UNIFORM_SOURCE_MOMENTUM_POLE_DOMAIN_AND_ACTUAL_RAY_INVERSE_DERIVATIVES',
        'source_sha256':hashlib.sha256((HERE/'source.json').read_bytes()).hexdigest(),
        'q_domain':['-1/32768','1/32768'],'physical_momentum_ball':'|k|<=sqrt(2)/32768',
        'all_q_zero_included':True,'all_native_factor_margins':margins,
        'complete_frequency_degree':frequency_degree,'scalar_G9_over_N_determinant':str(gdet),
        'normalized112_circle_abs_x5_determinant_lower':str(lower),
        'all_direction_pole_domain':'native all-angle covariance on the transported original section; |lambda_pole|<5c<5; Re lambda>=5 regular',
        'common_x_point':str(point),'common_physical_lambda':str(s.expand(c*point)),
        'normalized112_determinant_lower_at_point':str(point_lower),
        'normalized112_max_entry_bound':str(entry0),
        'normalized112_q_derivative_row_norms':list(map(str,row_bounds)),
        'source_inverse_definition':'R(q)=adj(A(q))/det(A(q)); A=D complete112(x*,q) D/N, with source p0=c*x*, p3=i*sqrt(2)*q',
        'actual_inverse_definition':'P(q)=D R(q) D/N=M112(q)^(-1), with both inverse identities',
        'normalized_inverse_bound':str(inverse),'normalized_first_derivative_bound':str(first),
        'normalized_second_derivative_bound':str(second),
        'physical_coordinate_scale_factor_bound':str(physical_factor),
        'actual_M112_inverse_and_q_derivative_bounds':list(map(str,actual)),
        'derivative_identities':['Rprime=-R Aprime R','Rsecond=2R Aprime R Aprime R-R Asecond R',
            'Pprime=-P Mprime P','Psecond=2P Mprime P Mprime P-P Msecond P'],
        'physical_signed_ray':'k=s*n with fixed unit n; q=s/sqrt(2); d/ds=(1/sqrt(2))*d/dq, d2/ds2=(1/2)*d2/dq2',
        'actual_signed_ray_derivative_bounds':['C0','C1/sqrt(2)','C2/2'],
        'Taylor_readback':'For q,q+h and their segment inside the q interval, ||P(q+h)-P(q)-hPprime(q)||_infinity <= C2*h^2/2. For physical signed shift ds, bound=C2*ds^2/4.',
        'all_angle_native_frame_infinity_bound':str(common_frame),
        'frame_scope':'The same direction is fixed for ray derivatives; this is not a derivative of a chosen global angular chart.',
        'direct_transfer':{'incoming_q':src['original_incoming_q'],'outgoing_q':src['outgoing_q'],
            'external_q':src['external_q_magnitude'],'frequency':str(s.expand(c*point)),
            'light_ball_plus_fixed_external_margin':src['light_plus_fixed_external_strict_margin'],
            'whole_light_times_3_over_2_margin':src['whole_light_one_and_half_strict_margin']},
        'no_experiment_units_or_kinetic_beta_assigned':True,
        'elapsed_seconds':round(time.monotonic()-began,3)}
    (HERE/'domain.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS source actual112 inverse, first/second ray derivatives and uniform Taylor consumer',result['elapsed_seconds'],flush=True)


if __name__=='__main__':main()
