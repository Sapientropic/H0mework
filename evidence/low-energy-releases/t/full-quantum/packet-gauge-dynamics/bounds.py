#!/usr/bin/env python3
"""Exact polynomial Laplace bounds and an actual nonzero continuum consumer."""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import time
import sympy as s

HERE=Path(__file__).resolve().parent;FQ=HERE.parent


def record_interval(record):return tuple(map(F,record['rational']))


def decimal_endpoint(x, lower, digits=20):
    scale=10**digits
    numerator=x.numerator*scale
    value=numerator//x.denominator if lower else -(-numerator//x.denominator)
    return f'{value//scale}.{value%scale:0{digits}d}'


def main():
    started=time.monotonic()
    alpha,v,h,r1,r2,t,u,eta1,eta2=s.symbols('alpha v h r1 r2 t u eta1 eta2',positive=True)
    a1,a2=alpha*(2*h+r1),alpha*(2*h+r2)
    b=2*alpha*v
    z1,z2=b+2*v*a1*t,b+2*v*a2*u
    d1,d2=2*v*b*t+2*v**2*a1*t**2,2*v*b*u+2*v**2*a2*u**2

    def laplace(polynomial,variable,damping):
        return s.expand(sum(c*s.factorial(n)/damping**(n+1)
            for (n,),c in s.Poly(s.expand(polynomial),variable).terms()))

    L1,L2=laplace(z1,t,eta1),laplace(z2,u,eta2)
    D1,D2=laplace(d1,t,eta1),laplace(d2,u,eta2)
    rem=s.expand(d1*a2+a1*d2+z1*z2)
    integrated=laplace(laplace(rem,t,eta1),u,eta2)
    assert s.expand(integrated-(D1*a2/eta2+a1/eta1*D2+L1*L2))==0
    assert s.expand(D1-(4*alpha*v**2/eta1**2+4*v**2*a1/eta1**3))==0
    assert s.expand(L1-(2*alpha*v/eta1+2*v*a1/eta1**2))==0
    assert all(c>=0 for _,c in s.Poly(rem,alpha,v,h,r1,r2,t,u).terms())
    print('PASS source polynomial remainder moments and complete double-Laplace bound',flush=True)

    old_path=FQ/'packet-gauge-noise/intervals.json'
    moments_path=FQ/'packet-current-hessian/integrals.json'
    old=json.loads(old_path.read_text());moments=json.loads(moments_path.read_text())
    n2=record_interval(moments['raw_filtered_norm_squared'])
    variance=record_interval(moments['noise_zero'])
    variation=record_interval(old['generated_intervals']['variation_vector_norm_squared'])
    derivative=record_interval(old['generated_intervals']['noise_derivative'])
    N2=F(54,125);n_lower=F(457,1000)
    assert n2[0]>n_lower*n_lower
    assert F(0)<N2/n2[1]-1<=N2/n2[0]-1<F(4)
    assert N2<F(4,9) and F(3)<F(7,4)**2 and F(3,5)<F(4,5)**2
    Xpsi=(F(7,4)*N2+F(2,3)*F(4,5))/n_lower
    XHpsi=Xpsi+F(2,3)*F(4,5)/n_lower
    assert Xpsi<3 and XHpsi<4
    assert F(2)<F(3,2)**2 and F(3,2)/N2<4
    assert variance[1]<49 and variation[1]<16
    assert F(239,100)<derivative[0]<derivative[1]<F(12,5)
    c2=2*N2;absolute_frequency_squared=2*c2
    assert c2>F(9,10)**2 and absolute_frequency_squared>1
    A=4*(9/F(9,10)+4/F(9,10)**2)
    C=4*(6/F(9,10)+20/F(9,10)**2+16/F(9,10)**3)
    assert A<60 and C<214
    radius=F(1,90000)
    error=2*radius*(214*7+60*4)+2*radius**2*214*60
    lower=derivative[0]/absolute_frequency_squared-error
    upper=derivative[1]/absolute_frequency_squared+error
    assert F(4,3)<lower<upper<F(3,2)
    assert F(14,2**40)<radius**2
    zero_transform=[x/absolute_frequency_squared for x in derivative]
    baseline_error=2*7*60*radius+60**2*radius**2
    baseline_zero=[x/absolute_frequency_squared for x in variance]
    baseline=[baseline_zero[0]-baseline_error,baseline_zero[1]+baseline_error]
    assert 26<baseline[0]<baseline[1]<27
    print('PASS actual continuum transfer ball: 4/3 < double-Laplace noise derivative < 3/2',flush=True)
    result={'scope':'STRIKE_TRUE_ALL_TIME_NOISE_PARAMETER_DERIVATIVE_AND_DOUBLE_LAPLACE_CONSUMER',
        'source_inputs_sha256':{str(path.relative_to(FQ)):hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [old_path,moments_path]},
        'source_constants':{'alpha':'norm(K)/N^2=sqrt(2)/N^2','v':'norm(V)=N',
            'h':'norm(H psi)=sqrt(N^2/n^2-1); only the original H domain is used',
            'r_i':'norm(H_k_i)=N*norm(k_i)'},
        'whole_time_bounds':{'J0_i':'a_i=alpha*(2*h+r_i)',
            'Z_i':'b+2*v*a_i*abs(t); b=2*alpha*v',
            'J_epsilon_minus_J0':'abs(epsilon)*(b+2*v*a_i*abs(t))',
            'J_remainder':'epsilon^2*(2*v*b*abs(t)+2*v^2*a_i*t^2)',
            'noise_remainder':'epsilon^2*(d_left(t)*a_right+a_left*d_right(s)+z_left(t)*z_right(s))',
            'all_real_epsilon':True},
        'laplace_parameters':'z=eta1-i E1, w=eta2-i E2 with eta1,eta2>0 independently',
        'double_time_weight':'exp(-conjugate(z)*t-w*s)',
        'vector_Laplace_slope_bound':str(L1),
        'vector_Laplace_remainder_bound':str(D1),
        'double_Laplace_remainder_bound':str(integrated),
        'actual_zero_transfer_all_time_splice':'J_epsilon,0(t) is independent of t; derivative at every two times is exactly the original GaugeNoise t0 derivative.',
        'actual_nonzero_consumer':{
            'frequency':'z=w=(6*sqrt(15)/25)*(1-I), in original physical time',
            'frequency_absolute_square':str(absolute_frequency_squared),
            'zero_transfer_exact_interval':list(map(str,zero_transform)),
            'unvaried_zero_transfer_interval':list(map(str,baseline_zero)),
            'unvaried_noise_transfer_error':str(baseline_error),
            'unvaried_noise_interval_for_every_k_in_ball':list(map(str,baseline)),
            'unvaried_noise_decimal_interval':[decimal_endpoint(baseline[0],True),decimal_endpoint(baseline[1],False)],
            'unvaried_noise_decimal_endpoints_outward_rounded':True,
            'unvaried_noise_simple_strict_interval':['26','27'],
            'whole_physical_transfer_ball_radius':str(radius),
            'coarse_original_bounds':{'H_psi':2,'directional_x_psi':3,'directional_x_Hpsi':4,
                'J0_zero_transfer':7,'Z0_zero_transfer':4,'alpha':4,'N_and_v':1},
            'position_bounds_generated_from_original_packet':{'x_psi':str(Xpsi),'x_H_psi':str(XHpsi)},
            'integrated_J_transfer_Lipschitz_upper':60,'integrated_Z_transfer_Lipschitz_upper':214,
            'noise_derivative_transfer_error':str(error),
            'rigorous_interval_for_every_k_in_ball':list(map(str,[lower,upper])),
            'simple_strict_interval':['4/3','3/2'],
            'new_nonaxial_physical_transfer':['1/1048576','1/524288','3/1048576'],
            'no_new_UV_cutoff_or_time_tail_omitted':True},
        'frequency_scope':'A sesquilinear two-parameter Laplace Gram. No identification with Kernel one-ordered independent-dual +/-p response follows merely by the shared numerical frequency.',
        'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'bounds.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS double-Laplace source bound construction',result['elapsed_seconds'],flush=True)


if __name__=='__main__':main()
