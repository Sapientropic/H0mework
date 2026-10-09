#!/usr/bin/env python3
"""Source coefficient domination, with same-domain noise consumers."""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sympy as s

HERE=Path(__file__).resolve().parent;FQ=HERE.parent
x=s.symbols('x',real=True)


def interval(r):return tuple(map(F,r['rational']))


def main():
    src=json.loads((HERE/'source.json').read_text())
    out=[]
    for block in src['all103_source_factor_blocks']:
        for factor in block['factors']:
            p=s.Poly(s.sympify(factor['polynomial'],locals={'x':x}),x,domain=s.QQ)
            cs=p.all_coeffs();d=p.degree();rad=1
            while abs(cs[0])*rad**d<=sum(abs(a)*rad**(d-j) for j,a in enumerate(cs[1:],1)):rad+=1
            margin=abs(cs[0])*rad**d-sum(abs(a)*rad**(d-j) for j,a in enumerate(cs[1:],1))
            assert margin>0 and rad<=5
            out.append({'original_block_indices':block['indices'],'polynomial':str(p.as_expr()),
                'multiplicity':factor['multiplicity'],'degree':d,'strict_root_modulus_bound':rad,
                'coefficient_domination_margin':str(margin)})
    c2=F(108,125)
    assert c2<1
    # Every possible pole of the original complete112 is in |lambda|<5c<5.
    # This is a regular half-plane statement, not yet a claim of source excitation.
    old=json.loads((FQ/'packet-gauge-noise/intervals.json').read_text())
    moments=json.loads((FQ/'packet-current-hessian/integrals.json').read_text())
    nu=interval(moments['noise_zero'])
    slope=interval(old['generated_intervals']['noise_derivative'])
    eta=F(5);abs2=2*eta**2;radius=F(1,90000)
    A=4*(9/eta+4/eta**2)
    C=4*(6/eta+20/eta**2+16/eta**3)
    assert 49<abs2
    ja,za=F(1),F(4,7)
    error0=2*radius*A*ja+radius**2*A*A
    error1=2*radius*(C*ja+A*za)+2*radius**2*A*C
    bounds0=[nu[0]/abs2-error0,nu[1]/abs2+error0]
    bounds1=[slope[0]/abs2-error1,slope[1]/abs2+error1]
    assert F(9,10)<bounds0[0]<bounds0[1]<F(91,100)
    assert F(47,1000)<bounds1[0]<bounds1[1]<F(49,1000)
    result={'scope':'STRIKE_ORIGINAL_COMPLETE112_POLE_BOUND_AND_COMMON_NOISE_DOMAIN',
        'source_input_sha256':hashlib.sha256((HERE/'source.json').read_bytes()).hexdigest(),
        'complete112_scalar9_has_no_frequency_denominator':True,
        'auxiliary168_have_no_frequency_denominator':True,
        'all_original_factors':out,
        'dimensionless_x_strict_root_modulus_bound':5,
        'physical_clock':'lambda=(6*sqrt(15)/25)*x; original t is unchanged',
        'physical_strict_root_modulus_bound':'5*c < 5, c^2=108/125',
        'closed_safe_physical_halfplane':'Re(lambda)>=5',
        'excitation_scope':'All possible original112 poles. Actual X0/X1 pole survival is a separate numerator calculation.',
        'common_noise_consumer':{'z':'5*(1-I)','w':'5*(1-I)','physical_transfer_radius':str(radius),
            'unvaried_interval':list(map(str,bounds0)),'derivative_interval':list(map(str,bounds1)),
            'unvaried_simple_strict_interval':['9/10','91/100'],
            'derivative_simple_strict_interval':['47/1000','49/1000'],
            'integrated_J_transfer_bound':str(A),'integrated_Z_transfer_bound':str(C),
            'unvaried_error':str(error0),'derivative_error':str(error1),
            'derivation':'Actual PacketGaugeDynamics all-time position bounds evaluated at eta=5; no new time truncation or UV cutoff.'}}
    (HERE/'halfplane.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS complete112 source-root domination; all possible poles in |lambda|<5c<5')
    print('PASS common actual double-Laplace noise: .9<N<.91 and .047<Nprime<.049')


if __name__=='__main__':main()
