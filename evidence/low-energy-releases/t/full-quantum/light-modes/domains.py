#!/usr/bin/env python3
"""The original full characteristic factors generate real root domains and one 98-unit chart."""
import hashlib
import json
from pathlib import Path
import sympy as s

HERE=Path(__file__).resolve().parent;BASE=HERE.parents[1];ROOT=HERE.parents[4]
u,q,v,w,r=s.symbols('u q v w r',real=True)
actual=json.loads((BASE/'active-gauge/receipt.json').read_text())
prop=json.loads((BASE/'active-gauge/propagation.json').read_text())
quot=json.loads((BASE/'active-gauge/quotient.json').read_text())
old=json.loads((HERE.parent/'boson-effective/receipt.json').read_text())
light=json.loads((HERE.parent/'light-kernel/direct-receipt.json').read_text())
for path,digest in actual['source_sha256'].items():
    assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path

def encode(M):
    return {'shape':list(M.shape),'entries':[[int(i),int(j),str(s.factor(x))]
        for (i,j),x in s.SparseMatrix(M).todok().items()]}

def decode(record):
    return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(x) for i,j,x in record['entries']})

def polynomial_norm(P,x,y):
    return sum(abs(c)*2**power[0] for power,c in s.Poly(P,x,y).terms())

def squared_time(P):
    result=0
    for (a,b),c in s.Poly(P,u,q).terms():
        assert a%2==0
        result+=c*v**(a//2)*q**b
    return s.expand(result)

factors=[]
for block in prop['blocks']:
    for entry in block['factors']:
        P=s.sympify(entry['polynomial'],locals={'u':u,'q':q})
        factors.append((P,squared_time(P),entry['multiplicity']))
source_factors=prop['blocks'][-1]['factors']
names=['vector_real','vector_phase','axial_phase','quadratic_pair']
selections=[0,4,5,1]
orders=[1,1,1,2]
branches={};all_bounds=[s.S.One]
for name,index,order in zip(names,selections,orders):
    factor=s.sympify(source_factors[index]['polynomial'],locals={'u':u,'q':q})
    assert sum(multiplicity for F,Q,multiplicity in factors if F==factor)==1
    P=squared_time(factor)
    squared=0
    for (a,b),c in s.Poly(P,v,q).terms():
        assert b%2==0
        squared+=c*v**a*w**(b//2)
    substituted=s.cancel(squared.subs(v,w**order*r)/w**order)
    initial=s.Poly(substituted.subs(w,0),r)
    assert initial.degree()==1
    leading=initial.coeff_monomial(r);center=-initial.coeff_monomial(1)/leading
    remainder=s.cancel((substituted/leading-(r-center))/w)
    assert s.Poly(remainder,r,w).is_multivariate
    assert s.expand(s.diff(squared,v).subs(v,w**order*r)-leading*(1+w*s.diff(remainder,r)))==0
    bound=polynomial_norm(remainder,r,w)
    derivative_bound=polynomial_norm(s.diff(remainder,r),r,w)
    epsilon=1/(40*(1+bound+derivative_bound))
    assert abs(center)+s.Rational(1,20)<2 and abs(center)>s.Rational(1,20)
    assert epsilon>0
    all_bounds.append(epsilon)
    separated=[]
    for num,(F,Q,multiplicity) in enumerate(factors):
        if F==factor:
            assert multiplicity==1
            continue
        pull=s.Poly(Q.subs(v,q**(2*order)*r),q)
        degree=min(power[0] for power,c in pull.terms() if c)
        normal=s.cancel(pull.as_expr()/q**degree)
        principal=s.Poly(normal.subs(q,0),r)
        assert principal.degree()<=1
        margin=abs(principal.eval(center))-abs(principal.coeff_monomial(r))/20
        assert margin>0,(name,num,principal,center)
        rest=s.cancel((normal-principal.as_expr())/q)
        bound_rest=polynomial_norm(rest,r,q)
        threshold=s.Min(1,margin/(2*(1+bound_rest)))
        assert threshold>0
        all_bounds.append(threshold)
        separated.append({'factor':num,'q_power':degree,'origin_polynomial':str(principal.as_expr()),
            'strict_origin_margin':str(margin),'remainder_bound':str(bound_rest),'q_threshold':str(threshold)})
    branches[name]={'full_source_factor':str(factor),'squared_time_factor':str(squared),
        'v_scaling_power':order,'r_origin':str(center),'source_linear_coefficient':str(leading),
        'normalized_remainder':str(remainder),'selected_factor_has_multiplicity_one':True,
        'full_time_derivative_identity':'partial_u F = 2 u * source_linear_coefficient * (1+w partial_r remainder)',
        'source_derivative_identity_verified':True,
        'remainder_coefficients':[[int(a),int(b),str(c)] for (a,b),c in s.Poly(remainder,r,w).terms() if c],
        'remainder_bound':str(bound),'r_derivative_bound':str(derivative_bound),'w_threshold':str(epsilon),
        'root_interval_half_width':'1/20','other_factors_nonzero':separated}
    print('generated unique root interval',name,'r0=',center,'w<=',epsilon,flush=True)

# Source G0 and the actual normalized98 polynomial give one uniform matrix-unit neighborhood.
N=s.sympify(actual['source_lapse']);lam,k=s.symbols('lam k',real=True)
ret=old['original_retained103'];sc=list(map(s.sympify,old['normalized_field_scaling']))
K=s.SparseMatrix(103,103,{(i,j):s.expand(s.sympify(x.replace('lambda','lam'),locals={'lam':lam,'k':k}).subs({lam:N*s.sqrt(2)*u,k:s.sqrt(2)*q})*sc[i]*sc[j]/N)
    for i,j,x in quot['quotient_operator_103_by_103']})
heavy=[ret.index(i) for i in light['heavy98_source_indices']]
D=K.extract(heavy,heavy);D0=D.subs({u:0,q:0});G0=decode(light['heavy98_origin_inverse'])
assert G0*D0==D0*G0==s.eye(98)
GD=s.SparseMatrix((G0*(D-D0)).applyfunc(s.expand));row_bounds=[s.S.Zero]*98
for (i,j),x in GD.todok().items():
    for (a,b),c in s.Poly(x,u,q).terms():
        assert a+b>=1
        row_bounds[i]+=(abs(s.re(c))+abs(s.im(c)))*2**a
matrix_bound=max(row_bounds);matrix_threshold=1/(2*(1+matrix_bound));all_bounds.append(matrix_threshold)
print('generated original98 common unit domain',matrix_threshold,'matrix bound',matrix_bound,flush=True)

# The actual g00 numerator is separated from zero on the axial branch.
dynamic=json.loads((HERE.parent/'boson-effective/dynamic-receipt.json').read_text())
response=s.sympify(dynamic['dynamic_metric_inverse_response'],locals={'u':u,'q':q})
numerator,denominator=s.fraction(s.cancel(response))
numerator=s.cancel(numerator/s.sqrt(30))
assert all(a%2==0 for (a,b),c in s.Poly(numerator,u,q).terms())
num_v=squared_time(numerator)
normal=s.cancel(num_v.subs(v,q*q*r)/q**2)
principal=s.Poly(normal.subs(q,0),r)
center=s.sympify(branches['axial_phase']['r_origin'])
margin=abs(principal.eval(center))-abs(principal.coeff_monomial(r))/20
assert margin>0
rest=s.cancel((normal-principal.as_expr())/q)
nbound=polynomial_norm(rest,r,q);nthreshold=s.Min(1,margin/(2*(1+nbound)))
all_bounds.append(nthreshold)
epsilon=min(all_bounds)/2
assert epsilon>0
# One explicit nonzero momentum lies in the common source domain.
sample=s.Rational(1,2)
while sample>=epsilon:sample/=2
report={'scope':'FULL_SOURCE_FOUR_LIGHT_ROOTS_EXPLICIT_COMMON_DOMAIN',
 'source_sha256':actual['source_sha256'],'branches':branches,
 'source_full_determinant_constant':str(s.prod(s.sympify(block['constant']) for block in prop['blocks'])),
 'source_full_determinant_factors':[{'polynomial':str(F),'multiplicity':multiplicity} for F,Q,multiplicity in factors],
 'original98_G_delta_row_bound':str(matrix_bound),'original98_q_threshold':str(matrix_threshold),
 'axial_g00_normalized_numerator':str(normal),'axial_g00_origin_numerator':str(principal.as_expr()),
 'axial_g00_strict_margin':str(margin),'axial_g00_remainder_bound':str(nbound),
 'axial_g00_q_threshold':str(nthreshold),'common_positive_q_threshold':str(epsilon),
 'actual_nonzero_q':str(sample),'u_bound_along_branches':'|u|<=2q; 0<q<common threshold',
 'all_other_full_factors_nonzero_on_each_branch':True,
 'original98_unit_from_row_norm':True,'actual_g00_numerator_nonzero_at_axial_root':True}
(HERE/'domain-receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS full source domain',epsilon,'actual nonzero q',sample,flush=True)
