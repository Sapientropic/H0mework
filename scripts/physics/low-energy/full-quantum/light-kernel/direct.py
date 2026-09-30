#!/usr/bin/env python3
"""Return the light jet to the one original103 source and verify its first determinants."""
import importlib.util
import json
from pathlib import Path
import time
import sympy as s
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('light_source_jet',HERE/'compute.py')
built=importlib.util.module_from_spec(spec);spec.loader.exec_module(built)
u,q=built.u,built.q
decode,encode,clean,zero,homogeneous,truncate=built.decode,built.encode,built.clean,built.zero,built.homogeneous,built.truncate
start=time.monotonic()
r=json.loads((HERE/'receipt.json').read_text());p=json.loads((HERE/'propagation-receipt.json').read_text())
old=json.loads((HERE.parent/'boson-effective/receipt.json').read_text())
actual=json.loads((HERE.parents[1]/'active-gauge/receipt.json').read_text())
quotient=json.loads((HERE.parents[1]/'active-gauge/quotient.json').read_text())
prop=json.loads((HERE.parents[1]/'active-gauge/propagation.json').read_text())
N=s.sympify(actual['source_lapse']);sc=list(map(s.sympify,old['normalized_field_scaling']));ret=old['original_retained103']
lam,k=s.symbols('lam k',real=True)
K=s.SparseMatrix(103,103,{(i,j):s.expand(s.sympify(v.replace('lambda','lam'),locals={'lam':lam,'k':k}).subs({lam:N*s.sqrt(2)*u,k:s.sqrt(2)*q})*sc[i]*sc[j]/N)
    for i,j,v in quotient['quotient_operator_103_by_103']})
light=[ret.index(i) for i in r['light5_source_indices']];heavy=[i for i in range(103) if i not in light]
D=K.extract(heavy,heavy);C=K.extract(heavy,light);B=K.extract(light,heavy);A=K.extract(light,light)
D0=D.subs({u:0,q:0});G0=s.SparseMatrix(D0.inv(method='DM'))
zero(D0*G0-s.eye(98));zero(G0*D0-s.eye(98))
Ds=[homogeneous(D,n) for n in range(3)];Cs=[homogeneous(C,n) for n in range(3)]
W=[clean(-G0*Cs[0])]
for n in range(1,3):W.append(clean(-G0*(Cs[n]+sum((Ds[j]*W[n-j] for j in range(1,n+1)),s.zeros(98,5)))))
write=clean(sum(W,s.zeros(98,5)))
S=truncate(A+B*write,2)
zero(S-decode(r['light5_degree2']))
E=s.MutableSparseMatrix(103,5,{(i,j):1 for j,i in enumerate(light)})
for (i,j),v in write.todok().items():E[heavy[i],j]=v
P=s.SparseMatrix(103,5,{(i,j):1 for j,i in enumerate(light)})
zero(truncate(K*E-P*S,2))
det0=s.factor(D0.det(method='domain-ge'));assert det0!=0
def minimum_part(f,weight):
    terms=s.Poly(f,u,q).terms()
    degree=min(weight[0]*power[0]+weight[1]*power[1] for power,c in terms if c)
    return degree,sum(c*u**power[0]*q**power[1] for power,c in terms if weight[0]*power[0]+weight[1]*power[1]==degree)
fullFirst={}
for weight in [(1,1),(2,1)]:
    degree=0;value=s.S.One
    for block in prop['blocks']:
        value*=s.sympify(block['constant'])
        for factor in block['factors']:
            polynomial=s.sympify(factor['polynomial'],locals={'u':u,'q':q})
            n,part=minimum_part(polynomial,weight)
            degree+=n*factor['multiplicity'];value*=part**factor['multiplicity']
    value=s.factor(value/det0)
    fullFirst[str(weight)]={'degree':degree,'polynomial':str(value)}
zero(s.Matrix([s.sympify(fullFirst['(1, 1)']['polynomial'],locals={'u':u,'q':q})-
    s.sympify(p['first_isotropic_characteristic'],locals={'u':u,'q':q})]))
slow=s.symbols('slow',real=True)
weighted=s.sympify(fullFirst['(2, 1)']['polynomial'],locals={'u':u,'q':q})
zero(s.Matrix([s.expand(weighted.subs({u:slow*q*q})/q**10)-s.sympify(p['quadratic_time_characteristic'],locals={'slow':slow})]))
print('PASS same original103 direct98 elimination; original full determinant first orders8/10 exactly match the light jet',flush=True)
report={'scope':'ONE_ORIGINAL103_COMPLEMENT_AND_FULL_SOURCE_LOW_CHARACTERISTICS',
 'heavy98_source_indices':[ret[i] for i in heavy],'light5_source_indices':r['light5_source_indices'],
 'heavy98_origin_inverse':encode(G0),'heavy98_origin_determinant':str(det0),
 'direct103_field_jet':encode(E),'two_elimination_routes_same_light_jet':True,
 'original103_order2_residual_zero':True,'full_source_determinant_first_terms':fullFirst,
 'first_terms_match_light_jet':True,'elapsed_seconds':round(time.monotonic()-start,3)}
(HERE/'direct-receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['scope','heavy98_origin_determinant','elapsed_seconds']},indent=2),flush=True)
