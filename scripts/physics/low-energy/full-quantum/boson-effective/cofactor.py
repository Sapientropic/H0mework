"""Actual dynamic metric response from the original source's 33-coordinate block."""
import json
from pathlib import Path
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix
HERE=Path(__file__).resolve().parent;BASE=HERE.parents[1]
a=json.loads((BASE/'active-gauge/receipt.json').read_text());quo=json.loads((BASE/'active-gauge/quotient.json').read_text());prop=json.loads((BASE/'active-gauge/propagation.json').read_text())
u,q=s.symbols('u q',real=True);lam,k=s.symbols('lam k',real=True);n=s.sympify(a['source_lapse']);start=time.monotonic()
ret=quo['retained_original_fields'];scale=list(map(s.sympify,prop['constant_diagonal_field_scaling']))
K=s.SparseMatrix(103,103,{(i,j):s.expand(s.sympify(v.replace('lambda','lam'),locals={'lam':lam,'k':k}).subs({lam:n*s.sqrt(2)*u,k:s.sqrt(2)*q})*scale[i]*scale[j]/n) for i,j,v in quo['quotient_operator_103_by_103']})
source_index=next(j for j,i in enumerate(ret) if a['fields'][i]=={'group':'coframe','coordinate':[0,0]})
ids=next(block['quotient_indices'] for block in prop['blocks'] if source_index in block['quotient_indices']);slot=ids.index(source_index)
sub=K.extract(ids,ids);rhs=s.zeros(len(ids),1);rhs[slot]=1
# The same original canonical graph reduces this source without altering its
# complete independent-dual equations. In normalized103 coordinates it is integral.
kept=[i for i,index in enumerate(ids) if a['fields'][ret[index]]['group']!='dual_H']
canonical=s.MutableSparseMatrix(len(ids),len(kept),{})
for j,i in enumerate(kept):canonical[i,j]=1
for i,index in enumerate(ids):
 field0=a['fields'][ret[index]]
 if field0['group']=='dual_H':
  imaginary,spin,color=field0['coordinate'];partner={'group':'primal_H','coordinate':[imaginary,(spin+2)%4,color]}
  fullindex=next(j for j in ids if a['fields'][ret[j]]==partner)
  partnerrow=ids.index(fullindex)
  canonical[i,kept.index(partnerrow)]=s.simplify((-1)**imaginary*s.sqrt(2)*scale[fullindex]/scale[index])
canonical=s.SparseMatrix(canonical)
assert not any(value.has(s.sqrt(2)) for value in canonical.todok().values())
reduced=canonical.T*sub*canonical;reduced_rhs=canonical.T*rhs

field=s.QQ_I.poly_ring(u,q)
slot_reduced=kept.index(slot)
minor_indices=[i for i in range(len(kept)) if i!=slot_reduced]
print('source canonical determinants',len(kept),len(minor_indices),flush=True)
D=DomainMatrix.from_Matrix(reduced).convert_to(field).det()
print('source denominator generated',round(time.monotonic()-start,2),flush=True)
num=DomainMatrix.from_Matrix(reduced.extract(minor_indices,minor_indices)).convert_to(field).det()
response=s.factor(s.cancel(4*n**3*field.to_sympy(num)/field.to_sympy(D)))
assert response
u_axis=s.factor(s.cancel(response.subs(q,0)));q_axis=s.factor(s.cancel(response.subs(u,0)))
r=s.symbols('r',real=True)
ray=s.factor(s.limit(response.subs(u,r*q),q,0));ray_next=s.factor(s.limit((response.subs(u,r*q)-ray)/q**2,q,0))
report={'scope':'SOURCE_DYNAMIC_G00_COFACTOR_PROPAGATOR','source_sha256':a['source_sha256'],'dynamic_metric_inverse_response':str(response),'source_reduced_determinant':str(s.factor(field.to_sympy(D))),'source_cofactor':str(s.factor(field.to_sympy(num))),'time_axis':str(u_axis),'space_axis':str(q_axis),'ray_leading':str(ray),'ray_quadratic':str(ray_next),'elapsed_seconds':round(time.monotonic()-start,3)}
(HERE/'cofactor-receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2),flush=True)
