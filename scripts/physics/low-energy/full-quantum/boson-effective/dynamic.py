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
A=DomainMatrix.from_Matrix(reduced).convert_to(field);B=DomainMatrix.from_Matrix(reduced_rhs).convert_to(field)
print('solve source canonical dynamic block',len(kept),'with original rows',len(ids),flush=True)
num,den=A.solve_den(B,method='rref');assert A*num==B*den
raw=(canonical*num.to_Matrix()/field.to_sympy(den)).applyfunc(s.cancel)
assert (sub*raw-rhs).applyfunc(s.cancel)==s.zeros(len(ids),1)
print('solved',round(time.monotonic()-start,2),flush=True)
# Original delta g00=-2 N delta e00 and the original field scaling e00=N*normalized e00.
response=s.cancel(4*n**3*raw[slot])
row={str(j):str(s.factor(raw[i])) for i,j in enumerate(ids) if raw[i]}
def encode(M):return {'shape':list(M.shape),'entries':[[int(i),int(j),str(s.factor(v))] for (i,j),v in s.SparseMatrix(M).todok().items()]}
# Full physical field coefficients and exact source writeback.
full=s.MutableSparseMatrix(289,1,{})
for j,index in enumerate(ids):full[ret[index],0]=-2*n*scale[index]*raw[j]
for step in reversed(a['algebraic_Schur_steps']):
 for i,j,power,value in step['write_back_auxiliary_from_retained']:
  coefficient=s.sympify(value)*(n*s.sqrt(2)*u)**power[0]*(s.I*s.sqrt(2)*q)**power[3] if not any(power[1:3]) else 0
  if coefficient:full[i,0]+=coefficient*full[j,0]
 for i in step['eliminated_fields']:full[i,0]=s.cancel(full[i,0])
original=s.MutableSparseMatrix(289,289,{})
for i,j,power,value in a['Fourier_Jacobi_entries']:
 if not any(power[1:3]): original[i,j]+=s.sympify(value)*(n*s.sqrt(2)*u)**power[0]*(s.I*s.sqrt(2)*q)**power[3]
source=s.zeros(289,1);source[ret[source_index],0]=-2*n
assert (original*full-source).applyfunc(s.cancel)==s.zeros(289,1)
assert s.cancel(-2*n*full[ret[source_index],0]-response)==0
print('PASS dynamic g00 actual289 equations',flush=True)
static=json.loads((BASE/'metric-response/receipt.json').read_text())
old=next(s.sympify(v,locals={'q':q}) for i,j,v in static['metric_inverse_response']['entries'] if i==0 and j==0)
assert s.cancel(response.subs(u,0)-old)==0
u_axis=s.factor(s.cancel(response.subs(q,0)));q_axis=s.factor(s.cancel(response.subs(u,0)))
# A joint low-frequency test follows rays u=r q; retain possible sound denominators.
r=s.symbols('r',real=True)
ray=s.factor(s.limit(response.subs(u,r*q),q,0));ray_next=s.factor(s.limit((response.subs(u,r*q)-ray)/q**2,q,0))
report={'scope':'SOURCE_DYNAMIC_G00_PROPAGATOR_WITH_WHOLE289_READBACK','u_convention':'lambda=N sqrt(2) u','q_convention':'k=sqrt(2) q',
 'source_convention':'+J00 delta g00; induced response is minus the inverse response below',
 'source_sha256':a['source_sha256'],'dynamic_metric_inverse_response':str(s.factor(response)),
 'full289_dynamic_metric_green':encode(full),'all289_source_rows':True,'matches_old_static_response':True,
 'time_axis':str(u_axis),'space_axis':str(q_axis),'low_frequency_ray_variable':'u=r q',
 'ray_leading':str(ray),'ray_quadratic':str(ray_next),'elapsed_seconds':round(time.monotonic()-start,3)}
(HERE/'dynamic-receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['scope','time_axis','space_axis','ray_leading','ray_quadratic','elapsed_seconds']},indent=2),flush=True)
