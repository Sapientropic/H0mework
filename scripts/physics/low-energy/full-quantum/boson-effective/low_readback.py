#!/usr/bin/env python3
"""Actual low-momentum field and source maps return the degree-two kernel to all289 equations."""
import importlib.util
from ast import literal_eval
import json
from pathlib import Path
import time
import sympy as s
HERE=Path(__file__).resolve().parent;BASE=HERE.parents[1]
spec=importlib.util.spec_from_file_location('boson_low_builder',HERE/'compute.py');built=importlib.util.module_from_spec(spec);spec.loader.exec_module(built)
clean,encode=built.clean,built.encode
u,q=s.symbols('u q',real=True);lam,k=s.symbols('lam k',real=True);start=time.monotonic()
r=json.loads((HERE/'receipt.json').read_text());a=json.loads((BASE/'active-gauge/receipt.json').read_text());quo=json.loads((BASE/'active-gauge/quotient.json').read_text())
N=s.sympify(a['source_lapse']);momenta=[N*s.sqrt(2)*u,0,0,s.I*s.sqrt(2)*q];ret=r['original_retained103'];sc=list(map(s.sympify,r['normalized_field_scaling']))
heavy=[ret.index(i) for i in r['heavy42_source_indices']];keep=[ret.index(i) for i in r['local61_source_indices']]
def read(record):return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(v,locals={'u':u,'q':q}) for i,j,v in record['entries']})
def truncate(M):
 return clean(M).applyfunc(lambda v:sum((c*u**power[0]*q**power[1] for power,c in s.Poly(v,u,q).terms() if sum(power)<=2),s.S.Zero))
K=s.SparseMatrix(103,103,{(i,j):s.expand(s.sympify(v.replace('lambda','lam'),locals={'lam':lam,'k':k}).subs({lam:momenta[0],k:s.sqrt(2)*q})*sc[i]*sc[j]/N) for i,j,v in quo['quotient_operator_103_by_103']})
G0=read(r['origin_heavy_inverse']);D=K.extract(heavy,heavy);delta=clean(D-D.subs({u:0,q:0}));G2=clean(G0-G0*delta*G0+G0*delta*G0*delta*G0)
low=clean(sum((read(value)*u**literal_eval(power)[0]*q**literal_eval(power)[1] for power,value in r['local61_coefficients_degree2'].items()),s.SparseMatrix.zeros(61)))
E=s.MutableSparseMatrix(103,61,{(i,j):1 for j,i in enumerate(keep)});WB=truncate(-G2*K.extract(heavy,keep))
for (i,j),v in WB.todok().items():E[heavy[i],j]=v
full=s.MutableSparseMatrix(289,61,{})
for (i,j),v in E.todok().items():full[ret[i],j]=sc[i]*v
for step in reversed(a['algebraic_Schur_steps']):
 for row,col,power,value in step['write_back_auxiliary_from_retained']:
  coefficient=s.sympify(value)*s.prod(p**a for p,a in zip(momenta,power))
  if coefficient:full[row,:]+=coefficient*full[col,:]
 for row in step['eliminated_fields']:full[row,:]=truncate(full[row,:])
Q=s.SparseMatrix(103,112,{(i,j):s.sympify(v.replace('lambda','lam'),locals={'lam':lam,'k':k}).subs({lam:momenta[0],k:s.sqrt(2)*q}) for i,j,v in quo['quotient_readback_103_by_112']})
J112=clean(Q.subs({u:-u,q:-q},simultaneous=True).T*s.SparseMatrix(103,61,{(i,j):N/sc[i] for j,i in enumerate(keep)}));J=s.MutableSparseMatrix(289,61,{})
for (i,j),v in J112.todok().items():J[i+9,j]=v
broken=a['Ward_constraint_elimination']['broken_parameter_columns'];T=s.MutableSparseMatrix(121,9,{})
for i,j,power,v in a['source_primitive_gauge_tangent']:
 if i<121 and j in broken:T[i,broken.index(j)]+=s.sympify(v)*s.prod((-p)**a for p,a in zip(momenta,power))
for j in range(9):J[j,:]=-(T[9:,j].T*J112)
H=built.source_matrix(a['Fourier_Jacobi_entries'],289,momenta)
residual=clean(H*full-J*low)
assert truncate(residual)==s.zeros(289,61)
minimum=min(sum(power) for value in residual.todok().values() for power,c in s.Poly(value,u,q).terms() if c)
assert minimum==3
rank=low.subs({u:0,q:0}).rank();assert rank==56
report={'scope':'SOURCE61_LOW_MOMENTUM_EFFECTIVE_SYSTEM_WHOLE289_ORDER2','source_sha256':a['source_sha256'],
 'whole289_low_field_lift':encode(full),'whole289_low_source_injection':encode(J),'low61_effective_operator':encode(low),
 'whole289_residual_minimal_total_degree':minimum,'constant61_rank':rank,'constant61_kernel_dimension':61-rank,
 'light6_source_fields':[a['fields'][i] for i in r['light6_source_indices']],
 'heavy42_origin_determinant':str(s.factor(D.subs({u:0,q:0}).det(method='domain-ge'))),
 'elapsed_seconds':round(time.monotonic()-start,3)}
(HERE/'low-readback-receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({key:report[key] for key in ['scope','whole289_residual_minimal_total_degree','constant61_rank','constant61_kernel_dimension','heavy42_origin_determinant','elapsed_seconds']},indent=2),flush=True)
