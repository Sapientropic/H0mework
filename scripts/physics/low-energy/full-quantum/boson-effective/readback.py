#!/usr/bin/env python3
"""Full symbolic source response of the new boson kernel, including Ward source rows."""
import importlib.util
import json
from pathlib import Path
import time
import sympy as s
HERE=Path(__file__).resolve().parent;BASE=HERE.parents[1]
spec=importlib.util.spec_from_file_location('boson_effective_builder',HERE/'compute.py');built=importlib.util.module_from_spec(spec);spec.loader.exec_module(built)
clean,decode,encode=built.clean,built.decode,built.encode
u,q=s.symbols('u q',real=True);lam,k=s.symbols('lam k',real=True);start=time.monotonic()
a=json.loads((BASE/'active-gauge/receipt.json').read_text());quo=json.loads((BASE/'active-gauge/quotient.json').read_text());r=json.loads((HERE/'receipt.json').read_text())
N=s.sympify(a['source_lapse']);momenta=[N*s.sqrt(2)*u,0,0,s.I*s.sqrt(2)*q]
ret=r['original_retained103'];sc=list(map(s.sympify,r['normalized_field_scaling']));b=r['boson55_source_indices'];m=r['matter48_source_indices']
names={'u':u,'q':q}
def read(record):return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(v,locals=names) for i,j,v in record['entries']})
W=read(r['matter48_writeback_from_boson55']);S=read(r['effective_boson55'])
full=s.MutableSparseMatrix(289,55,{})
for j,i in enumerate(b):full[i,j]=sc[ret.index(i)]
for (i,j),v in W.todok().items():full[m[i],j]=sc[ret.index(m[i])]*v
for step in reversed(a['algebraic_Schur_steps']):
 for row,col,power,value in step['write_back_auxiliary_from_retained']:
  coefficient=s.sympify(value)*s.prod(p**a for p,a in zip(momenta,power))
  if coefficient:full[row,:]+=coefficient*full[col,:]
 for row in step['eliminated_fields']:full[row,:]=full[row,:].applyfunc(s.cancel)
print('source original289 field lift constructed',flush=True)
Q=s.SparseMatrix(103,112,{(i,j):s.sympify(v.replace('lambda','lam'),locals={'lam':lam,'k':k}).subs({lam:momenta[0],k:s.sqrt(2)*q}) for i,j,v in quo['quotient_readback_103_by_112']})
sectionSource=s.SparseMatrix(103,55,{(ret.index(i),j):N/sc[ret.index(i)] for j,i in enumerate(b)})
source112=clean(Q.subs({u:-u,q:-q},simultaneous=True).T*sectionSource)
J=s.MutableSparseMatrix(289,55,{})
for (i,j),v in source112.todok().items():J[i+9,j]=v
broken=a['Ward_constraint_elimination']['broken_parameter_columns']
T=s.MutableSparseMatrix(121,9,{})
for i,j,power,v in a['source_primitive_gauge_tangent']:
 if i<121 and j in broken:T[i,broken.index(j)]+=s.sympify(v)*s.prod((-p)**a for p,a in zip(momenta,power))
for j in range(9):J[j,:]=-(T[9:,j].T*source112)
H=built.source_matrix(a['Fourier_Jacobi_entries'],289,momenta)
residual=H*full-J*S
nonzero={}
for (i,j),v in s.SparseMatrix(residual).todok().items():
 value=s.cancel(v)
 if value:nonzero[i,j]=value
assert not nonzero,list(nonzero.items())[:3]
print('PASS all(u,q) actual289 original field response and independently generated compatible bosonic source map',flush=True)
assert not J[m,:].todok()
aux=sorted(set(range(289))-set(range(121)));assert not J[aux,:].todok()
result={'scope':'ALL_AXIAL_MOMENTA_BOSON55_WHOLE289_SOURCE_RESPONSE','source_sha256':a['source_sha256'],
 'field_response_lift':encode(full),'source_injection':encode(J),'all289_factorization':'H289(p) F289x55(p)=J289x55(p) S55(p)',
 'source_injection_generated_from_original_symmetry_Q_and_Ward':True,'no_matter_or_auxiliary_forcing':True,
 'scalar_Ward_source_rows_retained':len(J[:9,:].todok()),'elapsed_seconds':round(time.monotonic()-start,3)}
(HERE/'readback-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({key:result[key] for key in ['scope','scalar_Ward_source_rows_retained','elapsed_seconds']},indent=2),flush=True)
