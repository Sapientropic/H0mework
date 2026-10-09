#!/usr/bin/env python3
"""Exact full-source field lift and a nonzero axial pole leg from the actual metric source."""
import importlib.util
import json
from pathlib import Path
import time
import sympy as s
HERE=Path(__file__).resolve().parent;BASE=HERE.parents[1]
spec=importlib.util.spec_from_file_location('light_modes_coefficients',HERE.parent/'light-kernel/compute.py')
built=importlib.util.module_from_spec(spec);spec.loader.exec_module(built)
u,q=built.u,built.q;clean,zero,encode=built.clean,built.zero,built.encode
start=time.monotonic()
a=json.loads((BASE/'active-gauge/receipt.json').read_text())
quot=json.loads((BASE/'active-gauge/quotient.json').read_text())
old=json.loads((HERE.parent/'boson-effective/receipt.json').read_text())
domain=json.loads((HERE/'domain-receipt.json').read_text())
dynamic=json.loads((HERE.parent/'boson-effective/dynamic-receipt.json').read_text())
N=s.sympify(a['source_lapse']);ret=old['original_retained103'];sc=list(map(s.sympify,old['normalized_field_scaling']))
momenta=[N*s.sqrt(2)*u,0,0,s.I*s.sqrt(2)*q];lam,k=s.symbols('lam k',real=True)
K=s.SparseMatrix(103,103,{(i,j):s.expand(s.sympify(v.replace('lambda','lam'),locals={'lam':lam,'k':k}).subs({lam:momenta[0],k:s.sqrt(2)*q})*sc[i]*sc[j]/N)
    for i,j,v in quot['quotient_operator_103_by_103']})
F=s.MutableSparseMatrix(289,103,{(i,j):sc[j] for j,i in enumerate(ret)})
for step in reversed(a['algebraic_Schur_steps']):
    for row,col,power,value in step['write_back_auxiliary_from_retained']:
        coefficient=s.sympify(value)*s.prod(x**degree for x,degree in zip(momenta,power))
        if coefficient:F[row,:]+=coefficient*F[col,:]
F=clean(F)
Q=s.SparseMatrix(103,112,{(i,j):s.sympify(v.replace('lambda','lam'),locals={'lam':lam,'k':k}).subs({lam:momenta[0],k:s.sqrt(2)*q})
    for i,j,v in quot['quotient_readback_103_by_112']})
J112=clean(Q.subs({u:-u,q:-q},simultaneous=True).T*s.diag(*[N/x for x in sc]))
J=s.MutableSparseMatrix(289,103,{})
for (i,j),v in J112.todok().items():J[i+9,j]=v
broken=a['Ward_constraint_elimination']['broken_parameter_columns'];T=s.MutableSparseMatrix(121,9,{})
for i,j,power,v in a['source_primitive_gauge_tangent']:
    if i<121 and j in broken:T[i,broken.index(j)]+=s.sympify(v)*s.prod((-x)**degree for x,degree in zip(momenta,power))
for j in range(9):J[j,:]=-(T[9:,j].T*J112)
H=s.MutableSparseMatrix(289,289,{})
for i,j,power,v in a['Fourier_Jacobi_entries']:
    H[i,j]+=s.sympify(v)*s.prod(x**degree for x,degree in zip(momenta,power))
zero(H*F-J*K)
left=s.SparseMatrix(103,289,{(j,i):1/sc[j] for j,i in enumerate(ret)})
zero(left*F-s.eye(103))
print('PASS exact original289 field/source lift, with generated left inverse',flush=True)
factor=s.sympify(domain['branches']['axial_phase']['full_source_factor'],locals={'u':u,'q':q})
G=s.SparseMatrix(289,1,{(i,j):s.sympify(v,locals={'u':u,'q':q}) for i,j,v in dynamic['full289_dynamic_metric_green']['entries']})
leg=s.SparseMatrix((factor*G).applyfunc(s.cancel))
source=s.zeros(289,1);source[57]=-2*N
zero(H*leg-factor*source)
reader=-2*N*leg[57]
expected=s.cancel(factor*s.sympify(dynamic['dynamic_metric_inverse_response'],locals={'u':u,'q':q}))
zero(s.Matrix([reader-expected]))
remaining=set()
for value in leg.todok().values():
    den=s.fraction(s.cancel(value))[1]
    assert s.Poly(s.gcd(den,factor),u,q).total_degree()==0
    for other,power in s.factor_list(den,extension=s.sqrt(30))[1]:remaining.add(str(other))
# Every remaining denominator is a source nonzero coordinate or a numerical unit.
print('actual axial pole-leg remaining denominators',sorted(remaining),flush=True)
report={'scope':'EXACT_ORIGINAL289_ONSHELL_FIELD_LIFT_AND_AXIAL_POLE_LEG',
 'source_sha256':a['source_sha256'],'full_source103_operator':encode(K),
 'whole289_exact_field_lift':encode(F),'whole289_exact_source_injection':encode(J),
 'generated_field_left_inverse':encode(left),'whole289_exact_intertwining':True,
 'full_source103_zero_modes_return_nonzero_original_fields':True,
 'axial_source_factor':str(factor),'axial_original289_pole_leg':encode(leg),
 'axial_whole289_residual':encode(factor*source),'axial_metric_pole_numerator':str(s.factor(reader)),
 'axial_pole_leg_remaining_denominators':sorted(remaining),
 'axial_residue_normalization':'divide pole leg by partial_u of the same source factor; physical lambda residue multiplies N sqrt(2)',
 'elapsed_seconds':round(time.monotonic()-start,3)}
(HERE/'field-receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS actual full axial leg and nonzero original metric reader on the generated simple root',report['elapsed_seconds'],flush=True)
