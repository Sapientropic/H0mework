#!/usr/bin/env python3
"""Resolve the actual first/second-order light pencil and its original metric source."""
import importlib.util
import json
from pathlib import Path
import time
import sympy as s
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('light_origin_producer',HERE/'compute.py')
built=importlib.util.module_from_spec(spec);spec.loader.exec_module(built)
u,q=built.u,built.q
decode,encode,clean,zero,homogeneous,truncate=built.decode,built.encode,built.clean,built.zero,built.homogeneous,built.truncate
start=time.monotonic()
r=json.loads((HERE/'receipt.json').read_text())
old=json.loads((HERE.parent/'boson-effective/receipt.json').read_text())
back=json.loads((HERE.parent/'boson-effective/low-readback-receipt.json').read_text())
actual=json.loads((HERE.parents[1]/'active-gauge/receipt.json').read_text())
N=s.sympify(actual['source_lapse'])
S=decode(r['light5_degree2']);J=clean(homogeneous(S,1)/u);S2=homogeneous(S,2)
assert J.rank()==2
K=s.Matrix([[0,-1,0],[1,0,0],[1,0,0],[0,1,0],[0,0,1]])
zero(J*K)
P=s.Matrix.hstack(s.eye(5)[:,0:2],K)
assert P.det()==1
block=clean(P.T*S*P);L3=clean(K.T*S2*K)
zero(P.T*J*P-s.diag(s.Matrix([[0,4],[-4,0]]),s.zeros(3)))
det3=s.factor(L3.det());leading=s.factor(16*u*u*det3)
zero(s.Matrix([leading-homogeneous(s.Matrix([S.det(method='domain-ge')]),8)[0]]))
slow=s.symbols('slow',real=True)
quadraticTime=clean(J*slow+S2.subs({u:0,q:1}))
slowdet=s.factor(quadraticTime.det(method='domain-ge'))
print('FIRST ORDER rank2; second-order kernel3:',L3,flush=True)
print('degree8 characteristic:',leading,flush=True)
print('u=slow*q² degree10 characteristic:',slowdet,flush=True)
# Original physical g00 source is pulled through the actual same complement, retaining its contact.
e00=next(i for i,field in enumerate(actual['fields']) if field=={'group':'coframe','coordinate':[0,0]})
reader=clean(-2*N*decode(back['whole289_low_field_lift'])[e00,:]);assert all(not v.has(u,q) for v in reader)
heavy=r['heavy56_local61_indices'];light=r['light5_local61_indices'];G0=decode(r['heavy56_origin_inverse'])
rho=truncate(reader*decode(r['light61_writeback_degree2']),2)
source=rho.subs({u:-u,q:-q},simultaneous=True).T
rho1=homogeneous(rho,1)
rho3=clean(rho1*K)
source3=clean(K.T*source.applyfunc(lambda v:homogeneous(s.Matrix([v]),1)[0]))
contact=s.factor((reader[:,heavy]*G0*reader[:,heavy].T)[0]/N)
ray=s.symbols('ray',real=True)
Lray=L3.subs({u:ray,q:1})
readray=rho3.subs({u:ray,q:1});forceray=source3.subs({u:ray,q:1})
solved=Lray.inv(method='DM')*forceray
lightread=s.factor((readray*solved)[0]/N)
expected=54*s.sqrt(30)*(297*ray**2-125)/(3125*(162*ray**2-125))
zero(s.Matrix([s.cancel(contact+lightread-expected)]))
print('g00 contact:',contact,'light ray response:',lightread,'reader:',rho3,flush=True)
report={'scope':'SOURCE5_LIGHT_PENCIL_FIRST_CHARACTERISTICS_AND_G00_VISIBILITY',
 'first_order_matrix':encode(J),'first_order_rank':2,'kernel_of_first_order':encode(K),
 'source_basis_change':encode(P),'transformed_light5_degree2':encode(block),
 'second_order_kernel3':encode(L3),'second_order_kernel3_determinant':str(det3),
 'first_nonzero_isotropic_determinant_degree':8,'first_isotropic_characteristic':str(leading),
 'quadratic_time_scaling':'u=slow*q^2','quadratic_time_leading_matrix':encode(quadraticTime),
 'quadratic_time_first_determinant_degree':10,'quadratic_time_characteristic':str(slowdet),
 'physical_g00_reader61':encode(reader),'g00_reader5_through_degree2':encode(rho),
 'g00_source5_through_degree2':encode(source),'g00_reader_on_kernel3':encode(rho3),
 'g00_source_on_kernel3':encode(source3),'g00_origin_contact':str(contact),
 'g00_ray_light_response':str(lightread),'g00_ray_total_response':str(s.factor(contact+lightread)),
 'native_linear_lambda_squared_per_k_squared':list(map(str,[s.simplify(-N*N*s.Rational(5,3)),s.simplify(-N*N*s.Rational(55,67)),s.simplify(N*N*s.Rational(125,162))])),
 'native_quadratic_lambda_squared_per_k_fourth':str(s.simplify(-N*N*s.Rational(25,72))),
 'matches_original_g00_ray_response':True,'elapsed_seconds':round(time.monotonic()-start,3)}
(HERE/'propagation-receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS actual metric source sees the original characteristic divisor in the common5 kernel',report['elapsed_seconds'],flush=True)
