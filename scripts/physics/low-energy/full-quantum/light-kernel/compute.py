#!/usr/bin/env python3
"""Source-selected constant complement and true light jet, with full field return."""
from ast import literal_eval
import hashlib
import json
from pathlib import Path
import time
import sympy as s

HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
ROOT=HERE.parents[4]
u,q=s.symbols('u q',real=True)
start=time.monotonic()

def clean(M):
    return s.SparseMatrix(M).applyfunc(s.expand)

def zero(M):
    rest=s.SparseMatrix(M.applyfunc(s.cancel)).todok()
    assert not rest,list(rest.items())[:3]

def decode(record):
    return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(v,locals={'u':u,'q':q}) for i,j,v in record['entries']})

def encode(M):
    return {'shape':list(M.shape),'entries':[[int(i),int(j),str(s.factor(v))]
        for (i,j),v in s.SparseMatrix(M).todok().items()]}

def homogeneous(M,degree):
    return clean(M).applyfunc(lambda v:sum((c*u**p[0]*q**p[1] for p,c in s.Poly(v,u,q).terms()
        if sum(p)==degree),s.S.Zero))

def truncate(M,degree):
    return clean(M).applyfunc(lambda v:sum((c*u**p[0]*q**p[1] for p,c in s.Poly(v,u,q).terms()
        if sum(p)<=degree),s.S.Zero))

def main():
    old=json.loads((HERE.parent/'boson-effective/receipt.json').read_text())
    back=json.loads((HERE.parent/'boson-effective/low-readback-receipt.json').read_text())
    source=json.loads((BASE/'active-gauge/receipt.json').read_text())
    quotient=json.loads((BASE/'active-gauge/quotient.json').read_text())
    for path,digest in source['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    coefficients={literal_eval(power):decode(value) for power,value in old['local61_coefficients_degree2'].items()}
    K61=clean(sum((value*u**power[0]*q**power[1] for power,value in coefficients.items()),s.zeros(61)))
    K0=coefficients[0,0]
    heavy=list(K0.rref()[1]);light=[i for i in range(61) if i not in heavy]
    assert len(heavy)==56 and len(light)==5
    A0=K0.extract(heavy,heavy);G0=s.SparseMatrix(A0.inv(method='DM'))
    zero(A0*G0-s.eye(56));zero(G0*A0-s.eye(56))
    E0=s.MutableSparseMatrix(61,5,{(i,j):1 for j,i in enumerate(light)})
    W0=clean(-G0*K0.extract(heavy,light))
    for (i,j),v in W0.todok().items():E0[heavy[i],j]=v
    zero(K0*E0)
    assert E0.rank()==5
    print('PASS source56 invertible complement, actual5 zero graph',light,[source['fields'][old['local61_source_indices'][i]] for i in light],flush=True)
    D1=homogeneous(K61.extract(heavy,heavy),1);D2=homogeneous(K61.extract(heavy,heavy),2)
    G1=clean(-G0*D1*G0);G2=clean(G0*D1*G0*D1*G0-G0*D2*G0)
    W=truncate(-(G0+G1+G2)*K61.extract(heavy,light),2)
    S=truncate(K61.extract(light,light)+K61.extract(light,heavy)*W,2)
    assert S.subs({u:0,q:0})==s.zeros(5)
    print('LIGHT5 degree2',S,flush=True)
    determinant=s.factor(S.det(method='domain-ge'))
    print('LIGHT5 degree2 determinant',determinant,flush=True)
    E=s.MutableSparseMatrix(61,5,{(i,j):1 for j,i in enumerate(light)})
    for (i,j),v in W.todok().items():E[heavy[i],j]=v
    R=s.SparseMatrix(61,5,{(i,j):1 for j,i in enumerate(light)})
    zero(truncate(K61*E-R*S,2))
    full=truncate(decode(back['whole289_low_field_lift'])*E,2)
    J=decode(back['whole289_low_source_injection'])*R
    N=s.sympify(source['source_lapse']);momenta=[N*s.sqrt(2)*u,0,0,s.I*s.sqrt(2)*q]
    H=s.MutableSparseMatrix(289,289,{})
    for i,j,power,v in source['Fourier_Jacobi_entries']:
        H[i,j]+=s.sympify(v)*s.prod(x**a for x,a in zip(momenta,power))
    residual=clean(H*full-J*S)
    zero(truncate(residual,2))
    residual_order=min(sum(power) for value in residual.todok().values() for power,c in s.Poly(value,u,q).terms() if c)
    assert residual_order>=3
    report={'scope':'SOURCE56_COMPLEMENT_AND_TRUE_LIGHT5_KERNEL_JET',
      'source_sha256':source['source_sha256'],'heavy56_local61_indices':heavy,'light5_local61_indices':light,
      'heavy56_source_indices':[old['local61_source_indices'][i] for i in heavy],
      'light5_source_indices':[old['local61_source_indices'][i] for i in light],
      'heavy56_origin_inverse':encode(G0),'true_zero_graph61':encode(E0),
      'light5_degree2':encode(S),'light5_degree2_determinant':str(determinant),
      'light61_writeback_degree2':encode(E),'whole289_field_writeback_degree2':encode(full),
      'whole289_source_injection':encode(J),'whole289_order2_residual_zero':True,
      'whole289_exact_remainder':encode(residual),'whole289_remainder_first_total_degree':residual_order,
      'elapsed_seconds':round(time.monotonic()-start,3)}
    (HERE/'receipt.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS source five-coordinate light kernel and whole289 degree2 return',report['elapsed_seconds'],flush=True)

if __name__=='__main__':main()
