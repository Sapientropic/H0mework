#!/usr/bin/env python3
"""Original all-frequency, all-ray affine solution maps and complete289 residual."""
from functools import lru_cache
import gzip
import hashlib
import json
from pathlib import Path
import sys
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent;FQ=HERE.parent;BASE=FQ.parent
sys.path.insert(0,str(FQ/'packet-gauge-kernel'))
import propagation as old

clean,encode=old.clean,old.encode
u,q,U=old.u,old.q,old.U
rho=s.Rational(1,131072)
ray=s.Symbol('s',real=True)
x=s.Symbol('x',real=True)


def read(path):return json.loads(path.read_bytes())
def matrix(r):return old.matrix(r,{'u':u,'q':q,'U':U,'s':ray,'x':x})
def json_integer(value):
    if isinstance(value,s.Integer):return int(value)
    raise TypeError(f'Unexpected exact-data JSON type: {type(value).__name__}')
def small_inverse(M):
    domain=s.QQ.algebraic_field(s.sqrt(2),s.sqrt(15),s.I)
    result=DomainMatrix.from_Matrix(M).convert_to(domain).inv().to_Matrix()
    result=clean(result)
    assert clean(M*result)==s.eye(M.rows) and clean(result*M)==s.eye(M.rows)
    return result


def main():
    started=time.monotonic()
    paths=[HERE/'source.json',FQ/'packet-field/pole-source.json',
        FQ/'light-modes/field-receipt.json',FQ/'packet-gauge-causal/source.json',
        BASE/'active-gauge/receipt.json',BASE/'active-gauge/quotient.json',
        BASE/'active-gauge/propagation.json',
        FQ/'packet-gauge-momentum-domain/source.json',
        FQ/'packet-gauge-momentum-domain/domain.json',
        FQ/'packet-gauge-joint-transfer/solution.json']
    insertion,pole,fields,frame,actual,quotient,catalog,domain_source,domain,joint_receipt=map(read,paths)
    for path,h in insertion['source_sha256'].items():
        assert hashlib.sha256((old.source.ROOT/path).read_bytes()).hexdigest()==h,path
    N=s.sympify(actual['source_lapse']);c=N*s.sqrt(2);lam=s.sympify(insertion['physical_lambda'],locals={'x':x})
    assert s.simplify(lam-c*x)==0
    L,Li=matrix(frame['L']),matrix(frame['L_inverse'])
    assert clean(Li*L)==s.eye(289) and clean(L*Li)==s.eye(289)
    removed=quotient['fixed_section_removed_original_fields']
    retained=[i for i in range(289) if i not in removed]
    keep=[i for i in range(121) if i not in removed]
    assert keep==list(range(9))+quotient['retained_original_fields']
    fullF=s.Poly(s.sympify(fields['axial_source_factor'],locals={'u':u,'q':q}),u,q)
    assert all(a%2==b%2==0 for (a,b),v in fullF.terms())
    Fhat=s.Poly(sum(v*U**(a//2)*rho**b for (a,b),v in fullF.terms()),U,domain=s.QQ)
    degree=Fhat.degree()
    assert degree==6 and Fhat.count_roots(3*rho*rho/4,4*rho*rho/5)==1
    assert Fhat.gcd(Fhat.diff()).degree()==0
    @lru_cache(None)
    def power(n):
        return {(a,):v for (a,),v in s.Poly(U**n,U,domain=s.QQ).rem(Fhat).terms()}
    def reduce(columns):
        out=s.MutableSparseMatrix(columns.rows,degree,{})
        for (i,n),v in s.SparseMatrix(columns).todok().items():
            for (j,),coef in power(n).items():out[i,j]+=v*coef
        return clean(out)
    def even(expr):
        poly=s.Poly(s.expand(expr),u)
        assert all(n%2==0 for (n,),v in poly.terms())
        return sum(v*U**(n//2) for (n,),v in poly.terms())
    def columns(record):
        out={}
        for i,_,text in record['entries']:
            poly=s.Poly(even(s.sympify(text,locals={'u':u,'q':q}).subs(q,rho)),U,domain=s.EX)
            for (j,),coef in poly.terms():out[i,j]=coef
        return reduce(s.SparseMatrix(289,1+max(j for i,j in out),out))
    A,B,Z=map(columns,[pole['pair_numerator_linear'],pole['pair_numerator_constant'],pole['source_projection_numerator']])
    X0=clean(lam*A+B)
    Iraw=s.zeros(289,degree+1);Iraw[:,:degree]=lam*lam*Z;Iraw[:,1:]-=c*c*Z
    I0=reduce(Iraw)
    D=even(s.sympify(pole['factor_D'],locals={'u':u,'q':q}).subs(q,rho))
    theta_den=s.expand(D*(lam*lam-c*c*U))
    assert s.Poly(D,U,domain=s.QQ).gcd(Fhat).degree()==0
    pin_axis=[lam,0,0,s.I*s.sqrt(2)*rho]
    Hin=old.ward.operator(actual['Fourier_Jacobi_entries'],values=pin_axis)
    assert clean(Hin*X0-I0)==s.zeros(289,degree)
    assert X0.extract(removed,range(degree))==s.zeros(9,degree)
    Xw0,Iw0=clean(L*X0),clean(Li.T*I0)
    pin=[s.sympify(v,locals={'x':x}) for v in insertion['physical_p_in']]
    Hin_world=old.ward.operator(actual['Fourier_Jacobi_entries'],values=pin)
    assert clean(Hin_world*Xw0-Iw0)==s.zeros(289,degree)
    scalings=dict(zip(quotient['retained_original_fields'],map(s.sympify,catalog['constant_diagonal_field_scaling'])))
    scales=s.diag(*[s.Integer(1) if i<9 else scalings[i] for i in keep])
    print('PASS original incoming theta/source, small-root domain and fixed frame',flush=True)

    def witness(M,preferred):
        order=list(dict.fromkeys(preferred+list(range(M.rows))))
        for row in order:
            if not any(M[row,j] for j in range(degree)):continue
            for radical in [s.Integer(1),s.sqrt(2),s.sqrt(15),s.sqrt(30)]:
                values=[s.expand(M[row,j]/radical) for j in range(degree)]
                if all(s.re(v).is_Rational and s.im(v).is_Rational for v in values):
                    pol=s.Poly(sum(v*U**j for j,v in enumerate(values)),U,domain=s.QQ_I)
                    if pol and pol.gcd(Fhat).degree()==0:
                        return {'world_field_row':row,'field':actual['fields'][row],
                            'radical':str(radical),'numerator_after_radical':str(pol.as_expr()),
                            'gcd_with_full_incoming_Fhat_degree':0}
        raise AssertionError('no full-factor nonzero row generated')

    data={key:matrix(value) for key,value in insertion['source_polynomial'].items()}
    K1,Vw,Cw,Kmout=(data[key] for key in ['K1','V','C1','K0_minus_out'])
    contact=clean(-K1.T*Iw0-Cw.T*Xw0)
    minor=clean(Li*Kmout).extract(removed,range(9))
    assert minor==matrix(insertion['constant_symmetry_minor'])
    assert all(not v.has(ray) for v in minor.todok().values())
    source_values=clean(small_inverse(minor.T)*contact)
    I1=s.MutableSparseMatrix(289,degree,{})
    for i,row in enumerate(removed):I1[row,:]=source_values[i,:]
    I1=clean(I1);Iw1=clean(Li.T*I1)
    assert I1.extract(retained,range(degree))==s.zeros(280,degree)
    assert clean(Kmout.T*Iw1+K1.T*Iw0+Cw.T*Xw0)==s.zeros(9,degree)
    source_degree=max(s.Poly(v,ray).degree() for v in Iw1.todok().values())
    assert source_degree==2
    print('PASS actual polynomial Noether source generated before field inverse',flush=True)
    V=clean(L.T*Vw*L)
    ax=[lam,0,0,s.I*(s.sqrt(2)*rho+ray)]
    Hout=old.ward.operator(actual['Fourier_Jacobi_entries'],values=ax)
    current=Hout;rhs=clean(I1-V*X0);indices=list(range(289));steps=[];aux_reports=[]
    for step in actual['algebraic_Schur_steps']:
        eliminated=step['eliminated_fields']
        erows=[indices.index(i) for i in eliminated]
        kept=[i for i in indices if i not in eliminated];krows=[indices.index(i) for i in kept]
        inverse=s.SparseMatrix(len(eliminated),len(eliminated),
            {(eliminated.index(i),eliminated.index(j)):s.sympify(v) for i,j,v in step['algebraic_block_inverse']})
        assert clean(current.extract(erows,erows)*inverse)==s.eye(len(eliminated))
        assert clean(inverse*current.extract(erows,erows))==s.eye(len(eliminated))
        left=current.extract(krows,erows);right=current.extract(erows,krows)
        particular=clean(inverse*rhs.extract(erows,range(degree)))
        back=clean(-inverse*right)
        steps.append((eliminated,kept,particular,back))
        aux_reports.append({'dimension':len(eliminated),'particular_source_entries':len(particular.todok())})
        rhs=clean(rhs.extract(krows,range(degree))-left*particular)
        current=clean(current.extract(krows,krows)+left*back);indices=kept
    assert indices==list(range(121)) and sum(r['dimension'] for r in aux_reports)==168
    expected=old.ward.operator(actual['primitive_121_Fourier_Jacobi_entries'],values=ax)[:121,:121]
    assert clean(current-expected)==s.zeros(121)
    section=current.extract(keep,keep)
    qout=rho+ray/s.sqrt(2)
    assert keep==domain_source['keep112']
    assert clean(section-matrix(domain_source['complete112']).subs({q:qout}))==s.zeros(112)
    assert scales==matrix(domain_source['scales112'])

    at=lambda M,m:clean(M.diff(ray,m).subs(ray,0))
    retained103=quotient['retained_original_fields']
    D103=scales[9:,9:];Di=s.diag(*[1/D103[i,i] for i in range(103)])
    T=matrix(domain_source['scalar_torque_graph']).subs({q:qout})
    minusT=clean(T.subs(x,-x).conjugate())
    G=matrix(domain_source['scalar_G9']);Gi=small_inverse(G)
    scalar=clean(Gi*minusT.extract(keep,range(9)).T*rhs.extract(keep,range(degree)))
    part=s.MutableSparseMatrix(289,degree,{})
    secpart=clean(T*scalar)
    for row in keep:part[row,:]=secpart[row,:]
    lift=s.MutableSparseMatrix(289,103,{})
    for i,row in enumerate(retained103):lift[row,i]=D103[i,i]/N
    for eliminated,kept,particular,back in reversed(steps):
        pv=clean(particular+back*part.extract(kept,range(degree)))
        lv=clean(back*lift.extract(kept,range(103)))
        for i,row in enumerate(eliminated):part[row,:]=pv[i,:];lift[row,:]=lv[i,:]
    part,lift=clean(part),clean(lift)
    normalized=clean(D103*current.extract(retained103,retained103)*D103/N)
    force=clean(D103*rhs.extract(retained103,range(degree)))
    names={str(v):v for v in old.ward.p}
    off=read(FQ/'packet-gauge-kernel/ward.json')
    Kformal=old.matrix(off['K0'],names)
    Km=clean(Kformal.subs(dict(zip(old.ward.p,[-v for v in ax]))))
    mi=small_inverse(Km.extract(removed,range(9)).T)
    W=s.MutableSparseMatrix(289,103,{})
    for i,row in enumerate(retained103):W[row,i]=Di[i,i]
    W[:9,:]=clean(-minusT.extract(retained103,range(9)).T*Di)
    complement=clean(-mi*Km.extract(retained,range(9)).T*W.extract(retained,range(103)))
    for i,row in enumerate(removed):W[row,:]=complement[i,:]
    W=clean(W)
    assert clean(Hout*lift-W*normalized)==s.zeros(289,103)
    assert clean(Hout*part+V*X0-I1+W*force)==s.zeros(289,degree)
    assert part.extract(removed,range(degree))==s.zeros(9,degree)
    assert lift.extract(removed,range(103))==s.zeros(9,103)
    print('PASS complete original289 polynomial residual factorization through true103 block equation',flush=True)
    actual_catalog=read(FQ/'packet-gauge-causal/source.json')
    assert clean(at(normalized,0)-matrix(actual_catalog['normalized103']))==s.zeros(103)
    blocks=actual_catalog['all103_source_factor_blocks']
    allslots=set()
    for block in blocks:
        idx=block['indices']
        allslots.update((i,j) for i in idx for j in idx)
    assert all(ij in allslots for ij in normalized.todok())
    records={}
    for key,M in [('part',part),('lift',lift),('W',W),('normalized103',normalized),('force',force),
                  ('Haxis',Hout),('Vaxis',V),('NoetherSource_axis',I1)]:
        records[key]=[encode(at(M,j)) for j in range(3)]
    result={'scope':'STRIKE_ORIGINAL_VARIABLE_FREQUENCY_WHOLE289_RESIDUAL_FACTORIZATION',
      'source_sha256':actual['source_sha256'],
      'input_sha256':{str(path.relative_to(old.source.ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
      'Fhat':str(Fhat.as_expr()),'D':str(D),'theta_denominator':str(theta_den),
      'physical_clock':'lambda=c*x; s is physical external ray displacement',
      'x0_axis':encode(X0),'i0_axis':encode(I0),'Frame':encode(L),'Frame_inverse':encode(Li),
      'source_polynomial_Noether_degree':source_degree,
      'physical_s_jets':records,'original103_blocks':blocks,
      'whole289_polynomial_identities':['H(s) lift(s)=W(s) A103(s)',
        'H(s) part(s)+V(s) X0-I1(s)=-W(s) force(s)'],
      'actual_field_recipe':'X1(s)=[part(s)+lift(s) A103(s)^-1 force(s)]/theta_denominator, then original Frame',
      'no_source_target_premise':True,'all_symbolic_x_and_s':True,
      'elapsed_seconds':round(time.monotonic()-started,3)}
    data=(json.dumps(result,separators=(',',':'),default=json_integer)+'\n').encode()
    if '--full-only' not in sys.argv:
        (HERE/'maps.json').write_bytes(data)
    full={'source_sha256':result['source_sha256'],'input_sha256':result['input_sha256'],
          'Fhat':str(Fhat.as_expr()),'D':str(D),'theta_denominator':str(theta_den),
          'normalized103':encode(normalized),'force':encode(force),
          'part':encode(part),'lift':encode(lift),'W':encode(W),
          'all_symbolic_x_and_s':True}
    (HERE/'full-maps.json').write_text(json.dumps(full,separators=(',',':'),default=json_integer)+'\n')
    print('PASS variable-frequency original source maps',result['elapsed_seconds'],flush=True)


if __name__=='__main__':main()
