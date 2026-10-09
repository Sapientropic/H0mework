#!/usr/bin/env python3
"""Original complete112 section at variable physical lambda=c*x."""
import hashlib
import json
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
FQ=HERE.parent;BASE=FQ.parent
sys.path.insert(0,str(FQ/'packet-gauge-kernel'))
import propagation as old

clean,encode=old.clean,old.encode
x,U=s.symbols('x U',real=True)
rho=s.Rational(1,131072)


def zero(M):
    return s.SparseMatrix(M.rows,M.cols,{ij:c for ij,v in s.SparseMatrix(M).todok().items()
        if (c:=s.cancel(s.expand(v)))!=0})


def build():
    began=time.monotonic()
    actual=old.read(BASE/'active-gauge/receipt.json')
    quotient=old.read(BASE/'active-gauge/quotient.json')
    propagation=old.read(BASE/'active-gauge/propagation.json')
    primitive=old.read(FQ/'packet-gauge-kernel/source.json')
    off=old.read(FQ/'packet-gauge-kernel/ward.json')
    rotation=old.read(BASE/'active-gauge/rotation/finite.json')
    for path,digest in actual['source_sha256'].items():
        assert hashlib.sha256((old.source.ROOT/path).read_bytes()).hexdigest()==digest
    N=s.sympify(actual['source_lapse']);c=N*s.sqrt(2)
    axis=[c*x,0,0,s.I*s.sqrt(2)*rho]
    Ly,Ry=old.circle(rotation['certificates'][1],s.Rational(1,5))
    Lz,Rz=old.circle(rotation['certificates'][2],s.Rational(1,3))
    L,R=clean(Lz*Ly),clean(Ry*Rz)
    V=clean(old.circle(rotation['certificates'][1],-s.Rational(1,5))[0]*
        old.circle(rotation['certificates'][2],-s.Rational(1,3))[0])
    assert clean(V*L)==s.eye(289)
    k=R.T*s.Matrix([0,0,0,s.sqrt(2)*rho]);world=[c*x,*[s.I*k[i] for i in range(1,4)]]
    H=old.ward.operator(actual['Fourier_Jacobi_entries'],values=axis)
    assert zero(L.T*old.ward.operator(actual['Fourier_Jacobi_entries'],values=world)*L-H)==s.zeros(289)
    H1=clean(L.T*old.ward.operator(primitive['H1'],values=world)*L)
    H2=clean(L.T*old.ward.operator(primitive['H2'],values=world)*L)
    removed=quotient['fixed_section_removed_original_fields']
    retained=quotient['retained_original_fields'];keep121=list(range(9))+retained
    names={str(v):v for v in old.ward.p}
    Kformal=old.matrix(off['K0'],names)
    K=clean(Kformal.subs(dict(zip(old.ward.p,axis))))
    Kworld=clean(Kformal.subs(dict(zip(old.ward.p,world))))
    minor=K.extract(removed,range(9));mi=minor.inv(method='DM')
    basis_change=clean(mi*(V*Kworld).extract(removed,range(9)))
    bi=basis_change.inv(method='DM')
    assert zero(V*Kworld-K*basis_change)==s.zeros(289,9)
    K1=clean(V*old.matrix(off['K1'],names).subs(dict(zip(old.ward.p,world)))*bi)
    contact=clean(L.T*old.matrix(off['C1'],names)*bi)
    assert zero(H1*K+H*K1+contact)==s.zeros(289,9)

    current=H;indices=list(range(289));steps=[]
    for step in actual['algebraic_Schur_steps']:
        eliminated=step['eliminated_fields'];ei=[indices.index(i) for i in eliminated]
        kept=[i for i in indices if i not in eliminated];ki=[indices.index(i) for i in kept]
        inverse=s.SparseMatrix(len(eliminated),len(eliminated),
            {(eliminated.index(i),eliminated.index(j)):s.sympify(value)
                for i,j,value in step['algebraic_block_inverse']})
        assert zero(current.extract(ei,ei)*inverse)==s.eye(len(ei))
        right=current.extract(ei,ki);left=current.extract(ki,ei)
        back=clean(-inverse*right)
        steps.append({'eliminated':eliminated,'kept':kept,'inverse':encode(inverse),
            'left':encode(left),'back':encode(back)})
        current=clean(current.extract(ki,ki)+left*back);indices=kept
    assert indices==list(range(121))
    expected=old.ward.operator(actual['primitive_121_Fourier_Jacobi_entries'],values=axis)[:121,:121]
    assert zero(current-expected)==s.zeros(121)

    # Source broken-gauge columns: H*T has only the genuine scalar torque.
    # Remove the old9 symmetry section coordinates before any inversion.
    Tg=old.ward.operator(actual['source_primitive_gauge_tangent'],cols=12,values=axis)
    T=Tg[:,actual['J_independent_columns']]
    T=clean(T-K*mi*T.extract(removed,range(9)))
    assert T[:9,:]==s.eye(9) and T.extract(removed,range(9))==s.zeros(9)
    T121=T[:121,:];G=clean((current*T121)[:9,:])
    assert not any(x in value.free_symbols for value in G)
    target=s.zeros(121,9);target[:9,:]=G
    assert zero(current*T121-target)==s.zeros(121,9)
    assert G.det()!=0
    E=s.SparseMatrix(121,103,{(i,j):1 for j,i in enumerate(retained)})
    Q=clean(current.extract(retained,retained))
    C=clean(T121.row_join(E).extract(keep121,range(112)))
    M=clean(current.extract(keep121,keep121))
    minus=C.subs(x,-x).conjugate().subs(s.conjugate(x),x)
    # Conjugation reverses the fixed spatial Fourier derivative, x changes sign.
    assert zero(minus.T*M*C-s.diag(G,Q))==s.zeros(112)
    assert C.det()==1
    print('PASS all168 auxiliaries and full112 scalar9/103 polynomial separation',flush=True)
    scales=s.diag(*map(s.sympify,propagation['constant_diagonal_field_scaling']))
    A=zero(scales*Q*scales/N)
    assert all(s.Poly(value,x,domain=s.QQ_I) is not None for value in A)
    legacy={'lam':c*x,'k':s.sqrt(2)*rho}
    expected_q=s.SparseMatrix(103,103,{(i,j):s.sympify(v.replace('lambda','lam'),locals=legacy)
        for i,j,v in quotient['quotient_operator_103_by_103']})
    assert zero(Q-expected_q)==s.zeros(103)
    fact=[]
    for block in propagation['blocks']:
        factors=[]
        for f in block['factors']:
            polynomial=s.Poly(s.sympify(f['polynomial'],locals={'u':x,'q':old.q}).subs(old.q,rho),x,domain=s.QQ)
            factors.append({'polynomial':str(polynomial.as_expr()),'multiplicity':f['multiplicity']})
        fact.append({'indices':block['quotient_indices'],'factors':factors,'constant':block['constant']})
    result={'scope':'STRIKE_ORIGINAL_FULL112_SCALAR_TORQUE_SEPARATION_AND_VARIABLE_FREQUENCY_SOURCE',
        'source_sha256':actual['source_sha256'],'rho':str(rho),'physical_lambda':'(6*sqrt(15)/25)*x',
        'physical_momentum':list(map(str,k[1:,0])),'removed':removed,'keep121':keep121,'retained103':retained,
        'L':encode(L),'L_inverse':encode(V),'H0':encode(H),'H1':encode(H1),'H2':encode(H2),
        'K0':encode(K),'K1':encode(K1),'C1':encode(contact),'symmetry_minor_inverse':encode(mi),
        'auxiliary_steps':steps,'scalar_graph':encode(T121.extract(keep121,range(9))),
        'scalar_block':encode(G),'scalar_block_inverse':encode(G.inv(method='DM')),
        'complete112':encode(M),'Q103':encode(Q),'normalized103':encode(A),'scales103':encode(scales),
        'polynomial_separation':encode(C),'determinant_separation':'det M112=det scalar_block * det Q103; det C=1',
        'all103_source_factor_blocks':fact,'elapsed_seconds':round(time.monotonic()-began,3)}
    (HERE/'source.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS full-frequency source construction',result['elapsed_seconds'],flush=True)


if __name__=='__main__':build()
