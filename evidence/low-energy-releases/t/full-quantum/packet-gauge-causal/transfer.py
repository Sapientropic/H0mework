#!/usr/bin/env python3
"""Generate the actual rational source derivative before assigning a causal domain."""
import hashlib
import argparse
import gzip
import json
from functools import lru_cache
from pathlib import Path
import sys
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent;FQ=HERE.parent;BASE=FQ.parent
sys.path.insert(0,str(FQ/'packet-gauge-kernel'))
import propagation as old

x,U=s.symbols('x U',real=True)
rho=s.Rational(1,131072)
clean,encode=old.clean,old.encode


def read(path):return json.loads(path.read_text())
def matrix(record):return old.matrix(record,{'x':x,'U':U})


def canceled(M):
    return s.SparseMatrix(M.rows,M.cols,{ij:c for ij,v in s.SparseMatrix(M).todok().items()
        if (c:=s.cancel(s.expand(v)))!=0})


def main():
    began=time.monotonic()
    parser=argparse.ArgumentParser();parser.add_argument('--reuse-blocks',action='store_true');args=parser.parse_args()
    src=read(HERE/'source.json');pole=read(FQ/'packet-field/pole-source.json')
    fields=read(FQ/'light-modes/field-receipt.json')
    N=s.Rational(3,25)*s.sqrt(30);c=N*s.sqrt(2)
    u,q=old.u,old.q
    F=s.Poly(s.sympify(fields['axial_source_factor'],locals={'u':u,'q':q}),u,q)
    Fhat=s.Poly(sum(coef*U**(a//2)*rho**b for (a,b),coef in F.terms()),U,domain=s.QQ)
    degree=Fhat.degree()
    assert all(a%2==b%2==0 for (a,b),_ in F.terms())
    @lru_cache(None)
    def power(n):return dict((a,v) for (a,),v in s.Poly(U**n,U,domain=s.QQ).rem(Fhat).terms())
    def reduce(M):
        result=s.MutableSparseMatrix(M.rows,degree,{})
        for (i,j),v in s.SparseMatrix(M).todok().items():
            for a,b in power(j).items():result[i,a]+=v*b
        return clean(result)
    def even(expr):
        poly=s.Poly(s.expand(expr),u)
        assert all(n%2==0 for (n,),_ in poly.terms())
        return sum(v*U**(n//2) for (n,),v in poly.terms())
    def columns(record):
        result={}
        for i,_,v in record['entries']:
            expr=even(s.sympify(v,locals={'u':u,'q':q}).subs(q,rho))
            for (a,),coef in s.Poly(expr,U,domain=s.EX).terms():result[i,a]=coef
        return reduce(s.SparseMatrix(289,1+max(j for i,j in result),result))
    A,B,Z=map(columns,[pole['pair_numerator_linear'],pole['pair_numerator_constant'],pole['source_projection_numerator']])
    X0=clean(c*x*A+B)
    I0=reduce(s.Matrix.hstack(c**2*x*x*Z,s.zeros(289,1))-s.Matrix.hstack(s.zeros(289,1),c**2*Z))
    D=even(s.sympify(pole['factor_D'],locals={'u':u,'q':q}).subs(q,rho))
    theta_den=c*c*D*(x*x-U)
    H,H1=matrix(src['H0']),matrix(src['H1'])
    assert reduce(H*X0-I0)==s.zeros(289,degree)
    rhs=clean(-H1*X0);steps=[];indices=list(range(289))
    for step in src['auxiliary_steps']:
        eliminated=step['eliminated'];kept=step['kept']
        erows=[indices.index(i) for i in eliminated];krows=[indices.index(i) for i in kept]
        inverse,left,back=map(matrix,[step['inverse'],step['left'],step['back']])
        particular=clean(inverse*rhs.extract(erows,range(degree)))
        steps.append((eliminated,kept,particular,back))
        rhs=clean(rhs.extract(krows,range(degree))-left*particular);indices=kept
    keep=src['keep121'];ret=src['retained103']
    graph=matrix(src['scalar_graph']);Ginv=matrix(src['scalar_block_inverse'])
    minus_graph=graph.subs(x,-x).conjugate()
    scalar=clean(Ginv*minus_graph.T*rhs.extract(keep,range(degree)))
    scales=matrix(src['scales103']);M=matrix(src['normalized103'])
    force=clean(scales*rhs.extract(ret,range(degree)))
    # Split only the coefficient field.  This keeps the original irrational
    # normalizations while all fraction-free solves use Q(i)[x].
    radicals=[s.Integer(1),s.sqrt(2),s.sqrt(15),s.sqrt(30)]
    R=s.QQ_I.poly_ring(x)
    def split(M):
        result=s.MutableSparseMatrix(M.rows,4*M.cols,{})
        for (i,j),value in s.SparseMatrix(M).todok().items():
            remaining=s.expand(value)
            for a,radical in enumerate(radicals[1:],1):
                coefficient=remaining.coeff(radical)
                if coefficient:result[i,j+a*M.cols]=coefficient;remaining-=radical*coefficient
            result[i,j]=s.expand(remaining)
        return DomainMatrix.from_Matrix(result).convert_to(R)
    solutions=[];blocks=[];common=s.Poly(1,x,domain=s.QQ_I)
    cache=HERE/'blocks';cache.mkdir(exist_ok=True)
    for block in src['all103_source_factor_blocks']:
        idx=block['indices'];mb=M.extract(idx,idx);fb=force.extract(idx,range(degree))
        if not fb.todok():
            blocks.append({'indices':idx,'source_zero':True});continue
        print('solve original block',len(idx),'source terms',len(fb.todok()),flush=True)
        dm=DomainMatrix.from_Matrix(mb).convert_to(R);db=split(fb)
        blockpath=cache/f'block-{len(idx)}.json'
        input_digest=hashlib.sha256((str(mb)+str(fb)).encode()).hexdigest()
        if args.reuse_blocks and blockpath.exists():
            cached=read(blockpath);assert cached['input_sha256']==input_digest
            nm=matrix(cached['split_numerator']);denexpr=s.sympify(cached['denominator'],locals={'x':x})
            num=DomainMatrix.from_Matrix(nm).convert_to(R);den=R.from_sympy(denexpr)
        else:
            num,den=dm.solve_den(db)
            assert dm*num==db.scalarmul(den)
            num,den=num.cancel_denom(den)
            nm=num.to_Matrix();denexpr=R.to_sympy(den)
            blockpath.write_text(json.dumps({'input_sha256':input_digest,
                'split_numerator':encode(nm),'denominator':str(denexpr)},separators=(',',':'))+'\n')
        assert dm*num==db.scalarmul(den)
        rebuilt=s.Matrix(len(idx),degree,lambda i,j:sum(radicals[a]*nm[i,j+a*degree] for a in range(4)))
        solutions.append((idx,clean(rebuilt),denexpr))
        denpoly=s.Poly(denexpr,x,domain=s.QQ_I)
        conjugate=s.Poly(s.conjugate(denexpr),x,domain=s.QQ_I)
        common=s.lcm(common,s.lcm(denpoly,conjugate)).monic()
        blocks.append({'indices':idx,'source_zero':False,'solve_denominator':str(s.factor(denexpr)),
            'original_det_factors':block['factors']})
        print('PASS original block solved',len(idx),'den degree',s.degree(denexpr,x),flush=True)
    common=s.Poly(common.as_expr(),x,domain=s.QQ);Q=common.as_expr()
    solution=s.MutableSparseMatrix(103,degree,{})
    for idx,num,den in solutions:
        multiplier=R.to_sympy(R.exquo(R.from_sympy(Q),R.from_sympy(den)))
        values=clean(num*multiplier)
        for i,row in enumerate(idx):solution[row,:]=values[i,:]
    normalized=clean(scales*solution/N)
    section=clean(Q*graph*scalar)
    for i in range(103):section[i+9,:]+=normalized[i,:]
    X1=s.MutableSparseMatrix(289,degree,{})
    for i,row in enumerate(keep):X1[row,:]=section[i,:]
    for eliminated,kept,particular,back in reversed(steps):
        values=clean(Q*particular+back*X1.extract(kept,range(degree)))
        for i,row in enumerate(eliminated):X1[row,:]=values[i,:]
    X1=clean(X1)
    print('generated full289 rational field derivative',len(X1.todok()),flush=True)
    K,K1,C1=map(matrix,[src['K0'],src['K1'],src['C1']])
    Km=K.subs(x,-x).conjugate();K1m=K1.subs(x,-x).conjugate();C1m=C1.subs(x,-x).conjugate()
    removed=src['removed']
    contact=canceled(-K1m.T*I0-C1m.T*X0)
    I1=s.MutableSparseMatrix(289,degree,{})
    values=canceled(Km.extract(removed,range(9)).T.inv(method='DM')*contact)
    for i,row in enumerate(removed):I1[row,:]=values[i,:]
    assert clean(H*X1+Q*(H1*X0-I1))==s.zeros(289,degree)
    print('PASS full289 equations with independently Noether-generated source derivative',flush=True)
    L=matrix(src['L']);Li=matrix(src['L_inverse'])
    world0,world1,worldI1=map(clean,[L*X0,L*X1,Li.T*I1])
    proper=[]
    for row in range(289):
        degrees=[]
        for j in range(degree):
            value=world1[row,j]
            if value:
                degrees.append(int(s.degree(value,x)-common.degree()-2))
        if degrees:proper.append([row,max(degrees)])
    result={'scope':'STRIKE_ACTUAL_SOURCE_TRANSFER_AT_VARIABLE_PHYSICAL_LAMBDA',
        'input_sha256':hashlib.sha256((HERE/'source.json').read_bytes()).hexdigest(),
        'Fhat':str(Fhat.as_expr()),'theta_denominator':str(theta_den),
        'coefficient_convention':'columns j are U^j; all field/source numerator columns divided by theta_denominator; Fhat(U)=0 selects the original small positive root',
        'X0':encode(world0),'X1_numerator':encode(world1),'X1_frequency_denominator':str(Q),'I1':encode(worldI1),
        'X1_convention':'X1_numerator / (X1_frequency_denominator * theta_denominator); original fields in world coordinates, U^j columns',
        'actual_source_blocks':blocks,
        'relative_degrees_X1_after_theta_denominator':proper,
        'all289_equations':True,'elapsed_seconds':round(time.monotonic()-began,3)}
    payload=(json.dumps(result,separators=(',',':'))+'\n').encode()
    (HERE/'transfer.json').write_bytes(payload)
    (HERE/'transfer.json.gz').write_bytes(gzip.compress(payload,mtime=0))
    print('PASS actual source transfer',result['elapsed_seconds'],'max relative degree',max(d for i,d in proper),flush=True)


if __name__=='__main__':main()
