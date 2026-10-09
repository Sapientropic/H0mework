#!/usr/bin/env python3
"""Solve the reconstituted A/B shifted insertion on the same native section."""
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


def read(path):return json.loads(path.read_bytes())
def matrix(r):return old.matrix(r,{'u':u,'q':q,'U':U})
def small_inverse(M):
    domain=s.QQ.algebraic_field(s.sqrt(2),s.sqrt(15),s.I)
    result=DomainMatrix.from_Matrix(M).convert_to(domain).inv().to_Matrix()
    result=clean(result)
    assert clean(M*result)==s.eye(M.rows) and clean(result*M)==s.eye(M.rows)
    return result


def main():
    started=time.monotonic()
    paths=[HERE/'insertion.json',FQ/'packet-field/pole-source.json',
        FQ/'light-modes/field-receipt.json',FQ/'packet-gauge-causal/source.json',
        BASE/'active-gauge/receipt.json',BASE/'active-gauge/quotient.json',
        BASE/'active-gauge/propagation.json']
    insertion,pole,fields,frame,actual,quotient,catalog=map(read,paths)
    for path,h in insertion['source_sha256'].items():
        assert hashlib.sha256((old.source.ROOT/path).read_bytes()).hexdigest()==h,path
    N=s.sympify(actual['source_lapse']);c=N*s.sqrt(2);lam=s.sympify(insertion['physical_lambda'])
    assert s.simplify(lam-6*c*(1-s.I))==0 and s.re(lam)>5
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
    assert s.Poly(theta_den,U,extension=s.I).gcd(Fhat).degree()==0
    pin_axis=[lam,0,0,s.I*s.sqrt(2)*rho]
    Hin=old.ward.operator(actual['Fourier_Jacobi_entries'],values=pin_axis)
    assert clean(Hin*X0-I0)==s.zeros(289,degree)
    assert X0.extract(removed,range(degree))==s.zeros(9,degree)
    Xw0,Iw0=clean(L*X0),clean(Li.T*I0)
    pin=list(map(s.sympify,insertion['physical_p_in']))
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

    branches=[]
    constantV=old.ward.operator(read(FQ/'packet-gauge-kernel/source.json')['H1'],values=pin)
    for branch in insertion['branches']:
        sign=branch['external_sign'];rout=s.Rational(branch['rho_out'])
        K1=matrix(branch['K1'])
        Vw=matrix(branch['V']);Cw=matrix(branch['C1']);Kmout=matrix(branch['K0_minus_out'])
        # Source generation precedes the target field solve. Only the nine
        # original complement rows vary in the common transported section.
        contact=clean(-K1.T*Iw0-Cw.T*Xw0)
        minor=clean(Li*Kmout).extract(removed,range(9))
        source_values=clean(small_inverse(minor.T)*contact)
        I1=s.MutableSparseMatrix(289,degree,{})
        for i,row in enumerate(removed):I1[row,:]=source_values[i,:]
        I1=clean(I1);Iw1=clean(Li.T*I1)
        assert I1.extract(retained,range(degree))==s.zeros(280,degree)
        assert clean(Kmout.T*Iw1+K1.T*Iw0+Cw.T*Xw0)==s.zeros(9,degree)
        source_witness=witness(Iw1,[81,85,9])
        print('PASS independently Noether-generated output source',sign,len(Iw1.todok()),flush=True)

        V=clean(L.T*Vw*L)
        ax=[lam,0,0,s.I*s.sqrt(2)*rout]
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
        rational=clean(scales*section*scales/N)
        inverse,blocks=old.rational_inverse(rational)
        invsection=clean(scales*inverse*scales/N)
        assert clean(section*invsection)==clean(invsection*section)==s.eye(112)
        print('PASS actual output112 double inverse with scalar9',sign,blocks,flush=True)
        reduced=clean(invsection*rhs.extract(keep,range(degree)))
        X1=s.MutableSparseMatrix(289,degree,{})
        for i,row in enumerate(keep):X1[row,:]=reduced[i,:]
        for eliminated,kept,particular,back in reversed(steps):
            values=clean(particular+back*X1.extract(kept,range(degree)))
            for i,row in enumerate(eliminated):X1[row,:]=values[i,:]
        X1=clean(X1)
        assert X1.extract(removed,range(degree))==s.zeros(9,degree)
        assert clean(Hout*X1+V*X0-I1)==s.zeros(289,degree)
        Xw1=clean(L*X1)
        pout=list(map(s.sympify,branch['physical_p_out']))
        Hwout=old.ward.operator(actual['Fourier_Jacobi_entries'],values=pout)
        assert clean(Hwout*Xw1+Vw*Xw0-Iw1)==s.zeros(289,degree)
        field_witness=witness(Xw1,[57,22,9])
        shifted_failure=clean(Hin_world*Xw1+Vw*Xw0-Iw1)
        shifted_witness=witness(shifted_failure,[57,22,9])
        vertex_input_difference=clean((Vw-constantV)*Xw0)
        branches.append({'external_sign':sign,'physical_k_out':branch['physical_k_out'],
            'physical_q_external':branch['physical_q_external'],'rho_out':str(rout),
            'X1_numerator_coefficients':encode(Xw1),'I1_numerator_coefficients':encode(Iw1),
            'all289_by6_shifted_equation_zero':True,'source_retained280_zero':True,
            'field_removed9_zero':True,'output_complete112_inverse_block_sizes':blocks,
            'auxiliary_steps':aux_reports,'nonzero_field_rows':len(set(i for i,j in Xw1.todok())),
            'nonzero_source_rows':len(set(i for i,j in Iw1.todok())),
            'field_nonzero_witness':field_witness,'source_nonzero_witness':source_witness,
            'wrong_unshifted_operator_witness':shifted_witness,
            'vertex_difference_annihilates_this_incoming_theta':not bool(vertex_input_difference.todok())})
        print('PASS full289 shifted source solution',sign,'field',branches[-1]['nonzero_field_rows'],
            'source',branches[-1]['nonzero_source_rows'],'field witness',field_witness['world_field_row'],flush=True)

    result={'scope':'STRIKE_RECONSTITUTED_A_B_ORDERED_SPATIAL_TRANSFER_WITH_NOETHER_SOURCE',
        'source_sha256':actual['source_sha256'],
        'input_sha256':{str(path.relative_to(old.source.ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'physical_lambda':str(lam),'physical_k_in':insertion['physical_k_in'],
        'incoming_complete_Fhat':str(Fhat.as_expr()),'incoming_small_root_interval':[str(3*rho*rho/4),str(4*rho*rho/5)],
        'common_incoming_theta_denominator':str(theta_den),
        'coefficient_convention':'Column j is U^j, every field/source column is divided by the same incoming theta denominator; U remains the original incoming small root.',
        'X0_numerator_coefficients':encode(Xw0),'I0_numerator_coefficients':encode(Iw0),
        'source_generation':'I1_axis is supported on removed9; (L^-1 K0(-pout))_removed^T I1_removed=-K1^T I0_world-C1(q)^T X0_world, computed before X1.',
        'branches':branches,
        'real_cosine_consumer':'For external cos(q.x) dx1 S01, take half of the two generated ordered output modes at k_in+q and k_in-q, with their independently generated half-weight sources.',
        'fixed_background_path':'Original A and its source-constitutive gauge B move together: b_q=-star_e D_A a_q/sigma; coframe fixed along the external path and live in all fluctuation vertices.',
        'scope_of_momenta':'Parallel q=+/-k_in/2, same original two-circle frame; not arbitrary external momentum.',
        'elapsed_seconds':round(time.monotonic()-started,3)}
    payload=(json.dumps(result,separators=(',',':'))+'\n').encode()
    compressed=gzip.compress(payload,mtime=0)
    (HERE/'solution.json.gz').write_bytes(compressed)
    small={'scope':result['scope'],'source_sha256':actual['source_sha256'],'input_sha256':result['input_sha256'],
        'solution_gzip_sha256':hashlib.sha256(compressed).hexdigest(),'solution_uncompressed_sha256':hashlib.sha256(payload).hexdigest(),
        'uncompressed_bytes':len(payload),'compressed_bytes':len(compressed),
        'physical_lambda':str(lam),'physical_k_in':result['physical_k_in'],
        'incoming_complete_Fhat':str(Fhat.as_expr()),'common_incoming_theta_denominator':str(theta_den),
        'branches':[{k:v for k,v in branch.items() if k not in ['X1_numerator_coefficients','I1_numerator_coefficients']} for branch in branches],
        'elapsed_seconds':result['elapsed_seconds']}
    (HERE/'solution.json').write_text(json.dumps(small,indent=2)+'\n')
    print('PASS actual source transfer producer',result['elapsed_seconds'],'compressed bytes',len(compressed),flush=True)


if __name__=='__main__':main()
