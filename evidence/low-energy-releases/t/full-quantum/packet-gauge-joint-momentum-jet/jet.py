#!/usr/bin/env python3
"""Actual first two physical-ray derivatives of the original insertion family."""
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
    assert clean(section-matrix(domain_source['complete112']).subs({x:6*(1-s.I),q:qout}))==s.zeros(112)
    assert scales==matrix(domain_source['scales112'])
    at=lambda M,m:clean(M.diff(ray,m).subs(ray,0))
    ms=[at(section,m) for m in range(3)]
    fs=[at(rhs.extract(keep,range(degree)),m) for m in range(3)]
    inverse,blocks=old.rational_inverse(clean(scales*ms[0]*scales/N))
    P=clean(scales*inverse*scales/N)
    assert clean(ms[0]*P)==clean(P*ms[0])==s.eye(112)
    y=[clean(P*fs[0])]
    y.append(clean(P*(fs[1]-ms[1]*y[0])))
    y.append(clean(P*(fs[2]-2*ms[1]*y[1]-ms[2]*y[0])))
    for m in range(3):
        assert clean(sum((s.binomial(m,j)*ms[j]*y[m-j] for j in range(m+1)),s.zeros(112,degree))-fs[m])==s.zeros(112,degree)
    print('PASS actual complete112 inverse-family derivative recursion, physical s factors included',flush=True)
    vectors=[s.MutableSparseMatrix(289,degree,{}) for m in range(3)]
    for m in range(3):
        for i,row in enumerate(keep):vectors[m][row,:]=y[m][i,:]
    for eliminated,kept,particular,back in reversed(steps):
        b=[at(back,m) for m in range(3)];f=[at(particular,m) for m in range(3)]
        values=[vector.extract(kept,range(degree)) for vector in vectors]
        new=[clean(f[m]+sum((s.binomial(m,j)*b[j]*values[m-j] for j in range(m+1)),s.zeros(len(eliminated),degree))) for m in range(3)]
        for m in range(3):
            for i,row in enumerate(eliminated):vectors[m][row,:]=new[m][i,:]
    vectors=list(map(clean,vectors));world=[clean(L*v) for v in vectors]
    pout=list(map(lambda v:s.sympify(v,locals={'s':ray}),insertion['physical_p_out']))
    Hwout=old.ward.operator(actual['Fourier_Jacobi_entries'],values=pout)
    assert clean(L.T*Hwout*L-Hout)==s.zeros(289)
    h=[at(Hout,m) for m in range(3)];hw=[at(Hwout,m) for m in range(3)]
    source_jets=[at(Iw1,m) for m in range(3)]
    reports=[]
    for m in range(3):
        assert vectors[m].extract(removed,range(degree))==s.zeros(9,degree)
        residual=clean(sum((s.binomial(m,j)*h[j]*vectors[m-j] for j in range(m+1)),s.zeros(289,degree))+at(V,m)*X0-at(I1,m))
        residualw=clean(sum((s.binomial(m,j)*hw[j]*world[m-j] for j in range(m+1)),s.zeros(289,degree))+at(Vw,m)*Xw0-source_jets[m])
        assert residual==residualw==s.zeros(289,degree)
        w=witness(world[m],[57])
        assert w['world_field_row']==57
        reports.append({'physical_s_derivative_order':m,
            'X1_numerator_coefficients':encode(world[m]),'I1_numerator_coefficients':encode(source_jets[m]),
            'all_original289_by6_equations':True,'field_removed9_zero':True,
            'nonzero_field_rows':len({i for i,j in world[m].todok()}),
            'nonzero_source_rows':len({i for i,j in source_jets[m].todok()}),
            'actual_coframe57_nonzero':w})
        print('PASS full289 physical derivative',m,'g00 full-F nonzero',flush=True)
    # The second derivative is not its Taylor coefficient, and s is not q.
    wrong_scale=clean(hw[0]*(s.sqrt(2)*world[1])+hw[1]*world[0]+at(Vw,1)*Xw0-source_jets[1])
    wrong_second=clean(hw[0]*(world[2]/2)+2*hw[1]*world[1]+hw[2]*world[0]+at(Vw,2)*Xw0-source_jets[2])
    scale_core=clean(hw[0]*world[1])
    assert clean(wrong_scale-(s.sqrt(2)-1)*scale_core)==s.zeros(289,degree)
    controls={'wrong_q_derivative_as_physical_s':{
                  'additional_nonzero_factor':'sqrt(2)-1','factor_positive':True,
                  **witness(scale_core,[57])},
              'wrong_second_derivative_as_Taylor_coefficient':witness(wrong_second,[57])}
    # At both finite endpoints the previously generated columns solve this
    # exact analytic family. The regular section and removed9 condition give
    # equality with its actual inverse, not a Taylor approximation.
    joint_path=FQ/'packet-gauge-joint-transfer/solution.json.gz'
    blob=joint_path.read_bytes();payload=gzip.decompress(blob)
    assert hashlib.sha256(blob).hexdigest()==joint_receipt['solution_gzip_sha256']
    assert hashlib.sha256(payload).hexdigest()==joint_receipt['solution_uncompressed_sha256']
    joint=json.loads(payload)
    assert joint['common_incoming_theta_denominator']==str(theta_den)
    assert matrix(joint['X0_numerator_coefficients'])==Xw0
    assert matrix(joint['I0_numerator_coefficients'])==Iw0
    endpoints=[]
    for branch in joint['branches']:
        sign=branch['external_sign'];point=sign*s.sqrt(2)*rho/2
        field=matrix(branch['X1_numerator_coefficients']);src=matrix(branch['I1_numerator_coefficients'])
        assert clean(Iw1.subs(ray,point)-src)==s.zeros(289,degree)
        assert clean(Hwout.subs(ray,point)*field+Vw.subs(ray,point)*Xw0-src)==s.zeros(289,degree)
        assert clean(Li*field).extract(removed,range(degree))==s.zeros(9,degree)
        endpoints.append({'external_sign':sign,'physical_s':str(point),
            'same_finite_source_and_field_inverse':True,'all_original289_rows':True})
    print('PASS both finite JointTransfer endpoints lie on this same inverse family',flush=True)
    paths.append(joint_path)
    result={'scope':'STRIKE_ACTUAL_RECONSTITUTED_SOURCE_RESPONSE_PHYSICAL_RAY_DERIVATIVES',
        'source_sha256':actual['source_sha256'],
        'input_sha256':{str(path.relative_to(old.source.ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'physical_lambda':str(lam),'physical_k_in':insertion['physical_k_in'],
        'incoming_complete_Fhat':str(Fhat.as_expr()),'incoming_small_root_interval':[str(3*rho*rho/4),str(4*rho*rho/5)],
        'common_incoming_theta_denominator':str(theta_den),
        'coefficient_convention':'Column j is U^j, every field/source column is divided by the same incoming theta denominator; U remains the original incoming small root.',
        'X0_numerator_coefficients':encode(Xw0),'I0_numerator_coefficients':encode(Iw0),
        'source_generation':'Noether polynomial I1(s) supported on original removed9; generated before the actual field inverse, with incoming X0/I0/U held fixed.',
        'polynomial_Noether_source_degree':source_degree,'I1_world_polynomial_coefficients':encode(Iw1),
        'physical_s_interval':insertion['physical_s_interval'],'axial_q_out':str(qout),
        'actual_complete112_double_inverse_block_sizes':blocks,'auxiliary_steps':aux_reports,
        'derivatives':reports,'controls':controls,'finite_endpoint_identity':endpoints,
        'derivative_not_Taylor_coefficient':'Order2 is d^2/ds^2; its Taylor coefficient is one half of the reported column.',
        'actual_family':'Use the certified original complete112 inverse at q_out=rho+s/sqrt2 on the polynomial Schur source, then original polynomial auxiliary backwrite. These columns are its real derivatives at s=0.',
        'same_source_identity':'Original A/B constitutive path, same incoming theta and physical time; external ray parameter only.',
        'elapsed_seconds':round(time.monotonic()-started,3)}
    payload=(json.dumps(result,separators=(',',':'),default=json_integer)+'\n').encode()
    compressed=gzip.compress(payload,mtime=0)
    (HERE/'jets.json.gz').write_bytes(compressed)
    small={'scope':result['scope'],'source_sha256':actual['source_sha256'],'input_sha256':result['input_sha256'],
        'solution_gzip_sha256':hashlib.sha256(compressed).hexdigest(),'solution_uncompressed_sha256':hashlib.sha256(payload).hexdigest(),
        'uncompressed_bytes':len(payload),'compressed_bytes':len(compressed),
        'physical_lambda':str(lam),'physical_k_in':result['physical_k_in'],
        'incoming_complete_Fhat':str(Fhat.as_expr()),'common_incoming_theta_denominator':str(theta_den),
        'derivatives':[{k:v for k,v in report.items() if k not in ['X1_numerator_coefficients','I1_numerator_coefficients']} for report in reports],
        'controls':controls,'finite_endpoint_identity':endpoints,
        'physical_s_interval':insertion['physical_s_interval'],'axial_q_out':str(qout),
        'polynomial_Noether_source_degree':source_degree,'actual_complete112_double_inverse_block_sizes':blocks,
        'auxiliary_steps':aux_reports,
        'elapsed_seconds':result['elapsed_seconds']}
    (HERE/'jets.json').write_text(json.dumps(small,indent=2,default=json_integer)+'\n')
    print('PASS actual continuous-family physical momentum jets',result['elapsed_seconds'],'compressed bytes',len(compressed),flush=True)


if __name__=='__main__':main()
