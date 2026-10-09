#!/usr/bin/env python3
"""Original reconstituted source at variable physical frequency and external ray."""
import hashlib
import json
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent;FQ=HERE.parent;BASE=FQ.parent
sys.path.insert(0,str(FQ/'packet-gauge-kernel'))
import propagation as original

clean,encode=original.clean,original.encode
rho=s.Rational(1,131072)
ray=s.Symbol('s',real=True)
x=s.Symbol('x',real=True)


def read(p):return json.loads(p.read_bytes())
def matrix(r):return original.matrix(r,{str(p):p for p in original.ward.p})
def evaluate(entries,left,right):
    out=s.MutableSparseMatrix(289,289,{})
    for i,j,a,b,text in entries:
        out[i,j]+=s.sympify(text)*(left[a] if a>=0 else 1)*(right[b] if b>=0 else 1)
    return clean(out)


def main():
    start=time.monotonic()
    paths=[BASE/'active-gauge/receipt.json',BASE/'active-gauge/rotation/finite.json',
        FQ/'packet-gauge-kernel/source.json',FQ/'packet-gauge-kernel/ward.json',
        FQ/'packet-gauge-bilocal/vertices.json',FQ/'packet-gauge-causal/source.json',
        FQ/'packet-gauge-constitutive-vertex/vertices.json',
        FQ/'packet-gauge-kinetic/receipt.json',
        FQ/'packet-gauge-momentum-domain/source.json',
        FQ/'packet-gauge-momentum-domain/domain.json',
        FQ/'packet-gauge-joint-transfer/insertion.json']
    actual,rotation,primitive,oldward,bijet,incoming,constitutive,kinetic,domain_source,domain,joint=map(read,paths)
    for path,digest in actual['source_sha256'].items():
        assert hashlib.sha256((original.source.ROOT/path).read_bytes()).hexdigest()==digest,path
    idx={(f['group'],tuple(f['coordinate'])):i for i,f in enumerate(actual['fields'])}
    N=s.sympify(actual['source_lapse']);c=N*s.sqrt(2);lam=c*x
    kin=list(map(s.sympify,incoming['physical_momentum']))
    assert s.expand(sum(k*k for k in kin))==2*rho*rho
    pin=[lam,*[s.I*k for k in kin]]
    ext=s.SparseMatrix(289,1,{(idx['gauge_A',(1,1)],0):1})
    assert idx['gauge_A',(1,1)]==22
    selected=next(r for r in bijet['readers'] if r['reader']==[1,1])
    Kformal=matrix(oldward['K0'])
    K1=matrix(oldward['K1'])
    p=original.ward.p
    evalK=lambda values:clean(Kformal.subs(dict(zip(p,values))))
    H=lambda values:original.ward.operator(actual['Fourier_Jacobi_entries'],values=values)
    Hin=H(pin);Kin=evalK(pin)
    assert clean(Hin*Kin)==s.zeros(289,9)
    gen=list(map(matrix,primitive['fundamental']))
    gram=s.Matrix(12,12,lambda i,j:s.re(-s.trace(gen[i]*gen[j])))
    gi=gram.inv()
    adjoint=[]
    for g in range(12):
        cols=[]
        for b in range(12):
            comm=gen[g]*gen[b]-gen[b]*gen[g]
            cols.append(gi*s.Matrix([s.re(-s.trace(t*comm)) for t in gen]))
        adjoint.append(s.Matrix.hstack(*cols))
    native=original.source.load(BASE/'active-gauge/compute.py','transfer_native_field_actions')
    color=s.zeros(12,3);color[1,0]=s.Rational(1,2);color[0,1]=s.Rational(1,2)
    color[6,2]=s.Rational(1,2);color[7,2]=-s.Rational(1,2)
    Tg1=s.zeros(289,12)
    for g in range(12):
        for j in range(12):Tg1[idx['gauge_A',(1,j)],g]=adjoint[g][j,1]
    assert clean((Tg1*color).row_join(s.zeros(289,6))-K1)==s.zeros(289,9)
    gauge_actions=[]
    for g in range(12):
        M=s.MutableSparseMatrix(289,289,{})
        for group,count in [('gauge_A',4),('gauge_B',6)]:
            for mu in range(count):
                for (i,j),value in s.SparseMatrix(adjoint[g]).todok().items():
                    M[idx[group,(mu,i)],idx[group,(mu,j)]]=value
        internal=s.kronecker_product(s.eye(4),gen[g][:3,:3]+gen[g][5,5]*s.eye(3))
        for group,action in [('primal_H',internal),('dual_H',-internal.T)]:
            for (i,j),value in s.SparseMatrix(native.active.realify(action)).todok().items():
                M[idx[group,(i//12,(i%12)//3,i%3)],idx[group,(j//12,(j%12)//3,j%3)]]=value
        gauge_actions.append(s.SparseMatrix(M))
    lorentz_actions=[]
    for a,b in native.PAIRS:
        M=s.MutableSparseMatrix(289,289,{})
        lor=s.zeros(4);lor[a,b]=native.ETA[a,a];lor[b,a]=-native.ETA[b,b]
        for mu in range(4):
            for (i,j),value in s.SparseMatrix(lor).todok().items():
                M[idx['coframe',(i,mu)],idx['coframe',(j,mu)]]=value
        spin=s.kronecker_product(native.GAMMA[a]*native.GAMMA[b]/2,s.eye(3))
        for group,action in [('primal_H',spin),('dual_H',-spin.T)]:
            for (i,j),value in s.SparseMatrix(native.active.realify(action)).todok().items():
                M[idx[group,(i//12,(i%12)//3,i%3)],idx[group,(j//12,(j%12)//3,j%3)]]=value
        lorentz_actions.append(s.SparseMatrix(M))
    Tg_in=original.ward.operator(actual['source_primitive_gauge_tangent'],cols=12,values=pin)
    n=[s.simplify(k/(s.sqrt(2)*rho)) for k in kin]
    assert s.expand(sum(v*v for v in n))==1 and all(v!=0 for v in n)
    qext=[ray*v for v in n];kout=[k+d for k,d in zip(kin,qext)]
    pout=[lam,*[s.I*k for k in kout]];pe=[0,*[s.I*k for k in qext]]
    curvature_derivative=matrix(kinetic['curvature_derivative'])
    star=s.kronecker_product(matrix(kinetic['source_hodge']),s.eye(12))
    sigma=s.sympify(actual['source_coupling'])
    a=s.zeros(48,1);a[13]=1
    F1=clean(curvature_derivative.subs(dict(zip(p,pe)))*a)
    B1=clean(-star*F1/sigma)
    assert clean(F1-sigma*star*B1)==s.zeros(72,1)
    complete_direction=s.MutableSparseMatrix(ext)
    for record in constitutive['original_unit_auxiliary_readers']:
        pair,g=record['auxiliary']
        complete_direction[record['original_field'],0]=B1[12*pair+g,0]
    complete_direction=clean(complete_direction)
    extra=clean(sum((B1[12*record['auxiliary'][0]+record['auxiliary'][1],0]*matrix(record['Q'])
                    for record in constitutive['original_unit_auxiliary_readers']),s.zeros(289)))
    V=clean(evaluate(selected['Q0_bijet'],[-v for v in pout],pin)+extra)
    E=clean(H(pe)*complete_direction)
    for group in ['scalar_J','gauge_B','Lorentz','gravity_B','multiplier']:
        assert all(E[i,0]==0 for i,f in enumerate(actual['fields']) if f['group']==group)
    Tg1joint=clean(s.SparseMatrix.hstack(*(M*complete_direction for M in gauge_actions)))
    K1=clean((Tg1joint*color).row_join(s.SparseMatrix.hstack(*(M*complete_direction for M in lorentz_actions))))
    Cg=clean(s.SparseMatrix.hstack(*(M.T*E for M in gauge_actions)))
    C=clean((Cg*color).row_join(s.SparseMatrix.hstack(*(M.T*E for M in lorentz_actions))))
    Hout=H(pout);Kout=evalK(pout);Kmout=evalK([-v for v in pout])
    assert clean(Hout*Kout)==s.zeros(289,9)
    assert clean(V*Kin+Hout*K1+C)==s.zeros(289,9)
    assert clean(V*Tg_in+Hout*Tg1joint+Cg)==s.zeros(289,12)
    assert clean(Kmout.T*V+K1.T*Hin+C.T)==s.zeros(9,289)
    assert clean((evaluate(selected['Q0_bijet'],pin,[-v for v in pout])+extra).T-V)==s.zeros(289)
    L,Li=matrix(incoming['L']),matrix(incoming['L_inverse'])
    assert clean(Li*L)==s.eye(289)
    qout=rho+ray/s.sqrt(2)
    Haxis=H([lam,0,0,s.I*s.sqrt(2)*qout])
    assert clean(L.T*Hout*L-Haxis)==s.zeros(289)
    minor=clean(Li*Kmout).extract(domain_source['removed'],range(9))
    assert all(not v.has(ray) for v in minor.todok().values())
    assert minor.det()!=0
    polynomial={'B1':B1,'complete_background_direction':complete_direction,
                'V':V,'E1':E,'K1':K1,'C1':C,'K0_out':Kout,'K0_minus_out':Kmout}
    degrees={key:max((s.Poly(v,ray).degree() for v in value.todok().values()),default=0)
             for key,value in polynomial.items()}
    assert degrees['B1']==degrees['V']==degrees['K1']==1
    assert degrees['E1']==degrees['C1']==2
    assert clean(V.diff(ray,2))==s.zeros(289)
    R=s.Rational(domain_source['q_radius'])
    assert rho/2>0 and 3*rho/2<R
    endpoint_reports=[]
    for branch in joint['branches']:
        sign=branch['external_sign'];endpoint=sign*s.sqrt(2)*rho/2
        for key in ['V','E1','K1','C1','complete_background_direction','K0_minus_out','K0_out']:
            assert clean(polynomial[key].subs({ray:endpoint,x:6*(1-s.I)})-matrix(branch[key]))==s.zeros(*polynomial[key].shape),key
        assert [s.simplify(v.subs({ray:endpoint,x:6*(1-s.I)})) for v in pout]==list(map(s.sympify,branch['physical_p_out']))
        endpoint_reports.append({'external_sign':sign,'physical_s':str(endpoint),
                                 'all_frozen_joint_source_data_identical':True})
    print('PASS source polynomial in physical s, all shifted Ward and both frozen endpoints',flush=True)
    result={'scope':'STRIKE_RECONSTITUTED_JOINT_VARIABLE_FREQUENCY_AND_PHYSICAL_RAY_SOURCE',
        'source_sha256':actual['source_sha256'],
        'input_sha256':{str(path.relative_to(original.source.ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'primitive_external':'a_q=exp(i q.x) dx1 S01 and b_q=-star_e D_A(a_q)/sigma; coframe fixed in the external path, live in field variations',
        'rho_in':str(rho),'physical_lambda':str(lam),'normalized_x':'variable x=lambda/c',
        'physical_k_in':list(map(str,kin)),'physical_p_in':list(map(str,pin)),
        'frame':'original quarterY=1/5, quarterZ=1/3, common L unchanged',
        'ray_parameter':'s is physical signed external momentum magnitude, not axial q',
        'unit_direction':list(map(str,n)),'physical_p_out':list(map(str,pout)),
        'physical_q_external':list(map(str,qext)),'axial_q_out':str(qout),
        'physical_s_interval':[str(-s.sqrt(2)*rho/2),str(s.sqrt(2)*rho/2)],
        'complete112_regular_axial_domain':str(R),'constant_symmetry_minor':encode(minor),
        'polynomial_degrees':degrees,'source_polynomial':{key:encode(value) for key,value in polynomial.items()},
        'frequency_degrees':{key:max((s.Poly(v,x).degree() for v in value.todok().values()),default=0)
                             for key,value in polynomial.items()},
        'K0_in':encode(Kin),'endpoint_readback':endpoint_reports,
        'Ward_identities':['V(pout,pin)K0(pin)+H0(pout)K1=-C1(q)',
            'K0(-pout)^T V(pout,pin)+K1^T H0(pin)=-C1(q)^T'],
        'contact_source':'K1_g=(D field_action_g)(a_q+b_q), C1_g=(D field_action_g)^T H0(p_ext)(a_q+b_q); no target response used',
        'actual_regular_family':'Actual polynomial source, constant Noether minor, and the certified complete112 adjugate inverse at q_out=rho+s/sqrt2',
        'elapsed_seconds':round(time.monotonic()-start,3)}
    (HERE/'source.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS variable-frequency continuous physical-ray source stage',result['elapsed_seconds'],flush=True)


if __name__=='__main__':main()
