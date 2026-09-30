#!/usr/bin/env python3
"""Independent affine12 equation audit of the source canonical clock jets.

The simultaneous original broken/residual system generates every phase jet.
The clock is differentiated through its defining quadratic equation, and the
canonical Moyal tensor is contracted by explicit paired canonical indices.
The candidate constructor and its two separate inverse recipes are not used.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_scalar_form_hamiltonian import (
    RawGaussSection,raw_coefficients,HERE,ROOT,ROOT_ID,bindings,clean,rational,eq,decode,encode)
from independent_source_coframe_live_ordering import RawLiveCoefficients


SIZE=100


def zero(value): assert s.factor(s.cancel(value))==0,value


def record_jet(v,g,H):
    eq(H,H.T)
    return {'value':s.factor(v),'gradient':rational(g),'Hessian':rational(H)}


def encoded(j):
    return {'value':str(j['value']),'gradient200':encode(j['gradient']),'Hessian200':encode(j['Hessian'])}


def compare(j,saved):
    zero(j['value']-s.sympify(saved['value']))
    eq(j['gradient'],decode(saved['gradient200']));eq(j['Hessian'],decode(saved['Hessian200']))


def quotient_jets(numerator,denominator):
    # Derivatives of the original product denominator * quotient = numerator.
    v=s.factor(numerator['value']/denominator['value'])
    g=rational((numerator['gradient']-v*denominator['gradient'])/denominator['value'])
    H=rational((numerator['Hessian']-v*denominator['Hessian']-
        g*denominator['gradient'].T-denominator['gradient']*g.T)/denominator['value'])
    return record_jet(v,g,H)


def symplectic2(a,b):
    # For each original coordinate q_i, J^{q_i,p_i}=+1 and
    # J^{p_i,q_i}=-1. Both canonical indices are contracted explicitly.
    out=0
    for (i,j),v in a['Hessian'].todok().items():
        paired_i=i+100 if i<100 else i-100
        paired_j=j+100 if j<100 else j-100
        out+=v*(1 if i<100 else -1)*(1 if j<100 else -1)*b['Hessian'][paired_i,paired_j]
    return s.factor(out)


def poisson(a,b):
    return s.factor(sum(a['gradient'][j]*b['gradient'][100+j]-
        a['gradient'][100+j]*b['gradient'][j] for j in range(100)))


def original_coupled_phase_jets(section,raw,p):
    point=section.source;q=tuple(point[:6,0]);x=point[6:67,:];A=point[67:,:].reshape(3,12)
    e=raw.at(raw.e,q);native=section.native
    ambient=raw_coefficients(native,e,x,A)
    retained=tuple(j-6 for j in section.free if j>=6);pivots=tuple(j-6 for j in section.fixed)
    assert len(retained)==94 and retained[:61]==tuple(range(61))
    y=point[6:,:];S=clean(s.Matrix.hstack(*(T*y for T in native.Ts)))
    B=clean(s.Matrix.vstack(*((T*y).T for T in native.Tb)));D=ambient['D'];M=S[list(pivots),:]
    L=D.T.row_join(B[:,list(pivots)]).col_join(s.zeros(3,9).row_join(M.T))
    rhs=B[:,list(retained)].col_join(S[list(retained),:].T)
    inv,params=L.gauss_jordan_solve(s.eye(12));assert params.rows==0
    inv=rational(inv);eq(L*inv,s.eye(12));eq(inv*L,s.eye(12))
    X=rational(inv*rhs);p94=p[6:,:];u=rational(X*p94)
    eq(L*u,rhs*p94)
    dL=[];dR=[];du=s.zeros(12,200)
    for j,k in enumerate(retained):
        dD=clean(native.O.T*s.Matrix.hstack(*(T*native.R[:,k] for T in native.rhob))) if k<61 else s.zeros(9)
        dB=clean(s.Matrix.vstack(*(T[:,k].T for T in native.Tb)))
        dS=clean(s.Matrix.hstack(*(T[:,k] for T in native.Ts)))
        li=dD.T.row_join(dB[:,list(pivots)]).col_join(s.zeros(3,9).row_join(dS[list(pivots),:].T))
        ri=dB[:,list(retained)].col_join(dS[list(retained),:].T)
        dL.append(li);dR.append(ri)
        du[:,6+j]=rational(inv*(ri*p94-li*u))
        eq(L*du[:,6+j]+li*u,ri*p94)
    du[:,106:]=X
    E=native.Rd.row_join(s.zeros(70,33));O=native.O
    eq(E.T*O,s.zeros(94,9))
    w=rational(E*p94-O*u[:9,:]);dw=rational(-O*du[:9,:]);dw[:,106:]+=E
    Ep=s.eye(97)[61:,list(pivots)];Ef=s.eye(97)[61:,list(retained)]
    Pi=rational(Ef*p94-Ep*u[9:,:]);dPi=rational(-Ep*du[9:,:]);dPi[:,106:]+=Ef
    geo=section.implicit_jets(point);pull=rational(geo['tangent'].T*section.free_reader.T)
    eq(w,ambient['a']*pull[6:,:]*p);eq(Pi,pull[67:,:]*p)
    scalar=record_jet((w.T*w)[0],2*dw.T*w,2*dw.T*dw)
    qsym=s.Matrix(raw.q);Lq=s.Matrix([[qsym[0],0,0],[qsym[1],qsym[2],0],[qsym[3],qsym[4],qsym[5]]])
    volume=Lq.det();Ginv=native.Gram.inv()
    # Derive the 36-index quadratic tensor from direct spatial/internal
    # contractions. This does not import the candidate's Kronecker formula.
    spatial=rational(Lq.inv()*Lq.inv().T*volume/2)
    weight=s.Matrix(36,36,lambda i,j:spatial[i//12,j//12]*Ginv[i%12,j%12])
    at=dict(zip(qsym,q));W=rational(weight.subs(at))
    eq((Pi.T*W*Pi),s.Matrix([[s.trace(Pi.reshape(3,12)*Ginv*Pi.reshape(3,12).T*spatial.subs(at))]]))
    trace=record_jet((Pi.T*W*Pi)[0],2*dPi.T*W*Pi,2*dPi.T*W*dPi)
    for i in range(94):
        uip=rational(inv*(dR[i]-dL[i]*X))
        eq(L*uip+dL[i]*X,dR[i])
        for j in range(94):
            wij=-O*uip[:9,j];pij=-Ep*uip[9:,j]
            a=s.factor(2*(w.T*wij)[0]);b=s.factor(2*(Pi.T*W*pij)[0])
            scalar['Hessian'][6+i,106+j]+=a;scalar['Hessian'][106+j,6+i]+=a
            trace['Hessian'][6+i,106+j]+=b;trace['Hessian'][106+j,6+i]+=b
        for j in range(i,94):
            forcing=-(dL[i]*du[:,6+j]+dL[j]*du[:,6+i])
            uij=rational(inv*forcing);eq(L*uij,forcing)
            wij=-O*uij[:9,:];pij=-Ep*uij[9:,:]
            a=s.factor(2*(w.T*wij)[0]);b=s.factor(2*(Pi.T*W*pij)[0])
            scalar['Hessian'][6+i,6+j]+=a;trace['Hessian'][6+i,6+j]+=b
            if i!=j:
                scalar['Hessian'][6+j,6+i]+=a;trace['Hessian'][6+j,6+i]+=b
        if i in (30,60,93):print('PASS independent affine12 full mixed/position Hessian rows',i+1,'/94',flush=True)
    for i in range(6):
        Wi=rational(weight.diff(qsym[i]).subs(at))
        trace['gradient'][i]=(Pi.T*Wi*Pi)[0]
        for j in range(6):trace['Hessian'][i,j]=(Pi.T*weight.diff(qsym[i],qsym[j]).subs(at)*Pi)[0]
        row=2*Pi.T*Wi*dPi
        for j in range(6,200):
            trace['Hessian'][i,j]=row[j];trace['Hessian'][j,i]=row[j]
    v=record_jet(volume.subs(at),s.zeros(200,1),s.zeros(200))
    for i in range(6):
        v['gradient'][i]=s.diff(volume,qsym[i]).subs(at)
        for j in range(6):v['Hessian'][i,j]=s.diff(volume,qsym[i],qsym[j]).subs(at)
    # Original epsilon-Hessian/primary graph coframe coefficient, independent
    # of the candidate common-family K constructor.
    K=rational(raw.A.T*raw.Q*raw.A/(2*raw.N));pq=p[:6,:];K0=rational(K.subs(at))
    cf=record_jet((pq.T*K0*pq)[0],s.zeros(200,1),s.zeros(200))
    cf['gradient'][100:106,:]=2*K0*pq;cf['Hessian'][100:106,100:106]=2*K0
    for i in range(6):
        Ki=rational(K.diff(qsym[i]).subs(at));cf['gradient'][i]=(pq.T*Ki*pq)[0]
        for j in range(6):
            cf['Hessian'][i,j]=(pq.T*K.diff(qsym[i],qsym[j]).subs(at)*pq)[0]
            cf['Hessian'][i,100+j]=2*(Ki*pq)[j];cf['Hessian'][100+j,i]=2*(Ki*pq)[j]
    loss=quotient_jets(scalar,v)
    a0=record_jet(cf['value']-loss['value']/2,cf['gradient']-loss['gradient']/2,
                 cf['Hessian']-loss['Hessian']/2)
    trace=record_jet(trace['value'],trace['gradient'],trace['Hessian'])
    return a0,trace,{'coupled_original_affine12':encode(L),'all94_first_original_equations':True,
        'all94x94_original_position_second_equations':True,
        'all94x94_original_mixed_momentum_equations':True,
        'original_E_transpose_O_zero':True,'actual_source_gauss_pullback_equal':True,
        'gauge_weight':'v/2 times (L^-1 L^-T) spatial contraction and the original native inverse Gram; both mixed coframe/remaining-phase derivative slots are retained.'}


def implicit_clock(a,t):
    C=s.sqrt(t['value']/(2*a['value']))
    g=rational((t['gradient']-2*C*C*a['gradient'])/(4*a['value']*C))
    H=rational((t['Hessian']-2*C*C*a['Hessian']-
        4*C*(a['gradient']*g.T+g*a['gradient'].T)-4*a['value']*g*g.T)/(4*a['value']*C))
    return record_jet(C,g,H)


def homogeneity(j,p,q,pdegree,qdegree):
    v,g,H=j['value'],j['gradient'],j['Hessian']
    zero((p.T*g[100:,:])[0]-pdegree*v)
    eq(H[100:,100:]*p,(pdegree-1)*g[100:,:])
    eq(H[:100,100:]*p,pdegree*g[:100,:])
    dil=s.zeros(200,1);dil[:6,:]=s.Matrix(q);dil[100:106,:]=-p[:6,:]
    weight=s.zeros(200);weight[:6,:6]=s.eye(6);weight[100:106,100:106]=-s.eye(6)
    zero((dil.T*g)[0]-qdegree*v)
    eq(H*dil+weight*g,qdegree*g)


def jordan_inverse_identity():
    q,p=s.symbols('q p');C=s.Function('C')(q,p);X=s.Function('X')(q,p)
    P2=lambda a,b:s.diff(a,q,2)*s.diff(b,p,2)-2*s.diff(a,q,p)*s.diff(b,q,p)+s.diff(a,p,2)*s.diff(b,q,2)
    u=X/C;u2=P2(C,u)/(8*C)
    assert s.simplify(C*u-X)==0
    assert s.simplify(C*u2-P2(C,u)/8)==0
    v=u/C;v2=(u2+P2(C,v)/8)/C
    expected=(P2(C,X/C**2)/C+P2(C,X/C)/C**2)/16
    assert s.simplify(v2/2-expected)==0
    # The signed symplectic tensor must distinguish mixed and unmixed tests.
    assert P2(q*p,q*p)==-2 and P2(q*q,p*p)==4
    return {'original_Jordan_inverse_and_inverse_square_from_equations':True,
        'all_scalar_first_Poisson_terms_cancel_between_left_and_right':True,
        'mixed_qp_Moyal_sign_control':-2,'unmixed_qq_pp_Moyal_sign_control':4,
        'pure_geometric_shift_scope':'The original principal shift force is identically zero for b=0 as a function of lapse and remaining canonical variables. With leading clock b=0 identically, no pure scalar geometric shift correction is generated; lower source force and matrix subprincipal terms remain separate.'}


def main():
    started=time.monotonic();path=HERE/'source_clock_principal_jets.json'
    candidate=json.loads(path.read_text());count=bindings(candidate);assert candidate['root']==ROOT_ID
    deps=('independent_source_scalar_weyl_symbol','independent_source_common_weyl_symbol',
        'independent_source_principal_clock_cone','independent_source_coframe_volume_shape',
        'independent_source_common_volume_pencil')
    for name in deps:
        receipt=json.loads((HERE/(name+'.json')).read_text());count+=bindings(receipt);assert receipt['root']==ROOT_ID
    principal=json.loads((HERE/'source_principal_clock_cone.json').read_text());count+=bindings(principal)
    section=RawGaussSection();raw=RawLiveCoefficients();assert section.native.hashes==candidate['source_sha256']
    saved=candidate['actual_consumer'];p=decode(principal['actual_source_cotangent_witness']['canonical_p100'])
    eq(p,decode(saved['source_covector']['canonical_p100']))
    a,t,facts=original_coupled_phase_jets(section,raw,p);c=implicit_clock(a,t)
    zero(c['value']-raw.N)
    for j,key in ((a,'a0_2'),(t,'traceS2'),(c,'principal_clock')):compare(j,saved[key])
    for j,pd,qd in ((a,2,-3),(t,2,1),(c,0,2)):homogeneity(j,p,tuple(section.source[:6,0]),pd,qd)
    print('PASS independent full canonical200 A/T/C jets, implicit clock and both complete homogeneity laws',flush=True)
    first=quotient_jets(t,c);second=quotient_jets(first,c)
    p1=symplectic2(c,first);p2=symplectic2(c,second)
    zero(p1-s.sympify(saved['canonical_second_Moyal_contractions']['P2_C_T_over_C']))
    zero(p2-s.sympify(saved['canonical_second_Moyal_contractions']['P2_C_T_over_C2']))
    bracket=poisson(a,t);zero(bracket-s.sympify(saved['canonical_Poisson_A_T']))
    force=s.factor((p2/c['value']+p1/c['value']**2)/16)
    correction=s.factor(force*c['value']**3/t['value'])
    zero(force-s.sympify(saved['original_lapse_force_second_Moyal']))
    zero(correction-s.sympify(saved['geometric_clock_order_minus2']))
    assert force!=0 and correction!=0
    jordan=jordan_inverse_identity()
    print('PASS original Jordan inverse-square Moyal force, full symplectic contraction and nonzero geometric clock correction',flush=True)
    files=[Path(__file__),path,HERE/'source_clock_principal_jets.py',HERE/'source_principal_clock_cone.json',
        HERE/'independent_source_scalar_form_hamiltonian.py',HERE/'independent_source_quantum_gauss_section.py',
        HERE/'independent_source_coframe_live_ordering.py']+[HERE/(name+'.json') for name in deps]
    out={'verdict':'CERTIFIED_FULL_SOURCE_CANONICAL200_CLOCK_TWOJET_AND_SCALAR_JORDAN_MOYAL_FORCE',
        'root':ROOT_ID,'source_sha256':section.native.hashes,
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'source_binding_checks':count,'candidate_constructor_imported':False,
        'independent_method':'Simultaneous original affine12 equations for normal9 and residual3; all position and momentum derivatives generated by differentiating the original linear system. Raw epsilon-Hessian coframe, original native gauge Gram contractions and implicit 2AC^2=T generate all200 jets.',
        'original_equations':facts,'full200_componentwise_A_T_C_agreement':True,
        'all_momentum_and_configuration_dilation_identities':True,
        'canonical_Poisson_A_T':str(bracket),
        'canonical_second_Moyal_contractions':{'P2_C_T_over_C2':str(p2),'P2_C_T_over_C':str(p1)},
        'original_lapse_force_second_Moyal':str(force),'geometric_clock_order_minus2':str(correction),
        'Jordan_equations':jordan,
        'claim_scope':'Complete actual canonical principal-clock jets and their scalar geometric order-minus2 correction. The original order0 force, original Y, and matrix subprincipal clock products are not included in this geometric term.',
        'complete_order_minus2_clock_or_spectrum_certified':False,
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'independent_source_clock_principal_jets.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('PASS independent source principal clock jets',out['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
