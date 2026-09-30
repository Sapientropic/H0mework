#!/usr/bin/env python3
"""Actual 200-dimensional canonical jets of the source principal clock.

Both Gauss inverses are differentiated in every original slice direction.
The resulting Moyal contraction uses the original canonical symplectic form,
not a bracket imposed on compressed energy coefficients.
"""
from __future__ import annotations
import hashlib
import json
import time
import sympy as s
from dynamic import HERE, ROOT, ROOT_ID
from source_principal_clock_cone import SourcePrincipalClockCone
from source_canonical_star_temporal_reduction import bound
from source_coframe_legendre import rational
from source_lorentz_contact import clean, equal, encode

SIZE=100

class Jet:
    def __init__(self, value, gradient=None, Hessian=None):
        self.value=s.factor(value)
        self.gradient=s.zeros(2*SIZE,1) if gradient is None else rational(gradient)
        self.Hessian=s.zeros(2*SIZE) if Hessian is None else rational(Hessian)
    def __add__(self, other):
        if not isinstance(other,Jet):other=Jet(other)
        return Jet(self.value+other.value,self.gradient+other.gradient,self.Hessian+other.Hessian)
    def __mul__(self, other):
        if not isinstance(other,Jet):other=Jet(other)
        return Jet(self.value*other.value,self.gradient*other.value+other.gradient*self.value,
            self.Hessian*other.value+other.Hessian*self.value+
            self.gradient*other.gradient.T+other.gradient*self.gradient.T)
    def power(self, exponent):
        c=s.factor(self.value**exponent)
        return Jet(c,exponent*c/self.value*self.gradient,
            exponent*c/self.value*self.Hessian+
            exponent*(exponent-1)*c/self.value**2*self.gradient*self.gradient.T)
    def encode(self):
        return {'value':str(self.value),'gradient200':encode(self.gradient),'Hessian200':encode(self.Hessian)}


def symplectic_hessian(H):
    return H[SIZE:,SIZE:].row_join(-H[SIZE:,:SIZE]).col_join(
        (-H[:SIZE,SIZE:]).row_join(H[:SIZE,:SIZE]))


def moyal2(a,b):
    return s.factor(sum(value*b.Hessian[i,j] for (i,j),value in symplectic_hessian(a.Hessian).todok().items()))


def poisson(a,b):
    return s.factor((a.gradient[:SIZE,:].T*b.gradient[SIZE:,:]-
                     a.gradient[SIZE:,:].T*b.gradient[:SIZE,:])[0])


def generate():
    model=SourcePrincipalClockCone(); f=model.source_factors(); p,point=model.actual_covector(f)
    native=model.native; section=model.section; raw=f['data']['scalar']; graph=native.graph
    free=tuple(j-6 for j in section.free if j>=6); piv=tuple(j-6 for j in section.pivots)
    y=section.b0[6:,:]; O=graph.O; G=clean(O.T*O); F=raw['F']; B=raw['vectors']
    S=clean(s.Matrix.hstack(*(T*y for T in native.T_s)))
    U=rational(S[list(piv),:].inv()); T=rational(S[list(free),:]*U)
    W=rational(B[:,list(free)]-B[:,list(piv)]*T.T)
    p94=p[6:,:]; normal=rational(F*W*p94)
    E=graph.dual_R.row_join(s.zeros(70,33))
    equal(rational(E-O*F*W),f['scalar_factor70x100'][:,6:])
    dD=[];dB=[];dM=[];dT=[];dW=[]
    for u in free:
        dd=clean(O.T*s.Matrix.hstack(*(R*graph.R[:,u] for R in native.rho_b))) if u<61 else s.zeros(9)
        db=clean(s.Matrix.vstack(*(R[:,u].T for R in native.T_b)))
        ds=clean(s.Matrix.hstack(*(R[:,u] for R in native.T_s)));dm=ds[list(piv),:]
        dt=rational((ds[list(free),:]-T*dm)*U)
        dw=rational(db[:,list(free)]-db[:,list(piv)]*T.T-B[:,list(piv)]*dt.T)
        dD.append(dd);dB.append(db);dM.append(dm);dT.append(dt);dW.append(dw)
    normal_p=rational(F*W)
    normal_z=[rational(F*(dw*p94-dd.T*normal)) for dw,dd in zip(dW,dD)]
    dn=s.zeros(9,200)
    for j,v in enumerate(normal_z):dn[:,6+j]=v
    dn[:,106:]=normal_p
    scalar=Jet((p94.T*E.T*E*p94)[0]+(normal.T*G*normal)[0],
        2*dn.T*G*normal,2*dn.T*G*dn)
    scalar.gradient[106:,:]+=2*E.T*E*p94
    scalar.Hessian[106:,106:]+=2*E.T*E
    # Pi depends on the residual3 inverse; its other 33 entries are the
    # original independent canonical gauge momenta.
    Ep=s.eye(97)[61:,list(piv)]; Ef=s.eye(97)[61:,list(free)]
    ga=rational(Ef-Ep*T.T); Pi=rational(ga*p94)
    equal(Pi,f['gauge_factor36x100']*p)
    dp=s.zeros(36,200)
    for j,dt in enumerate(dT):dp[:,6+j]=rational(-Ep*dt.T*p94)
    dp[:,106:]=ga
    q=s.Matrix(native.joint.coframe.q);v=q[0]*q[2]*q[5]
    L=s.Matrix([[q[0],0,0],[q[1],q[2],0],[q[3],q[4],q[5]]])
    Wq=rational(v*s.kronecker_product(L.inv()*L.inv().T,f['native_inverse_Gram'])/2)
    at=dict(zip(q,f['q'])); W0=rational(Wq.subs(at))
    trace=Jet((Pi.T*W0*Pi)[0],2*dp.T*W0*Pi,2*dp.T*W0*dp)
    for j in range(94):
        hp=rational(F*(dW[j]-dD[j].T*normal_p))
        gp=rational(-Ep*dT[j].T)
        for k in range(94):
            a=s.factor(2*(normal.T*G*hp[:,k])[0])
            b=s.factor(2*(Pi.T*W0*gp[:,k])[0])
            scalar.Hessian[6+j,106+k]+=a;scalar.Hessian[106+k,6+j]+=a
            trace.Hessian[6+j,106+k]+=b;trace.Hessian[106+k,6+j]+=b
        for k in range(j,94):
            ddt=rational(-dT[j]*dM[k]*U-dT[k]*dM[j]*U)
            ddw_p=rational(-dB[j][:,list(piv)]*dT[k].T*p94-
                dB[k][:,list(piv)]*dT[j].T*p94-B[:,list(piv)]*ddt.T*p94)
            hn=rational(F*(ddw_p-dD[j].T*normal_z[k]-dD[k].T*normal_z[j]))
            pi2=rational(-Ep*ddt.T*p94)
            a=s.factor(2*(normal.T*G*hn)[0]);b=s.factor(2*(Pi.T*W0*pi2)[0])
            scalar.Hessian[6+j,6+k]+=a;trace.Hessian[6+j,6+k]+=b
            if k!=j:
                scalar.Hessian[6+k,6+j]+=a;trace.Hessian[6+k,6+j]+=b
        if j in (30,60,93):print('PASS complete source Gauss inverse Hessian rows',j+1,'/94',flush=True)
    for j in range(6):
        dWq=rational(Wq.diff(q[j]).subs(at))
        trace.gradient[j]=(Pi.T*dWq*Pi)[0]
        for k in range(6):trace.Hessian[j,k]=(Pi.T*Wq.diff(q[j],q[k]).subs(at)*Pi)[0]
        cross=rational(2*Pi.T*dWq*dp)
        for k in range(6,200):trace.Hessian[j,k]=cross[k];trace.Hessian[k,j]=cross[k]
    volume=Jet(v.subs(at))
    for j in range(6):
        volume.gradient[j]=s.diff(v,q[j]).subs(at)
        for k in range(6):volume.Hessian[j,k]=s.diff(v,q[j],q[k]).subs(at)
    n=model.original.family.y[0];K=rational(model.original.family.cf['K']/n)
    K0=rational(K.subs(at));pq=p[:6,:]
    coframe=Jet((pq.T*K0*pq)[0]);coframe.gradient[100:106,:]=2*K0*pq
    coframe.Hessian[100:106,100:106]=2*K0
    for j in range(6):
        dj=rational(K.diff(q[j]).subs(at));coframe.gradient[j]=(pq.T*dj*pq)[0]
        for k in range(6):
            coframe.Hessian[j,k]=(pq.T*K.diff(q[j],q[k]).subs(at)*pq)[0]
            coframe.Hessian[j,100+k]=2*(dj*pq)[k];coframe.Hessian[100+k,j]=2*(dj*pq)[k]
    A=coframe+scalar*volume.power(-1)*s.Rational(-1,2)
    Tj=trace
    equal(A.Hessian,A.Hessian.T);equal(Tj.Hessian,Tj.Hessian.T)
    assert s.factor(A.value-s.sympify(point['source_a0_2']))==0
    assert s.factor(Tj.value-s.sympify(point['source_traceS2']))==0
    C=(Tj*A.power(-1)*s.Rational(1,2)).power(s.Rational(1,2))
    assert C.value==model.native.joint.coframe.N
    # The equation holds as a full canonical two-jet, not just in value.
    residual=C*C*A*2+Tj*(-1)
    assert residual.value==0
    equal(residual.gradient,s.zeros(200,1));equal(residual.Hessian,s.zeros(200))
    pure1=Tj*C.power(-1);pure2=Tj*C.power(-2)
    quantum_force=s.factor((moyal2(C,pure2)/C.value+moyal2(C,pure1)/C.value**2)/16)
    force_slope=-Tj.value/C.value**3
    clock_correction=s.factor(-quantum_force/force_slope)
    assert quantum_force!=0 and clock_correction!=0
    print('PASS full canonical200 principal-clock two-jet and nonzero original Jordan Moyal force',flush=True)
    return model,{'source_covector':point,'a0_2':A.encode(),'traceS2':Tj.encode(),'principal_clock':C.encode(),
        'full_principal_clock_equation_twojet_zero':True,
        'canonical_Poisson_A_T':str(poisson(A,Tj)),
        'canonical_second_Moyal_contractions':{'P2_C_T_over_C2':str(moyal2(C,pure2)),
            'P2_C_T_over_C':str(moyal2(C,pure1))},
        'original_lapse_force_second_Moyal':str(quantum_force),
        'geometric_clock_order_minus2':str(clock_correction),
        'all_shift_pure_geometric_force_terms_zero':True,
        'actual_gauge_second_inverse_derivatives_paid':94*94,
        'actual_scalar_second_inverse_derivatives_paid':94*94,
        'scope':'The displayed correction is the actual scalar Moyal part of the order-zero original force at the generated source clock cone point. Complete clock order-minus2 also consumes original force degree0 including Y and the generated matrix subprincipal clock terms.'}


def main():
    started=time.monotonic()
    deps=('source_principal_clock_cone','independent_source_principal_clock_cone',
        'source_scalar_weyl_symbol','independent_source_scalar_weyl_symbol',
        'source_common_weyl_symbol','independent_source_common_weyl_symbol')
    for name in deps:bound(name)
    model,actual=generate()
    files=[HERE/(name+'.json') for name in deps]+[HERE/name for name in (
        'source_clock_principal_jets.py','source_principal_clock_cone.py',
        'source_scalar_weyl_symbol.py','source_common_weyl_symbol.py','source_quantum_gauss_section.py')]
    out={'root':ROOT_ID,'scope':'SOURCE_FULL_CANONICAL200_PRINCIPAL_CLOCK_TWOJET_AND_FIRST_SCALAR_MOYAL_FORCE',
        'source_sha256':model.native.graph.common.source_hashes,
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'canonical_convention':'All100 actual coordinates followed by their100 canonical momenta; P2 uses the original canonical symplectic tensor.',
        'same_primary_graph_identity':'J_C X=(C star X+X star C)/2=C X-P2(C,X)/8+lower canonical order for scalar leading C. Thus the order-zero correction of J_C^-2(T)/2 is [P2(C,T/C^2)/C+P2(C,T/C)/C^2]/16.',
        'actual_consumer':actual,'complete_order_minus2_clock_or_spectrum_claimed':False,
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'source_clock_principal_jets.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('PASS source principal clock canonical jets',out['elapsed_seconds'],'seconds',flush=True)

if __name__=='__main__':main()
