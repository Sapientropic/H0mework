#!/usr/bin/env python3
"""Reconstituted A/B external direction and its source shifted Ward identities."""
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
        FQ/'packet-gauge-constitutive-vertex/vertices.json']
    actual,rotation,primitive,oldward,bijet,incoming,constitutive=map(read,paths)
    for path,digest in actual['source_sha256'].items():
        assert hashlib.sha256((original.source.ROOT/path).read_bytes()).hexdigest()==digest,path
    idx={(f['group'],tuple(f['coordinate'])):i for i,f in enumerate(actual['fields'])}
    N=s.sympify(actual['source_lapse']);c=N*s.sqrt(2);lam=6*c*(1-s.I)
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
    oldE=matrix(next(r for r in constitutive['profiles'] if r['wave_sign']==0)['reconstituted_E1'])
    primitive_K1=K1
    constantV=original.ward.operator(primitive['H1'],values=pin)
    branches=[]
    for direction in [1,-1]:
        qext=[direction*k/2 for k in kin];kout=[k+d for k,d in zip(kin,qext)]
        pout=[lam,*[s.I*k for k in kout]]
        pe=[0,*[s.I*k for k in qext]]
        profile=next(r for r in constitutive['profiles'] if r['wave_sign']==direction)
        assert list(map(s.sympify,profile['external_derivative_symbol']))==pe
        complete_direction=matrix(profile['complete_background_direction'])
        extra=matrix(profile['additional_B_vertex'])
        V=clean(evaluate(selected['Q0_bijet'],[-v for v in pout],pin)+extra)
        E=clean(H(pe)*complete_direction)
        assert E==matrix(profile['reconstituted_E1'])
        assert all(E[i,0]==0 for i,f in enumerate(actual['fields']) if f['group']=='gauge_B')
        assert E[:9,:]==s.zeros(9,1)
        # These source Euler rows vanish; omitted Lorentz auxiliary actions
        # and the larger scalar action therefore contribute exactly zero.
        for group in ['Lorentz','gravity_B','multiplier']:
            assert all(E[i,0]==0 for i,f in enumerate(actual['fields']) if f['group']==group)
        Tg1joint=clean(s.SparseMatrix.hstack(*(M*complete_direction for M in gauge_actions)))
        K1=clean((Tg1joint*color).row_join(s.SparseMatrix.hstack(*(M*complete_direction for M in lorentz_actions))))
        assert clean(K1-primitive_K1).todok()
        Cg=clean(s.SparseMatrix.hstack(*(M.T*E for M in gauge_actions)))
        C=clean((Cg*color).row_join(s.SparseMatrix.hstack(*(M.T*E for M in lorentz_actions))))
        Hout=H(pout);Kout=evalK(pout);Kmout=evalK([-v for v in pout])
        assert clean(Hout*Kout)==s.zeros(289,9)
        residual=clean(V*Kin+Hout*K1+C)
        assert residual==s.zeros(289,9),('right shifted Ward',direction,list(residual.todok().items())[:3])
        residual12=clean(V*Tg_in+Hout*Tg1joint+Cg)
        assert residual12==s.zeros(289,12),('all12 shifted Ward',direction,list(residual12.todok().items())[:3])
        reverse=clean(evaluate(selected['Q0_bijet'],pin,[-v for v in pout])+extra)
        assert clean(reverse.T-V)==s.zeros(289)
        left=clean(Kmout.T*V+K1.T*Hin+C.T)
        assert left==s.zeros(9,289),('left shifted Ward',direction,list(left.todok().items())[:3])
        wrong_K1=clean(V*Kin+Hout*primitive_K1+C)
        assert wrong_K1.todok()
        deltaV=clean(V-constantV);deltaE=clean(E-oldE)
        assert deltaV.todok() and deltaE.todok()
        constant_vertex_error=clean(constantV*Tg_in+Hout*Tg1joint+Cg)
        assert constant_vertex_error.todok()
        branches.append({'external_sign':direction,'rho_out':str((1+s.Rational(direction,2))*rho),
            'physical_k_out':list(map(str,kout)),'physical_q_external':list(map(str,qext)),
            'physical_p_out':list(map(str,pout)),'V':encode(V),'E1':encode(E),'C1':encode(C),
            'K1':encode(K1),'complete_background_direction':encode(complete_direction),
            'E1_support_groups':sorted({actual['fields'][i]['group'] for i,j in E.todok()}),
            'all72_background_auxiliary_rows_zero':True,'old_primitive_K1_Ward_error_entries':len(wrong_K1.todok()),
            'gauge12_C1':encode(Cg),'K0_out':encode(Kout),'K0_minus_out':encode(Kmout),
            'right_shifted_289_by9_Ward':True,'right_shifted_289_by12_Ward':True,'left_shifted_9_by289_Ward':True,
            'wrong_constant_vertex_289_by12_Ward_error_entries':len(constant_vertex_error.todok()),
            'source_vertex_not_constant_H1':len(deltaV.todok()),'source_E1_not_constant_background_E1':len(deltaE.todok())})
        print('PASS original shifted insertion/Ward',direction,'V',len(V.todok()),'E1',len(E.todok()),'C1',len(C.todok()),flush=True)
    result={'scope':'STRIKE_RECONSTITUTED_A_B_DIFFERENT_MOMENTUM_INSERTION_AND_SOURCE_WARD',
        'source_sha256':actual['source_sha256'],
        'input_sha256':{str(path.relative_to(original.source.ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'primitive_external':'a_q=exp(i q.x) dx1 S01 and b_q=-star_e D_A(a_q)/sigma; coframe fixed in the external path, live in field variations',
        'rho_in':str(rho),'physical_lambda':str(lam),'normalized_x':'6*(1-I)',
        'physical_k_in':list(map(str,kin)),'physical_p_in':list(map(str,pin)),
        'frame':'original quarterY=1/5, quarterZ=1/3, common L unchanged',
        'K0_in':encode(Kin),'branches':branches,
        'Ward_identities':['V(pout,pin)K0(pin)+H0(pout)K1=-C1(q)',
            'K0(-pout)^T V(pout,pin)+K1^T H0(pin)=-C1(q)^T'],
        'contact_source':'K1_g=(D field_action_g)(a_q+b_q), C1_g=(D field_action_g)^T H0(p_ext)(a_q+b_q); no target response used',
        'cosine_amplitude_rule':'(a_q+a_-q)/2; no cosine factor inserted into either unit-amplitude Fourier vertex',
        'elapsed_seconds':round(time.monotonic()-start,3)}
    (HERE/'insertion.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS source insertion stage',result['elapsed_seconds'],flush=True)


if __name__=='__main__':main()
