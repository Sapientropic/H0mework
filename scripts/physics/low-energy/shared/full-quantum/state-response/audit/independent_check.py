#!/usr/bin/env python3
"""Reverse-bit full CAR, direct source matrix inverses and independent causal weights."""
from collections import Counter
from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path
import time

import sympy as s
from sympy.polys.matrices import DomainMatrix

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[5]
BASE=ROOT/'Verification/physics/low-energy-phenomenology'


@lru_cache(None)
def simplify(value): return s.radsimp(s.cancel(s.expand(value)))


def clean(matrix): return s.SparseMatrix(matrix).applyfunc(simplify)


def equal(left,right): assert not clean(left-right).todok()


def decode(record,symbols=None):
    return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(value,locals=symbols or {})
        for i,j,value in record['entries']})


def components(matrix):
    adjacent={j:set() for j in range(matrix.rows)}
    for i,j in matrix.todok(): adjacent[i].add(j);adjacent[j].add(i)
    remaining=set(adjacent);groups=[]
    while remaining:
        queue=[min(remaining)];group=set(queue)
        while queue:
            for j in adjacent[queue.pop()]-group: group.add(j);queue.append(j)
        remaining-=group;groups.append(sorted(group))
    return groups


class ReverseBitFock:
    def __init__(self,n): self.n=n
    def flag(self,j): return 1 << (self.n-1-j)
    def initial(self,w): return {self.flag(i):v for (i,_),v in w.todok().items()}
    def step(self,bits,j,create):
        bit=self.flag(j)
        if bool(bits&bit)==create:return None
        return bits^bit,(-1)**(bits&(bit-1)).bit_count()
    def number(self,A,state):
        out={}
        columns={}
        for (i,j),v in A.todok().items():columns.setdefault(j,[]).append((i,v))
        for bits,amplitude in state.items():
            for j,entries in columns.items():
                removed=self.step(bits,j,False)
                if removed is None:continue
                middle,sign=removed
                for i,value in entries:
                    created=self.step(middle,i,True)
                    if created is None:continue
                    output,second=created
                    out[output]=out.get(output,0)+amplitude*sign*second*value
        return {bits:simplify(v) for bits,v in out.items() if simplify(v)!=0}
    def pair(self,state,result):
        return simplify(sum(s.conjugate(value)*result.get(bits,0) for bits,value in state.items()))


def main():
    start=time.monotonic()
    phase=json.loads((BASE/'full-phase/receipt.json').read_text())
    full=json.loads((BASE/'full-quantum/receipt.json').read_text())
    old=json.loads((BASE/'occupied-response/receipt.json').read_text())
    vertices=json.loads((BASE/'matter-vertices/receipt.json').read_text())
    active=json.loads((BASE/'active-gauge/receipt.json').read_text())
    candidate=json.loads((HERE.parent/'receipt.json').read_text())
    causal=json.loads((HERE.parent/'time-receipt.json').read_text())
    for record in [full,old,vertices,candidate,causal]: assert record['source_sha256']==phase['source_sha256']
    for name,digest in phase['source_sha256'].items():assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest
    eye=lambda n:s.eye(n,cls=s.SparseMatrix)
    zero=lambda n:s.zeros(n,cls=s.SparseMatrix)
    n,omega=s.sympify(phase['source_lapse']),s.sympify(phase['source_frequency'])
    C=[decode(value) for value in phase['principal_coefficients']]
    gamma0=clean(n*C[0]/s.I)
    gamma5=s.kronecker_product(s.diag(-1,-1,1,1,cls=s.SparseMatrix),eye(63))
    S=clean(gamma0*gamma5);Q=decode(phase['phase_generator'])
    H=decode(full['original_H_full']);h=clean(H-omega*Q)
    spatial=[clean(-n*gamma0*c/s.I) for c in C[1:]]
    w=s.MutableSparseMatrix(252,1,{})
    b2=list(itertools.combinations(range(7),2))
    for spin,pair,a in [(0,(1,5),1),(1,(0,5),-1),(2,(1,5),1),(3,(0,5),-1)]:
        w[spin*63+7+b2.index(pair),0]=s.Rational(a,2)
    w=s.SparseMatrix(w);P=clean(w*w.H)
    equal(w.H*w,s.ones(1));equal(P*P,P);equal(h*w,s.zeros(252,1));equal(w.H*h,s.zeros(1,252))
    assert clean(P*H-H*P).todok()
    frame=decode(old['occupied_frame']);equal(frame*decode(old['source_prepared']),w)
    equal(Q*frame,gamma5*frame)
    p=s.symbols('p0:4',real=True);symbol_map={str(x):x for x in p};pzero=dict.fromkeys(p,0)
    Ts=[];Bs=[];groups={};derivative_channels=[];full_Q_mismatches=0
    for number,row in enumerate(vertices['primitive_vertices']):
        V=decode(row['operator'],symbol_map);V0=V.subs(pzero)
        T=clean(gamma0*(V0+V.diff(p[0])*(-s.I*h)))
        B=clean(s.sqrt(2)*(S*V0+V0.H*S)/2)
        Ts.append(T);Bs.append(B);groups.setdefault(row['group'],[]).append(number)
        equal(B.H,B)
        if V.diff(p[0]).todok():
            derivative_channels.append([row['group'],row['coordinate']])
            assert clean(T-gamma0*V0).todok()
        if row['group']=='gauge_A':
            equal(T.H,T);equal(B,-s.sqrt(2)*gamma5*T)
            equal(Q*T,T*Q);equal(Q*B,B*Q)
            equal((eye(252)-frame*frame.T)*T*frame,s.zeros(252,12))
            equal((eye(252)-frame*frame.T)*B*frame,s.zeros(252,12))
            if clean(B+s.sqrt(2)*Q*T).todok():full_Q_mismatches+=1
    assert derivative_channels==candidate['coframe_time_derivative_channels']
    assert full_Q_mismatches>0
    fock=ReverseBitFock(252);state=fock.initial(w)
    Ts_state=[fock.number(T,state) for T in Ts];Bs_state=[fock.number(B,state) for B in Bs]
    Tmean=[fock.pair(state,out) for out in Ts_state];Bmean=[fock.pair(state,out) for out in Bs_state]
    connected=decode(candidate['connected_equal_time_static_jet'])
    reversed_connected=decode(candidate['reverse_connected_equal_time_static_jet'])
    count=0
    for b,B in enumerate(Bs):
        for c,T in enumerate(Ts):
            first=fock.pair(state,fock.number(B,Ts_state[c]))-Bmean[b]*Tmean[c]
            second=fock.pair(state,fock.number(T,Bs_state[b]))-Tmean[c]*Bmean[b]
            assert simplify(first-connected[b,c])==0
            assert simplify(second-reversed_connected[b,c])==0
            count+=2
    scalar=groups['scalar']
    scalar_open=s.SparseMatrix.hstack(*[Ts[i]*w for i in scalar])
    scalar_connected=connected.extract(scalar,scalar)
    assert len(scalar_open.todok())==20 and len(scalar_connected.todok())==36
    equal(sum((Ts[i]*Ts[j] for i in scalar for j in scalar),zero(252)),zero(252))
    print('PASS reverse-bit full49928 CAR words, full gamma5 weights, 35 complex scalar channels',flush=True)

    cache={}
    def inverse(matrix):
        entries={}
        for group in components(matrix):
            block=s.ImmutableMatrix(matrix.extract(group,group))
            if block not in cache:
                domain=DomainMatrix.from_Matrix(block,extension=True).to_field()
                inv=clean(domain.inv().to_Matrix())
                equal(block*inv,eye(len(group)));equal(inv*block,eye(len(group)))
                cache[block]=inv
            for (i,j),value in cache[block].todok().items():entries[group[i],group[j]]=value
        return s.SparseMatrix(matrix.rows,matrix.cols,entries)
    gauge=groups['gauge_A'];Tcol=s.SparseMatrix.hstack(*[Ts[i]*w for i in gauge]);Bcol=s.SparseMatrix.hstack(*[Bs[i]*w for i in gauge])
    Trow=Tcol.H;Brow=Bcol.H
    Hessian=s.MutableSparseMatrix(289,289,{})
    for i,j,powers,value in active['Fourier_Jacobi_entries']:
        Hessian[i,j]+=s.sympify(value)*s.prod(p[mu]**power for mu,power in enumerate(powers))
    Hessian=s.SparseMatrix(Hessian);fields=active['fields']
    matter=[i for i,row in enumerate(fields) if row['group'] in ['primal_H','dual_H']]
    gauges=[i for i,row in enumerate(fields) if row['group']=='gauge_A']
    samples=[];pole_witnesses=[]
    for sample,saved in zip(old['samples'],candidate['samples']):
        E=s.sympify(sample['energy']);k=list(map(s.sympify,sample['momentum']));z=E+s.I*omega
        hk=clean(h+sum((x*A for x,A in zip(k,spatial)),zero(252)))
        hm=clean(h-sum((x*A for x,A in zip(k,spatial)),zero(252)))
        rp,rm=inverse(z*eye(252)-hk),inverse(z*eye(252)+hm)
        plus=clean(Brow*rp*Tcol);minus=clean((Trow*rm*Bcol).T);pi=clean(4*(plus-minus))
        equal(pi,decode(saved['upper_half_plane_current_response']))
        assert clean(4*plus-pi).todok() and clean(pi-pi/4).todok()
        assert clean(4*(Trow*rp*Tcol-(Trow*rm*Tcol).T)-pi).todok()
        Hsample=clean(Hessian.subs(dict(zip(p,[-s.I*z,*[s.I*x for x in k]]))))
        M=Hsample.extract(matter,matter);Minv=inverse(M)
        equal(M*Minv,eye(48));equal(Minv*M,eye(48))
        response=clean(-Minv*Hsample.extract(matter,gauges))
        residual=clean(Hsample[:,matter]*response+Hsample[:,gauges])
        equal(residual[matter,:],s.zeros(48));equal(Hsample.extract(gauges,matter)*response,pi)
        equal(residual[gauges,:],Hsample.extract(gauges,gauges)+pi)
        assert residual.todok()
        rk=inverse(E*eye(12)-frame.T*hk*frame);rminus=inverse(E*eye(12)+frame.T*hm*frame)
        equal(rk,decode(sample['twelve_mode_positive_resolvent']));equal(rminus,decode(sample['twelve_mode_negative_resolvent']))
        realpi=clean(4*(Brow*frame*rk*frame.T*Tcol-(Trow*frame*rminus*frame.T*Bcol).T))
        equal(realpi,decode(saved['real_limit_current_response']))
        for group in components(E*eye(252)-hk):
            block=s.ImmutableMatrix((E*eye(252)-hk).extract(group,group))
            if DomainMatrix.from_Matrix(block,extension=True).to_field().det().is_zero:
                v=s.MutableSparseMatrix(252,1,{})
                for i,value in enumerate(block.nullspace()[0]):v[group[i],0]=value
                v=clean(v);equal((E*eye(252)-hk)*v,s.zeros(252,1))
                equal(frame.T*v,s.zeros(12,1))
                pole_witnesses.append({'label':sample['label'],'side':'plus','nonzero_vector':[(i,str(value)) for (i,_),value in v.todok().items()]})
                break
        def channel(A,target,incoming):return s.SparseMatrix(756,756,{(252*target+i,252*incoming+j):v for (i,j),v in A.todok().items()})
        T,B=Ts[gauge[0]],Bs[gauge[0]]
        tf=channel(T,1,0)+channel(T,0,2);br=channel(B*rp,0,1)+channel(rm*B,2,0)
        wf=s.SparseMatrix.vstack(w,s.zeros(504,1));transfer=ReverseBitFock(756);incoming=transfer.initial(wf)
        four_first=transfer.pair(incoming,transfer.number(br,transfer.number(tf,incoming)))
        four_second=transfer.pair(incoming,transfer.number(tf,transfer.number(br,incoming)))
        assert simplify(4*(four_first-four_second)-pi[0,0])==0
        assert pi[0,0]!=0
        assert transfer.pair(incoming,transfer.number(tf,incoming))==0
        assert transfer.pair(incoming,transfer.number(br,incoming))==0
        samples.append({'label':sample['label'],'full252_positive_damping_two_sided_inverses':True,
            'all2304_Schur_entries':True,'all289_rows_retained':True,
            'nonzero_residual_rows':dict(Counter(fields[i]['group'] for i in {i for i,j in residual.todok()})),
            'real_H12_denominators_both_invertible':True,'same756_full_CAR_channel00_matches':True})
        print('PASS source full252/direct48 inverse, all289 rows and756 fullCAR',sample['label'],flush=True)
    assert pole_witnesses

    # Independent H12 spectral projectors, generated from its actual characteristic polynomial.
    small=clean(frame.T*h*frame/omega)
    rates=list(small.eigenvals());projectors={}
    for rate in rates:
        projector=eye(12)
        for other in rates:
            if rate!=other:projector=clean(projector*(small-other*eye(12))/(rate-other))
        equal(projector**2,projector);equal(small*projector,rate*projector)
        projectors[rate*omega]=clean(frame*projector*frame.T)
    equal(sum(projectors.values(),zero(252)),frame*frame.T)
    weights={}
    for rate,projector in projectors.items():
        weights[simplify(rate)]=(clean(4*s.I*(Trow*projector*Bcol).T),clean(-4*s.I*Brow*projector*Tcol))
    for row in causal['source_generated_spectral_weights']:
        rate=simplify(s.sympify(row['rate']))
        expected=weights.get(rate,(zero(48),zero(48)))
        equal(decode(row['positive_time_weight']),expected[0]);equal(decode(row['negative_time_weight']),expected[1])
    t=s.sympify(causal['time']);response_time=zero(48);response_frequency=zero(48);z=(3+s.I)*omega
    for rate,(left,right) in weights.items():
        response_time+=s.expand_complex(s.exp(s.I*rate*t))*left+s.expand_complex(s.exp(-s.I*rate*t))*right
        response_frequency+=s.I/(z+rate)*left+s.I/(z-rate)*right
    time_difference=clean(response_time-decode(causal['retarded_time_kernel']))
    # The two exact trigonometric routes may use different nested-radical representatives.
    assert all(s.simplify(value)==0 for value in time_difference.todok().values()), list(time_difference.todok().items())[:3]
    equal(clean(response_frequency),decode(candidate['samples'][0]['upper_half_plane_current_response']))
    print('PASS independently generated H12 spectral weights and original time/frequency response',flush=True)
    result={'status':'PASS','full_CAR_words_independent_reverse_bit_order':count,
        'full252_B_not_equal_minus_s_Q_T_channels':full_Q_mismatches,
        'actual_P_H_commutator_nnz':len(clean(P*H-H*P).todok()),
        'source_scalar_open_force_nnz':len(scalar_open.todok()),'canonical_scalar_connected_nnz':len(scalar_connected.todok()),
        'coframe_derivative_channels':derivative_channels,'source_amplitude_squared':4,
        'samples':samples,'full_real_frequency_complement_pole_witnesses':pole_witnesses,
        'real_limit_scope':'only the source gauge T/B H12 legs; full252 inverse not evaluated at a witnessed real pole',
        'spectral_projectors_generated_from_actual_H12':sorted(map(str,rates)),
        'all_causal_weights_and_time_kernel_match':True,'inverse_algorithm':'direct algebraic-number-field inverses of actual full252 and raw48 source blocks',
        'independent_dual_vs_canonical_reader_kept_distinct':True,
        'seconds':round(time.monotonic()-start,3)}
    (HERE/'independent-receipt.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
