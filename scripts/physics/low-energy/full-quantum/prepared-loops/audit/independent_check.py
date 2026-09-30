#!/usr/bin/env python3
"""Original exterior arrows, chiral elimination and reverse-bit complete prepared words."""
from functools import lru_cache
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import re
import sys
import time

import sympy as s
from sympy.polys.matrices import DomainMatrix

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[5]
BASE=ROOT/'Verification/physics/low-energy-phenomenology'
CORE=ROOT/'Lean/SaturationMonoid/PhysicsCore'


@lru_cache(None)
def norm(value):return s.radsimp(s.cancel(s.expand(value)))


def clean(matrix):return s.SparseMatrix(matrix).applyfunc(norm)


def equal(left,right):assert not clean(left-right).todok()


def decode(record):return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(v) for i,j,v in record['entries']})


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module);return module


def main():
    started=time.monotonic()
    phase=json.loads((BASE/'full-phase/receipt.json').read_text())
    vertices=json.loads((BASE/'matter-vertices/receipt.json').read_text())
    saved=json.loads((HERE.parent/'receipt.json').read_text())
    for record in [phase,vertices,saved]:
        for path,digest in record['source_sha256'].items():assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest
    exterior=load('prepared_word_exterior',BASE/'mixed-symbol/audit/independent_check.py')
    car=load('prepared_word_car',BASE/'full-quantum/state-response/audit/independent_check.py')
    eye=lambda n:s.eye(n,cls=s.SparseMatrix)
    zero=lambda n:s.zeros(n,cls=s.SparseMatrix)
    N=s.sympify(phase['source_lapse']);spin=s.sqrt(2)
    gamma_text=(CORE/'DiracCliffordRepresentation.lean').read_text();gamma=[]
    for name in ['Zero','One','Two','Three']:
        text=gamma_text.split(f'def diracGamma{name} : DiracMatrix :=',1)[1].split(']',1)[0].split('!![',1)[1]
        gamma.append(s.SparseMatrix([[s.sympify(v.strip().replace('Complex.I','I')) for v in row.split(',')] for row in text.split(';')]))
    text=(CORE/'Stage9C/Material/SpinPair/ColorDoublet.lean').read_text().split('def sourceColorPauli',1)[1].split('theorem',1)[0]
    colors=[s.SparseMatrix([[s.sympify(v.strip().replace('Complex.I','I')) for v in row.split(',')] for row in body.split(';')]) for body in re.findall(r'!!\[([^\]]+)\]',text)]
    Gamma=[s.kronecker_product(g,eye(63)) for g in gamma]
    C=[clean(s.I*Gamma[0]/N)]+[clean(s.I*g) for g in Gamma[1:]]
    for a,b in zip(C,phase['principal_coefficients']):equal(a,decode(b))
    rho=[s.kronecker_product(eye(4),s.diag(*(exterior.exterior(s.diag(color,s.zeros(5)),d) for d in [6,2,4]),cls=s.SparseMatrix)) for color in colors]
    rotation=[gamma[2]*gamma[3],gamma[3]*gamma[1],gamma[1]*gamma[2]]
    B=clean(sum((C[j+1]*(spin/2*s.kronecker_product(rotation[j],eye(63))+3*spin/5*rho[j]) for j in range(3)),zero(252)))
    equal(B,decode(phase['original_constant_B']))
    basis={d:exterior.basis(d) for d in [2,4,6]};ys=[]
    for word in basis[4]:
        y=s.zeros(63,cls=s.SparseMatrix)
        for j,pair in enumerate(basis[2]):
            if set(pair).isdisjoint(word):
                y[basis[6].index(tuple(sorted(pair+word))),7+j]=exterior.wedge_sign(pair,word)
        ys.append(s.kronecker_product(s.diag(0,0,1,1),y))
    rawScalar=[clean(decode(row['operator'])/N) for row in vertices['primitive_vertices'] if row['group']=='scalar']
    for j,y in enumerate(ys):equal(rawScalar[j],y);equal(rawScalar[j+35],s.I*y)
    vacuum=[(0,1,2,6),(0,1,2,4),(0,1,5,6),(0,1,4,5)]
    Y=clean(sum((ys[basis[4].index(word)] for word in vacuum),zero(252)))
    equal(Y,decode(phase['original_Y']))
    rawGauge=[clean(decode(row['operator'])/N) for row in vertices['primitive_vertices'] if row['group']=='gauge_A']
    g5=s.kronecker_product(s.diag(-1,-1,1,1),eye(63));S=clean(Gamma[0]*g5)
    CI=clean(s.I*N*Gamma[0]);K=clean(-s.I*N*spin*S*C[0]);equal(K,spin*g5)
    I,Z=eye(252),zero(252);equal(C[0]*CI,I);equal(CI*C[0],I)
    P=s.kronecker_product(eye(4),s.diag(eye(7),zero(56)));equal(P*P,P);equal(P.H,P)
    w=s.zeros(252,1,cls=s.SparseMatrix)
    for j,pair,c in [(0,(1,5),1),(1,(0,5),-1),(2,(1,5),1),(3,(0,5),-1)]:w[63*j+7+basis[2].index(pair)]=s.Rational(c,2)
    equal(w.H*w,s.ones(1));equal(P*w,s.zeros(252,1));equal(Y*w,s.zeros(252,1))
    for A in [*C,CI,K,B,*rawGauge]:equal(P*A,A*P)
    for y in rawScalar:equal(P*y,y);equal(y*P,Z)

    cache={};block_sizes=[]
    def invert_blocks(matrix):
        entries={}
        for group in car.components(matrix):
            block=s.ImmutableMatrix(matrix.extract(group,group));block_sizes.append(len(group))
            if block not in cache:
                domain=DomainMatrix.from_Matrix(block,extension=True).to_field()
                inverse=clean(domain.inv().to_Matrix())
                equal(block*inverse,eye(len(group)));equal(inverse*block,eye(len(group)))
                cache[block]=inverse
            for (i,j),value in cache[block].todok().items():entries[group[i],group[j]]=value
        return s.SparseMatrix(matrix.rows,matrix.cols,entries)
    def inverse(kernel):
        equal(kernel[:126,:126],zero(126))
        A,B0,Yright=kernel[:126,126:],kernel[126:,:126],kernel[126:,126:]
        Ai,Bi=invert_blocks(A),invert_blocks(B0)
        G=s.SparseMatrix.vstack(s.SparseMatrix.hstack(clean(-Bi*Yright*Ai),Bi),s.SparseMatrix.hstack(Ai,zero(126)))
        equal(kernel*G,I);equal(G*kernel,I)
        return G
    samples=[(0,1,[0,0,0]),(s.Rational(1,3),s.Rational(2,5),[0,0,s.Rational(1,3)]),
        (-s.Rational(2,7),s.Rational(3,2),[s.Rational(1,5),-s.Rational(1,4),s.Rational(1,3)])]
    greens=[];frees=[];resolvents=[];rfree=[]
    for energy,damping,k in samples:
        z=energy+s.I*damping;D0=clean(-s.I*z*C[0]+B+sum((s.I*x*c for x,c in zip(k,C[1:])),Z));D=clean(D0+Y)
        G,G0=inverse(D),inverse(D0);greens.append(G);frees.append(G0)
        arrow=clean(G-G0);assert arrow.todok();equal(P*G0,G0*P);equal(P*arrow,arrow);equal(arrow*P,Z)
        R,R0=clean(-s.I*G*C[0]),clean(-s.I*G0*C[0]);resolvents.append(R);rfree.append(R0)
        H=clean(-s.I*CI*(D+s.I*z*C[0]));equal((z*I-H)*R,I);equal(R*(z*I-H),I)
        assert clean(D*(s.I*CI*R)-I).todok()
    print('PASS independently rebuilt source and three chiral two-sided full252 inverses',flush=True)

    channels=[0,2,13,25]
    lines=[clean(greens[j%2]*rawGauge[a]) for j,a in enumerate(channels)]
    diagonal=[clean(frees[j%2]*rawGauge[a]) for j,a in enumerate(channels)]
    fock=car.ReverseBitFock(252)
    def literal(matrices,vector=w):
        initial=fock.initial(vector);state=initial
        for matrix in reversed(matrices):state=fock.number(matrix,state)
        return norm(fock.pair(initial,state))
    # A different primitive coframe changes K but still preserves exterior degree.
    e=s.diag(N,1,1,1);e[0,1]=s.Rational(1,10);e[1,1]=2
    ei=e.inv();newC0=clean(s.I*sum((ei[0,j]*Gamma[j] for j in range(4)),Z))
    otherK=clean(-s.I*abs(e.det())*spin*S*newC0);equal(otherK*P,P*otherK)
    phasepoint=s.kronecker_product(s.diag((1+s.I)/s.sqrt(2),(1+s.I)/s.sqrt(2),(1-s.I)/s.sqrt(2),(1-s.I)/s.sqrt(2)),eye(63))
    later=clean(phasepoint*w);equal(later.H*later,s.ones(1));equal(P*later,s.zeros(252,1))
    words=0;nonzero_words=0
    labels=[item for length in range(4) for item in itertools.product(range(4),repeat=length)]
    labels.extend([(0,1,2,3,0),(3,2,1,0,3)])
    for vector in [w,later]:
        for weight in [K,otherK]:
            for word in labels:
                actual=literal([weight]+[lines[i] for i in word],vector)
                expected=literal([weight]+[diagonal[i] for i in word],vector)
                assert norm(actual-expected)==0;words+=1;nonzero_words+=bool(actual)
    assert nonzero_words
    open_scalar=[]
    for j,y in enumerate(rawScalar):
        assert literal([K,lines[0],y,lines[2]])==0
        if clean(y*w).todok():open_scalar.append(j)
    assert open_scalar==saved['scalar_directions_with_nonzero_open_prepared_output']
    assert len(open_scalar)==18
    projection=clean(w*w.H)
    lost=sum(norm((w.H*K*A*D*w)[0]-(w.H*K*A*projection*D*w)[0])!=0 for A in lines for D in lines)
    assert lost==saved['premature_rank_one_middle_compression_changes_words']==6

    forces=[clean(-s.I*CI*A) for A in rawGauge];readers=[clean(-K*T) for T in forces]
    for A,T,reader in zip(rawGauge,forces,readers):
        equal(reader,N*spin*S*A)
        assert norm(N*((2*spin*S*w).H*A*(2*w))[0]-4*(w.H*reader*w)[0])==0
        equal(reader,-spin*g5*T)
    Q=clean(g5+2*P)
    wrong_q=sum(bool(clean(reader+spin*Q*T).todok()) for T,reader in zip(forces,readers));assert wrong_q==48
    sf=[clean(-s.I*CI*y) for y in rawScalar];sr=[clean(-K*t) for t in sf]
    left=s.SparseMatrix.vstack(*[w.H*b for b in sr]);right=s.SparseMatrix.hstack(*[t*w for t in sf])
    equal(left*right,s.zeros(70));canonical=s.SparseMatrix.vstack(*[w.H*clean((b+b.H)/2) for b in sr])
    real=clean(canonical*right);assert len(real.todok())==36
    for t,b in zip(sf,sr):equal(P*t,t);equal(t*P,Z);equal(P*b,b);equal(b*P,Z)
    print('PASS complete weighted words, open scalar and distinct canonical-reader controls',flush=True)

    fc=s.SparseMatrix.hstack(*[T*w for T in forces]);bc=s.SparseMatrix.hstack(*[reader*w for reader in readers])
    fr=s.SparseMatrix.vstack(*[w.H*T for T in forces]);br=s.SparseMatrix.vstack(*[w.H*reader for reader in readers])
    transfer=clean(br*resolvents[0]*fc-(fr*resolvents[2]*bc).T)
    free_transfer=clean(br*rfree[0]*fc-(fr*rfree[2]*bc).T);equal(transfer,free_transfer)
    assert transfer.todok()
    equal(br*resolvents[0]*right-(s.SparseMatrix.vstack(*[w.H*t for t in sf])*resolvents[2]*bc).T,s.zeros(48,70))
    equal(left*resolvents[0]*fc-(fr*resolvents[2]*s.SparseMatrix.hstack(*[b*w for b in sr])).T,s.zeros(70,48))
    three=car.ReverseBitFock(756);incoming=s.SparseMatrix.vstack(w,s.zeros(504,1));initial=three.initial(incoming)
    def channel(target,start,A):return s.SparseMatrix(756,756,{(target*252+i,start*252+j):v for (i,j),v in A.todok().items()})
    def read2(A,B):return three.pair(initial,three.number(A,three.number(B,initial)))
    transferred=0
    for a,b in itertools.product([0,2,13,25],repeat=2):
        T=forces[a];reader=readers[b]
        force=channel(1,0,T)+channel(0,2,T)
        observable=channel(0,1,clean(reader*resolvents[0]))+channel(2,0,clean(resolvents[2]*reader))
        assert three.pair(initial,three.number(force,initial))==0
        assert three.pair(initial,three.number(observable,initial))==0
        assert norm(read2(observable,force)-read2(force,observable)-transfer[b,a])==0
        transferred+=1
    print('PASS actual common756 full four-CAR transfer and all2304 source matrix entries',flush=True)

    # The existing original ReturnChannel is outside the permitted diagonal word class.
    direction=(0,2,3,4);y=ys[basis[4].index(direction)]
    output_row=2*63+basis[6].index((0,1,2,3,4,5));row=s.zeros(1,252);row[0,output_row]=1
    original_return=clean(2*w*row);amplitude=norm((row*y*(2*w))[0])
    assert amplitude==-1
    equal(original_return*y*w,amplitude*w)
    assert literal([original_return,y])==amplitude
    assert literal([original_return,projection,y])==0
    assert clean(P*original_return-original_return*P).todok()
    T=clean(-s.I*CI*S);weighted=literal([K,T]);assert norm(weighted+N*spin)==0
    complex_amplitude=literal([K,s.I*T]);assert norm(complex_amplitude+s.I*N*spin)==0
    assert complex_amplitude.is_real is False
    assert literal([I])==1 and s.trace(I)==252
    result={'status':'PASS','source_hashes_current':True,
        'source_reconstruction':'Literal Clifford/connection and bit exterior action; all35 complex and70 real scalar vertices match original source',
        'inverse_method':'Direct chiral block elimination, both original252 identities checked; no candidate inverse algorithm',
        'positive_damping_samples':3,'max_inverse_component':max(block_sizes),'weighted_reverse_bit_complete_words':words,
        'nonzero_weighted_word_reads':nonzero_words,'source_preparation_phases':2,'primitive_boundary_weights':2,
        'raw_scalar_inserted_words_zero':70,'open_scalar_directions':open_scalar,'premature_projection_failures':lost,
        'raw_scalar_reader_force_entries':0,'canonical_real_scalar_reader_force_nonzero_entries':len(real.todok()),
        'all48_original_gauge_amplitude4_and_volume':True,'wrong_full_Q_reader_operator_failures':wrong_q,
        'source_transfer_matrix_entries':2304,'full756_reverse_bit_four_word_responses':transferred,
        'both_raw_scalar_transfer_legs_zero':True,'original_ReturnChannel_complete_read':str(amplitude),
        'original_ReturnChannel_premature_P_read':0,'weighted_exchange_read':str(weighted),
        'complex_weighted_amplitude':str(complex_amplitude),
        'scope':'Original prepared weighted words and positive-damping spectral transfer; no assigned physical denominator pairing or continuum quantum measure.',
        'seconds':round(time.monotonic()-started,3)}
    (HERE/'independent-receipt.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
