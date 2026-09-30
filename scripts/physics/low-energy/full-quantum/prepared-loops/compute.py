#!/usr/bin/env python3
"""Full source CAR words with the actual preparation and pi-boundary weight."""
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4];BASE=ROOT/'Verification/physics/low-energy-phenomenology'
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
control=load('prepared_control',HERE.parent/'gauge-green/compute.py')
fock=load('source_car_words',HERE.parent/'state-response/compute.py')
clean,equal,decode,norm=control.clean,control.equal,control.decode,control.norm

def main():
    started=time.monotonic();phase=json.loads((BASE/'full-phase/receipt.json').read_text());vertices=json.loads((BASE/'matter-vertices/receipt.json').read_text())
    for r in [phase,vertices]:
        for path,digest in r['source_sha256'].items():assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest
    N=s.sympify(phase['source_lapse']);spin=s.sqrt(2);C=[decode(x) for x in phase['principal_coefficients']]
    B,Y=decode(phase['original_constant_B']),decode(phase['original_Y']);I=s.eye(252,cls=s.SparseMatrix);Z=s.zeros(252,cls=s.SparseMatrix)
    gamma0=clean(N*C[0]/s.I);gamma5=s.kronecker_product(s.diag(-1,-1,1,1),s.eye(63));S=clean(gamma0*gamma5)
    K=clean(-s.I*N*spin*S*C[0]);equal(K,spin*gamma5)
    Ci=clean(s.I*N*gamma0);equal(C[0]*Ci,I)
    basis=list(itertools.combinations(range(7),2));w=s.zeros(252,1)
    for j,pair,value in [(0,(1,5),1),(1,(0,5),-1),(2,(1,5),1),(3,(0,5),-1)]:w[63*j+7+basis.index(pair)]=s.Rational(value,2)
    w=s.SparseMatrix(w);equal(w.H*w,s.ones(1));prepared={(i,):value for i,value in enumerate(w) if value}
    raw=[clean(decode(r['operator'])/N) for r in vertices['primitive_vertices'] if r['group']=='gauge_A']
    ys=[clean(decode(r['operator'])/N) for r in vertices['primitive_vertices'] if r['group']=='scalar']
    P6=s.kronecker_product(s.eye(4),s.diag(s.eye(7),s.zeros(56)));equal(P6*w,s.zeros(252,1))
    cache={}
    def inverse(matrix):
        entries={}
        for group in control.components(matrix):
            block=s.ImmutableMatrix(matrix.extract(group,group))
            if block not in cache:
                dm=DomainMatrix.from_Matrix(block,extension=True).to_field();iv=dm.inv();assert dm.matmul(iv)==DomainMatrix.eye(dm.shape,dm.domain);cache[block]=clean(iv.to_Matrix())
            for (i,j),v in cache[block].todok().items():entries[group[i],group[j]]=v
        return s.SparseMatrix(252,252,entries)
    greens=[];free=[]
    for energy,damping,k in [(0,1,[0,0,0]),(s.Rational(1,3),s.Rational(2,5),[0,0,s.Rational(1,3)])]:
        D0=clean(-s.I*(energy+s.I*damping)*C[0]+B+sum((s.I*x*c for x,c in zip(k,C[1:])),Z));D=clean(D0+Y)
        g,g0=inverse(D),inverse(D0);equal(D*g,I);equal(D0*g0,I);assert clean(g-g0).todok();greens.append(g);free.append(g0)
    channels=[0,2,13,25];lines=[clean(greens[i%2]*raw[j]) for i,j in enumerate(channels)];diagonal=[clean(free[i%2]*raw[j]) for i,j in enumerate(channels)]
    def literal(matrices):
        state=prepared
        for matrix in reversed(matrices):state=fock.number_action(matrix,state)
        return norm(fock.read(prepared,state))
    words=0
    for length in [0,1,2,3]:
        for labels in itertools.product(range(4),repeat=length):
            first=[K]+[lines[i] for i in labels];second=[K]+[diagonal[i] for i in labels]
            actual=literal(first);expected=literal(second);assert norm(actual-expected)==0;words+=1
    print('PASS actual boundary-weighted complete Fock words',words,flush=True)
    scalar_nonzero=[];zero_reads=0
    for index,y in enumerate(ys):
        value=literal([K,lines[0],y,lines[2]])
        assert value==0;zero_reads+=1
        if clean(y*w).todok():scalar_nonzero.append(index)
    assert scalar_nonzero
    forces=[clean(-s.I*Ci*y) for y in ys];readers=[clean(-K*t) for t in forces];canonical=[clean((b+b.H)/2) for b in readers]
    columns=s.SparseMatrix.hstack(*[t*w for t in forces]);rows=s.SparseMatrix.vstack(*[w.H*b for b in readers]);realrows=s.SparseMatrix.vstack(*[w.H*b for b in canonical])
    original=clean(rows*columns);replacement=clean(realrows*columns)
    assert not original.todok();assert len(replacement.todok())==36
    print('PASS raw scalar force/reader zero; distinct canonical reader retains 36 entries',flush=True)
    # Source normalization controls remain independent of the grade simplification.
    assert literal([I])==1 and s.trace(I)==252
    T=clean(-s.I*Ci*S);equal(K*T,-N*spin*I)
    weighted=literal([K,T]);assert norm(weighted+N*spin)==0
    assert norm(weighted-s.trace(K*T))!=0
    identity4=norm(N*((2*spin*S*w).H*S*(2*w))[0]);assert norm(identity4-4*N*spin)==0
    current_fail=0
    for rawVertex in raw:
        force=clean(-s.I*Ci*rawVertex);reader=clean(-K*force)
        equal(reader,N*spin*S*rawVertex)
        expected=norm(N*((2*spin*S*w).H*rawVertex*(2*w))[0]);actual=norm(4*(w.H*reader*w)[0]);assert norm(expected-actual)==0
        if actual:current_fail+=1
    assert current_fail
    # Original source-generated return map is allowed outside the grade-preserving word class.
    index=scalar_nonzero[0];out=clean(ys[index]*w);row=next(i for i,v in enumerate(out) if v)
    dual=s.zeros(1,252);dual[0,row]=1;return_map=clean(w*dual)
    recovered=norm((w.H*return_map*ys[index]*w)[0]);assert recovered!=0
    badP=clean(w*w.H);lost=0
    for A in lines:
        for D in lines:
            if norm((w.H*K*A*D*w)[0]-(w.H*K*A*badP*D*w)[0])!=0:lost+=1
    assert lost
    result={'status':'PASS','source_hashes_current':True,'source_sha256':phase['source_sha256'],
      'full_dimension':252,'weighted_complete_Fock_words':words,'scalar_inserted_words_zero':zero_reads,
      'scalar_directions_with_nonzero_open_prepared_output':scalar_nonzero,
      'raw_scalar_connected_entries':0,'canonical_real_scalar_reader_connected_entries':36,
      'unit_prepared_read':1,'unit_bare_trace':252,'weighted_exchange_read':str(weighted),
      'original_gauge_source_reader_identity_all48':True,'actual_nonzero_gauge_current_channels':current_fail,
      'premature_rank_one_middle_compression_changes_words':lost,'return_map_detects_open_output':str(recovered),
      'seconds':round(time.monotonic()-started,3),
      'scope':'Finite source-prepared spectral words and their original pi-boundary weights. No continuum loop measure, physical choice of transfer denominators or additional stationary vacuum is inferred.'}
    (HERE/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':main()
