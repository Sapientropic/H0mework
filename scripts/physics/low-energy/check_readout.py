#!/usr/bin/env python3
"""Independent checks. This module does not import the result producer."""
import argparse, hashlib, itertools, json, re
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path

def matrix(a): return [[Q(x) for x in row] for row in a]
def trans(a): return list(map(list, zip(*a)))
def product(a,b):
    return [[sum(x*y for x,y in zip(row,col)) for col in trans(b)] for row in a]
def identity(n): return [[Q(i==j) for j in range(n)] for i in range(n)]
def difference(a,b): return [[x-y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def polynomial_product(a,b):
    c=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c

def determinant_mod(a,p):
    a=[row[:] for row in a]; n=len(a); d=1
    for j in range(n):
        pivot=next((i for i in range(j,n) if a[i][j]%p),None)
        if pivot is None: return 0
        if pivot!=j: a[pivot],a[j]=a[j],a[pivot]; d=-d
        v=a[j][j]%p; d=d*v%p; inv=pow(v,-1,p)
        for i in range(j+1,n):
            f=a[i][j]*inv%p
            for k in range(j+1,n): a[i][k]=(a[i][k]-f*a[j][k])%p
    return d%p

def check_block(block):
    k,b,r,c,p0=[matrix(block[key]) for key in ['K','B','B_inverse_K','inverse_on_massive_current_slots','light_projector']]
    n=len(k); unit=identity(n); zero=[[Q(0)]*n for _ in range(n)]
    assert trans(k)==k and trans(b)==b and product(b,r)==k
    assert product(p0,p0)==p0 and product(k,p0)==zero
    assert trans(c)==c and product(c,k)==difference(unit,p0)
    assert product(k,c)==difference(unit,trans(p0))
    assert product(product(k,c),k)==k and product(product(c,k),c)==c
    pol=[Q(x) for x in block['characteristic_polynomial']]
    fact=[Q(x) for x in block['remaining_factor']]
    for f in block['linear_factors']:
        for _ in range(f['multiplicity']): fact=polynomial_product(fact,[Q(1),-Q(f['root'])])
    assert fact==pol and len(pol)==n+1
    for prime in (1009,1013):
        reduce=lambda q:(q.numerator*pow(q.denominator,-1,prime))%prime
        rr=[[reduce(x) for x in row] for row in r]; pp=[reduce(x) for x in pol]
        for x in range(n+1):
            val=0
            for coefficient in pp: val=(val*x+coefficient)%prime
            a=[[(int(i==j)*x-rr[i][j])%prime for j in range(n)] for i in range(n)]
            assert determinant_mod(a,prime)==val
    rem=[Q(x) for x in block['remaining_factor']]
    intervals=block['positive_root_intervals']
    def value(x):
        y=Q(0)
        for c in rem: y=y*x+c
        return y
    if len(rem)>1:
        assert len(intervals)==len(rem)-1
        last=Q(-1)
        for interval in intervals:
            a,b=Q(interval['lower']),Q(interval['upper'])
            assert last<a<b and value(a)*value(b)<0
            assert float(a)<interval['approximation']<float(b)
            last=b

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--receipt',type=Path,required=True)
    args=parser.parse_args(); data=json.loads(args.receipt.read_text())
    for name,digest in data['source_sha256'].items():
        assert hashlib.sha256((args.root/name).read_bytes()).hexdigest()==digest,name
    source=(args.root/'Lean/SaturationMonoid/PhysicsCore/SU7ExteriorYukawaMassSpectrum.lean').read_text()
    definition=source.split('def finiteGenerationScalarSubset :',1)[1].split('\ndef ',1)[0]
    terms=re.findall(r'\|\s*[01],\s*[01]\s*=>\s*\{([^}]+)\}',definition)
    scalar=Counter(tuple(sorted(data['basis_names'].index(x.strip()) for x in term.split(','))) for term in terms)
    assert dict(scalar)=={tuple(s):n for s,n in data['joint_scalar_terms']}
    ys=data['yukawa']; ins=[tuple(x) for x in ys['input_basis']]; outs=[tuple(x) for x in ys['output_basis']]
    y=[]
    for out in outs:
        row=[]
        for inp in ins:
            complement=tuple(i for i in out if i not in inp); v=0
            if set(inp).issubset(out) and len(complement)==4:
                crossings=sum(a>b for a in inp for b in complement)
                v=scalar[complement]*((-1)**crossings)
            row.append(Q(v))
        y.append(row)
    assert y==matrix(ys['matrix'])
    gram=product(y,trans(y)); assert gram==matrix(ys['output_gram'])
    assert all(i==j or gram[i][j]==0 for i in range(7) for j in range(7))
    rank=sum(gram[i][i]>0 for i in range(7))
    assert rank==ys['rank']==5 and ys['input_nullity']==21-rank
    def traces(degrees):
        result=[Q(0),Q(0),Q(0)]
        for degree in degrees:
            for s in itertools.combinations(range(7),degree):
                weights=[Q(int(0 in s)-int(1 in s),2),Q(int(3 in s)-int(4 in s),2),Q(int(5 in s)-int(6 in s))]
                for i,w in enumerate(weights): result[i]+=w*w
        return result
    assert [Q(x) for x in data['scalar_traces'][1:]]==traces([4])==[5,5,20]
    assert [Q(x) for x in data['weyl_traces'][1:]]==traces(data['weyl_degrees'])==[8,8,32]
    for key in ['mother_orbit_gram_not_48_dynamical_vectors','native_P286_scalar_gauge_block','P286_with_mother_metric_comparison_not_native']:
        check_block(data[key])
    assert len(data['factorized_current_operators'])==12 and data['proton_lifetime'] is None
    print('PASS: source hashes; independent complement-wedge matrix; Cartan-weight traces; exact projected-inverse identities; factor reconstruction; complete cubic root isolation; determinants modulo 1009 and 1013')

if __name__=='__main__': main()
