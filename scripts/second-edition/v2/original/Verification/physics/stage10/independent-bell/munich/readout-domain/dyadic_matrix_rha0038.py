"""Exact sparse complex arithmetic and overflow-bounded integer matrix products."""
from fractions import Fraction as Q
import numpy as np

BITS = 96
LIMB_BITS = 24


def require(value, reason):
    if not value: raise ValueError(reason)


def norm(matrix, bits=BITS):
    return Q(sum(abs(a)+abs(b) for a,b in matrix.values()), 1 << bits)


def adjoint(matrix):
    return {(j,i):(a,-b) for (i,j),(a,b) in matrix.items()}


def round_matrix(matrix, before, after=BITS):
    scale = 1 << max(0,before-after); centre = {}; error = Q(0)
    for key,(a,b) in matrix.items():
        x,y = (round(Q(a,scale)),round(Q(b,scale))) if before >= after else (a << (after-before),b << (after-before))
        if x or y: centre[key] = x,y
        if before >= after: error += Q(abs(a-x*scale)+abs(b-y*scale), 1 << before)
    return centre,error


def multiply(left,right,bits=BITS):
    indexed = {}; result = {}
    for (k,j),z in right.items(): indexed.setdefault(k,[]).append((j,z))
    for (i,k),(a,b) in left.items():
        for j,(c,d) in indexed.get(k,()):
            x,y = result.get((i,j),(0,0)); result[i,j] = x+a*c-b*d,y+a*d+b*c
    return round_matrix(result,2*bits,bits)


def scale(matrix,value,bits=BITS):
    a,b = map(Q,value); result = {}; error = Q(0); quantum = 1 << bits
    for key,(c,d) in matrix.items():
        x,y = a*c-b*d,a*d+b*c; u,v = round(x),round(y)
        if u or v: result[key] = u,v
        error += (abs(x-u)+abs(y-v))/quantum
    return result,error


def add(target,other):
    for key,(a,b) in other.items():
        c,d = target.get(key,(0,0)); value=c+a,d+b
        if value == (0,0):target.pop(key,None)
        else:target[key]=value


def integer_product(left,right):
    """Each signed int64 dot remains below 2^63 before exact recombination."""
    a,b = np.asarray(left,dtype=object),np.asarray(right,dtype=object)
    require(a.ndim == b.ndim == 2 and a.shape[1] == b.shape[0], 'compatible complete integer matrices required')
    require(all(type(x) is int for x in a.flat) and all(type(x) is int for x in b.flat),
            'integer coefficients required; floating lookalikes are not arithmetic witnesses')
    mask=(1 << LIMB_BITS)-1
    require(a.shape[1]*mask*mask < 1 << 63, 'integer limb dot could overflow int64')
    def limbs(matrix):
        maximum=max((abs(x).bit_length() for x in matrix.flat),default=0)
        return [np.fromiter((((abs(x) >> shift)&mask)*(-1 if x < 0 else 1) for x in matrix.flat),
            dtype=np.int64,count=matrix.size).reshape(matrix.shape) for shift in range(0,max(1,maximum),LIMB_BITS)]
    out=np.zeros((a.shape[0],b.shape[1]),dtype=object)
    first,second=limbs(a),limbs(b)
    for i,x in enumerate(first):
        for j,y in enumerate(second):
            out += (x@y).astype(object)*(1 << (LIMB_BITS*(i+j)))
    return out


def complex_product(first,second):
    ar,ai = first; br,bi = second
    return integer_product(ar,br)-integer_product(ai,bi),integer_product(ar,bi)+integer_product(ai,br)
