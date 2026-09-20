#!/usr/bin/env python3
"""Source isometry for all 216 free complex matter directions and their time flow."""
from __future__ import annotations
import argparse
import itertools
import json
from pathlib import Path
import sys
import time
import sympy as s

HERE=Path(__file__).resolve().parent
BASE=HERE.parent
sys.path.insert(0,str(BASE))
sys.path.insert(0,str(BASE/'nonlinear-contact'))
import exact_readout as source
from slice_checks import GAMMA,COLOR,source_matrices


def clean(matrix):return s.SparseMatrix(matrix).applyfunc(s.expand)


def zero(matrix):
    value=clean(matrix)
    assert not value.todok(),list(value.todok().items())[:5]


def encode(matrix):
    return {'shape':list(matrix.shape),'entries':[[int(i),int(j),str(s.factor(value))]
        for (i,j),value in sorted(s.SparseMatrix(matrix).todok().items())]}


def decode(value,**symbols):
    return s.SparseMatrix(*value['shape'],{(i,j):s.sympify(value,locals=symbols)
        for i,j,value in value['entries']})


def exterior(matrix,degree):
    basis=list(itertools.combinations(range(7),degree)); positions={word:i for i,word in enumerate(basis)}
    result=s.MutableSparseMatrix(len(basis),len(basis),{})
    for column,word in enumerate(basis):
        for slot,old in enumerate(word):
            for new in range(7):
                coefficient=matrix[new,old]
                changed=word[:slot]+(new,)+word[slot+1:]
                if coefficient and len(set(changed))==degree:
                    result[positions[tuple(sorted(changed))],column]+=coefficient*source.sign(changed)
    return s.SparseMatrix(result)


def source_frame(internal,spin_start,internal_offset):
    frame=s.MutableSparseMatrix(252,2*internal.cols,{})
    for spin in range(2):
        for (row,column),value in s.SparseMatrix(internal).todok().items():
            frame[(spin_start+spin)*63+internal_offset+row,spin*internal.cols+column]=value
    return s.SparseMatrix(frame)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args(); started=time.monotonic()
    source_matrices(args.root)
    _,vacuum,degrees,hashes=source.parse_source(args.root)
    phase=json.loads((BASE/'full-phase/receipt.json').read_text())
    peripheral=json.loads((BASE/'canonical-peripheral/generator.json').read_text())
    vertices=json.loads((BASE/'matter-vertices/receipt.json').read_text())
    assert phase['source_sha256']==peripheral['source_sha256']==hashes
    assert vertices['source_sha256']==hashes
    P=decode(peripheral['primal_free_projection'])
    Z=decode(peripheral['dual_free_projection'])
    Q=decode(phase['phase_generator'])
    gamma=list(map(s.SparseMatrix,GAMMA)); G0=s.kronecker_product(gamma[0],s.eye(63))
    S=s.kronecker_product(gamma[0]*s.diag(-1,-1,1,1),s.eye(63))
    principal=list(map(decode,phase['principal_coefficients']))
    N=s.sympify(phase['source_lapse']); omega=s.sympify(phase['source_frequency'])
    B,Y,M=[decode(phase[key]) for key in ['original_constant_B','original_Y','stationary_scalar_mixing']]
    H0=clean(G0*(B+Y)/s.sqrt(2))
    Hspace=[clean(-s.kronecker_product(gamma[0]*gamma[j+1],s.eye(63))) for j in range(3)]
    Hstationary=clean(s.I*decode(peripheral['primal_constant_generator']))
    zero(H0-Hstationary-s.Rational(3,5)*Q)
    for h in [H0]+Hspace:
        zero(h*P-P*h);zero((h*P).H-h*P)
    zero(P.H-P);zero(P*P-P);assert s.trace(P)==216
    zero(P*Q-Q*P)
    bases={degree:list(itertools.combinations(range(7),degree)) for degree in degrees}
    internal_index=[(degree,word) for degree in degrees for word in bases[degree]]
    offsets={6:0,2:7,4:28}
    pauli=[clean(-2*s.I*color) for color in COLOR]
    spin_dot=sum((s.kronecker_product(matrix,matrix) for matrix in pauli),s.zeros(4))
    hsing0=s.Rational(3,2)*s.eye(2)
    hdouble0=s.Rational(3,2)*s.eye(4)+s.Rational(3,10)*spin_dot
    frames=[];blocks=[];groups=[];cursor=0
    for chi,spin_start in [(-1,0),(1,2)]:
        pinternal=P[spin_start*63:(spin_start+1)*63,spin_start*63:(spin_start+1)*63]
        for degree in degrees:
            dimension=len(bases[degree]);offset=offsets[degree]
            p=clean(pinternal[offset:offset+dimension,offset:offset+dimension])
            if not s.trace(p):continue
            t=[exterior(s.diag(color,s.zeros(5)),degree) for color in COLOR]
            casimir=-sum((a*a for a in t),s.zeros(dimension))
            pd=clean(s.Rational(4,3)*p*casimir);ps=clean(p-pd)
            for projector in [p,pd,ps]:zero(projector.H-projector);zero(projector*projector-projector)
            zero(ps*pd)
            for action in t:zero(action*ps);zero(action*pd-pd*action)
            singles=s.GramSchmidt(ps.columnspace(),orthonormal=True)
            singles=[clean(column) for column in singles]
            doublets=[]
            for tail in itertools.combinations(range(2,7),degree-1):
                pair=[bases[degree].index((color,)+tail) for color in range(2)]
                basis=s.SparseMatrix(dimension,2,{(row,col):1 for col,row in enumerate(pair)})
                if clean(pd*basis)==basis:doublets.append(basis)
            zero(sum((column*column.H for column in singles),s.zeros(dimension))-ps)
            zero(sum((frame*frame.H for frame in doublets),s.zeros(dimension))-pd)
            assert len(singles)==s.trace(ps) and 2*len(doublets)==s.trace(pd)
            group={'chirality':chi,'degree':degree,'phase_charge':chi+2*int(degree==6),
                   'color_singlet_multiplicity':len(singles),'color_doublet_multiplicity':len(doublets)}
            groups.append(group)
            for kind,inside in [('singlet',frame) for frame in singles]+[('doublet',frame) for frame in doublets]:
                for axis in range(3):
                    zero(t[axis]*inside if kind=='singlet' else t[axis]*inside-inside*COLOR[axis])
                frame=source_frame(inside,spin_start,offset)
                size=frame.cols; h=hsing0 if kind=='singlet' else hdouble0
                spatial=pauli if kind=='singlet' else [s.kronecker_product(a,s.eye(2)) for a in pauli]
                zero(H0*frame-frame*(chi*h))
                for full,small in zip(Hspace,spatial):zero(full*frame-frame*(chi*small))
                zero(Q*frame-group['phase_charge']*frame)
                blocks.append({'kind':kind,'chirality':chi,'degree':degree,'phase_charge':group['phase_charge'],
                    'first_column':cursor,'dimension':size})
                frames.append(frame);cursor+=size
            print('PASS actual grade/chirality',group,flush=True)
    F=s.SparseMatrix.hstack(*frames)
    assert F.shape==(252,216)
    zero(F.H*F-s.eye(216));zero(F*F.H-P)
    small0=s.diag(*[block['chirality']*(hsing0 if block['kind']=='singlet' else hdouble0) for block in blocks])
    smallspace=[s.diag(*[block['chirality']*(pauli[axis] if block['kind']=='singlet' else
        s.kronecker_product(pauli[axis],s.eye(2))) for block in blocks]) for axis in range(3)]
    smallQ=s.diag(*[block['phase_charge'] for block in blocks for _ in range(block['dimension'])])
    zero(F.H*H0*F-small0)
    # Original independent-dual and scalar rows, before any spectral restriction.
    dualframe=clean(s.sqrt(2)*S*F.conjugate())
    zero(Z*dualframe-dualframe);zero(M.T*dualframe);zero(Y*F)
    dual0=clean((s.I*G0).T*(B+Y).T/s.sqrt(2))
    dualspace=list(map(decode,peripheral['dual_spatial_generators']))
    zero(dual0*dualframe-s.I*dualframe*small0.conjugate())
    for full,small in zip(dualspace,smallspace):zero(-s.I*full*dualframe-s.I*dualframe*small.conjugate())
    zero(principal[0]*(-s.I*N*s.sqrt(2))*F*small0+(B+Y)*F)
    for axis in range(3):
        zero(principal[0]*(-s.I*N*s.sqrt(2))*F*smallspace[axis]+s.I*s.sqrt(2)*principal[axis+1]*F)
    # Both original linear bosonic source legs vanish, including p-dependent coframe vertices.
    background=s.MutableSparseMatrix(252,1,{})
    for spin,pair,value in [(0,(1,5),1),(1,(0,5),-1),(2,(1,5),1),(3,(0,5),-1)]:
        background[spin*63+internal_index.index((2,pair)),0]=value
    background_dual=s.sqrt(2)*background.H*S
    momenta=s.symbols('p0:4'); substitutions={p:0 for p in momenta}
    source_counts={}
    for vertex in vertices['primitive_vertices']:
        action=decode(vertex['operator'],**{str(p):p for p in momenta})
        zero(background_dual*action*F)
        zero(dualframe.T*action.subs(substitutions)*background)
        source_counts[vertex['group']]=source_counts.get(vertex['group'],0)+1
    assert sum(source_counts.values())==158
    result={'scope':'FULL_SOURCE_216_FREE_MATTER_ISOMETRY_AND_ORIGINAL_TIME_BLOCKS',
        'source_sha256':hashes,'source_dimension':252,'free_complex_dimension':216,
        'source_lapse':str(N),'source_frequency':str(omega),'time_scale':str(N*s.sqrt(2)),
        'momentum_normalization':'q=k/sqrt(2); original i*d_t psi=(N*sqrt(2))*h_original(q)*psi',
        'free_projection':encode(P),'source_isometry':encode(F),'canonical_dual_frame':encode(dualframe),
        'isometry_two_sided_on_source_projection':True,'groups':groups,'blocks':blocks,
        'pauli_matrices':list(map(encode,pauli)),
        'singlet_constant':encode(hsing0),'doublet_constant':encode(hdouble0),
        'singlet_spatial':list(map(encode,pauli)),
        'doublet_spatial':[encode(s.kronecker_product(a,s.eye(2))) for a in pauli],
        'original_H_constant':encode(H0),'original_H_spatial':list(map(encode,Hspace)),
        'restricted_phase_generator':encode(smallQ),
        'stationary_frequency_readback':'e_stationary=e_original-(3/5)*phase_charge; E=(N*sqrt(2))*e',
        'original_primal_dual_and_scalar_rows_zero':True,
        'all_158_original_linear_bosonic_source_legs_zero':source_counts,
        'canonical_independent_dual_graph_preserved':True,
        'elapsed_seconds':round(time.monotonic()-started,3)}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print('PASS whole216 original primal/dual/scalar and all158 source legs;',result['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
