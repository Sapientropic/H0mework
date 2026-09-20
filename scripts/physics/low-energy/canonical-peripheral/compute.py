#!/usr/bin/env python3
"""Source peripheral canonical constraint propagation in the complete graded phase.

The 1082-real-coordinate first-order peripheral system is produced as invariant
86+132+864 blocks. Only the actual 132-coordinate Y/M support needs a constraint
closure calculation; the other blocks retain their source projections.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
import itertools
import json
from pathlib import Path
import sys
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix
from sympy.polys.matrices.normalforms import smith_normal_form
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import exact_readout as source


def clean(matrix): return s.SparseMatrix(matrix).applyfunc(s.expand)


def realify(matrix):
    real,imag=matrix.applyfunc(s.re),matrix.applyfunc(s.im)
    return s.SparseMatrix.vstack(s.SparseMatrix.hstack(real,-imag),s.SparseMatrix.hstack(imag,real))


def encode(matrix):
    return {"shape":list(matrix.shape),"entries":[[int(i),int(j),str(s.factor(value))]
        for (i,j),value in s.SparseMatrix(matrix).todok().items()]}


def exterior(matrix,degree):
    basis=list(itertools.combinations(range(7),degree)); position={word:i for i,word in enumerate(basis)}
    result=s.MutableSparseMatrix(len(basis),len(basis),{})
    for col,word in enumerate(basis):
        for slot,old in enumerate(word):
            for new in range(7):
                value=matrix[new,old]; changed=word[:slot]+(new,)+word[slot+1:]
                if value and len(set(changed))==degree:
                    result[position[tuple(sorted(changed))],col]+=value*source.sign(changed)
    return s.SparseMatrix(result)


def left_inverse(frame):
    return clean((frame.H*frame).inv(method="DM")*frame.H)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root",type=Path,required=True)
    parser.add_argument("--out",type=Path,required=True)
    args=parser.parse_args(); started=time.monotonic()
    names,vacuum,_,hashes=source.parse_source(args.root)
    b2,b6,yraw,_=source.yukawa(vacuum); y=s.SparseMatrix(yraw)
    b4=list(itertools.combinations(range(7),4)); rows6={word:i for i,word in enumerate(b6)}
    I=s.I; root2=s.sqrt(2); q=s.symbols("q",real=True)
    gamma=[s.SparseMatrix(rows) for rows in [
        [[0,0,1,0],[0,0,0,1],[-1,0,0,0],[0,-1,0,0]],
        [[0,0,0,1],[0,0,1,0],[0,1,0,0],[1,0,0,0]],
        [[0,0,0,-I],[0,0,I,0],[0,-I,0,0],[I,0,0,0]],
        [[0,0,1,0],[0,0,0,-1],[1,0,0,0],[0,-1,0,0]]]]
    gamma5=s.diag(-1,-1,1,1); G0=s.kronecker_product(gamma[0],s.eye(63))
    rotations=[gamma[2]*gamma[3],gamma[3]*gamma[1],gamma[1]*gamma[2]]
    T=[s.SparseMatrix(7,7,entries) for entries in [
        {(0,1):I/2,(1,0):I/2},{(0,1):s.Rational(1,2),(1,0):-s.Rational(1,2)},
        {(0,0):I/2,(1,1):-I/2}]]
    rho4=[exterior(t,4) for t in T]
    internal=[s.diag(exterior(t,6),exterior(t,2),exterior(t,4)) for t in T]
    yi=s.MutableSparseMatrix(63,63,{})
    yi[:7,7:28]=y
    Y=s.kronecker_product(s.diag(0,0,1,1),yi)
    M=s.MutableSparseMatrix(252,35,{})
    for spin,pair,amplitude in [(2,(1,5),1),(3,(0,5),-1)]:
        for col,four in enumerate(b4):
            if set(pair).isdisjoint(four):
                M[spin*63+rows6[tuple(sorted(pair+four))],col]=amplitude*source.sign(pair+four)
    M=s.SparseMatrix(M)
    gram=y*y.H
    occupied_outputs=[i for i in range(7) if gram[i,i]]
    assert len(occupied_outputs)==5
    W=y.H[:,occupied_outputs]
    gramW=W.H*W
    # Primal interacting coordinates (r_R2 in sqrt(2) W, l_L6 in the full six-basis).
    P=s.MutableSparseMatrix(252,24,{})
    Z=s.MutableSparseMatrix(252,24,{})
    for spin in range(2):
        P[(spin+2)*63+7:(spin+2)*63+28,spin*5:(spin+1)*5]=root2*W
        P[spin*63:spin*63+7,10+spin*7:10+(spin+1)*7]=s.eye(7)
        Z[(spin+2)*63:(spin+2)*63+7,spin*7:(spin+1)*7]=root2*s.eye(7)
        Z[spin*63+7:spin*63+28,14+spin*5:14+(spin+1)*5]=2*W
    P=clean(P); Z=clean(Z); Pleft=left_inverse(P); Zleft=left_inverse(Z)
    scalar_columns=[i for i in range(35) if M[:,i]!=s.zeros(252,1)]
    E=s.SparseMatrix(35,len(scalar_columns),{(row,col):1 for col,row in enumerate(scalar_columns)})
    assert len(scalar_columns)==9 and (M*E).rank()==9
    for action in rho4: assert clean(action*E-E*(E.T*action*E))==s.zeros(35,9)
    P6=s.diag(s.eye(7),s.zeros(56))
    phase=s.kronecker_product(gamma5,s.eye(63))+2*s.kronecker_product(s.eye(4),P6)
    # tau=N*sqrt(2)*t, k=sqrt(2)*q; omega/(N*sqrt(2))=3/5.
    Bhat=sum((I*s.kronecker_product(gamma[j+1],s.eye(63))*
        (s.kronecker_product(rotations[j],s.eye(63))/2+
         s.Rational(3,5)*s.kronecker_product(s.eye(4),internal[j])) for j in range(3)),s.zeros(252))
    K=clean(Bhat+Y/root2+s.Rational(3,5)*G0*phase)
    primal0=clean(-I*G0*K)
    dual0=clean((I*G0).T*K.T)
    primal_space=[s.kronecker_product(gamma[0]*gamma[j+1],s.eye(63)) for j in range(3)]
    dual_space=[s.kronecker_product(gamma[0].T*gamma[j+1].T,s.eye(63)) for j in range(3)]
    p0=clean(Pleft*primal0*P); z0=clean(Zleft*dual0*Z)
    ps=[clean(Pleft*a*P) for a in primal_space]
    zs=[clean(Zleft*a*Z) for a in dual_space]
    assert clean(primal0*P-P*p0)==s.zeros(252,24)
    assert clean(dual0*Z-Z*z0)==s.zeros(252,24)
    for full,small in zip(primal_space,ps): assert clean(full*P-P*small)==s.zeros(252,24)
    for full,small in zip(dual_space,zs): assert clean(full*Z-Z*small)==s.zeros(252,24)
    force=clean(Pleft*(-I*G0*M*E))
    assert clean(-I*G0*M*E-P*force)==s.zeros(252,9)
    # Read original scalar equation before inserting external Fourier i.
    Jreal=s.diag(s.eye(252),-s.eye(252))
    scalar_force=clean(realify(M*E).T*Jreal*realify(Z)/(2*root2))
    tr=[realify(E.T*action*E) for action in rho4]
    scalar_kinetic=clean(-sum(((I*(q if j==2 else 0)*s.eye(18)+s.Rational(3,5)*tr[j])**2
        for j in range(3)),s.zeros(18))-s.eye(18))
    A=s.MutableSparseMatrix(132,132,{})
    A[:18,18:36]=s.eye(18)
    A[18:36,:18]=-scalar_kinetic
    A[18:36,84:132]=-scalar_force
    A[36:84,:18]=realify(force)
    A[36:84,36:84]=realify(p0)+I*q*realify(ps[2])
    A[84:132,84:132]=realify(z0)+I*q*realify(zs[2])
    A=clean(A)
    for value in A.todok().values(): s.Poly(value,q,domain=s.QQ_I)
    # Actual unprojected Euler rows factor through the generated first-order rows.
    primal_time=realify(I*G0*P)
    primal_value=clean(realify(K*P)+I*q*realify(I*s.kronecker_product(gamma[3],s.eye(63))*P))
    primal_scalar=realify(M*E)
    dual_time=realify(-(I*G0).T*Z)
    dual_value=clean(realify(K.T*Z)-I*q*realify((I*s.kronecker_product(gamma[3],s.eye(63))).T*Z))
    scalar_frame=root2*realify(E)
    scalar_full_kinetic=clean(-sum(((I*(q if j==2 else 0)*s.eye(70)+s.Rational(3,5)*realify(rho4[j]))**2
        for j in range(3)),s.zeros(70))-s.eye(70))
    scalar_raw_force=clean(realify(M).T*Jreal*realify(Z)/2)
    assert clean(primal_time*A[36:84,36:84]+primal_value)==s.zeros(504,48)
    assert clean(primal_time*realify(force)+primal_scalar)==s.zeros(504,18)
    assert clean(dual_time*A[84:132,84:132]+dual_value)==s.zeros(504,48)
    assert clean(scalar_full_kinetic*scalar_frame-scalar_frame*scalar_kinetic)==s.zeros(70,18)
    assert clean(scalar_raw_force-scalar_frame*scalar_force)==s.zeros(70,48)
    primal_row_left=realify(Pleft*(I*G0))
    dual_row_left=realify(Zleft*(-(I*G0).T))
    assert primal_row_left*primal_time==s.eye(48) and dual_row_left*dual_time==s.eye(48)
    # z6=conj(l6), z2=conj(r2), exactly the source sqrt(2) canonical dual.
    swap=s.kronecker_product(gamma[0]*gamma5,s.eye(63))
    pairing=clean(Zleft*(root2*swap*P.conjugate()))
    assert clean(Z*pairing-root2*swap*P.conjugate())==s.zeros(252,24)
    assert pairing.conjugate()==pairing
    J=clean(s.diag(pairing,-pairing))
    D=s.SparseMatrix.hstack(s.zeros(48,36),-J,s.eye(48))
    C=s.SparseMatrix.vstack(s.eye(84),s.SparseMatrix.hstack(s.zeros(48,36),J))
    assert D*C==s.zeros(48,84)
    B=clean(A[:84,:]*C)
    compatibility=clean(D*A*C)
    defect_lift=s.SparseMatrix.vstack(s.zeros(84,48),s.eye(48))
    assert clean(A*C-C*B-defect_lift*compatibility)==s.zeros(132,84)
    print("PASS: complete graded-phase Y/M interacting generator 132; canonical candidate carrier 84",flush=True)
    # Generate the untouched source projectors and verify the exact full peripheral split.
    Pint=clean(P*Pleft); Zint=clean(Z*Zleft)
    h2=s.diag(*[int(word in [(0,5),(1,5),(2,5)]) for word in b2])
    H=s.kronecker_product(s.eye(4),s.diag(s.zeros(7),h2,s.zeros(35)))
    Pfree=clean(s.eye(252)-H-Pint); Zfree=clean(s.eye(252)-H-Zint)
    assert s.trace(Pfree)==216 and Pfree*Pfree==Pfree
    assert s.trace(Zfree)==216 and Zfree*Zfree==Zfree
    for action in [primal0]+primal_space:
        assert clean(action*Pfree-Pfree*action)==s.zeros(252)
    for action in [dual0]+dual_space:
        assert clean(action*Zfree-Zfree*action)==s.zeros(252)
    for primal_action,dual_action in zip([primal0]+primal_space,[dual0]+dual_space):
        assert clean(dual_action*swap*Pfree.conjugate()-swap*(primal_action*Pfree).conjugate())==s.zeros(252)
    assert clean(Y*Pfree)==s.zeros(252) and clean(Pfree*G0*M)==s.zeros(252,35)
    assert clean(realify(M).T*Jreal*realify(Zfree))==s.zeros(70,504)
    scalar_receipt=json.loads((args.root/'Verification/physics/low-energy-phenomenology/real-scalar-sector/receipt.json').read_text())
    scalar_free=s.Matrix([[s.Rational(value) for value in row] for row in scalar_receipt['basis']])
    assert scalar_free.shape==(70,43)
    scalar_left=(scalar_free.T*scalar_free).inv(method='DM')*scalar_free.T
    scalar_free_actions=[]
    for action in rho4:
        ar=realify(action); small=clean(scalar_left*ar*scalar_free)
        assert clean(ar*scalar_free-scalar_free*small)==s.zeros(70,43)
        scalar_free_actions.append(small)
    assert clean(realify(M)*scalar_free)==s.zeros(504,43)
    assert clean(scalar_free.T*realify(E))==s.zeros(43,18)
    assert s.Matrix.hstack(scalar_free,realify(E)).rank()==61
    scalar_free_kinetic=clean(-sum(((I*(q if j==2 else 0)*s.eye(43)+s.Rational(3,5)*scalar_free_actions[j])**2
        for j in range(3)),s.zeros(43))-s.eye(43))
    scalar_free_generator=s.SparseMatrix.vstack(
        s.SparseMatrix.hstack(s.zeros(43),s.eye(43)),
        s.SparseMatrix.hstack(-scalar_free_kinetic,s.zeros(43)))
    print("PASS: source free matter projection dimension216 complex; untouched scalar43 gives full 86+132+864=1082",flush=True)
    # Couple coordinates into the smallest complete coefficient/constraint graph, before elimination.
    adjacency=defaultdict(set)
    for row,col in B.todok(): adjacency[row].add(col); adjacency[col].add(row)
    for row in range(compatibility.rows):
        support=[col for col in range(84) if compatibility[row,col]!=0]
        for col in support:
            adjacency[col].update(support)
    unseen=set(range(84)); blocks=[]
    while unseen:
        seed=unseen.pop(); block={seed}; stack=[seed]
        while stack:
            new=adjacency[stack.pop()]&unseen
            unseen-=new;block|=new;stack+=list(new)
        blocks.append(sorted(block))
    blocks.sort(key=lambda block:(len(block),block[0]))
    print("Generated prepared coefficient blocks:",[len(block) for block in blocks],flush=True)
    result={"scope":"SOURCE_PERIPHERAL_MAXIMAL_CANONICAL_INVARIANT_FOURIER_FIBRES",
        "source_sha256":hashes,"basis_names":names,
        "normalization":"tau=N*sqrt(2)*t; k3=sqrt(2)*q; scalar_eta=sqrt(2)*E a; actual primal=P p; actual dual=Z z",
        "phase_generator":"gamma5+2 P6","phase_ratio":"frequency/(N*sqrt(2))=3/5",
        "full_first_order_real_dimension":1082,"source_block_dimensions":[86,132,864],
        "scalar_M_columns":[list(b4[i]) for i in scalar_columns],"scalar_M_inclusion":encode(E),
        "primal_interacting_frame":encode(P),"dual_interacting_frame":encode(Z),
        "primal_free_projection":encode(Pfree),"dual_free_projection":encode(Zfree),
        "primal_free_canonical_real_dimension":432,
        "primal_constant_generator":encode(primal0),"dual_constant_generator":encode(dual0),
        "primal_spatial_generators":[encode(value) for value in primal_space],
        "dual_spatial_generators":[encode(value) for value in dual_space],
        "free_canonical_graph_preserved_coefficientwise":True,
        "scalar_free_frame":encode(scalar_free),"scalar_free_first_order_generator":encode(scalar_free_generator),
        "interacting_first_order_generator":encode(A),"canonical_constraint":encode(D),
        "original_normalized_Euler_readback":{
            "primal_time_frame":encode(primal_time),"primal_value":encode(primal_value),
            "primal_scalar":encode(primal_scalar),"primal_time_left_inverse":encode(primal_row_left),
            "dual_time_frame":encode(dual_time),"dual_value":encode(dual_value),
            "dual_time_left_inverse":encode(dual_row_left),
            "scalar_frame":encode(scalar_frame),"scalar_kinetic":encode(scalar_full_kinetic),
            "scalar_dual_force":encode(scalar_raw_force),
            "normalization":"original scalar Euler divided by2 after tau scaling; original Dirac/dual vector rows divided bysqrt(2); source nonzero volume factor unchanged"},
        "canonical_embedding":encode(C),"prepared_generator":encode(B),
        "first_preparation_derivative_constraint":encode(compatibility),
        "whole_generator_readback_defect_lift":encode(defect_lift),
        "prepared_coefficient_blocks":blocks,"constraints_propagated":False}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n")
    print("PASS source generator build, seconds",round(time.monotonic()-started,3),flush=True)


if __name__=="__main__":main()
