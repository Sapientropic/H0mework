#!/usr/bin/env python3
"""Source-native P286 active carrier and two-sided current projection.

Exact projected coefficients, not a solved 121-component Jacobi equation.
No source/current, gauge fixing or Hermitian-conjugate Yukawa term is added.
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys
from pathlib import Path

import sympy as s

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import exact_readout as source


def exterior(matrix,degree):
    basis=list(itertools.combinations(range(7),degree))
    indices={word:i for i,word in enumerate(basis)}
    out=s.MutableSparseMatrix(len(basis),len(basis),{})
    for col,word in enumerate(basis):
        for slot,old in enumerate(word):
            for new in range(7):
                value=matrix[new,old]
                changed=word[:slot]+(new,)+word[slot+1:]
                if value and len(set(changed))==degree:
                    out[indices[tuple(sorted(changed))],col]+=value*source.sign(changed)
    return s.SparseMatrix(out)


def realify(matrix):
    real,imag=matrix.applyfunc(s.re),matrix.applyfunc(s.im)
    return s.SparseMatrix.vstack(s.SparseMatrix.hstack(real,-imag),s.SparseMatrix.hstack(imag,real))


def encoded(matrix):
    return {"shape":list(matrix.shape),"entries":[[int(i),int(j),str(value)]
            for (i,j),value in sorted(s.SparseMatrix(matrix).todok().items())]}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root",type=Path,required=True)
    parser.add_argument("--out",type=Path,required=True)
    args=parser.parse_args()
    names,vacuum,degrees,hashes=source.parse_source(args.root)
    b2=list(itertools.combinations(range(7),2)); b4=list(itertools.combinations(range(7),4))
    b6=list(itertools.combinations(range(7),6)); rows6={word:i for i,word in enumerate(b6)}
    raw=source.generators([(0,1,2),(3,4)])
    fundamental=[s.SparseMatrix(m)*(s.I if imaginary else 1) for _,imaginary,m in raw]
    rho2=[exterior(t,2) for t in fundamental]
    rho4=[exterior(t,4) for t in fundamental]
    rho6=[exterior(t,6) for t in fundamental]
    h_indices=[b2.index((color,5)) for color in range(3)]
    inclusion=s.MutableSparseMatrix(21,3,{(row,col):1 for col,row in enumerate(h_indices)})
    P2=s.SparseMatrix(inclusion*inclusion.T)
    assert P2*P2==P2 and P2.T==P2 and P2.rank()==3
    restricted=[]
    for t,a in zip(fundamental,rho2):
        expected=t[:3,:3]+t[5,5]*s.eye(3)
        assert a*inclusion==inclusion*expected
        assert P2*a==a*P2
        assert a.H==-a
        restricted.append(expected)
    # Whole-spin native H projection: 4 spins times the three actual color/h+ words.
    Pi=s.diag(s.zeros(7),P2,s.zeros(35),cls=s.SparseMatrix)
    P=s.kronecker_product(s.eye(4),Pi)
    Q=s.eye(252)-P
    assert P.rank()==12
    y=s.MutableSparseMatrix(7,21,{})
    for col,pair in enumerate(b2):
        for four,value in vacuum.items():
            if set(pair).isdisjoint(four):
                y[rows6[tuple(sorted(pair+four))],col]+=value*source.sign(pair+four)
    assert y*inclusion==s.zeros(7,3)
    yi=s.MutableSparseMatrix(63,63,{})
    yi[:7,7:28]=y
    Y=s.kronecker_product(s.diag(0,0,1,1),yi)
    assert Y*P==s.zeros(252) and P*Y==s.zeros(252)
    # Background columns span the full arbitrary upper/lower phase preparation.
    preparations=[]
    for upper,lower in [(1,0),(0,1)]:
        psi=s.zeros(252,1)
        for spin,color,coefficient in [(0,1,upper),(1,0,-upper),(2,1,lower),(3,0,-lower)]:
            psi[spin*63+7+b2.index((color,5))]=coefficient
        assert P*psi==psi and psi.T*P==psi.T
        preparations.append(psi)
    fullrho=[s.diag(a6,a2,a4) for a6,a2,a4 in zip(rho6,rho2,rho4)]
    # A third color is necessary: the original occupied doublet is not P286 invariant.
    old_doublet=s.diag(*[int(i in h_indices[:2]) for i in range(21)])
    third_color_generator=[name for name,_,_ in raw].index("A02")
    third_color_leak=(s.eye(21)-old_doublet)*rho2[third_color_generator]*old_doublet
    assert third_color_leak!=s.zeros(21)
    mother_cross=s.SparseMatrix(7,7,{(0,3):1,(3,0):-1})
    mother_leak=(s.eye(21)-P2)*exterior(mother_cross,2)*P2
    assert mother_leak!=s.zeros(21)
    spin_basis=[]
    for row in range(4):
        for col in range(4):
            spin_basis.append(s.SparseMatrix(4,4,{(row,col):1}))
    # This spans the exact spin/coframe/Lorentz coefficients and spin*P286 coefficients.
    # Both current legs are checked for every independent background phase column.
    checked=0
    for internal in [s.eye(63)]+fullrho:
        for spin in spin_basis:
            action=s.SparseMatrix(s.kronecker_product(spin,internal))
            assert action*P==P*action
            for psi in preparations:
                assert Q*action*psi==s.zeros(252,1)
                assert psi.T*action*Q==s.zeros(1,252)
                # Independent chi coefficients use the same retained rows, without conjugation.
                assert psi.T*Y==s.zeros(1,252)
            checked+=1
    # P286 scalar orbit J is a REAL subspace; keep its real and imaginary columns.
    v=s.Matrix([vacuum.get(word,0) for word in b4])
    complex_orbit=s.Matrix.hstack(*[a*v for a in rho4])
    orbit=s.Matrix.vstack(complex_orbit.applyfunc(s.re),complex_orbit.applyfunc(s.im))
    pivot=orbit.rref()[1]
    J=orbit[:,list(pivot)]
    gram=J.T*J
    PJ=s.SparseMatrix(J*gram.inv()*J.T)
    QJ=s.eye(70)-PJ
    assert J.rank()==9 and PJ*PJ==PJ and PJ.T==PJ
    assert PJ.rank()==9 and QJ.rank()==61
    M=s.MutableSparseMatrix(14,35,{})
    for spin,pair,coefficient in [(0,(1,5),1),(1,(0,5),-1)]:
        for col,four in enumerate(b4):
            if set(pair).isdisjoint(four):
                M[spin*7+rows6[tuple(sorted(pair+four))],col]=coefficient*source.sign(pair+four)
    MR=realify(M)
    Msharp=MR.T*s.diag(s.eye(14),-s.eye(14))
    assert MR*PJ==s.zeros(28,70) and PJ*Msharp==s.zeros(70,28)
    # The source background is the color SU2 that fixes v.
    T=[]
    for entries in [[(0,1,s.I/2),(1,0,s.I/2)],[(0,1,s.Rational(1,2)),(1,0,-s.Rational(1,2))],
                    [(0,0,s.I/2),(1,1,-s.I/2)]]:
        t=s.MutableSparseMatrix(7,7,{(row,col):value for row,col,value in entries})
        a=exterior(t,4)
        assert a*v==s.zeros(35,1)
        ar=realify(a)
        assert ar.T==-ar and ar*PJ==PJ*ar
        assert orbit.T*ar*QJ==s.zeros(12,70)
        T.append(ar)
    assert orbit.T*QJ==s.zeros(12,70)
    # Coefficient-level all-momentum split of the actual scalar operator and its gauge source.
    restrictions=[gram.inv()*J.T*ar*J for ar in T]
    for full,small in zip(T,restrictions):
        assert full*J==J*small
    Casimir=-sum((small*small for small in restrictions),s.zeros(9))
    casimir_eigen={str(value):int(count) for value,count in Casimir.eigenvals().items()}
    u,k1,k2,k3,amplitude=s.symbols("u k1 k2 k3 alpha",real=True)
    momenta=[k1,k2,k3]
    ks=u*u+k1*k1+k2*k2+k3*k3-2
    kd=(ks+3*amplitude*amplitude/4)**2-amplitude*amplitude*(k1*k1+k2*k2+k3*k3)
    scalar_active=(u*u-2)*s.eye(9)-sum(
        ((s.I*momenta[j]*s.eye(9)+amplitude*restrictions[j])**2 for j in range(3)),s.zeros(9))
    active_scalar_det=s.factor(scalar_active.det(method="domain-ge"))
    assert s.cancel(active_scalar_det-ks**5*kd**2)==0
    # Count primitive unknowns before any gauge quotient: this is not a polarization count.
    components={"scalar_J_real":J.cols,"gauge_connection_real":4*len(raw),"coframe_real":4*4,
                "primal_H_real":2*4*inclusion.cols,"independent_dual_H_real":2*4*inclusion.cols}
    original_middle=9+4*len(raw)+16+2*(2*4*21)
    reduced=sum(components.values())
    assert original_middle==409 and reduced==121
    auxiliary={"Lorentz_admissible_connection":4*6,"gravity_B":6*6,
               "gravity_simplicity_multiplier":6*6,"gauge_B":6*len(raw)}
    result={
        "scope":"SOURCE_P286_ACTIVE_JACOBI_CARRIER_AND_TWO_SIDED_COUPLING_PROJECTIONS",
        "source_sha256":hashes,"basis_names":names,"source_degrees":degrees,
        "H_degree_two_basis":[b2[i] for i in h_indices],"H_complex_dimension":3,
        "H_inclusion":encoded(inclusion),"H_internal_projection":encoded(P2),
        "H_whole_spin_projection":encoded(P),"H_whole_complex_dimension":12,
        "p286_labels":[name for name,_,_ in raw],
        "p286_H_actions":[encoded(action) for action in restricted],
        "all_P286_generators_commute_H":True,"Yv_H_zero":True,"H_Yv_zero":True,
        "old_doublet_leakage_generator":"A02","old_doublet_leakage":encoded(third_color_leak),
        "full_mother_counterexample_generator":"A03","full_mother_leakage":encoded(mother_leak),
        "two_sided_spin_gauge_action_basis_checks":checked,
        "independent_background_phase_columns":[encoded(psi) for psi in preparations],
        "scalar_orbit":encoded(orbit),"scalar_orbit_independent_columns":list(pivot),
        "J_basis":encoded(J),"J_Gram":encoded(gram),"J_projector":encoded(PJ),
        "J_real_dimension":9,"J_perp_real_dimension":61,
        "M_real":encoded(MR),"M_sharp":encoded(Msharp),"M_J_zero":True,"J_M_sharp_zero":True,
        "background_scalar_J_actions":[encoded(action) for action in restrictions],
        "background_J_Casimir":encoded(Casimir),"background_J_Casimir_eigenvalues":casimir_eigen,
        "active_scalar_all_momentum_determinant":"Ks^5 Kd^2",
        "outer_real_dimension":61+2*(2*4*(63-3)),
        "outer_diagonal_factor_exponents":{"Ks":25,"Kd":18,"F0":120,"Fplus_Fminus":60},
        "scalar_current_ignores_J_perp":True,"scalar_background_preserves_J_split":True,
        "active_primitive_components":components,"active_real_dimension":reduced,
        "previous_middle_real_dimension":original_middle,
        "algebraic_fields_still_registered":auxiliary,
        "unreduced_Lorentz_admissible_active_real_dimension":reduced+sum(auxiliary.values()),
        "gravity_connection_ambient_storage_real_dimension":4*4*4,
        "full_nine_field_jacobi_matrix_assembled":False,
        "polarization_or_physical_particle_count":None,
    }
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n")
    print("PASS: original H is P286 invariant; Y(v)H=0; all 208 spin/gauge action coefficients satisfy both current projections")
    print("PASS: J real dimension 9, J-perp dimension 61; M J=0, P_J Msharp=0; background scalar propagation preserves the split")
    print("J Casimir:",casimir_eigen)
    print("Primitive middle:",original_middle,"->",reduced,"real; Lorentz-admissible unreduced carrier:",reduced+sum(auxiliary.values()))


if __name__=="__main__":
    main()
