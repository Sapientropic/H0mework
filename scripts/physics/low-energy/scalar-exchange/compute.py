#!/usr/bin/env python3
"""All peripheral scalar source responses with original one-way matter readback."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sympy as s
from sympy.polys.matrices import DomainMatrix


def clean(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.expand)


def decode(record):
    return s.SparseMatrix(*record["shape"],{(i,j):s.sympify(v) for i,j,v in record["entries"]})


def encode(matrix):
    return {"shape":list(matrix.shape),"entries":[[int(i),int(j),str(value)]
        for (i,j),value in sorted(s.SparseMatrix(matrix).todok().items())]}


def realify(matrix):
    return clean(s.SparseMatrix.vstack(s.SparseMatrix.hstack(matrix.applyfunc(s.re),-matrix.applyfunc(s.im)),
        s.SparseMatrix.hstack(matrix.applyfunc(s.im),matrix.applyfunc(s.re))))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root",type=Path,required=True)
    parser.add_argument("--out",type=Path,required=True)
    args=parser.parse_args()
    base=args.root/"Verification/physics/low-energy-phenomenology"
    sector=json.loads((base/"active-sector/receipt.json").read_text())
    scalar=json.loads((base/"real-scalar-sector/receipt.json").read_text())
    phase=json.loads((base/"full-phase/receipt.json").read_text())
    n=s.sympify(phase["source_lapse"])
    alpha=3*s.sqrt(2)/5
    u,*r=s.symbols("u r1 r2 r3",real=True)
    variables=[u,*r]
    radius=sum(x*x for x in r)
    J=decode(sector["J_basis"])
    PJ=decode(sector["J_projector"])
    P=s.eye(70)-PJ
    rotations=[s.SparseMatrix(item["full"]).applyfunc(s.sympify) for item in scalar["background_color"]]
    assert all(P*R==R*P for R in rotations)
    casimir=sum((R*R for R in rotations),s.zeros(70))
    doublet=clean(-s.Rational(4,3)*casimir*P)
    singlet=clean(P-doublet)
    assert P*P==P and P.T==P and P.rank()==61
    assert doublet*doublet==doublet and singlet*singlet==singlet
    assert doublet*singlet==singlet*doublet==s.zeros(70)
    assert doublet.rank()==36 and singlet.rank()==25
    R=clean(sum((r[i]*rotations[i] for i in range(3)),s.zeros(70))*P)
    assert clean(R*R+radius*doublet/4)==s.zeros(70)
    a=2*u*u-2*radius-2
    b=a+s.Rational(27,50)
    d=s.expand(b*b+2*alpha*alpha*radius)
    operator=clean((2*u*u-2*radius-2)*s.eye(70)-2*s.sqrt(2)*alpha*
        sum((r[i]*rotations[i] for i in range(3)),s.zeros(70))-alpha*alpha*casimir)
    numerator=clean(d*singlet+a*(b*doublet+2*s.sqrt(2)*alpha*R))
    denominator=s.expand(n*a*d)
    assert clean(operator*numerator-a*d*P)==s.zeros(70)
    assert clean(numerator*operator-a*d*P)==s.zeros(70)
    neg=dict(zip(variables,[-v for v in variables]))
    assert clean(numerator.subs(neg,simultaneous=True).T-numerator)==s.zeros(70)
    gram=J.T*J
    assert J*gram.inv()*J.T==PJ and PJ+P==s.eye(70)
    print("PASS: complete scalar complement =25 real singlets+9 quaternion blocks; all-momentum two-sided projected inverse",flush=True)
    # Recover every degree-six primal response forced by M eta; no dual is sourced.
    Mcomplex=decode(phase["stationary_scalar_mixing"])
    degree_six=[63*spin+index for spin in range(4) for index in range(7)]
    other=[i for i in range(252) if i not in degree_six]
    assert Mcomplex[other,:]==s.zeros(224,35)
    M=realify(Mcomplex.extract(degree_six,list(range(35))))
    assert M*PJ==s.zeros(56,70)
    constants=decode(phase["stationary_primal_constant"])
    principal=list(map(decode,phase["principal_coefficients"]))
    full=clean(constants+n*s.sqrt(2)*u*principal[0]+sum((s.sqrt(2)*r[i]*principal[i+1] for i in range(3)),s.zeros(252)))
    assert full[other,degree_six]==s.zeros(224,28)
    Y=decode(phase["original_Y"])
    assert Y[:,degree_six]==s.zeros(252,28)
    D=clean(full[degree_six,degree_six]/s.sqrt(2))
    remaining=set(range(28));blocks=[]
    while remaining:
        queue=[min(remaining)];group=set(queue)
        while queue:
            i=queue.pop()
            for j in range(28):
                if j not in group and (D[i,j]!=0 or D[j,i]!=0):
                    group.add(j);queue.append(j)
        remaining-=group;blocks.append(sorted(group))
    assert sorted(map(len,blocks))==[4,4,4,4,4,8]
    field_blocks=[]
    ring=s.QQ_I.poly_ring(*variables)
    for ids in blocks:
        A=DomainMatrix.from_Matrix(D.extract(ids,ids)).convert_to(ring)
        num,den=A.inv_den()
        identity=DomainMatrix.eye(A.shape,ring)
        assert A*num==identity*den and num*A==identity*den
        complex_num=num.to_Matrix();complex_den=ring.to_sympy(den)
        real_num=realify(clean(complex_num*s.conjugate(complex_den)))
        real_den=s.expand(complex_den*s.conjugate(complex_den))
        assert s.im(real_den)==0
        real_ids=ids+[28+i for i in ids]
        block_M=M[real_ids,:]
        # FieldGreen solves H F=source, so primal F has the opposite sign to scalar F.
        field_num=clean(-real_num*block_M*numerator)
        real_operator=realify(D.extract(ids,ids))
        assert clean(real_operator*field_num+real_den*block_M*numerator)==s.zeros(2*len(ids),70)
        field_blocks.append({"complex_degree_six_indices":ids,"real_degree_six_indices":real_ids,
            "normalized_complex_operator":encode(A.to_Matrix()),
            "complex_inverse_numerator":encode(complex_num),"complex_inverse_denominator":str(complex_den),
            "primal_green_numerator":encode(field_num),
            "primal_green_denominator":str(s.expand(s.sqrt(2)*real_den*denominator))})
        print("original primal readback block",len(ids),"verified",flush=True)
    # The scalar equation retains exactly the independent-dual force M^T diag(I,-I) zeta.
    # zeta=0 makes it vanish; the nonzero induced primal cannot be erased.
    mixed_response=clean(M*numerator)
    assert mixed_response!=s.zeros(56,70)
    origin=dict.fromkeys(variables,0)
    static=clean(numerator.subs(origin)/denominator.subs(origin))
    assert clean(static+singlet/(2*n)+50*doublet/(73*n))==s.zeros(70)
    # Consume the complete 70 scalar vertices and the actual active nine-column source.
    vertices=json.loads((base/"matter-vertices/receipt.json").read_text())
    raw=[decode(item["operator"]) for item in vertices["primitive_vertices"] if item["group"]=="scalar"]
    actual={item["field"]:decode(item["operator"]) for item in vertices["active_289_bosonic_source_operators"]}
    assert len(raw)==70
    for column in range(9):
        projected=clean(sum((J[row,column]*raw[row] for row in range(70) if J[row,column]),s.zeros(252)))
        assert projected==actual[column]
    print("PASS: all70 scalar sources split exactly into original9 active sources and61 peripheral sources",flush=True)
    result={
        "scope":"COMPLETE_PERIPHERAL_SCALAR_TREE_EXCHANGE_WITH_ORIGINAL_MATTER_READBACK",
        "coordinates":"p0=N*sqrt(2)*u; pj=sqrt(2)*rj, then rj=I*kj/sqrt(2) for spatial Fourier",
        "source_lapse":str(n),"source_gauge_scale":str(alpha),
        "peripheral_projector":encode(P),"singlet_projector":encode(singlet),"doublet_projector":encode(doublet),
        "singlet_dimension":25,"doublet_real_dimension":36,
        "normalized_full_scalar_operator":encode(operator),
        "peripheral_scalar_green_numerator":encode(numerator),"peripheral_scalar_green_denominator":str(denominator),
        "projected_inverse_both_sides":True,"source_phase_mixing_real":encode(M),
        "original_primal_readback_blocks":field_blocks,
        "original_dual_response_identically_zero":True,
        "original_full_scalar_primal_dual_equations_restored":True,
        "primal_response_nonzero":True,
        "scalar_static_green":encode(static),
        "scalar_static_exchange":"(1/(4*N))*z^T Psinglet z + (25/(73*N))*z^T Pdoublet z",
        "full_scalar_source_split_active_map":encode(J.T),
        "full_scalar_source_split_peripheral_map":encode(P),
        "actual_all70_source_vertices_consumed":True,
        "exchange_formula":"-1/2 z_perp(-p)^T Gscalar(p) z_perp(p); add to source-complete active289 exchange",
        "full_field_inverse_regular_at_origin_claimed":False,
        "canonical_nonlinear_preparation_preservation_claimed":False,
        "quantum_external_state_or_empirical_units_identified":False}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n")


if __name__=="__main__":main()
