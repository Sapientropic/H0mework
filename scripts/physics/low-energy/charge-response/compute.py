#!/usr/bin/env python3
"""All twelve native static charge responses and the physical-source soft residue."""
import argparse
import json
from pathlib import Path
import sympy as s
from sympy.polys.matrices import DomainMatrix


def encode(matrix):
    return {"shape":list(matrix.shape),"entries":[[int(i),int(j),str(s.factor(v))]
        for (i,j),v in sorted(s.SparseMatrix(matrix).todok().items())]}


def decode(record):
    return s.SparseMatrix(*record["shape"],{(i,j):s.sympify(v) for i,j,v in record["entries"]})


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root",type=Path,required=True)
    parser.add_argument("--out",type=Path,required=True)
    args=parser.parse_args()
    base=args.root/"Verification/physics/low-energy-phenomenology"
    original=json.loads((base/"active-gauge/receipt.json").read_text())
    quotient=json.loads((base/"active-gauge/quotient.json").read_text())
    propagation=json.loads((base/"active-gauge/propagation.json").read_text())
    exchange=json.loads((base/"matter-vertices/exchange.json").read_text())
    soft=json.loads((base/"soft-phase/receipt.json").read_text())
    n=s.sympify(original["source_lapse"])
    p=s.symbols("p0 p1 p2 p3");q=s.symbols("q",real=True)
    lam,k=s.symbols("lam k",real=True)
    static={p[0]:0,p[1]:0,p[2]:0,p[3]:s.I*s.sqrt(2)*q}
    zero=dict.fromkeys(p,0)
    F=decode(exchange["full_polynomial_field_change"])
    Fi=decode(exchange["full_polynomial_inverse"])
    source_indices=exchange["source_field_indices"]
    source_injection=s.SparseMatrix(289,97,{(row,col):1 for col,row in enumerate(source_indices)})
    compatibility=decode(exchange["local_source_compatibility_map"])
    scale=s.diag(*map(s.sympify,soft["field_scaling"]))
    phase=decode(soft["constant_phase_basis"])
    Z=decode(soft["source_phase_columns_289"])
    actual_phase=F[:,9:88].subs(zero)*scale*phase
    coordinates=Fi.subs(zero)*(actual_phase-Z)
    assert coordinates[:112,:]==s.zeros(112,2) and coordinates[121:,:]==s.zeros(168,2)
    null_shift=coordinates[112:121,:]
    assert Z.T*source_injection==s.zeros(2,97)
    light_source=actual_phase.T*source_injection
    assert light_source==null_shift.T*compatibility.subs(zero)
    spatial_coefficient=s.diag(s.Rational(160,67),s.Rational(2500,81))
    residue=(light_source.T*spatial_coefficient.inv()*light_source/n).applyfunc(s.simplify)
    constraint_residue=(null_shift*spatial_coefficient.inv()*null_shift.T/n).applyfunc(s.simplify)
    assert residue==compatibility.subs(zero).T*constraint_residue*compatibility.subs(zero)
    assert s.SparseMatrix(constraint_residue).todok()=={(2,2):s.Rational(9023,5000)/n}
    # These twelve exact sources satisfy all null rows at every static axial momentum.
    source_fields=[i for i,f in enumerate(original["fields"]) if f["group"]=="gauge_A" and f["coordinate"][0]==0]
    source_columns=[source_indices.index(i) for i in source_fields]
    assert compatibility[:,source_columns].subs(static)==s.zeros(9,12)
    assert decode(exchange["independent_dual_source_map"])[:,source_columns]==s.zeros(24,12)
    assert residue.extract(source_columns,source_columns)==s.zeros(12)
    print("PASS: canonical static soft residue factors entirely through original source constraints",flush=True)
    kept=quotient["retained_original_fields"]
    K=s.SparseMatrix(103,103,{(i,j):s.sympify(value.replace("lambda","lam"),locals={"lam":lam,"k":k}).subs({lam:0,k:s.sqrt(2)*q})
        for i,j,value in quotient["quotient_operator_103_by_103"]})
    scaling=s.diag(*map(s.sympify,propagation["constant_diagonal_field_scaling"]))
    G=(scaling*K*scaling/n).applyfunc(s.simplify)
    rows=[kept.index(i) for i in source_fields]
    normalized_response=s.zeros(103,12)
    ring=s.QQ_I.poly_ring(q)
    for block in propagation["blocks"]:
        ids=block["quotient_indices"]
        columns=[j for j,row in enumerate(rows) if row in ids]
        if not columns:continue
        rhs=s.SparseMatrix(len(ids),len(columns),{(ids.index(rows[col]),j):1 for j,col in enumerate(columns)})
        A=DomainMatrix.from_Matrix(G.extract(ids,ids)).convert_to(ring)
        B=DomainMatrix.from_Matrix(rhs).convert_to(ring)
        num,den=A.solve_den(B,method="rref")
        assert A*num==B*den
        solved=(num.to_Matrix()/ring.to_sympy(den)).applyfunc(s.cancel)
        for i,row in enumerate(ids):
            for j,col in enumerate(columns):normalized_response[row,col]=solved[i,j]
        print("original charge response block",len(ids),"sources",len(columns),flush=True)
    response=s.zeros(103,12)
    for col,row in enumerate(rows):response[:,col]=scaling*normalized_response[:,col]*scaling[row,row]/n
    response=response.applyfunc(s.cancel)
    injection=s.SparseMatrix(103,12,{(row,col):1 for col,row in enumerate(rows)})
    assert (K*response-injection).applyfunc(s.cancel)==s.zeros(103,12)
    full=s.MutableSparseMatrix(289,12,{})
    for row,index in enumerate(kept):full[index,:]=response[row,:]
    for step in reversed(original["algebraic_Schur_steps"]):
        for row,col,powers,value in step["write_back_auxiliary_from_retained"]:
            if not any(powers[:3]):full[row,:]+=s.sympify(value)*(s.I*s.sqrt(2)*q)**powers[3]*full[col,:]
        for row in step["eliminated_fields"]:full[row,:]=full[row,:].applyfunc(s.cancel)
    H=s.MutableSparseMatrix(289,289,{})
    for row,col,powers,value in original["Fourier_Jacobi_entries"]:
        if not any(powers[:3]):H[row,col]+=s.sympify(value)*(s.I*s.sqrt(2)*q)**powers[3]
    full_injection=s.SparseMatrix(289,12,{(row,col):1 for col,row in enumerate(source_fields)})
    assert (H*full-full_injection).applyfunc(s.cancel)==s.zeros(289,12)
    readout=full[source_fields,:].applyfunc(s.cancel)
    assert (readout.subs(q,-q).T-readout).applyfunc(s.cancel)==s.zeros(12)
    assert all(s.denom(value).subs(q,0)!=0 for value in readout)
    infrared=readout.subs(q,0)
    assert (q*q*readout).applyfunc(lambda value:s.limit(value,q,0))==s.zeros(12)
    # The already certified whole-field rotation preserves this twelve-source slice.
    finite=json.loads((base/"active-gauge/rotation/finite.json").read_text())
    z=s.symbols("z",real=True)
    source_position={field:i for i,field in enumerate(source_fields)}
    charge_rotations=[];bounds=[]
    for entry in finite["certificates"]:
        U=s.MutableSparseMatrix(12,12,{})
        bound=s.MutableSparseMatrix(12,12,{})
        for i,j,coefficients in entry["field_numerator"]:
            assert (i in source_position)==(j in source_position) or not (i in source_position or j in source_position)
            if i not in source_position:continue
            assert len(coefficients)<=9
            U[source_position[i],source_position[j]]=sum(c*z**degree for degree,c in enumerate(coefficients))
            bound[source_position[i],source_position[j]]=sum(abs(c) for c in coefficients)/entry["field_constant_denominator"]
        U=U/(entry["field_constant_denominator"]*(1+z*z)**4)
        assert (U*U.subs(z,-z)-s.eye(12)).applyfunc(s.cancel)==s.zeros(12)
        charge_rotations.append(U);bounds.append(bound)
    # A bounded directional limit need not be the same matrix in every direction.
    oblique=charge_rotations[1].subs(z,s.Rational(1,2))
    directional_difference=(oblique*infrared*oblique.T-infrared).applyfunc(s.simplify)
    assert directional_difference!=s.zeros(12)
    result={"scope":"ORIGINAL_NATIVE_STATIC_CHARGE_RESPONSE_AND_COMPATIBLE_SOURCE_INFRARED_RESIDUE",
        "source_convention":"+sum_T j_T A_0^T; induced field=-FieldGreen*j",
        "source_fields":source_fields,"source_labels":original["native_P286_labels"],
        "Fourier_convention":"lambda=0, k=(0,0,sqrt(2)*q)",
        "source_null_phase_shift":encode(null_shift),
        "canonical_q_squared_source_inverse_residue":encode(residue),
        "canonical_residue_factor_through_null_constraints":encode(constraint_residue),
        "compatible_regular_sources_have_zero_q_squared_residue":True,
        "all_twelve_static_charge_sources_compatible":True,
        "full_289_field_green_columns":encode(full),"all_original_rows_restore_sources":True,
        "static_charge_inverse_response":encode(readout),"static_charge_zero_limit":encode(infrared),
        "all_144_charge_entries_regular_at_zero":True,
        "finite_charge_rotations":[encode(U) for U in charge_rotations],
        "uniform_entrywise_rotation_bounds":[encode(bound) for bound in bounds],
        "all_real_directions_have_zero_radial_squared_charge_residue":True,
        "nonzero_directional_difference_of_finite_charge_limit":encode(directional_difference),
        "electromagnetism_or_Newton_constant_identified":False,
        "loop_or_nonperturbative_response_claimed":False}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n")
    print("PASS: every original row; all144 static charge response entries regular at zero",flush=True)


if __name__=="__main__":main()
