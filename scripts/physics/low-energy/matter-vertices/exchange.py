#!/usr/bin/env python3
"""Source-aware normal form of all 289 active equations and their tree exchange.

Every primitive matter source is retained, including the spin connection.
The nine local null directions appear as explicit source compatibility rows.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sys
import sympy as s


def clean(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.expand)


def encode(matrix):
    return {"shape":list(matrix.shape),"entries":[[int(i),int(j),str(value)]
        for (i,j),value in sorted(s.SparseMatrix(matrix).todok().items())]}


def decode(entries, rows, cols):
    return s.SparseMatrix(rows,cols,{(i,j):s.sympify(value) for i,j,value in entries})


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root",type=Path,required=True)
    parser.add_argument("--out",type=Path,required=True)
    args=parser.parse_args()
    base=args.root/"Verification/physics/low-energy-phenomenology"
    source=json.loads((base/"active-gauge/receipt.json").read_text())
    canonical=json.loads((base/"canonical-active/receipt.json").read_text())
    symmetries=json.loads((base/"active-gauge/symmetries.json").read_text())
    p=s.symbols("p0 p1 p2 p3")
    neg=dict(zip(p,[-v for v in p]))
    def negative(matrix):
        return matrix.subs(neg,simultaneous=True)
    def polynomial(entries,rows,cols):
        matrix=s.MutableSparseMatrix(rows,cols,{})
        for i,j,powers,value in entries:
            matrix[i,j]+=s.sympify(value)*s.prod(x**power for x,power in zip(p,powers))
        return clean(matrix)
    original=polynomial(source["Fourier_Jacobi_entries"],289,289)
    fields=source["fields"]
    source_indices=[i for i,field in enumerate(fields)
        if field["group"] in ("scalar_J","gauge_A","coframe","Lorentz")]
    assert len(source_indices)==97
    injection=s.SparseMatrix(289,97,{(row,col):1 for col,row in enumerate(source_indices)})
    F=s.SparseMatrix(s.eye(289))
    inverse_F=s.SparseMatrix(s.eye(289))
    current=original
    auxiliary=[]
    for step in source["algebraic_Schur_steps"]:
        ids=step["eliminated_fields"]
        W=polynomial(step["write_back_auxiliary_from_retained"],289,289)
        assert W*W==s.zeros(289)
        change=s.SparseMatrix(s.eye(289))+W
        inverse=s.SparseMatrix(s.eye(289))-W
        D=current[ids,ids]
        inverse_global=decode(step["algebraic_block_inverse"],289,289)
        Dinv=inverse_global[ids,ids]
        assert clean(D*Dinv-s.eye(len(ids)))==s.zeros(len(ids))
        assert clean(Dinv*D-s.eye(len(ids)))==s.zeros(len(ids))
        current=clean(negative(change).T*current*change)
        F=clean(F*change)
        inverse_F=clean(inverse*inverse_F)
        outside=[i for i in range(289) if i not in ids]
        assert current[ids,outside]==s.zeros(len(ids),len(outside))
        assert current[outside,ids]==s.zeros(len(outside),len(ids))
        auxiliary.append({"indices":ids,"operator":D,"inverse":Dinv,"groups":step["eliminated_groups"]})
        print("actual source completion:",step["eliminated_groups"],flush=True)
    primitive=polynomial(source["primitive_121_Fourier_Jacobi_entries"],121,121)
    assert current[:121,:121]==primitive
    # The scalar Ward variables are genuine contact coordinates, not discarded source equations.
    gauge=polynomial(source["source_primitive_gauge_tangent"],289,12)[:121,:]
    broken=source["Ward_constraint_elimination"]["broken_parameter_columns"]
    Tbroken=gauge[:,broken]
    assert Tbroken[:9,:]==s.eye(9)
    ward_change=s.MutableSparseMatrix(s.eye(289))
    ward_change[9:121,:9]=Tbroken[9:,:]
    ward_inverse=s.MutableSparseMatrix(s.eye(289))
    ward_inverse[9:121,:9]=-Tbroken[9:,:]
    current=clean(negative(ward_change).T*current*ward_change)
    F=clean(F*ward_change);inverse_F=clean(ward_inverse*inverse_F)
    M=current[:9,:9]
    Minv=s.Matrix(source["Ward_constraint_elimination"]["scalar_constraint_inverse"]).applyfunc(s.sympify)
    assert M*Minv==Minv*M==s.eye(9)
    assert current[:9,9:121]==s.zeros(9,112) and current[9:121,:9]==s.zeros(112,9)
    H=current[9:121,9:121]
    C=decode(canonical["canonical_embedding_112_by_88"],112,88)
    R=decode(canonical["constant_whole_equation_readback_112_by_88"],112,88)
    E=decode(canonical["quotient_section"],88,79)
    Q=decode(canonical["quotient_readback"],79,88)
    Cminus=decode(canonical["independent_dual_complement_112_by_24"],112,24)
    T=polynomial(symmetries["source_symmetry_tangents_112"],121,9)[9:,:]
    companion=s.SparseMatrix.hstack(C,Cminus).inv(method="DM")[88:,:]
    removed=canonical["removed_canonical_fields"]
    selector=s.SparseMatrix(9,88,{(i,row):1 for i,row in enumerate(removed)})
    tangent_c=decode(canonical["canonical_source_symmetry_tangents"],88,9)
    parameter=tangent_c[removed,:].inv(method="DM")*selector
    frame=clean(s.SparseMatrix.hstack(C*E,Cminus,T))
    inverse_frame=clean(s.SparseMatrix.vstack(Q*R.T,companion,parameter*R.T))
    assert clean(frame*inverse_frame)==s.eye(112) and clean(inverse_frame*frame)==s.eye(112)
    A=decode(canonical["canonical_quotient_operator"],79,79)
    B=clean(Cminus.T*H*Cminus)
    assert clean(negative(frame).T*H*frame-s.diag(A,B,s.zeros(9)))==s.zeros(112)
    final_change=s.MutableSparseMatrix(s.eye(289));final_change[9:121,9:121]=frame
    final_inverse=s.MutableSparseMatrix(s.eye(289));final_inverse[9:121,9:121]=inverse_frame
    current=clean(negative(final_change).T*current*final_change)
    F=clean(F*final_change);inverse_F=clean(final_inverse*inverse_F)
    assert clean(F*inverse_F)==s.eye(289) and clean(inverse_F*F)==s.eye(289)
    assert clean(negative(F).T*original*F-current)==s.zeros(289)
    readback=clean(negative(F).T*injection)
    row_lift=negative(inverse_F).T
    source_can=readback[9:88,:]
    source_complement=readback[88:112,:]
    compatibility=readback[112:121,:]
    contact=s.MutableSparseMatrix(97,97,{})
    field_contact=s.MutableSparseMatrix(289,97,{})
    contacts=[]
    for item in auxiliary+[{"indices":list(range(9)),"operator":M,"inverse":Minv,"groups":["scalar_Ward"]}]:
        ids=item["indices"]
        source_map=readback[ids,:]
        response=clean(F[:,ids]*item["inverse"]*source_map)
        kernel=clean(negative(source_map).T*item["inverse"]*source_map)
        field_contact+=response;contact+=kernel
        contacts.append({"groups":item["groups"],"source_map":encode(source_map),"kernel":encode(kernel)})
    field_contact=clean(field_contact);contact=clean(contact)
    assert clean(negative(contact).T-contact)==s.zeros(97)
    assert clean(original*field_contact+row_lift[:,9:88]*source_can+
        row_lift[:,88:112]*source_complement+row_lift[:,112:121]*compatibility-injection)==s.zeros(289,97)
    assert clean(original*F[:,9:88]-row_lift[:,9:88]*A)==s.zeros(289,79)
    assert clean(original*F[:,88:112]-row_lift[:,88:112]*B)==s.zeros(289,24)
    assert clean(original*F[:,112:121])==s.zeros(289,9)
    # Source spin can enter the independent-dual complement; an action pullback would miss it.
    assert source_complement!=s.zeros(24,97)
    assert all(fields[source_indices[col]]["group"]=="Lorentz"
        for row,col in source_complement.todok())
    # Both original isolated weak quintuples are recovered as consumers of this full normal form.
    weak=json.loads((base/"weak-exchange/spatial/receipt.json").read_text())
    spatial_to_formal={s.Symbol("lam"):p[0],**{s.Symbol("k"+str(i)):-s.I*p[i] for i in range(1,4)}}
    def weak_matrix(record):
        return decode(record["entries"],*record["shape"]).subs(spatial_to_formal)
    for block in weak["generators"]:
        weak_lift=weak_matrix(block["original_289_field_lift"])
        weak_operator=weak_matrix(block["actual_five_field_operator"])
        coordinates=clean(inverse_F*weak_lift)
        assert clean(F*coordinates-weak_lift)==s.zeros(289,5)
        assert clean(negative(coordinates).T*current*coordinates-weak_operator)==s.zeros(5)
        selected=[source_indices.index(i) for i in block["original_fields"]]
        assert compatibility[:,selected]==s.zeros(9,5)
        assert source_complement[:,selected]==s.zeros(24,5)
    # Consume the actual full252 vertices, not arbitrary labels on a formal source vector.
    vertices=json.loads((base/"matter-vertices/receipt.json").read_text())
    operators={item["field"]:decode(item["operator"]["entries"],*item["operator"]["shape"])
        for item in vertices["active_289_bosonic_source_operators"]}
    S=s.SparseMatrix(s.kronecker_product(s.Matrix([[0,0,1,0],[0,0,0,1],[1,0,0,0],[0,1,0,0]]),s.eye(63)))
    complement_vertices=[]
    for row in range(24):
        vertex=s.MutableSparseMatrix(252,252,{})
        for col in range(97):
            if source_complement[row,col]:
                vertex+=source_complement[row,col]*operators[source_indices[col]]
        vertex=clean(vertex)
        assert clean(S*vertex+vertex.H*S)==s.zeros(252)
        complement_vertices.append(encode(vertex))
    print("PASS: raw spin source reaches complementary block; actual canonical real vertices cancel identically",flush=True)
    # The 24 real prepared spin sources are generated by four original axial bilinears.
    sys.path.insert(0,str(base/"nonlinear-contact"))
    from slice_checks import GAMMA
    gamma5=s.diag(-1,-1,1,1)
    spin_swap=GAMMA[0]*gamma5
    axial=[s.sqrt(2)*spin_swap*gamma*gamma5 for gamma in GAMMA]
    assert all(matrix.H==matrix for matrix in axial)
    basis=s.Matrix.hstack(*[matrix.reshape(16,1) for matrix in axial])
    left=(basis.T*basis).inv()*basis.T
    coefficients=[]
    for field in source["algebraic_Schur_steps"][-1]["eliminated_fields"]:
        full_vertex=operators[field]
        spin_vertex=full_vertex.extract([0,63,126,189],[0,63,126,189])
        assert full_vertex==s.kronecker_product(spin_vertex,s.eye(63))
        real_vertex=clean(s.sqrt(2)*(spin_swap*spin_vertex+spin_vertex.H*spin_swap)/2)
        vector=real_vertex.reshape(16,1)
        coeff=clean(left*vector)
        assert basis*coeff==vector
        coefficients.append(list(coeff))
    spin_map=s.Matrix(coefficients)
    assert spin_map.rank()==4
    spin_kernel=clean(spin_map.T*auxiliary[-1]["inverse"]*spin_map)
    n=s.sympify(source["source_lapse"])
    assert spin_kernel==3*n/8*s.diag(1,-1,-1,-1)
    print("PASS: actual prepared spin contact = (3*N/16)*eta_ab axial^a axial^b",flush=True)
    result={
        "scope":"SOURCE_COMPLETE_ACTIVE_289_TREE_EXCHANGE_NORMAL_FORM",
        "source_field_indices":source_indices,
        "source_fields":[fields[i] for i in source_indices],
        "full_polynomial_field_change":encode(F),"full_polynomial_inverse":encode(inverse_F),
        "all_four_momenta_checked":True,
        "ordered_blocks":{"scalar_contact":[0,9],"canonical":[9,88],"independent_dual":[88,112],"local_null":[112,121],
            "auxiliary_blocks":[item["indices"] for item in auxiliary]},
        "canonical_operator":encode(A),"independent_dual_operator":encode(B),
        "canonical_source_map":encode(source_can),"independent_dual_source_map":encode(source_complement),
        "local_source_compatibility_map":encode(compatibility),
        "source_contact_terms":contacts,"total_contact_kernel":encode(contact),
        "contact_field_response":encode(field_contact),
        "canonical_field_lift":encode(F[:,9:88]),"independent_dual_field_lift":encode(F[:,88:112]),
        "equation_row_lift":encode(row_lift),
        "all_original_equations_factor_through_source_blocks":True,
        "exchange_formula":"-1/2 [j(-p)^T Contact(p) j(p) + f79(-p)^T A79(p)^-1 f79(p) + f24(-p)^T B24(p)^-1 f24(p)]",
        "domain":"compatibility(p)*j(p)=0 and the two explicit dynamic blocks invertible; extend individual responses only after cancellation",
        "independent_dual_source_nonzero_and_only_from_original_spin_connection":True,
        "actual_complementary_source_vertices":complement_vertices,
        "canonical_real_complementary_vertices_identically_zero":True,
        "both_original_weak_quintuples_consume_full_normal_form":True,
        "canonical_axial_bilinear_spin_operators":[encode(matrix) for matrix in axial],
        "canonical_spin_source_axial_map":encode(spin_map),
        "canonical_spin_contact_kernel":encode(spin_kernel),
        "canonical_spin_contact_action":"3*N/16 * (-(axial0)^2+(axial1)^2+(axial2)^2+(axial3)^2), axial_a=sqrt(2)*xi^dagger S gamma_a gamma5 xi",
        "peripheral_61_scalar_exchange_included":False,
        "raw_spin_source_automatically_on_shell_or_prepared":False}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n")
    print("PASS: full polynomial two-sided frame; true auxiliary/scalar contacts; 79+24 propagation; all289 source equations",flush=True)


if __name__=="__main__":main()
