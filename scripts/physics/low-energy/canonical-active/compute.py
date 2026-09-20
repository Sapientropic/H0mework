#!/usr/bin/env python3
"""Canonical tangent restriction of the original Ward-reduced active symbol.

The discarded independent-dual equations are tested explicitly. A pullback
alone is never accepted as a closed propagation equation.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix


def clean(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.expand)


def encode(matrix):
    return [[int(i),int(j),str(s.factor(value))]
            for (i,j),value in s.SparseMatrix(matrix).todok().items()]


def consume_time(operator,lift,generator,p):
    """Apply the polynomial differential operator to lift*exp(t*generator)."""
    result=s.zeros(operator.rows,generator.rows)
    jets={0:lift}
    for (row,col),value in s.SparseMatrix(operator).todok().items():
        polynomial=s.Poly(value.subs({p[1]:0,p[2]:0,p[3]:0}),p[0])
        for (degree,),coefficient in polynomial.terms():
            if degree not in jets: jets[degree]=clean(lift*generator**degree)
            for target in range(generator.rows):
                result[row,target]+=coefficient*jets[degree][col,target]
    return clean(result)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt",type=Path,required=True)
    parser.add_argument("--symmetries",type=Path,required=True)
    parser.add_argument("--out",type=Path,required=True)
    args=parser.parse_args()
    started=time.monotonic()
    original=json.loads(args.receipt.read_text())
    symmetry=json.loads(args.symmetries.read_text())
    p=s.symbols("p0 p1 p2 p3")
    H=s.MutableSparseMatrix(112,112,{})
    for i,j,power,value in original["equivalent_112_Fourier_Jacobi_entries"]:
        H[i-9,j-9]+=s.sympify(value)*s.prod(variable**degree for variable,degree in zip(p,power))
    H=clean(H)
    fields=original["fields"][9:121]
    assert [field["group"] for field in fields[:64]].count("gauge_A")==48
    assert all(field["group"]=="primal_H" for field in fields[64:88])
    assert all(field["group"]=="dual_H" for field in fields[88:112])
    for i in range(24):
        expected=[i//12,(i%12)//3,i%3]
        assert fields[64+i]["coordinate"]==fields[88+i]["coordinate"]==expected
    swap=s.Matrix([[0,0,1,0],[0,0,0,1],[1,0,0,0],[0,1,0,0]])
    S=s.kronecker_product(swap,s.eye(3))
    spin=s.sympify(original["actual_background"]["dual_multiple"])
    prepared=s.Matrix(original["actual_background"]["primal_H"])
    assert spin*spin==2 and S*prepared==prepared
    canonical=spin*s.diag(S,-S)
    C=s.SparseMatrix.vstack(s.eye(88),s.SparseMatrix.hstack(s.zeros(24,64),canonical))
    complement=s.SparseMatrix.vstack(s.zeros(64,24),s.eye(24),-canonical)
    total=s.SparseMatrix.hstack(C,complement)
    assert total.rank()==112 and C.rank()==88
    pullback=clean(C.T*H*C)
    all_rows=clean(H*C)
    extra=clean(complement.T*all_rows)
    print("all-momentum independent-dual complement nonzeros:",len(extra.todok()),flush=True)
    # Candidate full row reconstruction is derived by inverting [C,Cminus]^T.
    row_lift=s.SparseMatrix.vstack(s.diag(s.eye(64),s.eye(24)/2),
        s.SparseMatrix.hstack(s.zeros(24,64),canonical/4))
    assert C.T*row_lift==s.eye(88) and complement.T*row_lift==s.zeros(24,88)
    closure=clean(all_rows-row_lift*pullback)
    exact_closure=(closure==s.zeros(112,88))
    assert exact_closure==(extra==s.zeros(24,88))
    tangents=s.MutableSparseMatrix(112,9,{})
    for i,j,power,value in symmetry["source_symmetry_tangents_112"]:
        tangents[i-9,j]+=s.sympify(value)*s.prod(variable**degree for variable,degree in zip(p,power))
    tangents=clean(tangents)
    readback=s.SparseMatrix.hstack(s.eye(88),s.zeros(88,24))
    retained_tangents=clean(readback*tangents)
    tangent_defect=clean(tangents-C*retained_tangents)
    assert clean(H*tangents)==s.zeros(112,9)
    print("canonical closure:",exact_closure,"; symmetry tangent defect entries:",len(tangent_defect.todok()),flush=True)
    result={"scope":"ORIGINAL_ACTIVE_SYMBOL_CANONICAL_PREPARATION_SUBCLASS",
        "source_fields":fields,"canonical_field_count":88,
        "canonical_embedding_112_by_88":encode(C),"independent_dual_complement_112_by_24":encode(complement),
        "restricted_action_88_by_88":encode(pullback),"whole_equations_112_by_88":encode(all_rows),
        "independent_dual_extra_rows_24_by_88":encode(extra),
        "constant_whole_equation_readback_112_by_88":encode(row_lift),
        "whole_equation_closure_defect":encode(closure),"full_equation_closure":exact_closure,
        "source_nine_tangents_canonical_defect":encode(tangent_defect),
        "canonical_source_symmetry_tangents":encode(retained_tangents),
        "all_four_momenta_checked":True,"physical_sector_uniqueness_claimed":False}
    if exact_closure and tangent_defect==s.zeros(112,9):
        # Construct a section from the actual constant symmetry minor, without naming a dimension.
        constant_rows=[i for i in range(88) if not any(retained_tangents[i,j].has(*p) for j in range(9))]
        pivots=retained_tangents[constant_rows,:].T.rref()[1]
        removed=[constant_rows[i] for i in pivots]
        kept=[i for i in range(88) if i not in removed]
        minor=retained_tangents[removed,:]
        inverse=minor.inv(method="DM")
        determinant=s.simplify(minor.det())
        assert determinant!=0 and not determinant.has(*p)
        selector=s.SparseMatrix(9,88,{(i,row):1 for i,row in enumerate(removed)})
        section=s.SparseMatrix(88,len(kept),{(row,i):1 for i,row in enumerate(kept)})
        quotient_readback=clean(section.T*(s.eye(88)-retained_tangents*inverse*selector))
        assert quotient_readback*section==s.eye(len(kept))
        assert clean(section*quotient_readback+retained_tangents*inverse*selector)==s.eye(88)
        reduced=clean(section.T*pullback*section)
        negative_readback=quotient_readback.subs(dict(zip(p,[-variable for variable in p])),simultaneous=True)
        assert clean(pullback-negative_readback.T*reduced*quotient_readback)==s.zeros(88)
        result.update({"quotient_real_coordinates":len(kept),"source_minor_determinant":str(determinant),
            "removed_canonical_fields":removed,"retained_canonical_fields":kept,
            "quotient_readback":encode(quotient_readback),"quotient_section":encode(section),
            "canonical_quotient_operator":encode(reduced),"quotient_uses_momentum_denominators":False})
        domain=s.QQ.algebraic_field(s.sqrt(2),s.sqrt(15),s.I)
        sample={p[0]:2,p[1]:0,p[2]:0,p[3]:s.I}
        sampled=DomainMatrix.from_Matrix(reduced.subs(sample)).convert_to(domain)
        result["generic_rank_witness"]={"point":["2","0","0","I"],"quotient_rank":sampled.rank(),
            "determinant":str(domain.to_sympy(sampled.det()))}
        print("canonical quotient dimension from source minor:",len(kept),"; exact sample rank",sampled.rank(),flush=True)
        # Consume the already generated five-state variation and all original nine-field rows.
        generator=s.Matrix(original["source_homogeneous_Jacobian"])
        original_lift=s.MutableSparseMatrix(289,5,{})
        for row,col,value in original["source_homogeneous_field_lift"]:
            original_lift[row,col]=s.sympify(value)
        original_lift=clean(original_lift)
        primitive_lift=original_lift[9:121,:]
        canonical_lift=primitive_lift[:88,:]
        assert C*canonical_lift==primitive_lift
        original_H=s.MutableSparseMatrix(289,289,{})
        for row,col,power,value in original["Fourier_Jacobi_entries"]:
            original_H[row,col]+=s.sympify(value)*s.prod(variable**degree for variable,degree in zip(p,power))
        assert consume_time(original_H,original_lift,generator,p)==s.zeros(289,5)
        assert consume_time(H,primitive_lift,generator,p)==s.zeros(112,5)
        assert consume_time(pullback,canonical_lift,generator,p)==s.zeros(88,5)
        quotient_lift=consume_time(quotient_readback,canonical_lift,generator,p)
        assert consume_time(reduced,quotient_lift,generator,p)==s.zeros(len(kept),5)
        parameter_lift=clean(inverse*selector*canonical_lift)
        reconstructed=clean(section*quotient_lift+consume_time(retained_tangents,parameter_lift,generator,p))
        assert reconstructed==canonical_lift
        jet_ranks=[]
        stacked=s.zeros(0,5)
        for degree in range(5):
            stacked=stacked.col_join(clean(quotient_lift*generator**degree))
            jet_ranks.append(stacked.rank())
            if jet_ranks[-1]==5: break
        growth=s.sqrt(s.Rational(50,3))
        lapse=s.sympify(original["source_lapse"])
        growing=s.Matrix([0,0,growth,s.Rational(50,3)*lapse,s.Rational(5,2)*lapse])
        assert clean(generator*growing-growth*growing)==s.zeros(5,1)
        growing_readback=clean(quotient_lift*growing)
        assert growing_readback!=s.zeros(len(kept),1)
        result["source_five_state_consumer"]={
            "source_generator":encode(generator),"canonical_88_field_lift":encode(canonical_lift),
            "quotient_79_differential_readback_lift":encode(quotient_lift),
            "source_symmetry_parameter_lift":encode(parameter_lift),
            "all_original_289_rows_zero":True,"whole_112_rows_zero":True,
            "canonical_88_rows_zero":True,"quotient_rows_zero":True,
            "whole_field_reconstruction_with_source_symmetry":True,
            "quotient_jet_observation_ranks":jet_ranks,
            "source_gauge_growth_rate_squared":"50/3",
            "source_gauge_growing_state":encode(growing),
            "nonzero_canonical_quotient_growing_field":encode(growing_readback)}
        print("PASS: original five-state variation consumes all 289/112/88/79 rows; quotient jet ranks",jet_ranks,
              "; original gauge growth survives as a nonzero canonical quotient field",flush=True)
    else:
        first=next(iter(extra.todok().items()),None)
        result["nonzero_witness"]=None if first is None else {"row":int(first[0][0]),"column":int(first[0][1]),"coefficient":str(first[1])}
    result["elapsed_seconds"]=round(time.monotonic()-started,3)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n")


if __name__=="__main__": main()
