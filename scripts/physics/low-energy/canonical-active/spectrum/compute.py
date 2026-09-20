#!/usr/bin/env python3
"""Split the certified 103 symbol into canonical 79 and independent-dual 24.

Both inverse polynomial changes and the signed-transpose congruence are
checked before determinant division. Only the small 24-block is recomputed.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix


def clean(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.expand)


def decode(entries,rows,cols,locals=None,replace=None):
    values={}
    for row,col,text in entries:
        if replace:
            for old,new in replace.items(): text=text.replace(old,new)
        values[row,col]=s.sympify(text,locals=locals)
    return s.SparseMatrix(rows,cols,values)


def encode(matrix):
    return [[int(i),int(j),str(s.factor(value))]
            for (i,j),value in s.SparseMatrix(matrix).todok().items()]


def monic_factors(expression,u,q):
    constant,pieces=s.factor_list(expression,u,q)
    factors=defaultdict(int)
    for factor,power in pieces:
        polynomial=s.Poly(factor,u,q,domain=s.QQ)
        constant*=polynomial.LC()**power
        factors[str(polynomial.monic().as_expr())]+=power
    return s.factor(constant),{key:int(value) for key,value in factors.items()}


def small_determinant(matrix,u,q):
    denominators=[]
    for row in matrix.tolist():
        den=1
        for value in row:
            for coefficient in s.Poly(value,u,q,domain=s.QQ_I).coeffs():
                den=s.ilcm(den,s.denom(s.re(coefficient)),s.denom(s.im(coefficient)))
        denominators.append(den)
    domain=s.ZZ_I.poly_ring(u,q)
    integer=s.diag(*denominators)*matrix
    determinant=DomainMatrix.from_Matrix(integer).convert_to(domain).det()
    return domain.to_sympy(determinant)/s.prod(denominators),denominators


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source",type=Path,required=True)
    parser.add_argument("--old-quotient",type=Path,required=True)
    parser.add_argument("--old-propagation",type=Path,required=True)
    parser.add_argument("--old-catalog",type=Path,required=True)
    parser.add_argument("--canonical",type=Path,required=True)
    parser.add_argument("--out",type=Path,required=True)
    args=parser.parse_args(); started=time.monotonic()
    source=json.loads(args.source.read_text()); old=json.loads(args.old_quotient.read_text())
    propagation=json.loads(args.old_propagation.read_text()); catalog=json.loads(args.old_catalog.read_text())
    canonical=json.loads(args.canonical.read_text())
    assert propagation["all_blocks_complete"] and propagation["quotient_dimension_verified"]==103
    assert canonical["full_equation_closure"] and canonical["quotient_real_coordinates"]==79
    lam,k,u,q=s.symbols("lam k u q",real=True)
    p=s.symbols("p0 p1 p2 p3"); local={str(x):x for x in [lam,k,u,q]+list(p)}
    axis={p[0]:lam,p[1]:0,p[2]:0,p[3]:s.I*k}
    minus={lam:-lam,k:-k}
    n=s.sympify(source["source_lapse"])
    Q103=decode(old["quotient_readback_103_by_112"],103,112,local,{"lambda":"lam"})
    S103=s.SparseMatrix(112,103,{(original-9,i):1 for i,original in enumerate(old["retained_original_fields"])})
    K103=decode(old["quotient_operator_103_by_103"],103,103,local,{"lambda":"lam"})
    C=decode(canonical["canonical_embedding_112_by_88"],112,88,local)
    Cm=decode(canonical["independent_dual_complement_112_by_24"],112,24,local)
    R=decode(canonical["constant_whole_equation_readback_112_by_88"],112,88,local)
    Cleft=R.T
    # Inverse of [C,Cminus], not C^T: the two source columns are not orthogonal.
    E=s.SparseMatrix.hstack(C,Cm)
    Einverse=E.inv(method="DM")
    assert Einverse[:88,:]==Cleft
    Cmleft=Einverse[88:,:]
    E79=decode(canonical["quotient_section"],88,79,local)
    Q79=clean(decode(canonical["quotient_readback"],79,88,local).subs(axis))
    A79=clean(decode(canonical["canonical_quotient_operator"],79,79,local).subs(axis))
    H=s.MutableSparseMatrix(112,112,{})
    momenta=[lam,0,0,s.I*k]
    for row,col,power,value in source["equivalent_112_Fourier_Jacobi_entries"]:
        H[row-9,col-9]+=s.sympify(value)*s.prod(variable**degree for variable,degree in zip(momenta,power))
    H=clean(H)
    F=clean(Q103*s.SparseMatrix.hstack(C*E79,Cm))
    inverseF=clean(s.SparseMatrix.vstack(Q79*Cleft*S103,Cmleft*S103))
    assert clean(inverseF*F)==s.eye(103)
    assert clean(F*inverseF)==s.eye(103)
    B24=clean(Cm.T*H*Cm)
    congruence=clean(F.subs(minus,simultaneous=True).T*K103*F)
    assert congruence==s.diag(A79,B24)
    print("PASS: polynomial two-sided 103 <-> (79+24) inverse and complete signed-transpose block congruence",flush=True)
    # Pay the determinant unit using an explicit square-zero polynomial update of F(0).
    F0=F.subs({lam:0,k:0})
    F0inverse=inverseF.subs({lam:0,k:0})
    update=clean(F0inverse*F-s.eye(103))
    update_square=clean(update*update)
    square_zero=(update_square==s.zeros(103))
    assert square_zero
    constant_field=s.QQ.algebraic_field(s.sqrt(2),s.sqrt(15),s.I)
    for value in list(F.todok().values())+list(inverseF.todok().values()):
        s.Poly(value,lam,k,domain=constant_field)
    determinant_F=constant_field.to_sympy(DomainMatrix.from_Matrix(F0).convert_to(constant_field).det())
    assert determinant_F!=0
    print("PASS: F=F(0)(I+U), U^2=0; constant determinant",determinant_F,flush=True)
    normalized_B=clean(B24.subs({lam:n*s.sqrt(2)*u,k:s.sqrt(2)*q})/n)
    for value in normalized_B.todok().values(): s.Poly(value,u,q,domain=s.QQ_I)
    determinant_Bbar,denominators=small_determinant(normalized_B,u,q)
    Bconstant,Bfactors=monic_factors(determinant_Bbar,u,q)
    print("PASS: computed original 24 complement determinant; total degree",s.Poly(determinant_Bbar,u,q).total_degree(),flush=True)
    # Assemble the previously certified full determinant with its exact constant.
    full_constant=s.sympify(propagation["determinant_constant_multiplier"])
    full_factors=defaultdict(int)
    for block in propagation["blocks"]:
        full_constant*=s.sympify(block["constant"])
        for factor in block["factors"]:
            polynomial=s.Poly(s.sympify(factor["polynomial"],locals=local),u,q,domain=s.QQ)
            power=factor["multiplicity"]
            full_constant*=polynomial.LC()**power
            full_factors[str(polynomial.monic().as_expr())]+=power
    remaining=dict(full_factors)
    for factor,power in Bfactors.items():
        assert remaining.get(factor,0)>=power,(factor,power,remaining.get(factor,0))
        remaining[factor]-=power
        if not remaining[factor]: del remaining[factor]
    Aconstant=s.factor(determinant_F**2*full_constant/(n**24*Bconstant))
    divisor_degree=sum(s.Poly(s.sympify(factor,locals=local),u,q).total_degree()*power
                       for factor,power in remaining.items())
    # Compare to the independently certified generic 79 determinant already in its receipt.
    witness=canonical["generic_rank_witness"]
    assert witness["point"]==["2","0","0","I"]
    sample=Aconstant
    for factor,power in remaining.items():
        sample*=s.sympify(factor,locals=local).subs({u:2/(n*s.sqrt(2)),q:1/s.sqrt(2)})**power
    assert s.simplify(sample-s.sympify(witness["determinant"]))==0
    print("PASS: exact 103/24 division produces canonical degree",divisor_degree,
          "and matches the independent 79 generic determinant constant",flush=True)
    def axis_factors(factors,variable,fixed):
        result=defaultdict(int)
        for text,multiplicity in factors.items():
            expression=s.sympify(text,locals=local).subs(fixed,0)
            assert expression!=0
            _,pieces=s.factor_list(expression,variable)
            for polynomial,power in pieces:
                result[str(s.Poly(polynomial,variable,domain=s.QQ).monic().as_expr())]+=multiplicity*power
        return {key:int(value) for key,value in result.items()}
    gapless=[]
    for branch in catalog["gapless_source_branches"]:
        factor=branch["factor"]
        canonical_power=remaining.get(factor,0); complement_power=Bfactors.get(factor,0)
        assert canonical_power+complement_power==branch["multiplicity"]
        gapless.append({**branch,"canonical_multiplicity":canonical_power,
                        "independent_dual_complement_multiplicity":complement_power})
    # The constant-unit block change transports the local polynomial-module orders.
    # Compute the small complement orders, then remove them from the certified 103 list.
    partials={}
    for variable,fixed in [(u,q),(q,u)]:
        axis_B=normalized_B.subs(fixed,0)
        axis_divisor=s.Poly(determinant_Bbar.subs(fixed,0),variable)
        determinant_order=min(degree[0] for degree,_ in axis_divisor.terms())
        coefficients=[axis_B.diff(variable,degree).subs(variable,0)/s.factorial(degree)
                      for degree in range(4)]
        nullities=[]
        for length in range(1,5):
            toeplitz=s.BlockMatrix([[coefficients[row-col] if row>=col else s.zeros(24)
                for col in range(length)] for row in range(length)]).as_explicit()
            rank=DomainMatrix.from_Matrix(toeplitz).convert_to(s.QQ_I).rank()
            nullities.append(24*length-rank)
            if nullities[-1]==determinant_order: break
        assert nullities[-1]==determinant_order
        slopes=[nullities[0]]+[nullities[i]-nullities[i-1] for i in range(1,len(nullities))]+[0]
        complement_orders=[]
        for degree in range(1,len(slopes)):
            complement_orders += [degree]*(slopes[degree-1]-slopes[degree])
        full_orders=catalog["origin_partial_multiplicities"][str(variable)]["nonzero_partial_multiplicities"]
        leftover=Counter(full_orders)
        for degree in complement_orders:
            leftover[degree]-=1
            assert leftover[degree]>=0
        canonical_orders=sorted(leftover.elements())
        canonical_axis=axis_factors(remaining,variable,fixed)
        assert sum(canonical_orders)==canonical_axis.get(str(variable),0)
        partials[str(variable)]={"complement_truncated_nullities":list(map(int,nullities)),
            "complement_partial_multiplicities":complement_orders,
            "canonical_partial_multiplicities":canonical_orders,
            "canonical_kernel_dimension_at_origin":len(canonical_orders),
            "canonical_determinant_order_at_origin":sum(canonical_orders)}
    # Identify the precise canonical polynomial carrying the original five-state roots.
    five_state_factors=[]
    for text,multiplicity in remaining.items():
        axis=s.Poly(s.sympify(text,locals=local).subs(q,0),u,domain=s.QQ)
        _,remainder=axis.div(s.Poly(u*(u*u+6)*(u*u-s.Rational(3125,162)),u,domain=s.QQ))
        if remainder.is_zero:
            five_state_factors.append({"polynomial":text,"multiplicity":multiplicity,
                "q_zero_factorization":str(s.factor(axis.as_expr()))})
    assert len(five_state_factors)==1
    result={"scope":"FAITHFUL_CANONICAL_79_AND_INDEPENDENT_DUAL_24_CHARACTERISTIC_SPLIT",
        "normalization":"lambda=N*sqrt(2)*u, k=sqrt(2)*q; Bbar=B24/N",
        "forward_103_by_103":encode(F),"inverse_103_by_103":encode(inverseF),
        "constant_F_at_origin":encode(F0),"square_zero_update":encode(update),
        "both_inverse_identities":True,"full_signed_transpose_block_congruence":True,
        "both_changes_are_polynomial_over_constant_field":True,
        "square_zero_update_verified":square_zero,"determinant_F_constant":str(determinant_F),
        "complement_24_normalized_operator":encode(normalized_B),
        "complement_row_denominators":list(map(str,denominators)),
        "complement_normalized_determinant_constant":str(Bconstant),
        "complement_factors":[{"polynomial":f,"multiplicity":m} for f,m in Bfactors.items()],
        "canonical_determinant_constant":str(Aconstant),
        "canonical_factors":[{"polynomial":f,"multiplicity":m} for f,m in remaining.items()],
        "canonical_factor_count":len(remaining),"canonical_total_divisor_degree":int(divisor_degree),
        "canonical_generic_determinant_crosscheck":True,
        "canonical_q_zero_factors":axis_factors(remaining,u,q),
        "complement_q_zero_factors":axis_factors(Bfactors,u,q),
        "canonical_u_zero_factors":axis_factors(remaining,q,u),
        "gapless_branch_assignments":gapless,
        "origin_partial_multiplicities":partials,
        "source_five_state_polynomial_owner":five_state_factors[0],
        "physical_uniqueness_or_particle_count_claimed":False,
        "elapsed_seconds":round(time.monotonic()-started,3)}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n")
    print("Complement factors:",Bfactors,flush=True)
    print("Gapless assignment:",[{key:value for key,value in b.items() if key!="factor"} for b in gapless],flush=True)


if __name__=="__main__": main()
