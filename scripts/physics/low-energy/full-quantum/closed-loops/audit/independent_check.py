#!/usr/bin/env python3
"""Independent complete-word expansion, coframe-density arrow and reverse-adjoint controls."""
import argparse
from collections import Counter
import itertools
import json
from pathlib import Path

import sympy as s


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root",type=Path,required=True)
    root=parser.parse_args().root.resolve()
    base=root/"Verification/physics/low-energy-phenomenology"
    audit=base/"full-quantum/closed-loops/audit"
    current=json.loads((base/"full-quantum/closed-loops/receipt.json").read_text())
    full=json.loads((base/"full-quantum/receipt.json").read_text())
    phase=json.loads((base/"full-phase/receipt.json").read_text())
    vertices=json.loads((base/"matter-vertices/receipt.json").read_text())
    upstream=json.loads((base/"full-quantum/triangular/audit/independent-receipt.json").read_text())
    assert upstream["status"]=="PASS"
    p=s.symbols("p0:4",real=True)
    def decode(record):return s.SparseMatrix(*record["shape"],{(i,j):s.sympify(v,locals={str(x):x for x in p})
        for i,j,v in record["entries"]})
    def clean(matrix):return s.SparseMatrix(matrix).applyfunc(s.expand)
    def canonical(matrix):return s.SparseMatrix(matrix).applyfunc(lambda v:s.radsimp(s.cancel(s.expand(v))))
    def equal(left,right):assert not canonical(left-right).todok()
    I=s.eye(252,cls=s.SparseMatrix);zero=s.zeros(252,cls=s.SparseMatrix)
    P=s.diag(*[int(j%63<7) for j in range(252)],cls=s.SparseMatrix);Q=I-P
    H0=decode(full["original_H_free"]);N=decode(full["original_H_yukawa"])
    Cinv=decode(full["time_principal_inverse"])
    C=[decode(x) for x in phase["principal_coefficients"]]
    lapse=s.sympify(phase["source_lapse"]);gamma0=lapse*C[0]/s.I
    Y=clean(s.I*C[0]*N)
    equal(Y,decode(phase["original_Y"]))
    def arrow(A):equal(P*A,A);equal(A*P,zero)
    def expansion(A,D):equal(P*D,D*P);arrow(A-D)
    arrow(N)
    evaluated=[];diagonals=[];counts=Counter();coframe_arrows=[];scalar_ids=[]
    values=dict(zip(p,[s.Rational(5,7),s.Rational(1,3),-s.Rational(2,5),s.Rational(3,7)]))
    for index,item in enumerate(vertices["primitive_vertices"]):
        V=decode(item["operator"]);D=clean(P*V*P+Q*V*Q);delta=clean(V-D)
        expansion(V,D);counts[item["group"]]+=1
        if item["group"]=="coframe":
            mu,a=item["coordinate"]
            volume_derivative=(1 if mu==0 else lapse) if mu==a else 0
            equal(delta,volume_derivative*Y)
            if delta.todok():
                coframe_arrows.append({"vertex":index,"coordinate":[mu,a],"coefficient_of_actual_Y":str(volume_derivative)})
                assert clean(P*V-V*P).todok()
        elif item["group"]=="scalar":
            arrow(V);equal(D,zero);assert V.todok();scalar_ids.append(index)
        else:equal(delta,zero)
        evaluated.append(clean(V.subs(values)));diagonals.append(clean(D.subs(values)))
    assert dict(counts)==current["automatic_original_vertex_triangular_expansions"]
    assert [x["coordinate"] for x in coframe_arrows]==[[0,0],[1,1],[2,2],[3,3]]
    print("PASS all158 symbolic source vertices; four coframe density Y terms retained",flush=True)

    # Inversion uses the independently audited trace recurrence on source blocks.
    def groups(A):
        parent=list(range(252))
        def find(i):
            while parent[i]!=i:parent[i]=parent[parent[i]];i=parent[i]
            return i
        for i,j in A.todok():
            a,b=find(i),find(j)
            if a!=b:parent[max(a,b)]=min(a,b)
        result={}
        for i in range(252):result.setdefault(find(i),[]).append(i)
        return list(result.values())
    cache={}
    def inverse(A):
        output=s.MutableSparseMatrix(252,252,{})
        for group in groups(A):
            block=s.ImmutableMatrix(A.extract(group,group))
            if block not in cache:
                n=block.rows;unit=s.eye(n);B=unit
                for j in range(1,n+1):
                    AB=block*B;c=s.simplify(-s.trace(AB)/j)
                    if j==n:
                        assert c!=0;inv=canonical(-B/c)
                    B=canonical(AB+c*unit)
                equal(B,s.zeros(n));equal(block*inv,unit);cache[block]=inv
            for (i,j),v in cache[block].todok().items():output[group[i],group[j]]=v
        answer=s.SparseMatrix(output);equal(A*answer,I);equal(answer*A,I);return answer
    spatial=[-lapse*gamma0*C[j+1]/s.I for j in range(3)]
    points=[([0,0,0],1+2*s.I),([0,0,3*s.sqrt(2)/2],3+s.I)]
    propagators=[];free=[]
    for momentum,z in points:
        H=clean(H0+sum((k*A for k,A in zip(momentum,spatial)),zero))
        K=z*I-H;R0=inverse(K);R=canonical(R0+R0*N*R0)
        equal((K-N)*R,I);equal(R*(K-N),I)
        GD=canonical(s.I*R*Cinv);G0=canonical(s.I*R0*Cinv)
        D=clean(-s.I*C[0]*(K-N))
        equal(D*GD,I);equal(GD*D,I);expansion(GD,G0)
        assert canonical(GD-G0).todok()
        propagators.append(GD);free.append(G0)

    def product(matrices):
        result=I
        for A in matrices:result=clean(result*A)
        return result
    records=[]
    for record in current["words"]:
        indices=record["vertices"]
        full_factors=[clean(propagators[j%2]*evaluated[i]) for j,i in enumerate(indices)]
        free_factors=[clean(free[j%2]*diagonals[i]) for j,i in enumerate(indices)]
        for A,D in zip(full_factors,free_factors):expansion(A,D)
        complete=product(full_factors);diagonal=product(free_factors)
        single=zero
        for j in range(len(indices)):
            single+=product(free_factors[:j])* (full_factors[j]-free_factors[j])*product(free_factors[j+1:])
        equal(complete-diagonal,single);arrow(single)
        trace=s.simplify(s.trace(complete));diagonal_trace=s.simplify(s.trace(diagonal))
        assert s.simplify(trace-diagonal_trace)==0
        assert s.simplify(trace-s.sympify(record["full_trace"]))==0
        records.append({"vertices":indices,"complete_single_arrow_identity":True,"trace_equals_free":True,
            "trace_nonzero":trace!=0,"open_difference_nonzero":bool(clean(single).todok())})
        print("PASS full ordered operator expansion",indices,flush=True)
    # Actual full operators must retain their order, not just the multiset of vertices.
    original_ids=current["words"][2]["vertices"]
    original_trace=s.sympify(current["words"][2]["full_trace"])
    order_control=None
    for swapped in itertools.permutations(original_ids):
        if list(swapped)==original_ids:continue
        candidate=product([free[j%2]*diagonals[i] for j,i in enumerate(swapped)])
        if s.simplify(s.trace(candidate)-original_trace)!=0:
            order_control=list(swapped);break
    assert order_control is not None
    for index in scalar_ids:
        V=evaluated[index]
        assert clean(propagators[0]*V).todok()
        assert s.simplify(s.trace(propagators[0]*evaluated[0]*propagators[1]*V))==0
        equal(V*propagators[0]*P,zero)
    # Every right scalar has P*V=V, so the previous 70 identities certify all
    # 70x70 distinct scalar pairs, without only rechecking equal-index pairs.
    for index in scalar_ids:equal(P*evaluated[index],evaluated[index])
    reverse=s.simplify(s.trace(N.H*N))
    assert reverse==s.Rational(1296,125)
    assert canonical(P*N.H-N.H*P).todok()
    hermitian=N+N.H
    assert s.simplify(s.trace(hermitian*hermitian))==2*reverse
    # A coframe lapse change changes the one-way Hamiltonian part itself.
    first=H0+N;second=2*(H0+N)
    variation=first-second;diagonal_variation=H0-2*H0
    expansion(variation,diagonal_variation)
    equal(variation-diagonal_variation,-N)
    assert clean(P*variation-variation*P).todok()
    result={"status":"PASS","full_source_vertex_counts":dict(counts),"coframe_density_arrows":coframe_arrows,
        "both_original_Dirac_propagators_two_sided":True,"ordered_words":records,
        "order_permutation_changes_trace":order_control,"all70_scalar_vertices_nonzero_and_closed_trace_zero":True,
        "all4900_distinct_scalar_pairs_zero_via_complete_G":True,
        "reverse_adjoint_trace":str(reverse),"Hermitian_replacement_squared_trace":str(2*reverse),
        "coframe_lapse_variation_keeps_nonzero_arrow":True,
        "scope":"Original independent-dual finite matrix words. No vacuum measure or replacement by Hermitian vertices is supplied."}
    (audit/"independent-receipt.json").write_text(json.dumps(result,indent=2)+"\n")
    print("PASS ordered source traces, current coframe Y, distinct scalar chains and reverse-adjoint controls",flush=True)


if __name__=="__main__":main()
