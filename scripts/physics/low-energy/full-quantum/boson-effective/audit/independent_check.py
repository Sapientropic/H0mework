#!/usr/bin/env python3
"""Original-Hessian reconstruction, independently constrained sources and whole-system inverse controls."""
from ast import literal_eval
from functools import lru_cache
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

import sympy as s
from sympy.polys.matrices import DomainMatrix

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[5]
BASE=ROOT/'Verification/physics/low-energy-phenomenology'
u,q=s.symbols('u q',real=True)


@lru_cache(None)
def norm(v):return s.radsimp(s.cancel(s.expand(v)))


def clean(A):return s.SparseMatrix(A).applyfunc(norm)


def equal(A,B):assert not clean(A-B).todok()


def decode(r):return s.SparseMatrix(*r['shape'],{(i,j):s.sympify(v,locals={'u':u,'q':q}) for i,j,v in r['entries']})


def encoded(M):return {'shape':list(M.shape),'entries':[[int(i),int(j),str(v)] for (i,j),v in sorted(s.SparseMatrix(M).todok().items())]}


def source_matrix(entries,n,momenta):
    M=s.zeros(n,cls=s.SparseMatrix)
    for i,j,power,value in entries:M[i,j]+=s.sympify(value)*s.prod(p**a for p,a in zip(momenta,power))
    return clean(M)


def truncate(M):return s.SparseMatrix(M).applyfunc(lambda v:s.expand(sum(c*u**a*q**b for (a,b),c in s.Poly(s.expand(v),u,q).terms() if a+b<=2)))


def components(M):
    graph={j:set() for j in range(M.rows)}
    for i,j in M.todok():graph[i].add(j);graph[j].add(i)
    remaining=set(graph);result=[]
    while remaining:
        queue=[min(remaining)];group=set(queue)
        while queue:
            for i in graph[queue.pop()]-group:group.add(i);queue.append(i)
        remaining-=group;result.append(sorted(group))
    return result


def main():
    started=time.monotonic();base=BASE/'active-gauge'
    original=json.loads((base/'receipt.json').read_text());quotient=json.loads((base/'quotient.json').read_text())
    propagation=json.loads((base/'propagation.json').read_text());symmetry=json.loads((base/'symmetries.json').read_text())
    saved=json.loads((HERE.parent/'receipt.json').read_text());wb=json.loads((HERE.parent/'readback-receipt.json').read_text())
    lowreceipt=json.loads((HERE.parent/'low-readback-receipt.json').read_text());dynamic=json.loads((HERE.parent/'dynamic-receipt.json').read_text())
    cofactor=json.loads((HERE.parent/'cofactor-receipt.json').read_text());old=json.loads((BASE/'full-quantum/full-current/receipt.json').read_text())
    for path,digest in original['source_sha256'].items():assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest
    for record in [saved,wb,lowreceipt,dynamic,cofactor]:assert record['source_sha256']==original['source_sha256']
    N=s.sympify(original['source_lapse']);momenta=[N*s.sqrt(2)*u,0,0,s.I*s.sqrt(2)*q]
    H=source_matrix(original['Fourier_Jacobi_entries'],289,momenta)
    fields=original['fields'];ret=saved['original_retained103'];scale=list(map(s.sympify,saved['normalized_field_scaling']))
    matter=[ret.index(i) for i in saved['matter48_source_indices']];bosons=[ret.index(i) for i in saved['boson55_source_indices']]
    current=H;remaining=list(range(289));steps=[];matter_feedback=[]
    originalMatter=saved['matter48_source_indices']
    # Rebuild the source121 operator from the original289, not from the candidate quotient table.
    for step in original['algebraic_Schur_steps']:
        elim=step['eliminated_fields'];ei=[remaining.index(i) for i in elim];ki=[i for i in range(len(remaining)) if i not in ei]
        kept=[remaining[i] for i in ki]
        inv=s.SparseMatrix(len(ei),len(ei),{(elim.index(i),elim.index(j)):s.sympify(v) for i,j,v in step['algebraic_block_inverse']})
        A=current.extract(ei,ei);equal(A*inv,s.eye(len(ei)));equal(inv*A,s.eye(len(ei)))
        C=current.extract(ei,ki);B=current.extract(ki,ei);write=clean(-inv*C)
        oldm=current.extract([remaining.index(i) for i in originalMatter],[remaining.index(i) for i in originalMatter])
        nextmatrix=clean(current.extract(ki,ki)+B*write)
        newm=nextmatrix.extract([kept.index(i) for i in originalMatter],[kept.index(i) for i in originalMatter])
        matter_feedback.append(len(clean(newm-oldm).todok()))
        steps.append((elim,kept,write));current=nextmatrix;remaining=kept
    assert remaining==list(range(121));assert matter_feedback[:2]==[0,0] and matter_feedback[2]>0
    scaling=s.diag(*scale);K=clean(scaling*current.extract(ret,ret)*scaling/N)
    lam,k=s.symbols('lam k',real=True)
    frozenK=s.SparseMatrix(103,103,{(i,j):s.sympify(v.replace('lambda','lam'),locals={'lam':lam,'k':k}).subs({lam:momenta[0],k:s.sqrt(2)*q})*scale[i]*scale[j]/N for i,j,v in quotient['quotient_operator_103_by_103']})
    equal(K,frozenK)
    W=decode(saved['matter48_writeback_from_boson55']);S=decode(saved['effective_boson55'])
    equal(K.extract(matter,matter)*W,-K.extract(matter,bosons))
    equal(K.extract(bosons,bosons)+K.extract(bosons,matter)*W,S)
    equal(S.subs({u:-u,q:-q},simultaneous=True).T,S)
    print('PASS actual289 auxiliary elimination generates candidate103/55; only Lorentz changes matter',flush=True)

    # Generate source injection from the original annihilator equations, without Q or H*F.
    negative=[-v for v in momenta];T=s.zeros(112,9,cls=s.SparseMatrix)
    for i,j,power,value in symmetry['source_symmetry_tangents_112']:
        T[i-9,j]+=s.sympify(value)*s.prod(p**a for p,a in zip(negative,power))
    T=clean(T);deleted=[i-9 for i in quotient['fixed_section_removed_original_fields']];selected=[i-9 for i in ret]
    constraint=T.extract(deleted,range(9)).T;constraintInverse=clean(constraint.inv(method='DM'))
    equal(constraint*constraintInverse,s.eye(9));assert not any(v.has(u,q) for v in constraint.todok().values())
    broken=original['Ward_constraint_elimination']['broken_parameter_columns'];Ward=s.zeros(121,9,cls=s.SparseMatrix)
    for i,j,power,value in original['source_primitive_gauge_tangent']:
        if i<121 and j in broken:Ward[i,broken.index(j)]+=s.sympify(value)*s.prod(p**a for p,a in zip(negative,power))
    Ward=clean(Ward);WI=clean(Ward[:9,:].T.inv(method='DM'));equal(WI*Ward[:9,:].T,s.eye(9))
    def injection(kept):
        raw=s.zeros(112,len(kept),cls=s.SparseMatrix)
        for j,i in enumerate(kept):raw[ret[i]-9,j]=N/scale[i]
        missing=clean(-constraintInverse*T.extract(selected,range(9)).T*raw[selected,:])
        for row,i in enumerate(deleted):raw[i,:]=missing[row,:]
        equal(T.T*raw,s.zeros(9,len(kept)))
        result=s.zeros(289,len(kept),cls=s.SparseMatrix)
        result[9:121,:]=raw;result[:9,:]=clean(-WI*Ward[9:,:].T*raw)
        equal(Ward.T*result[:121,:],s.zeros(9,len(kept)))
        return result
    J=injection(bosons);equal(J,decode(wb['source_injection']));assert len(J[:9,:].todok())==32
    assert not J[originalMatter,:].todok() and not J[121:,:].todok()
    def lift(section,cut=False):
        output=s.zeros(289,section.cols,cls=s.SparseMatrix)
        for (i,j),value in section.todok().items():output[ret[i],j]=scale[i]*value
        for elim,kept,write in reversed(steps):
            values=clean(write*output[kept,:]);values=truncate(values) if cut else values
            for i,row in enumerate(elim):output[row,:]=values[i,:]
        return output
    section=s.zeros(103,55,cls=s.SparseMatrix)
    for j,i in enumerate(bosons):section[i,j]=1
    for (i,j),value in W.todok().items():section[matter[i],j]=value
    F=lift(section);equal(F,decode(wb['field_response_lift']));equal(H*F,J*S)
    wrong_source=J.copy();wrong_source[:9,:]=s.zeros(9,55)
    assert clean(H*F-wrong_source*S).todok()
    print('PASS independently solved Ward/symmetry source injection and every all-symbol289 field row',flush=True)

    M0=K.extract(matter,matter).subs({u:0,q:0});pivots=list(M0.rref()[1]);heavy=[matter[i] for i in pivots];light=[i for i in matter if i not in heavy]
    assert len(heavy)==42 and len(light)==6
    assert [ret[i] for i in heavy]==saved['heavy42_source_indices'] and [ret[i] for i in light]==saved['light6_source_indices']
    A=K.extract(heavy,heavy).subs({u:0,q:0});G0=clean(A.inv(method='DM'));equal(A*G0,s.eye(42));equal(G0*A,s.eye(42))
    equal(G0,decode(saved['origin_heavy_inverse']));det=A.det(method='domain-ge');assert det!=0 and det==s.sympify(lowreceipt['heavy42_origin_determinant'])
    delta=clean(K.extract(heavy,heavy)-A);assert all(s.Poly(v,u,q).total_degree()<=1 for v in delta.todok().values())
    jet=clean(G0-G0*delta*G0+G0*delta*G0*delta*G0);exact_res=clean((A+delta)*jet-s.eye(42))
    equal(exact_res,delta*G0*delta*G0*delta*G0);assert exact_res.todok()
    kept=bosons+light;low=truncate(K.extract(kept,kept)-K.extract(kept,heavy)*jet*K.extract(heavy,kept))
    expectedLow=clean(sum((decode(v)*u**literal_eval(key)[0]*q**literal_eval(key)[1] for key,v in saved['local61_coefficients_degree2'].items()),s.zeros(61)))
    equal(low,expectedLow);equal(low,decode(lowreceipt['low61_effective_operator']))
    lowSection=s.zeros(103,61,cls=s.SparseMatrix)
    for j,i in enumerate(kept):lowSection[i,j]=1
    write=truncate(-jet*K.extract(heavy,kept))
    for (i,j),v in write.todok().items():lowSection[heavy[i],j]=v
    lowF=lift(lowSection,True);lowJ=injection(kept)
    equal(lowF,decode(lowreceipt['whole289_low_field_lift']));equal(lowJ,decode(lowreceipt['whole289_low_source_injection']))
    residual=clean(H*lowF-lowJ*low);assert truncate(residual)==s.zeros(289,61)
    degree=min(a+b for v in residual.todok().values() for (a,b),c in s.Poly(v,u,q).terms() if c);assert degree==3
    origin=low.subs({u:0,q:0});assert origin.rank()==56 and len(origin.nullspace())==5
    print('PASS actual origin42/6 and full61 coefficients/lift, nonzero cubic original289 remainder and five origin kernels',flush=True)

    # A distinct exact complex source point: use the inverse of the whole103 system,
    # instead of assuming or constructing a55 inverse first.
    at={u:s.Rational(1,4)+s.I/6,q:s.Rational(2,7)}
    domain=s.QQ.algebraic_field(s.sqrt(2),s.sqrt(15),s.I);cache={};maxblock=0
    def inverse(M):
        nonlocal maxblock
        result=s.zeros(M.rows,cls=s.SparseMatrix)
        for group in components(M):
            maxblock=max(maxblock,len(group));block=s.ImmutableMatrix(M.extract(group,group))
            if block not in cache:
                dm=DomainMatrix.from_Matrix(block).convert_to(domain);iv=dm.inv();assert dm.matmul(iv)==DomainMatrix.eye(dm.shape,domain)
                assert iv.matmul(dm)==DomainMatrix.eye(dm.shape,domain);cache[block]=clean(iv.to_Matrix())
            for (i,j),v in cache[block].todok().items():result[group[i],group[j]]=v
        return result
    Kv=clean(K.subs(at));Kinverse=inverse(Kv);Sv=clean(S.subs(at));R=Kinverse.extract(bosons,bosons)
    equal(Sv*R,s.eye(55));equal(R*Sv,s.eye(55));equal(Kinverse.extract(matter,bosons),W.subs(at)*R)
    Hv=clean(H.subs(at));full=clean(F.subs(at)*R);equal(Hv*full,J.subs(at))
    fullMatter=originalMatter;aux=list(range(121,289));originalD=Hv.extract(fullMatter,fullMatter)
    Aaux=Hv.extract(aux,aux);Ai=inverse(Aaux);Di=inverse(originalD)
    crossAM=Hv.extract(aux,fullMatter);crossMA=Hv.extract(fullMatter,aux)
    modified=clean(originalD-crossMA*Ai*crossAM);modifiedI=inverse(modified)
    feedback=clean(modified-originalD);assert feedback.todok()
    changed=clean(Aaux-crossAM*Di*crossMA)
    changedI=clean(Ai+Ai*crossAM*modifiedI*crossMA*Ai)
    equal(changed*changedI,s.eye(168));equal(changedI*changed,s.eye(168))
    # Compare the entire joint inverse, not only a selected55 reader.
    upper=clean(Ai+Ai*crossAM*modifiedI*crossMA*Ai);ur=clean(-Ai*crossAM*modifiedI);ll=clean(-modifiedI*crossMA*Ai)
    otherUR=clean(-changedI*crossAM*Di);otherLL=clean(-Di*crossMA*changedI)
    otherLower=clean(Di+Di*crossMA*changedI*crossAM*Di)
    equal(upper,changedI);equal(ur,otherUR);equal(ll,otherLL);equal(modifiedI,otherLower)
    joint=clean(Aaux.row_join(crossAM).col_join(crossMA.row_join(originalD)))
    jointInverse=clean(upper.row_join(ur).col_join(ll.row_join(modifiedI)))
    equal(joint*jointInverse,s.eye(216));equal(jointInverse*joint,s.eye(216))
    # The true untruncated heavy inverse obeys the exact cubic identity.
    dv=clean(delta.subs(at));actualHeavy=inverse(clean(A+dv));jv=clean(jet.subs(at))
    equal(actualHeavy,jv-G0*dv*G0*dv*G0*dv*actualHeavy);assert clean(actualHeavy-jv).todok()
    print('PASS distinct whole103 inverse yields55 propagator, true216 two-order inverse and untruncated heavy remainder',flush=True)

    # Direct unprojected33 source solve at this point checks the canonical25 result independently.
    source_index=next(i for i,j in enumerate(ret) if fields[j]=={'group':'coframe','coordinate':[0,0]})
    ids=next(b['quotient_indices'] for b in propagation['blocks'] if source_index in b['quotient_indices']);slot=ids.index(source_index)
    raw33=Kinverse.extract(ids,ids)[:,slot]
    equal(Kv.extract(ids,ids)*raw33,s.eye(len(ids))[:,slot]);metric=norm(4*N**3*raw33[slot])
    expr=s.sympify(dynamic['dynamic_metric_inverse_response'],locals={'u':u,'q':q});other=s.sympify(cofactor['dynamic_metric_inverse_response'],locals={'u':u,'q':q})
    assert s.cancel(expr-other)==0;assert norm(metric-expr.subs(at))==0
    dynamicFull=decode(dynamic['full289_dynamic_metric_green']);source=s.zeros(289,1);source[ret[source_index]]=-2*N
    equal(H*dynamicFull,source);assert s.cancel(-2*N*dynamicFull[ret[source_index]]-expr)==0
    n,d=s.fraction(s.cancel(expr/(-162*s.sqrt(30)/3125)));assert s.gcd(n,d)==1
    cd=s.sympify(cofactor['source_reduced_determinant'],locals={'u':u,'q':q});cn=s.sympify(cofactor['source_cofactor'],locals={'u':u,'q':q})
    assert s.cancel(4*N**3*cn/cd-expr)==0
    r=s.symbols('r',real=True);ray=s.limit(expr.subs(u,r*q),q,0)
    assert s.simplify(ray-54*s.sqrt(30)*(297*r*r-125)/(3125*(162*r*r-125)))==0
    static=s.limit(expr.subs(u,0),q,0);temporal=s.limit(expr.subs(q,0),u,0)
    assert static==54*s.sqrt(30)/3125 and temporal==99*s.sqrt(30)/3125 and static!=temporal
    assert (297*s.Rational(125,162)-125)==s.Rational(625,6)
    on_light=s.factor(d.subs(u,s.sqrt(s.Rational(125,162))*q));assert on_light!=0
    assert min(power[0] for power,c in s.Poly(on_light,q).terms())==4
    result={'status':'PASS','source_sha256_current':True,'original_H289_rebuilt_to_source103':True,
        'matter_feedback_entries_by_auxiliary_step':matter_feedback,'source_injection_method':'Solve original negative-momentum symmetry and Ward annihilator rows, with retained source entries fixed; no H F or targetS used',
        'all_symbol_HF_equals_JS':True,'nonzero_scalar_Ward_source_entries':32,
        'actual_M0_rank':42,'actual_heavy_minor_determinant':str(det),'retained_matter_null_directions':6,
        'all61_second_order_coefficients_and_original_lift':True,'original289_low_residual_minimum_degree':degree,
        'constant61_rank':56,'constant61_nullity':5,
        'new_point':{str(k):str(v) for k,v in at.items()},'whole103_inverse_generates55_and_all289_columns':True,
        'whole216_both_elimination_orders_actual_inverse':True,'true_heavy_inverse_differs_from_jet':True,
        'maximum_independent_inverse_block':maxblock,'unprojected33_metric_solve_matches':True,
        'original_dynamic_all289_source_rows':True,'metric_coprime_numerator_denominator':True,
        'static_limit':str(static),'time_axis_limit':str(temporal),'leading_pole_numerator':str(s.Rational(625,6)),
        'full_denominator_on_leading_light_line':str(on_light),'leading_light_line_is_not_exact_full_dispersion':True,
        'scope':'Original axial source matrices and generated generic consumers; metric inverse response has the opposite sign to the induced field for +J00 delta g00.',
        'seconds':round(time.monotonic()-started,3)}
    (HERE/'independent-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS independent full-source metric response and calibrated low-momentum divisor',flush=True)


if __name__=='__main__':main()
