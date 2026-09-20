#!/usr/bin/env python3
"""Complete static metric-to-metric response of the original coupled source.

The source is +sum_(mu<=nu) J_munu delta g_munu.  The induced field has
the overall minus sign from H delta field + source = 0.
"""
import argparse
import itertools
import json
from pathlib import Path
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix


def encode(matrix):
    return {'shape':list(matrix.shape),'entries':[[int(i),int(j),str(s.factor(value))]
        for (i,j),value in sorted(s.SparseMatrix(matrix).todok().items())]}


def decode_static(entries,size,q):
    result=s.MutableSparseMatrix(size,size,{})
    for row,col,powers,value in entries:
        if not any(powers[:3]):
            result[row,col]+=s.sympify(value)*(s.I*s.sqrt(2)*q)**powers[3]
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args();start=time.monotonic()
    base=args.root/'Verification/physics/low-energy-phenomenology/active-gauge'
    source=json.loads((base/'receipt.json').read_text())
    quotient=json.loads((base/'quotient.json').read_text())
    propagation=json.loads((base/'propagation.json').read_text())
    n=s.sympify(source['source_lapse']);q=s.symbols('q',real=True);lam,k=s.symbols('lam k',real=True)
    fields=source['fields'];pairs=list(itertools.combinations_with_replacement(range(4),2))
    coframe={(a,mu):i for i,field in enumerate(fields) if field['group']=='coframe'
        for a,mu in [field['coordinate']]}
    metric=s.MutableSparseMatrix(10,121,{})
    for row,(mu,nu) in enumerate(pairs):
        metric[row,coframe[nu,mu]]+=(-n if nu==0 else 1)
        metric[row,coframe[mu,nu]]+=(-n if mu==0 else 1)
    kept=quotient['retained_original_fields']
    section_metric=metric[:,kept]
    # Original metric variations annihilate all nine actual local symmetry directions.
    symmetry=json.loads((base/'symmetries.json').read_text())
    tangent_terms={}
    for row,col,powers,value in symmetry['source_symmetry_tangents_112']:
        for target in range(10):
            if metric[target,row]:
                key=(target,col,tuple(powers))
                tangent_terms[key]=tangent_terms.get(key,0)+metric[target,row]*s.sympify(value)
    assert all(s.simplify(value)==0 for value in tangent_terms.values())
    K=s.SparseMatrix(103,103,{(i,j):s.sympify(value.replace('lambda','lam'),
        locals={'lam':lam,'k':k}).subs({lam:0,k:s.sqrt(2)*q})
        for i,j,value in quotient['quotient_operator_103_by_103']})
    scaling=s.diag(*[s.sympify(value) for value in propagation['constant_diagonal_field_scaling']])
    normalized=(scaling*K*scaling/n).applyfunc(s.simplify)
    source_rows=[]
    for row in range(10):
        support=[col for col in range(103) if section_metric[row,col]]
        assert len(support)==1
        source_rows.append(support[0])
    unit_green=s.zeros(103,10)
    domain=s.QQ_I.poly_ring(q)
    for block in propagation['blocks']:
        ids=block['quotient_indices']
        selected=[col for col,row in enumerate(source_rows) if row in ids]
        if not selected:continue
        sub=normalized.extract(ids,ids)
        rhs=s.SparseMatrix(len(ids),len(selected),
            {(ids.index(source_rows[col]),j):1 for j,col in enumerate(selected)})
        A=DomainMatrix.from_Matrix(sub).convert_to(domain)
        B=DomainMatrix.from_Matrix(rhs).convert_to(domain)
        numerator,denominator=A.solve_den(B,method='rref')
        assert A*numerator==B*denominator
        solution=(numerator.to_Matrix()/domain.to_sympy(denominator)).applyfunc(s.cancel)
        for row,original in enumerate(ids):
            for j,col in enumerate(selected):unit_green[original,col]=solution[row,j]
        print('source block',len(ids),'with',len(selected),'metric sources solved exactly',flush=True)
    response=s.zeros(103,10)
    for col,index in enumerate(source_rows):
        response[:,col]=scaling*unit_green[:,col]*scaling[index,index]*section_metric[col,index]/n
    response=response.applyfunc(s.cancel)
    assert (K*response-section_metric.T).applyfunc(s.simplify)==s.zeros(103,10)
    full=s.MutableSparseMatrix(289,10,{})
    for row,index in enumerate(kept):full[index,:]=response[row,:]
    for step in reversed(source['algebraic_Schur_steps']):
        for row,col,powers,value in step['write_back_auxiliary_from_retained']:
            if not any(powers[:3]):full[row,:]+=s.sympify(value)*(s.I*s.sqrt(2)*q)**powers[3]*full[col,:]
        for row in step['eliminated_fields']:full[row,:]=full[row,:].applyfunc(s.simplify)
        print('source auxiliary writeback:',','.join(step['eliminated_groups']),flush=True)
    original=decode_static(source['Fourier_Jacobi_entries'],289,q)
    injection=s.MutableSparseMatrix(289,10,{})
    injection[:121,:]=metric.T
    residual=(original*full-injection).applyfunc(s.simplify)
    assert residual==s.zeros(289,10)
    observable=(metric*full[:121,:]).applyfunc(s.cancel)
    assert (observable.subs(q,-q).T-observable).applyfunc(s.cancel)==s.zeros(10)
    regular=[]
    for row in range(10):
        for col in range(10):
            denominator=s.denom(s.cancel(observable[row,col]))
            regular.append(s.simplify(denominator.subs(q,0))!=0)
    infrared=(q*q*observable).applyfunc(lambda value:s.limit(value,q,0))
    static_limit=observable.applyfunc(lambda value:s.limit(value,q,0))
    uv_time=s.limit(q*q*observable[0,0],q,s.oo)
    assert s.simplify(static_limit[0,0]-n**3/3)==0
    assert s.simplify(uv_time-n**3)==0
    # Verify that the actual sourced solution lies in the existing canonical subclass.
    spin_swap=s.kronecker_product(s.Matrix([[0,0,1,0],[0,0,0,1],[1,0,0,0],[0,1,0,0]]),s.eye(3))
    L=s.sqrt(2)*s.diag(spin_swap,-spin_swap)
    primal=[i for i,field in enumerate(fields) if field['group']=='primal_H']
    dual=[i for i,field in enumerate(fields) if field['group']=='dual_H']
    assert (full[dual,:]-L*full[primal,:]).applyfunc(s.simplify)==s.zeros(24,10)
    result={'scope':'ORIGINAL_STATIC_COUPLED_METRIC_LINEAR_RESPONSE',
        'source_convention':'+sum_(mu<=nu) J_munu delta(g_munu), induced field = -H_inverse source',
        'Fourier_convention':'lambda=0, spatial k=(0,0,sqrt(2)*q)',
        'metric_pairs':pairs,'source_lapse':str(n),'metric_variation_map':encode(metric),
        'metric_sources_annihilate_all_nine_symmetries':True,
        'full_289_field_green_columns':encode(full),
        'all_289_equations_with_original_metric_sources':True,
        'metric_inverse_response':encode(observable),'induced_metric_response':encode(-observable),
        'all_metric_entries_regular_at_zero':all(regular),
        'q_squared_metric_response_limit':encode(infrared),
        'metric_zero_limit':encode(static_limit),
        'q_squared_g00_response_ultraviolet_limit':str(uv_time),
        'original_k_squared_g00_response_ultraviolet_limit':str(s.simplify(2*uv_time)),
        'sourced_field_is_canonical':True,
        'Newton_constant_or_empirical_units_identified':False,
        'elapsed_seconds':round(time.monotonic()-start,3)}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print('PASS: all289 equations restore ten original metric sources; prepared relation is preserved',flush=True)
    print('All metric entries regular:',all(regular),'; q² infrared matrix nonzero entries:',len(s.SparseMatrix(infrared).todok()),flush=True)
    print('g00 inverse response:',s.factor(observable[0,0]),flush=True)


if __name__=='__main__':main()
