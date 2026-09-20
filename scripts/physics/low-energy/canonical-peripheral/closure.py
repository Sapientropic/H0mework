#!/usr/bin/env python3
"""Maximal invariant canonical Fourier fibres from actual constraint derivatives.

Smith forms classify every real axial momentum at which the finite derivative
rank can drop. Each resulting fibre is then checked for actual generator
invariance, so a pointwise kernel is never reported as a propagated space.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix
from sympy.polys.matrices.normalforms import smith_normal_form


def clean(matrix): return s.SparseMatrix(matrix).applyfunc(s.cancel)


def decode(value,q):
    return s.SparseMatrix(*value['shape'],{(row,col):s.sympify(text,locals={'q':q})
        for row,col,text in value['entries']})


def encode(matrix):
    return {'shape':list(matrix.shape),'entries':[[int(i),int(j),str(s.factor(value))]
        for (i,j),value in s.SparseMatrix(matrix).todok().items()]}


def basis_and_flow(observability,generator):
    columns=observability.nullspace()
    basis=s.Matrix.hstack(*columns) if columns else s.zeros(generator.rows,0)
    if basis.cols:
        left=(basis.H*basis).inv(method='DM')*basis.H
        flow=clean(left*generator*basis)
    else: flow=s.zeros(0)
    assert clean(observability*basis)==s.zeros(observability.rows,basis.cols)
    assert clean(generator*basis-basis*flow)==s.zeros(generator.rows,basis.cols)
    return clean(basis),flow


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--generator',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args(); started=time.monotonic()
    source=json.loads(args.generator.read_text()); q=s.symbols('q',real=True)
    A=decode(source['interacting_first_order_generator'],q)
    B=decode(source['prepared_generator'],q)
    E=decode(source['first_preparation_derivative_constraint'],q)
    C=decode(source['canonical_embedding'],q); D=decode(source['canonical_constraint'],q)
    raw={key:decode(value,q) for key,value in source['original_normalized_Euler_readback'].items()
         if isinstance(value,dict)}
    polynomial=s.QQ_I.poly_ring(q); rational=s.QQ_I.frac_field(q)
    completed=[]; exceptions=set()
    for number,indices in enumerate(source['prepared_coefficient_blocks']):
        n=len(indices); generator=B[indices,indices]
        rows=[row for row in range(E.rows) if any(E[row,col]!=0 for col in indices)]
        seed=E[rows,indices]
        observability=seed; power=seed; ranks=[]; last=-1
        for derivative in range(n+1):
            rank=DomainMatrix.from_Matrix(observability).convert_to(rational).rank() if observability.rows else 0
            ranks.append(rank)
            if rank==n or rank==last: break
            last=rank;power=clean(power*generator);observability=observability.col_join(power)
        generic_basis,generic_flow=basis_and_flow(observability,generator)
        if observability.rows:
            smith=smith_normal_form(DomainMatrix.from_Matrix(observability).convert_to(polynomial)).to_Matrix()
            factors=[s.Poly(smith[i,i],q,domain=s.QQ_I).monic().as_expr()
                     for i in range(min(smith.shape)) if smith[i,i]!=0]
        else: factors=[]
        roots=set()
        for factor in factors:
            exact_roots=s.roots(factor,q)
            assert sum(exact_roots.values())==s.degree(factor,q)
            for root in exact_roots:
                assert root.is_real is not None
                if root.is_real:
                    assert root.is_Rational
                    roots.add(root); exceptions.add(root)
        assert len(factors)==n-generic_basis.cols
        completed.append({'indices':indices,'generator':generator,'seed':seed,
            'observability':observability,'generic_ranks':ranks,'smith':factors,
            'generic_basis':generic_basis,'generic_flow':generic_flow,'exceptions':roots})
        print('PASS block',number,'size',n,'derivative ranks',ranks,
              'generic invariant',generic_basis.cols,'real exceptions',sorted(roots),flush=True)
    print('Complete real axial exceptional set:',sorted(exceptions),flush=True)
    # Classify every exceptional fibre, plus the generic rational-function fibre.
    strata=[]
    for value in [None]+sorted(exceptions):
        global_basis=s.zeros(84,0); flows=[]
        for block in completed:
            indices=block['indices']
            if value is None:
                basis,flow=block['generic_basis'],block['generic_flow']
            else:
                basis,flow=basis_and_flow(block['observability'].subs(q,value),block['generator'].subs(q,value))
                rank_from_smith=sum(factor.subs(q,value)!=0 for factor in block['smith'])
                assert basis.cols==len(indices)-rank_from_smith
            embedded=s.zeros(84,basis.cols)
            for row,original in enumerate(indices): embedded[original,:]=basis[row,:]
            global_basis=global_basis.row_join(embedded); flows.append(flow)
        flow=s.diag(*flows)
        if value is None:
            assert not any(coefficient.has(q) for coefficient in global_basis)
        point_A=A if value is None else A.subs(q,value)
        written=clean(C*global_basis)
        assert clean(point_A*written-written*flow)==s.zeros(132,written.cols)
        assert D*written==s.zeros(48,written.cols)
        assert written.rank()==written.cols
        point_raw=raw if value is None else {key:matrix.subs(q,value) for key,matrix in raw.items()}
        scalar,wvelocity,primal,dual=written[:18,:],written[18:36,:],written[36:84,:],written[84:,:]
        assert clean(scalar*flow-wvelocity)==s.zeros(18,written.cols)
        assert clean(point_raw['primal_time_frame']*primal*flow+point_raw['primal_value']*primal+
                     point_raw['primal_scalar']*scalar)==s.zeros(504,written.cols)
        assert clean(point_raw['dual_time_frame']*dual*flow+point_raw['dual_value']*dual)==s.zeros(504,written.cols)
        assert clean(point_raw['scalar_frame']*scalar*flow**2+
                     point_raw['scalar_kinetic']*point_raw['scalar_frame']*scalar+
                     point_raw['scalar_dual_force']*dual)==s.zeros(70,written.cols)
        X=s.symbols('X')
        characteristic=s.factor(flow.charpoly(X).as_expr())
        strata.append({'momentum_q':'generic' if value is None else str(value),
            'interacting_canonical_dimension':written.cols,
            'total_peripheral_canonical_fourier_dimension':518+written.cols,
            'prepared_basis':encode(global_basis),'full_132_field_basis':encode(written),
            'restricted_time_generator':encode(flow),'time_characteristic_polynomial':str(characteristic),
            'scalar_projection_rank':scalar.rank(),
            'scalar_velocity_projection_rank':wvelocity.rank(),
            'primal_projection_rank':primal.rank(),
            'dual_projection_rank':dual.rank(),
            'source_scalar_to_matter_mixing_rank':(point_raw['primal_scalar']*scalar).rank(),
            'whole_source_generator_intertwining':True,'canonical_constraint_zero':True,
            'original_unprojected_scalar_primal_and_dual_rows_zero':True,
            'maximality_from_exact_observability_rank':True})
        print('PASS full propagated fibre',strata[-1]['momentum_q'],'mixed dimension',written.cols,
              'total',518+written.cols,'characteristic',characteristic,flush=True)
    initial=s.zeros(84,1);initial[18,0]=1
    original_initial=C*initial;origin=A.subs(q,0)
    assert D*original_initial==s.zeros(48,1)
    assert D*origin*original_initial==s.zeros(48,1)
    second=clean(D*origin**2*original_initial)
    assert second!=s.zeros(48,1)
    result={'scope':'MAXIMAL_SOURCE_CANONICAL_PERIPHERAL_INVARIANT_AXIAL_FIBRES',
        'normalization':source['normalization'],
        'dimension_field':'complexification of the original real Fourier carrier; q=0 also gives real homogeneous Cauchy dimension',
        'free_scalar_Cauchy_dimension':86,'free_prepared_matter_dimension':432,
        'source_first_order_peripheral_dimension':1082,'interacting_unrestricted_dimension':132,
        'canonical_graph_candidate_dimension':84,
        'exact_real_exceptional_momenta_q':[str(value) for value in sorted(exceptions)],
        'source_physical_squared_momentum_exceptions':[str(2*value*value) for value in sorted(exceptions)],
        'source_generator_coefficient_blocks':[{
            'indices':block['indices'],'constraint_derivative_ranks':list(map(int,block['generic_ranks'])),
            'finite_observability_matrix':encode(block['observability']),
            'nonzero_smith_invariant_factors':[str(factor) for factor in block['smith']],
            'generic_invariant_basis':encode(block['generic_basis']),
            'generic_restricted_generator':encode(block['generic_flow'])} for block in completed],
        'strata':strata,'generic_fibre_means':'all real q outside exactly the displayed finite exceptional set',
        'generic_invariant_basis_is_constant':True,
        'instantaneous_first_compatibility_dimension':84-E.rank(),
        'instantaneous_kernel_nonpropagation_witness':{
            'momentum_q':'0','first_order_original_field_initial':encode(original_initial),
            'canonical_constraint_zero':True,'first_time_constraint_derivative_zero':True,
            'nonzero_second_time_constraint_derivative':encode(second)},
        'all_three_spatial_directions_classified':False,
        'instantaneous_kernel_replaced_by_generator_invariant_space':True,
        'elapsed_seconds':round(time.monotonic()-started,3)}
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')


if __name__=='__main__':main()
