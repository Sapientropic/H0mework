#!/usr/bin/env python3
"""Source seminorms for every finite clock/energy differential DAG.

The original14 Weyl leaves, scalar clock cone functions and actual finite
canonical Moyal contractions generate the bounds. Neither an unknown
remainder bound nor an operator clock is an input.
"""
from __future__ import annotations
from functools import lru_cache
import hashlib
import json
import math
import time
import sympy as s
from dynamic import HERE, ROOT, ROOT_ID, decode
from source_canonical_star_temporal_reduction import bound
from source_clock_symbol_recursion import (Engine, inspect_and_export, load_dag_asset,
    SourceWeylLeafFactory, c,T,s00,s11,s01,s02,s12,S)
from source_symbol_compact_majorants import Bounds,constant,principal_bounds,determinant_bound
from source_principal_clock_cone import SourcePrincipalClockCone
from source_weyl_leaf_majorants import all_leaf_bounds
from source_symbol_compact_majorants import absolute_ceiling

VARIABLES=(c,T,s00,s11,s01,s02,s12)
LOCALS={str(v):v for v in VARIABLES}


class SourceRationalCoefficientBounds:
    def __init__(self, principal,j):
        self.j=j;self.principal=principal;self.order=principal['C'].order
        self.fields={c:principal['C'],T:principal['T'],**{v:principal['S'] for v in VARIABLES[2:]}}
        self.detQ=s.factor((T*s.eye(3)-S).det())
        self.detQpoly=s.Poly(self.detQ,*VARIABLES)
        self.detQbounds=determinant_bound(principal['Q'],3)
        self.inverse_fields={c:principal['C_inverse'],T:principal['T'].inverse(j),
                             self.detQ:self.detQbounds.inverse(j**3)}
        self.denominator_classes=set();self.coefficient_count=0
    @lru_cache(None)
    def positive_power(self,variable,exponent):return self.fields[variable].power(exponent)
    @lru_cache(None)
    def inverse_power(self,variable,exponent):return self.inverse_fields[variable].power(exponent)
    @lru_cache(None)
    def coefficient(self,text):
        expression=s.sympify(text,locals=LOCALS);num,den=s.fraction(s.cancel(expression))
        polynomial=s.Poly(den,*VARIABLES)
        exponents=[]
        for variable in (c,T):
            axis=VARIABLES.index(variable);power=min(powers[axis] for powers,value in polynomial.terms())
            polynomial=polynomial.exquo(s.Poly(variable**power,*VARIABLES))
            exponents.append(power)
        power=0
        while polynomial.total_degree()>0:
            quotient,remainder=s.div(polynomial,self.detQpoly)
            assert remainder.is_zero,('unpaid source coefficient pole',polynomial.as_expr())
            polynomial=quotient;power+=1
        exponents.append(power)
        assert polynomial.total_degree()==0
        denominator_constant=polynomial.as_expr()
        numerator=s.Poly(num/denominator_constant,*VARIABLES)
        value=constant(0,self.order)
        for powers,coefficient in numerator.terms():
            term=constant(absolute_ceiling(coefficient),self.order)
            for variable,exponent in zip(VARIABLES,powers):
                if exponent:term=term*self.positive_power(variable,exponent)
            value=value+term
        for variable,exponent in zip((c,T,self.detQ),exponents):
            if exponent:value=value*self.inverse_power(variable,exponent)
        self.denominator_classes.add(tuple(exponents));self.coefficient_count+=1
        return value


def source_dag(order):
    assert isinstance(order,int) and order>=1
    saved=bound('source_clock_symbol_recursion')
    if order<=4:
        data=load_dag_asset(saved['differential_DAG'])
    else:
        data=inspect_and_export(Engine(order).generate())
    assert len(data['stages'])>=order
    return data,saved


class SourceClockDAGMajorants:
    """Every input selects finite work; all mathematical leaves remain source-owned."""
    def __init__(self,order,derivative_order):
        assert isinstance(derivative_order,int) and derivative_order>=0
        self.order,self.requested_order=order,derivative_order
        self.dag,self.saved=source_dag(order)
        self.nodes=self.dag['nodes'];self.polys=self.dag['polys']
        self.clock_def={(row['order'],row['axis']):row['expression'] for row in self.dag['clock_def']}
        targets=[row['energy_expr'] for row in self.dag['stages'][:order]]
        targets += [e for row in self.dag['stages'][:order] for e in row['clock_definition_exprs']]
        targets += [self.dag['leading_energy_expr']]
        budget=max(self.derivative_budget(e,derivative_order) for e in targets)
        self.source_derivative_budget=budget
        self.model=SourcePrincipalClockCone();self.factory=SourceWeylLeafFactory();self.j=15
        self.principal=principal_bounds(self.model,self.j,budget)
        self.leaf=all_leaf_bounds(self.factory,self.model,self.j,budget)
        self.scalar=SourceRationalCoefficientBounds(self.principal,self.j)
        self.visited_nodes=set();self.visited_expressions=set();self.moyal_orders=set()
    @lru_cache(None)
    def derivative_budget(self,expr,m):
        budget=m
        for word,coef in self.polys[expr]:
            for atom in word:
                kind,central,key=self.nodes[atom]
                if kind=='moyal':
                    r,a,b=key;budget=max(budget,self.derivative_budget(a,m+r),self.derivative_budget(b,m+r))
                elif kind=='clock':budget=max(budget,self.derivative_budget(self.clock_def[tuple(key)],m))
                else:assert kind=='source'
        return budget
    @lru_cache(None)
    def expression(self,expr,m):
        assert m<=self.source_derivative_budget
        self.visited_expressions.add(expr)
        total=constant(0,m)
        for word,coef in self.polys[expr]:
            item=self.scalar.coefficient(coef).truncate(m)
            for node in word:item=item*self.node(node,m)
            total=total+item
        return total
    @lru_cache(None)
    def node(self,node,m):
        self.visited_nodes.add(node);kind,central,key=self.nodes[node]
        if kind=='source':
            degree,slot=key
            return self.leaf['atoms'][degree][slot].truncate(m)
        if kind=='clock':return self.expression(self.clock_def[tuple(key)],m)
        assert kind=='moyal'
        r,left,right=key;self.moyal_orders.add(r)
        a=self.expression(left,m+r);b=self.expression(right,m+r)
        # Each of200 signed canonical tensor entries contributes a factor1/2;
        # collecting r ordered contractions divides by r!, exactly matching
        # the original finite multiindex differential evaluator.
        return s.Rational(100**r,math.factorial(r))*(a.shift(r,m)*b.shift(r,m))
    def stage(self,k,m):
        assert 1<=k<=self.order and 0<=m<=self.requested_order
        row=self.dag['stages'][k-1]
        assert row['order']==k and row['clock_homogeneous_degrees']==[-k]*4
        clocks=[self.expression(e,m) for e in row['clock_definition_exprs']]
        energy=self.expression(row['energy_expr'],m)
        return {'order':k,'clock_degrees':[-k]*4,'energy_degree':2-k,
            'clock_bounds':clocks,'energy_bounds':energy,
            'clock_expression_ids':row['clock_definition_exprs'],'energy_expression_id':row['energy_expr']}


@lru_cache(None)
def source_clock_bounds(order,derivative_order):
    """Public source-owned producer(k,m), with no supplied target or norm."""
    producer=SourceClockDAGMajorants(order,derivative_order)
    return producer.stage(order,derivative_order)


def actual_source_checks(producer,stages):
    actual=producer.saved['actual_consumers'];p=decode(actual['source_canonical_momentum'])
    norm2=s.factor((p.T*p)[0]);count=0;rows=[]
    for k in (1,2):
        row=stages[k-1]
        clocks=actual['actual_N2_clock_coefficients'][str(k)]
        values=[]
        for axis,image in enumerate(clocks):
            square=s.factor(norm2**k*sum(s.conjugate(s.sympify(v))*s.sympify(v) for word,v in image))
            assert square<=row['clock_bounds'][axis].b[0]**2;count+=1;values.append(str(square))
        image=actual['actual_N2_reduced_energy_coefficients'][str(k)]
        square=s.factor(norm2**(k-2)*sum(s.conjugate(s.sympify(v))*s.sympify(v) for word,v in image))
        assert square<=row['energy_bounds'].b[0]**2;count+=1
        rows.append({'order':k,'actual_unit_ray_four_clock_column_norms_squared':values,
                     'actual_unit_ray_energy_column_norm_squared':str(square)})
    return {'all10_original_first_two_order_columns_bounded':count,'normalized_source_momentum_norm_squared':str(norm2),
        'actual_readback':rows,'source_H0_and_original_Y_both_retained':True}


def main():
    started=time.monotonic()
    names=('source_symbol_compact_majorants','independent_source_symbol_compact_majorants',
        'source_weyl_leaf_majorants','source_clock_symbol_recursion','independent_source_clock_symbol_recursion')
    for name in names:bound(name)
    producer=SourceClockDAGMajorants(4,4)
    stages=[]
    for k in range(1,5):
        row=producer.stage(k,4);stages.append(row)
        print('PASS exact source clock/energy DAG bounds at order',k,'through all200 phase derivative order4',flush=True)
    actual=actual_source_checks(producer,stages)
    print('PASS original fullCAR first/second-order clock and energy readback under the generated unit-ray bounds',flush=True)
    files=[HERE/(name+'.json') for name in names]+[HERE/name for name in (
        'source_clock_dag_majorants.py','source_weyl_leaf_majorants.py','source_symbol_compact_majorants.py',
        'source_clock_symbol_recursion.py','source_clock_symbol_recursion.dag.json.gz')]
    out={'root':ROOT_ID,'scope':'SOURCE_GENERATED_ALL_FINITE_ORDER_CANONICAL_CLOCK_AND_ENERGY_DIFFERENTIAL_DAG_SEMINORMS',
        'source_sha256':producer.model.native.graph.common.source_hashes,
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'source_domain':'The same source K15 annulus and its generated inner/outer boxes; no pointwise-only norm or momentum truncation is substituted.',
        'public_API':'source_clock_bounds(k,m), or SourceClockDAGMajorants(k,m).stage(j,n) for j<=k,n<=m; both build the actual source leaves and finite canonical differential graph without norm/jet inputs.',
        'derivative_budget':producer.source_derivative_budget,
        'source_rational_poles':{'allowed':['c','T','det(T I-S)'],
            'guards':'c>0 with inverse bound generated from2 A c^2=T; T>=1/15; Q=T I-S>=I/15 gives detQ>=15^-3. Inverse derivatives are generated by differentiating D U=1.',
            'encountered_powers':sorted(map(list,producer.scalar.denominator_classes)),
            'distinct_coefficients_bounded':producer.scalar.coefficient_count},
        'canonical_Moyal_bound':'For every ordered derivative of length m, ||partial^m B_r(f,g)|| <=100^r/r! sum_{a=0}^m binom(m,a) f_(r+a) g_(r+m-a). This is the exact200-entry canonical tensor with(i/2)^r and r!, followed by the triangle inequality.',
        'ordered_noncommutative_products_preserved':True,
        'finite_stages':[{'order':row['order'],'clock_degrees':row['clock_degrees'],'energy_degree':row['energy_degree'],
            'clock_expression_ids':row['clock_expression_ids'],'energy_expression_id':row['energy_expression_id'],
            'clock_derivative_bounds':[b.encode() for b in row['clock_bounds']],
            'energy_derivative_bounds':row['energy_bounds'].encode()} for row in stages],
        'visited_DAG_nodes':len(producer.visited_nodes),'visited_DAG_expressions':len(producer.visited_expressions),
        'actual_Moyal_orders':sorted(producer.moyal_orders),'actual_source_consumer':actual,
        'uniform_finite_algorithm':'The independently signed source recursion supplies a finite acyclic expression at every k. Induction over each ordered product, rational coefficient, earlier clock and finite Moyal node produces all requested finite derivatives. The demand traversal computes the finite higher source derivative budget before constructing the leaf bounds. The four executed orders are consumers of this algorithm, not a finite substitute for its arbitrary-k induction.',
        'cutoff_parameter_source':'All R_k inputs can now be produced by this API on the same explicit source domain: take maxima of the generated C_-k and E_(2-k) derivative bounds through k and combine with the already generated radial cutoff derivative constants. No radius is inferred from an unspecified supremum.',
        'Borel_symbol_or_exact_operator_clock_claimed':False,
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'source_clock_dag_majorants.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('PASS source clock differential DAG majorants',out['elapsed_seconds'],'seconds',flush=True)

if __name__=='__main__':main()
