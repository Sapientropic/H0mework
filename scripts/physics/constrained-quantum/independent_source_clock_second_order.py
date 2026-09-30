#!/usr/bin/env python3
"""Independent full N2 second clock and reduced-energy symbol audit.

Original scalar/gauge implicit Weyl coefficients and exterior-slot normal
CAR rebuild every zeroth-order term. One nested-Jordan Taylor evaluator is
used for both original forces and energy. The paid full200-phase jets feed a
literal canonical contraction and two successive Sylvester inverse equations.
"""
from __future__ import annotations

from functools import lru_cache
from itertools import product,combinations
from math import factorial
import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_principal_clock_cone import (
    RawGaussSection,RawLiveCoefficients,HERE,ROOT,ROOT_ID,bindings,source_factors,
    cotangent_values,rational,eq,decode,encode,zero)
from independent_source_scalar_weyl_symbol import original_slice_coefficients
from independent_source_common_weyl_symbol import implicit_gauge_symbol
from independent_source_common_hamiltonian import original_inventory,raw_matter
from independent_source_full_quantum_adjoint import sparse,dual_pair
from independent_source_gauss_quantum_current import apply_state,add_terms,distinct_slot_product,decoded_state
from independent_source_coframe_live_ordering import state_encode
from independent_source_quantum_grade_structure import grade_predicate,grade_state
from independent_source_gauge_legendre import source
from independent_source_clock_subprincipal import pair,compare_pair,apply_pair


def normalize(state):return {w:s.factor(s.cancel(v)) for w,v in state.items() if s.cancel(v)!=0}
def total(*states):return normalize(add_terms((1,state) for state in states))
def scale(c,state):return normalize({w:c*v for w,v in state.items()})
def same(a,b):assert not total(a,scale(-1,b))
def at_state(state,point):return normalize({w:v.subs(point) for w,v in state.items()})


def read_jet(record):
    return (s.sympify(record['value']),decode(record['gradient200']),decode(record['Hessian200']))


def quotient(numerator,denominator):
    a,g,H=numerator;b,h,K=denominator
    value=s.factor(a/b);gradient=rational((g-value*h)/b)
    Hessian=rational((H-value*K-h*gradient.T-gradient*h.T)/b)
    eq(Hessian,Hessian.T)
    return value,gradient,Hessian


def canonical_second(a,b):
    A=a[2];B=b[2];assert A.shape==B.shape==(200,200)
    def symplectic_index(i):return (i+100,1) if i<100 else (i-100,-1)
    out=0
    for (i,j),v in A.todok().items():
        k,sgn=symplectic_index(i);l,sign=symplectic_index(j)
        out+=sgn*sign*v*B[k,l]
    return s.factor(out)


def geometric_terms(principal,independent,candidate):
    A,T,C=[read_jet(principal[key]) for key in ('a0_2','traceS2','principal_clock')]
    first=quotient(T,C);second=quotient(first,C)
    # J_C(U)=C U-P2(C,U)/8. Solve the two successive inverse
    # equations, keeping the first inverse's correction in the second.
    correction1=canonical_second(C,first)/(8*C[0])
    correction2=(correction1+canonical_second(C,second)/8)/C[0]
    force=s.factor(correction2/2)
    energy=s.factor(-canonical_second(C,A)/8+correction1/2)
    zero(force-s.sympify(independent['original_lapse_force_second_Moyal']))
    zero(force-s.sympify(candidate['actual_scalar_Moyal_force']))
    zero(energy-s.sympify(candidate['actual_scalar_Moyal_energy']))
    assert force!=0 and energy!=0 and force!=energy
    assert principal['all_shift_pure_geometric_force_terms_zero']
    return force,energy,{'all200_canonical_entries_contracted':True,
        'first_Jordan_inverse_correction':str(s.factor(correction1)),
        'second_Jordan_inverse_correction':str(s.factor(correction2)),
        'original_force_Moyal_term':str(force),'original_energy_Moyal_term':str(energy),
        'force_and_energy_derived_by_distinct_original_graph_equations':True}


def coframe_zero_coefficients(raw,number):
    q=raw.q;volume=q[0]*q[2]*q[5];K=raw.K
    loggrad=s.Matrix([s.diff(volume,x)/volume for x in q]);D=rational(s.I*raw.drift.T)
    drift_current=rational(K*loggrad)
    alpha=s.Rational(number+2,2)
    # Differentiate the actual inverse half density, then convert the
    # principal divergence operator to its canonical Weyl symbol.
    delta=s.cancel(alpha*((D+number*drift_current).T*loggrad)[0]-
        alpha**2*(loggrad.T*K*loggrad)[0]+
        alpha*sum(K[i,j]*s.diff(loggrad[i],q[j]) for i in range(6) for j in range(6)))
    quarter=s.cancel(sum(s.diff(K[i,j],q[i],q[j]) for i in range(6) for j in range(6))/4)
    zero(quarter+raw.N/(4*volume))
    return s.cancel(delta+quarter)


def original_context(candidate,principal,sub):
    section,raw=RawGaussSection(),RawLiveCoefficients();assert section.native.hashes==candidate['source_sha256']
    f=source_factors(section,raw,principal['original_source_factors'])
    p=decode(principal['actual_source_cotangent_witness']['canonical_p100'])
    eq(p,decode(sub['actual_canonical_covector']))
    ys=(s.Symbol('quantum_n',positive=True),*s.symbols('quantum_b1:4',real=True));n=ys[0]
    base=dict(zip(ys,(raw.N,0,0,0)));e=raw.at(raw.e,f['q']);e[:,0]=s.Matrix(ys)
    scalar=original_slice_coefficients(section,e,f['x'],f['A'],f['point'])
    gauge=implicit_gauge_symbol(section,f['point'],e);Q=section.native.Qb+section.native.Qs
    pr=p[6:,:]
    H1=(pr.T*scalar['identity']).row_join(pr.T*scalar['mixed'])
    H1+=(pr.T*gauge['momentum_identity']).row_join(s.zeros(1,9)).row_join(pr.T*gauge['momentum_current'])
    H1=rational(H1);total1=pair(list(H1),Q)
    compare_pair(total1,{'identity':sub['original_H1_identity'],'current504':sub['original_H1_current504']},ys)
    _,_,_,S,a,T=cotangent_values(section,raw,f,p);b=s.Matrix(ys[1:])
    H2=n*a+(n*n*T-(b.T*S*b)[0])/(2*n*(n*n-(b.T*b)[0]))
    F2=-s.Matrix([s.diff(H2,y) for y in ys]);eq(rational(F2.subs(base)),s.zeros(4,1))
    J=rational(F2.jacobian(s.Matrix(ys)).subs(base));eq(J,decode(sub['actual_force_Jacobian']))
    clock=[]
    for row in sub['four_clock_order_minus1_symbols']:
        clock.append((s.sympify(row['identity']),decode(row['current504'])))
    F1=[pair(list(-H1.diff(y).subs(base)),Q) for y in ys]
    for j in range(4):
        combined=pair(list(-H1.diff(ys[j]).subs(base)),Q)
        zero(combined[0]+sum(J[j,k]*clock[k][0] for k in range(4)))
        eq(combined[1]+sum((J[j,k]*clock[k][1] for k in range(4)),s.zeros(504)),s.zeros(504))
    cf=raw.coefficients(f['q']);spin=[sparse(s.kronecker_product(M,s.eye(63))) for M in cf['J']]
    cf_one=sparse(s.kronecker_product(cf['one_body']+cf['correction'],s.eye(63)))
    eq(cf_one.H,cf_one)
    pair_tensor=rational(sum((v*s.kronecker_product(cf['J'][i],cf['J'][j]) for (i,j),v in cf['W'].todok().items()),s.zeros(64)))
    eq(pair_tensor.H,pair_tensor)
    qpoint=dict(zip(raw.q,f['q']));correction=s.factor(coframe_zero_coefficients(raw,2).subs(qpoint))
    for block in (scalar,gauge):
        matrix=block['square'] if block is scalar else block['square_current']
        eq(matrix.H,matrix);eq(matrix.conjugate(),matrix)
    connection=s.zeros(4,12);connection[1:,:]=f['A']
    matter=raw_matter(e,scalar['ambient']['phi'],connection)
    M=dual_pair(rational(-s.I*matter['E_inverse']*matter['lower']))
    Y=dual_pair(rational(-s.I*matter['volume']*matter['E_inverse']*matter['Y']))
    M0=sparse(M-Y);eq(M0.H,M0)
    return locals()


def source_zero_actions(c,state):
    raw,ys,Q,cf=[c[key] for key in ('raw','ys','Q','cf')]
    assert all(len(word)==2 for word in state)
    normal=[]
    for word,value in state.items():
        for (i,j),weight in cf['W'].todok().items():
            normal.append((value*weight,distinct_slot_product(c['spin'][i],c['spin'][j],word)))
    coframe=scale(ys[0]/raw.N,total(normalize(add_terms(normal)),apply_state(c['cf_one'],state),
        scale(c['correction']+cf['constant'],state)))
    def polynomial(block,charges):
        if 'ambient' in block:
            scalar=block['constant']+block['potential']+block['second']/4
            linear=block['linear'];quadratic=block['square']
        else:
            scalar=block['classical_zero']+block['half_density_potential']+block['weyl_correction']
            linear=block['linear_current'];quadratic=block['square_current']
        output=[scale(scalar,state)];first=[apply_state(q,state) for q in charges]
        output.extend(scale(v,first[j]) for j,v in enumerate(linear) if v)
        output.extend(scale(v,apply_state(charges[i],first[j])) for (i,j),v in quadratic.todok().items())
        return total(*output)
    return {'coframe':coframe,'scalar_form':polynomial(c['scalar'],Q),
        'gauge':polynomial(c['gauge'],Q[9:]),
        'matter_noY':normalize(apply_state(c['M0'],state)),
        'original_Y':normalize(apply_state(c['Y'],state))}


def jordan(left,right):
    return lambda state:scale(s.Rational(1,2),total(left(right(state)),right(left(state))))


def taylor_readback(clock,derivative,order,state):
    output=[]
    for indices in product(range(4),repeat=order):
        operation=derivative(indices)
        for index in reversed(indices):
            def left(state,index=index):return apply_pair(clock[index],state)
            operation=jordan(left,operation)
        output.append(operation(state))
    return scale(s.Rational(1,factorial(order)),total(*output))


def solve_four(J,residual):
    words=sorted(set().union(*(set(state) for state in residual)))
    rhs=s.Matrix([[row.get(word,0) for word in words] for row in residual])
    solution,params=J.gauss_jordan_solve(-rhs);assert params.rows==0
    eq(rational(J*solution+rhs),s.zeros(4,len(words)))
    return [normalize(dict(zip(words,solution[i,:]))) for i in range(4)]


def original_Jordan_levels(c,state,geo_force,geo_energy):
    ys,base,H1,H2,J,clock,Q=[c[key] for key in ('ys','base','H1','H2','J','clock','Q')]
    components=source_zero_actions(c,state);Hzero=total(*components.values());grade0=total(*(v for key,v in components.items() if key!='original_Y'))
    force0=[at_state({w:-s.diff(v,y) for w,v in Hzero.items()},base) for y in ys]
    force0g=[at_state({w:-s.diff(v,y) for w,v in grade0.items()},base) for y in ys]
    def derivative1(initial,indices):
        row=initial
        for index in indices:row=row.diff(ys[index])
        value=pair(list(row.subs(base)),Q)
        return lambda state:apply_pair(value,state)
    def derivative2(initial,indices):
        value=initial
        for index in indices:value=s.diff(value,ys[index])
        coefficient=s.factor(value.subs(base))
        return lambda state:scale(coefficient,state)
    crossed=[];quadratic=[]
    for a,y in enumerate(ys):
        crossed.append(taylor_readback(clock,lambda indices:derivative1(-H1.diff(y),indices),1,state))
        quadratic.append(taylor_readback(clock,lambda indices:derivative2(-s.diff(H2,y),indices),2,state))
    residual=[total(force0[a],crossed[a],quadratic[a],scale(geo_force,state) if a==0 else {}) for a in range(4)]
    residualg=[total(force0g[a],crossed[a],quadratic[a],scale(geo_force,state) if a==0 else {}) for a in range(4)]
    C2=solve_four(J,residual);C2g=solve_four(J,residualg)
    H0point=at_state(Hzero,base)
    cross_energy=taylor_readback(clock,lambda indices:derivative1(H1,indices),1,state)
    quadratic_energy=taylor_readback(clock,lambda indices:derivative2(H2,indices),2,state)
    E0=total(H0point,cross_energy,quadratic_energy,scale(geo_energy,state))
    for y in ys:zero(s.diff(H2,y).subs(base))
    Yvalue=at_state(components['original_Y'],base)
    coefficient=s.factor(1/(J[0,0]*c['raw'].N));assert coefficient==-s.Rational(324,625)
    for a in range(4):same(total(C2[a],scale(-1,C2g[a])),scale(coefficient,Yvalue) if a==0 else {})
    missing=solve_four(J,[total(force0[a],crossed[a],quadratic[a]) for a in range(4)])
    defect=total(C2[0],scale(-1,missing[0]));assert defect
    return locals()


def compare_actual(computed,saved):
    for key,target in [('force0','four_original_force_order0'),('crossed','four_subprincipal_Jordan_terms'),
        ('quadratic','four_principal_quadratic_clock_terms'),('C2','four_clock_order_minus2'),('C2g','four_grade0_clock_order_minus2')]:
        for actual,expected in zip(computed[key],saved[target]):same(actual,decoded_state(expected))
    for key,image in computed['components'].items():same(at_state(image,computed['base']),decoded_state(saved['original_zero_order_Weyl_components'][key]))
    same(computed['E0'],decoded_state(saved['first_reduced_energy_order0']))
    same(computed['defect'],decoded_state(saved['omitting_Moyal_clock_defect']))
    pieces=saved['first_reduced_energy_components']
    for key,target in [('H0point','original_Weyl_H0_plus_Y'),('cross_energy','Jordan_clock_H1'),('quadratic_energy','principal_clock_quadratic')]:same(computed[key],decoded_state(pieces[target]))
    same(scale(computed['geo_energy'],computed['state']),decoded_state(pieces['canonical_Moyal']))
    same(scale(computed['coefficient'],computed['Yvalue']),decoded_state(saved['full_Y_clock_order_minus2']))


def main():
    started=time.monotonic();path=HERE/'source_clock_second_order.json';candidate=json.loads(path.read_text())
    count=bindings(candidate);assert candidate['root']==ROOT_ID
    paid=('source_principal_clock_cone','independent_source_principal_clock_cone',
        'source_clock_subprincipal','independent_source_clock_subprincipal',
        'source_clock_principal_jets','independent_source_clock_principal_jets',
        'independent_source_coframe_weyl_symbol','independent_source_scalar_weyl_symbol','independent_source_common_weyl_symbol')
    records={name:json.loads((HERE/(name+'.json')).read_text()) for name in paid}
    for receipt in records.values():count+=bindings(receipt);assert receipt['root']==ROOT_ID
    c=original_context(candidate,records['source_principal_clock_cone'],records['source_clock_subprincipal'])
    geo_force,geo_energy,geometry=geometric_terms(records['source_clock_principal_jets']['actual_consumer'],
        records['independent_source_clock_principal_jets'],candidate['actual_consumer'])
    state={(144,396):s.S.One};result=original_Jordan_levels(c,state,geo_force,geo_energy)
    compare_actual(result,candidate['actual_consumer'])
    _,_,degrees,hashes=source.parse_source(ROOT);assert hashes==candidate['source_sha256']
    labels=[(d,w) for d in degrees for w in combinations(range(7),d)]
    weights=[int(d==6) for _ in range(8) for d,_ in labels]
    for image in result['C2g']:grade_state(image,weights,2,0)
    for full,diagonal in zip(result['C2'],result['C2g']):grade_state(total(full,scale(-1,diagonal)),weights,2,1)
    grade_predicate(c['M0'],weights,0);grade_predicate(c['Y'],weights,1)
    assert result['Yvalue'] and total(result['Yvalue'],scale(-1,apply_state(c['Y'].H.subs(c['base']),state)))
    print('PASS independent original normal CAR/coframe and complete94 scalar/BF Weyl degree0, matter and unchangedY',flush=True)
    print('PASS all4 nested-Jordan C_minus2 equations, independent full200 Moyal force/energy, N2 grade split and reduced E0',flush=True)
    files=[Path(__file__),path,HERE/'source_clock_second_order.py']+[HERE/name for name in (
        'independent_source_principal_clock_cone.py','independent_source_scalar_weyl_symbol.py',
        'independent_source_common_weyl_symbol.py','independent_source_clock_subprincipal.py',
        'independent_source_gauss_quantum_current.py','independent_source_coframe_live_ordering.py')]+[HERE/(name+'.json') for name in paid]
    output={'verdict':'CERTIFIED_ORIGINAL_FULL_N2_SECOND_CANONICAL_CLOCK_AND_REDUCED_ENERGY_COEFFICIENT',
        'root':ROOT_ID,'source_sha256':candidate['source_sha256'],
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'source_binding_checks':count,'candidate_constructor_imported':False,
        'independent_method':'Original implicit12/94 Weyl zero-order symbols, inverse-half-density differentiation, exterior-slot distinct-particle normal product; one nested-Jordan Taylor evaluator for original forces and energy; direct4-row linear solve; paid full200 canonical jets and two successive Sylvester inverse equations.',
        'actual_original_zero_order_components':{key:state_encode(at_state(image,c['base'])) for key,image in result['components'].items()},
        'canonical_second_Moyal':geometry,'four_clock_order_minus2':[state_encode(image) for image in result['C2']],
        'four_grade0_clock_order_minus2':[state_encode(image) for image in result['C2g']],
        'all_four_corrected_original_force_order0_residuals_zero':True,
        'full_original_Y_clock_coefficient':str(result['coefficient']),
        'Y_clock_order_minus2':state_encode(scale(result['coefficient'],result['Yvalue'])),
        'omitted_scalar_Moyal_clock_defect':state_encode(result['defect']),
        'first_reduced_energy_order0':state_encode(result['E0']),
        'actual_source_stationarity_removes_C_minus2_from_E0':True,
        'original_Y_not_Hermitianized':True,
        'scope':'Actual source canonical100 point and complete original N2 CAR fibre symbol coefficients through C_minus2 and E0; full504 charges and normal pair actions are retained. No summed clock operator, Hilbert evolution, spectral measure or proton identification is asserted.',
        'complete_quantum_clock_operator_or_spectrum_generated':False,
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'independent_source_clock_second_order.json').write_text(json.dumps(output,separators=(',',':'))+'\n')
    print('PASS independent source clock second canonical order',output['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
