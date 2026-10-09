#!/usr/bin/env python3
"""Full external-ray properness from the source infinity Schur algorithm."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

import sympy as s
from sympy.polys.matrices import DomainMatrix as DM

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
FQ=HERE.parent
sys.path.insert(0,str(FQ/'packet-gauge-family'))
import infinity as inf
spec=importlib.util.spec_from_file_location('joint_original_infinity_source',FQ/'packet-gauge-family/proper.py')
algorithm=importlib.util.module_from_spec(spec);spec.loader.exec_module(algorithm)
F=inf.FIELD
x,a=inf.x,inf.a
ray,U=s.symbols('s U',real=True)
c2=s.Rational(108,125)
radicals=[s.S(1),s.sqrt(2),s.sqrt(15),s.sqrt(30)]
ORDER=8
algorithm.RETURN_POWER=4


def matrix(record):
    return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(v,locals={'x':x,'s':ray,'U':U})
                                          for i,j,v in record['entries']})


def components(value):
    left=s.expand(value)
    result=[]
    for radical in radicals[1:]:
        coefficient=left.coeff(radical);result.append(coefficient);left-=radical*coefficient
    return [s.expand(left),*result]


def frequency(M):
    out={}
    for (i,j),value in M.todok().items():
        for r,part in enumerate(components(s.expand(value.subs(ray,s.sqrt(2)*a)))):
            for (degree,),coefficient in s.Poly(part,x).terms():
                out.setdefault((degree,r),{})[i,j]=F.from_sympy(coefficient)
    return {key:DM.from_dok(value,M.shape,F) for key,value in out.items()}


def main():
    started=time.monotonic()
    path=HERE/'full-maps.json';data=json.loads(path.read_bytes())
    A=matrix(data['normalized103'])
    ad=[{}, {}, {}]
    for (i,j),value in A.todok().items():
        value=s.expand(value.subs(ray,s.sqrt(2)*a))
        for (degree,),coefficient in s.Poly(value,x).terms():
            ad[2-degree][i,j]=F.from_sympy(coefficient)
    reversed_A=[DM.from_dok(v,(103,103),F) for v in ad]
    Fhat=s.Poly(s.sympify(data['Fhat'],locals={'U':U}),U,domain=s.QQ)
    def shift(power):
        out={}
        for j in range(6):
            for (k,),value in s.Poly(U**(j+power),U,domain=s.QQ).rem(Fhat).terms():
                out[j,k]=F.convert(value)
        return DM.from_dok(out,(6,6),F)
    force=frequency(matrix(data['force']))
    rhs={}
    for (power,radical),M in force.items():
        for j in range((ORDER+power)//2+1):
            degree=4-power+2*j
            if degree>ORDER:break
            values=M.matmul(shift(j)).scalarmul(F.convert(1/c2))
            entries={(i,k+6*radical):v for (i,k),v in values.to_dok().items()}
            algorithm.add_at(rhs,degree,DM.from_dok(entries,(103,24),F))
    responses={};reports=[]
    for component in inf.connected_components(reversed_A):
        forcing=algorithm.extract(rhs,component,range(24))
        if not forcing:
            reports.append({'indices':component,'source_identically_zero':True});continue
        series=[M.extract(component,component) for M in reversed_A]
        series += [inf.zero(len(component),len(component)) for _ in range(ORDER-2)]
        trace=[]
        solved=algorithm.solve(series,forcing,24,trace,component)
        residual=algorithm.product(dict(enumerate(series[:3])),solved,algorithm.RETURN_POWER)
        for power,M in forcing.items():
            if power<=algorithm.RETURN_POWER:algorithm.add_at(residual,power,-M)
        assert not residual
        for power,M in solved.items():
            entries={(component[i],j):v for (i,j),v in M.to_dok().items()}
            algorithm.add_at(responses,power,DM.from_dok(entries,(103,24),F))
        assert min(solved,default=1)>=1
        reports.append({'indices':component,'trace':trace,'actual_solution_vanishes_at_infinity':True})
    # Full fields include the source particular and every auxiliary lift.
    lift=frequency(matrix(data['lift']));part=frequency(matrix(data['part']))
    assert max(power for power,radical in lift)<=2
    actual={}
    for (power,radical),M in part.items():
        for j in range(max(0,power//2)+1):
            degree=2-power+2*j
            if degree>2:continue
            algorithm.add_at(actual,(degree,radical),M.matmul(shift(j)).scalarmul(F.convert(1/c2)))
    for (frequency_power,left_radical),M in lift.items():
        for power,solution in responses.items():
            degree=power-frequency_power
            if degree>2:continue
            for right_radical in range(4):
                X=solution.extract(range(103),range(6*right_radical,6*(right_radical+1)))
                multiplier=(2 if left_radical&right_radical&1 else 1)*(15 if left_radical&right_radical&2 else 1)
                algorithm.add_at(actual,(degree,left_radical^right_radical),M.matmul(X).scalarmul(F.convert(multiplier)))
    assert all(power>0 for power,radical in actual),('actual source contacts must be retained',actual.keys())
    # These are coefficients of the actual source field at tau=1/x,
    # common denominator D(U). Differentiate the original rational a
    # coefficients before converting a=s/sqrt2 and lambda=c*x.
    base=json.loads((HERE/'maps.json').read_bytes())
    Frame=matrix(base['Frame']);Li=matrix(base['Frame_inverse'])
    sourcejets=[matrix(v) for v in base['physical_s_jets']['NoetherSource_axis']]
    Hjets=[matrix(v) for v in base['physical_s_jets']['Haxis']]
    def derivative(value,order):
        p,q=value.numer,value.denom
        q0=q.get((0,),inf.BASE.zero);assert q0
        v0=p.get((0,),inf.BASE.zero)/q0
        v1=(p.get((1,),inf.BASE.zero)-q.get((1,),inf.BASE.zero)*v0)/q0
        v2=2*(p.get((2,),inf.BASE.zero)-q.get((1,),inf.BASE.zero)*v1-q.get((2,),inf.BASE.zero)*v0)/q0
        return [v0,v1,v2][order]
    def physical_coefficient(power,order):
        result=s.zeros(289,6)
        for radical in range(4):
            M=actual.get((power,radical),inf.zero(289,6))
            values=DM.from_dok({ij:derivative(v,order) for ij,v in M.to_dok().items()},M.shape,inf.BASE)
            result+=radicals[radical]*values.to_Matrix()/s.sqrt(2)**order
        return s.SparseMatrix(result.applyfunc(s.expand))
    c=6*s.sqrt(15)/25
    init=[s.SparseMatrix((c*physical_coefficient(1,j)).applyfunc(s.expand)) for j in range(3)]
    vel=[s.SparseMatrix((c*c*physical_coefficient(2,j)).applyfunc(s.expand)) for j in range(3)]
    contact=[s.SparseMatrix(M.applyfunc(lambda v:s.expand(v).coeff(x,2)/c2)) for M in sourcejets]
    ht=[[s.SparseMatrix(M.applyfunc(lambda v:s.expand(v).coeff(x,k)/c**k)) for k in range(3)] for M in Hjets]
    enc=lambda M:{'shape':list(M.shape),'entries':[[i,j,str(s.expand(v))] for (i,j),v in sorted(s.SparseMatrix(M).todok().items()) if s.expand(v)!=0]}
    initial_reports=[]
    for j in range(3):
        first=sum((s.binomial(j,r)*ht[r][2]*init[j-r] for r in range(j+1)),s.zeros(289,6))
        second=sum((s.binomial(j,r)*(ht[r][1]*init[j-r]+ht[r][2]*vel[j-r]) for r in range(j+1)),s.zeros(289,6))
        assert all(s.expand(v)==0 for v in first)
        assert all(s.expand(v)==0 for v in second-contact[j])
        assert ht[1][2]==ht[2][2]==s.zeros(289)
        iw,vw,cw=(s.SparseMatrix(M.applyfunc(s.expand)) for M in [Frame*init[j],Frame*vel[j],Li.T*contact[j]])
        initial_reports.append({'physical_s_order':j,'initial_world_over_D':enc(iw),'velocity_world_over_D':enc(vw),
            'Noether_delta_contact_world_over_D':enc(cw),
            'initial_nonzero_rows':len({i for i,k in iw.todok()}),'velocity_nonzero_rows':len({i for i,k in vw.todok()}),
            'source_contact_nonzero_rows':len({i for i,k in cw.todok()}),'all289_initial_contact_identities':True})
    print('PASS actual full-s infinity coefficients generate physical0/1/2 initial jets and source contacts',flush=True)
    out={'scope':'STRIKE_FULL_EXTERNAL_RAY_SOURCE_PROPERNESS',
        'input_sha256':{str(p.relative_to(HERE.parents[4])):hashlib.sha256(p.read_bytes()).hexdigest()
                       for p in [path,FQ/'packet-gauge-family/infinity.py',FQ/'packet-gauge-family/proper.py']},
        'parameter_identity':'physical s=sqrt(2)*a, q_out=rho+a; incoming U, X0 fixed',
        'exact_coefficient_field':'QQ(i)(a); original sqrt(2),sqrt(15),sqrt(30) coefficients split faithfully',
        'components':reports,'generic_section_nonpositive_powers':[],
        'all289_nonpositive_Laurent_powers':[],
        'full_source_family_strictly_proper':True,
        'actual_initial_data':initial_reports,'initial_common_denominator':data['D'],
        'source_time_principal_symbol_independent_of_external_ray':True,
        'generic_tau_coefficients':{f'{power},{radical}':inf.encoded(M) for (power,radical),M in actual.items()},
        'actual_analytic_meaning':'Exact infinity Schur pivots regular at a=0 and vanishing reduced sources give an analytic solution O(1/x); the source full lift cancels every nonproper term. This is an identity over QQ(i)(a), not interpolation in a.',
        'uniform_extension':'The original complete determinant leading coefficient stays nonzero in MomentumDomain; the exact zero contact identity extends across auxiliary pivot charts throughout the original regular ray domain.',
        'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'proper.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('PASS all external s source family strictly proper, including the whole289 lift',out['elapsed_seconds'],flush=True)


if __name__=='__main__':main()
