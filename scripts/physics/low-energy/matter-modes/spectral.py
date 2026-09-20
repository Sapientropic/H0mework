#!/usr/bin/env python3
"""Exact source spectral resolution for every real spatial momentum.

The universal projectors use n=q/|q| and t=sqrt(|q|^2+9/25). All matrix
identities are verified over the exact coordinate ring n.n=1,t^2=r^2+9/25;
the origin has its own direction-independent merged resolution.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
import json
from pathlib import Path
import time
import sympy as s
from compute import HERE,clean,decode,encode,zero


def radical_zeros(coefficients,r):
    a,b,c=coefficients
    expression=a+b*r+c*s.sqrt(r*r+s.Rational(9,25))
    if c==0:
        if b==0:
            return 'all' if a==0 else []
        candidates=[-a/b]
    else:
        polynomial=s.Poly(s.expand((a+b*r)**2-c*c*(r*r+s.Rational(9,25))),r)
        assert not polynomial.is_zero
        roots=s.roots(polynomial.as_expr(),r)
        assert sum(roots.values())==polynomial.degree()
        candidates=list(roots)
    answer=[]
    for candidate in candidates:
        assert candidate.is_real is not None and candidate.is_nonnegative is not None
        if candidate.is_real and candidate.is_nonnegative:
            value=s.simplify(expression.subs(r,candidate))
            assert value==0 or value.is_zero is False,value
            if value==0:answer.append(candidate)
    return sorted(set(answer),key=lambda value:float(value))


def pole_catalog(groups,stationary):
    r=s.symbols('r',real=True)
    branches={'singlet_plus':(s.Rational(3,2),1,0),'singlet_minus':(s.Rational(3,2),-1,0),
        'parallel_plus':(s.Rational(9,5),1,0),'parallel_minus':(s.Rational(9,5),-1,0),
        'mixed_plus':(s.Rational(6,5),0,1),'mixed_minus':(s.Rational(6,5),0,-1)}
    grouped=defaultdict(lambda:{'multiplicity':0,'source_labels':[]})
    for group in groups:
        for name,abc in branches.items():
            multiplicity=group['color_singlet_multiplicity'] if name.startswith('singlet') else group['color_doublet_multiplicity']
            coefficient=tuple(group['chirality']*s.sympify(value) for value in abc)
            if stationary:coefficient=(coefficient[0]-s.Rational(3,5)*group['phase_charge'],)+coefficient[1:]
            grouped[coefficient]['multiplicity']+=multiplicity
            grouped[coefficient]['source_labels'].append({'chirality':group['chirality'],
                'degree':group['degree'],'branch':name,'multiplicity':multiplicity})
    entries=[];zeros=defaultdict(list);crossings=defaultdict(list)
    for number,(coefficients,value) in enumerate(grouped.items()):
        expression=coefficients[0]+coefficients[1]*r+coefficients[2]*s.sqrt(r*r+s.Rational(9,25))
        entries.append({'id':number,'coefficients':list(map(str,coefficients)),
            'scaled_frequency':str(expression),**value})
        for root in radical_zeros(coefficients,r):zeros[root].append(number)
    for i,left in enumerate(entries):
        for right in entries[i+1:]:
            delta=tuple(s.sympify(a)-s.sympify(b) for a,b in zip(left['coefficients'],right['coefficients']))
            roots=radical_zeros(delta,r);assert roots!='all'
            for root in roots:crossings[root].append([left['id'],right['id']])
    zero_rows=[{'r':str(root),'physical_momentum_squared':str(s.simplify(2*root**2)),
        'zero_eigenspace_dimension':sum(entries[number]['multiplicity'] for number in ids),
        'branch_ids':ids} for root,ids in sorted(zeros.items(),key=lambda row:float(row[0]))]
    collision_rows=[]
    for root,pairs in sorted(crossings.items(),key=lambda row:float(row[0])):
        equal=defaultdict(list)
        for entry in entries:
            energy=s.simplify(s.sympify(entry['scaled_frequency'],locals={'r':r}).subs(r,root))
            equal[energy].append(entry['id'])
        collision_rows.append({'r':str(root),'physical_momentum_squared':str(s.simplify(2*root**2)),
            'colliding_pairs':pairs,'eigenspaces':[{'scaled_frequency':str(energy),'branch_ids':ids,
                'dimension':sum(entries[number]['multiplicity'] for number in ids)}
                for energy,ids in equal.items()]})
    return {'branches':entries,'all_zero_frequency_shells':zero_rows,'all_branch_crossing_radii':collision_rows,
        'persistent_degeneracies_merged_by_identical_frequency_function':True,
        'all_radical_equations_filtered_against_unsquared_source_equation':True}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args();started=time.monotonic()
    source=json.loads(args.source.read_text())
    nx,ny,nz,r,t,x=s.symbols('nx ny nz r t x',real=True)
    direction=[nx,ny,nz]
    groebner=s.groebner([nx*nx+ny*ny+nz*nz-1,t*t-r*r-s.Rational(9,25)],
        t,nz,ny,nx,r,x,domain=s.QQ_I)

    def reduce(value):
        numerator,denominator=s.together(value).as_numer_denom()
        remainder=groebner.reduce(s.expand(numerator))[1]
        return s.cancel(remainder/denominator)

    def check(matrix):
        for position,value in s.SparseMatrix(matrix).todok().items():
            residual=reduce(value)
            assert residual==0,(position,residual)

    pauli=list(map(decode,source['pauli_matrices']))
    sigma=sum((component*matrix for component,matrix in zip(direction,pauli)),s.zeros(2))
    hsing=decode(source['singlet_constant'])+r*sigma
    hd=decode(source['doublet_constant'])+r*s.kronecker_product(sigma,s.eye(2))
    one,two=s.eye(2),s.eye(4)
    up,down=(one+sigma)/2,(one-sigma)/2
    parallel_up=s.kronecker_product(up,up)
    parallel_down=s.kronecker_product(down,down)
    middle=two-parallel_up-parallel_down
    K=(hd-s.Rational(6,5)*two)*middle
    check(K*K-(r*r+s.Rational(9,25))*middle)
    singlet=[('singlet_plus',s.Rational(3,2)+r,up),('singlet_minus',s.Rational(3,2)-r,down)]
    doublet=[('parallel_plus',s.Rational(9,5)+r,parallel_up),
             ('parallel_minus',s.Rational(9,5)-r,parallel_down),
             ('mixed_plus',s.Rational(6,5)+t,(middle+K/t)/2),
             ('mixed_minus',s.Rational(6,5)-t,(middle-K/t)/2)]
    families={}
    clock,other_clock=s.symbols('time other_time',real=True)
    physical_scale=s.sympify(source['time_scale'])
    for kind,hamiltonian,projectors in [('singlet',hsing,singlet),('doublet',hd,doublet)]:
        size=hamiltonian.rows
        check(sum((matrix for _,_,matrix in projectors),s.zeros(size))-s.eye(size))
        check(sum((e*matrix for _,e,matrix in projectors),s.zeros(size))-hamiltonian)
        for i,(_,energy,projector) in enumerate(projectors):
            check(projector.H-projector)
            check(hamiltonian*projector-energy*projector)
            assert reduce(s.trace(projector))==1
            for j,(_,_,other) in enumerate(projectors):
                check(projector*other-(projector if i==j else s.zeros(size)))
            for chirality in [-1,1]:
                frequency=physical_scale*chirality*energy
                phase=s.exp(-s.I*frequency*clock)
                assert s.simplify(s.I*s.diff(phase,clock)-frequency*phase)==0
                assert s.simplify(s.conjugate(phase)*phase-1)==0
                assert s.simplify(phase.subs(clock,clock+other_clock)-phase*phase.subs(clock,other_clock))==0
        resolvent=sum((matrix/(x-energy) for _,energy,matrix in projectors),s.zeros(size))
        check((x*s.eye(size)-hamiltonian)*resolvent-s.eye(size))
        check(resolvent*(x*s.eye(size)-hamiltonian)-s.eye(size))
        families[kind]={'hamiltonian':encode(hamiltonian),
            'projectors':[{'name':name,'scaled_frequency':str(energy),
                'rank':1,'matrix':encode(matrix.applyfunc(reduce))} for name,energy,matrix in projectors],
            'all_projector_eigenvalue_orthogonality_and_sum_identities':True,
            'actual_two_sided_resolvent_identity':True,
            'original_time_exponential_derivative_unitarity_and_composition':True}
        print('PASS all-direction',kind,'Hermitian spectral projectors and two-sided resolvent',flush=True)
    spin_dot=sum((s.kronecker_product(a,a) for a in pauli),s.zeros(4))
    triplet=(spin_dot+3*two)/4;antisymmetric=(two-spin_dot)/4
    for projector,energy,rank in [(triplet,s.Rational(9,5),3),(antisymmetric,s.Rational(3,5),1)]:
        zero(projector.H-projector);zero(projector*projector-projector)
        zero(decode(source['doublet_constant'])*projector-energy*projector)
        assert s.trace(projector)==rank
    check((parallel_up+parallel_down+(middle+K/t)/2).subs({r:0,t:s.Rational(3,5)})-triplet)
    check(((middle-K/t)/2).subs({r:0,t:s.Rational(3,5)})-antisymmetric)
    zero(triplet*antisymmetric);zero(triplet+antisymmetric-two)
    original=pole_catalog(source['groups'],False)
    stationary=pole_catalog(source['groups'],True)
    assert {row['physical_momentum_squared']:row['zero_eigenspace_dimension']
        for row in original['all_zero_frequency_shells']}=={'54/25':29,'9/2':50,'162/25':29}
    assert {row['physical_momentum_squared']:row['zero_eigenspace_dimension']
        for row in stationary['all_zero_frequency_shells']}=={'0':31,'9/50':5,'81/50':45,'72/25':28}
    result={'scope':'COMPLETE_216_SOURCE_FREE_HERMITIAN_SPECTRAL_RESOLUTION_ALL_REAL_MOMENTA',
        'source_sha256':source['source_sha256'],'normalization':source['momentum_normalization'],
        'nonzero_momentum_coordinates':'q=k/sqrt(2), r=|q|>0, n=q/r, t=sqrt(r^2+9/25)>0',
        'exact_polynomial_ideal':['nx^2+ny^2+nz^2-1','t^2-r^2-9/25'],
        'coordinate_reality':'nx,ny,nz,r,t are real; projectors use only denominator t, plus the direction n=q/r',
        'universal_families':families,
        'origin_resolution':{
            'singlet':[{'scaled_frequency':'3/2','rank':2,'matrix':encode(one)}],
            'doublet':[{'scaled_frequency':'9/5','rank':3,'matrix':encode(triplet)},
                       {'scaled_frequency':'3/5','rank':1,'matrix':encode(antisymmetric)}],
            'direction_independent_merged_limits_paid':True},
        'full_source_projector':'Pi_b(k)=sum_over_source_copies F_copy P_b(k) F_copy^dagger',
        'frequency_readback':'E_original=N*sqrt(2)*chi*e_b; E_stationary=E_original-omega*phase_charge',
        'propagator':'U_free(time,k)=sum_b exp(-i E_original_b(k)*time) Pi_b(k)',
        'resolvent':'G_free(E,k)=sum_b Pi_b(k)/(E-E_original_b(k)); (E-H)G=G(E-H)=Pfree',
        'unitarity_and_group_law':'U(0)=Pfree; U(t)^dagger U(t)=Pfree; U(t)U(s)=U(t+s)',
        'original_time_catalog':original,'stationary_time_catalog':stationary,
        'elapsed_seconds':round(time.monotonic()-started,3)}
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print('PASS origin isotropic degeneracies; all original and stationary zero shells/crossings;',
        result['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
