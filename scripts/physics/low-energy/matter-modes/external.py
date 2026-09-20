#!/usr/bin/env python3
"""Consumable original-field spectral projectors, resolvent and free external legs."""
from __future__ import annotations
import argparse
from collections import defaultdict
import json
from pathlib import Path
import sympy as s
from compute import BASE,decode,encode,clean,zero


def simplify(matrix):return s.SparseMatrix(matrix).applyfunc(s.simplify)


def source_resolution(momentum,source,spectral):
    """Physical k -> original252 projectors, retaining each actual phase charge."""
    momentum=s.Matrix(list(map(s.sympify,momentum)))
    q=momentum/s.sqrt(2);radius=s.simplify(s.sqrt((q.T*q)[0]))
    nx,ny,nz,r,t=s.symbols('nx ny nz r t',real=True)
    substitution={r:radius,t:s.sqrt(radius**2+s.Rational(9,25))}
    if radius!=0:substitution.update(dict(zip([nx,ny,nz],q/radius)))
    F=decode(source['source_isometry'])
    scale=s.sympify(source['time_scale']);omega=s.sympify(source['source_frequency'])
    grouped={}
    for block in source['blocks']:
        beginning=block['first_column'];frame=F[:,beginning:beginning+block['dimension']]
        family=(spectral['origin_resolution'][block['kind']] if radius==0 else
                spectral['universal_families'][block['kind']]['projectors'])
        for number,entry in enumerate(family):
            key=(block['chirality'],block['degree'],block['kind'],number)
            small=simplify(decode(entry['matrix'],nx=nx,ny=ny,nz=nz,r=r,t=t).subs(substitution))
            energy=s.simplify(scale*block['chirality']*
                s.sympify(entry['scaled_frequency'],locals={'r':r,'t':t}).subs(substitution))
            if key not in grouped:
                grouped[key]={'chirality':block['chirality'],'degree':block['degree'],
                    'name':entry.get('name',block['kind']+'_origin_'+str(number)),
                    'phase_charge':block['phase_charge'],'original_frequency':energy,
                    'stationary_frequency':s.simplify(energy-omega*block['phase_charge']),
                    'projector':s.zeros(252)}
            grouped[key]['projector']+=frame*small*frame.H
    for row in grouped.values():row['projector']=simplify(row['projector'])
    return list(grouped.values())


def source_resolvent(frequency,momentum,source,spectral):
    return simplify(sum((row['projector']/(frequency-row['original_frequency'])
        for row in source_resolution(momentum,source,spectral)),s.zeros(252)))


def source_propagator(time,momentum,source,spectral):
    return sum((s.exp(-s.I*row['original_frequency']*time)*row['projector']
        for row in source_resolution(momentum,source,spectral)),s.zeros(252))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,required=True)
    parser.add_argument('--spectral',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    source=json.loads(args.source.read_text());spectral=json.loads(args.spectral.read_text())
    phase=json.loads((BASE/'full-phase/receipt.json').read_text())
    F=decode(source['source_isometry']);P=decode(source['free_projection'])
    h0=decode(source['original_H_constant']);hspace=list(map(decode,source['original_H_spatial']))
    scale=s.sympify(source['time_scale']);omega=s.sympify(source['source_frequency'])
    Q=decode(phase['phase_generator']);C=list(map(decode,phase['principal_coefficients']))
    constant=decode(phase['original_constant_B'])+decode(phase['original_Y'])
    M=decode(phase['stationary_scalar_mixing'])
    gamma0=C[0]*s.sympify(source['source_lapse'])/s.I
    S=gamma0*s.kronecker_product(s.diag(-1,-1,1,1),s.eye(63))
    examples=[]
    for radius in [s.Integer(0),s.Integer(1),s.Rational(3,2),3*s.sqrt(3)/5,s.Rational(9,5)]:
        q=radius*s.Matrix([s.Rational(1,3),s.Rational(2,3),s.Rational(2,3)])
        momentum=s.sqrt(2)*q
        resolution=source_resolution(momentum,source,spectral)
        h=clean(scale*(h0+sum((q[i]*hspace[i] for i in range(3)),s.zeros(252))))
        zero(simplify(sum((row['projector'] for row in resolution),s.zeros(252))-P))
        zero(simplify(sum((row['original_frequency']*row['projector'] for row in resolution),s.zeros(252))-h*P))
        zero(simplify(h*P-(h*P).H))
        multiplicities=defaultdict(int);chosen=None
        for row in resolution:
            projector=row['projector'];energy=row['original_frequency']
            zero(simplify(projector.H-projector));zero(simplify(projector*projector-projector))
            zero(simplify(h*projector-energy*projector))
            zero(simplify(Q*projector-row['phase_charge']*projector))
            rank=s.simplify(s.trace(projector));assert rank.is_Integer
            multiplicities[energy]+=int(rank)
            if chosen is None or energy==0:
                column=next(j for j in range(252) if projector[:,j]!=s.zeros(252,1))
                vector=projector[:,column]
                norm=s.simplify((vector.H*vector)[0]);assert norm.is_positive
                vector=simplify(vector/s.sqrt(norm))
                symbol=clean(-s.I*energy*C[0]+sum((s.I*momentum[j]*C[j+1]
                    for j in range(3)),s.zeros(252))+constant)
                dual=simplify(s.sqrt(2)*vector.H*S)
                zero(simplify(symbol*vector));zero(simplify(dual*symbol));zero(simplify(dual*M))
                zero(simplify((h-omega*Q)*vector-row['stationary_frequency']*vector))
                time=s.symbols('time',real=True);position=s.symbols('x1:4',real=True)
                profile=s.exp(-s.I*energy*time+s.I*sum(momentum[j]*position[j] for j in range(3)))
                assert s.simplify(s.I*s.diff(profile,time)-energy*profile)==0
                assert all(s.simplify(s.diff(profile,position[j])-s.I*momentum[j]*profile)==0 for j in range(3))
                chosen={'chirality':row['chirality'],'degree':row['degree'],'branch':row['name'],
                    'original_frequency':str(energy),'stationary_frequency':str(row['stationary_frequency']),
                    'phase_charge':row['phase_charge'],'unit_source_primal_vector':encode(vector),
                    'actual_canonical_dual_row':encode(dual),
                    'original_primal_independent_dual_and_scalar_plane_wave_rows_zero':True}
        assert sum(multiplicities.values())==216
        if radius==1:
            resolvent=source_resolvent(0,momentum,source,spectral)
            zero(simplify((-h)*resolvent-P));zero(simplify(resolvent*(-h)-P))
        examples.append({'physical_momentum':list(map(str,momentum)),
            'physical_momentum_squared':str(s.simplify(2*radius**2)),
            'original_zero_frequency_dimension':multiplicities.get(s.Integer(0),0),
            'full_source_spectral_resolution_and_eigenvalues_checked':True,
            'nonzero_original_field_external_leg':chosen})
        print('PASS complete216 source resolution and actual external leg at |k|^2=',
              examples[-1]['physical_momentum_squared'],'zero dimension',examples[-1]['original_zero_frequency_dimension'],flush=True)
    result={'scope':'CONSUMABLE_252_FIELD_RESOLVENT_PROPAGATOR_AND_SOURCE_EXTERNAL_LEGS',
        'source_sha256':source['source_sha256'],'examples':examples,
        'all_examples_have_total_spectral_rank_216':True,
        'source_resolvent_generic_oblique_two_sided_inverse_checked':True,
        'functions':{'source_resolution':'physical k -> all original source projectors and both time frequencies',
            'source_resolvent':'physical E,k -> full252 matrix inverse on Pfree',
            'source_propagator':'original physical time,k -> full252 spectral evolution'},
        'original_time_phase_readback':'psi_original=exp(-i*omega*time*Q)*psi_stationary; canonical dual transformed by V=S U^dagger S',
        'nonzero_examples_are_consumers_not_all_momentum_coverage':True}
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')


if __name__=='__main__':main()
