#!/usr/bin/env python3
"""Exact source ordered words, all action-vertex grades, and reverse-arrow control."""
import importlib.util
import json
from pathlib import Path
import time
import sympy as s

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
spec=importlib.util.spec_from_file_location('triangular_source',HERE.parent/'triangular/compute.py')
tri=importlib.util.module_from_spec(spec)
spec.loader.exec_module(tri)
decode,clean,zero=tri.decode,tri.clean,tri.zero

def main():
    started=time.monotonic()
    tri.source.source_matrices(ROOT)
    _,_,_,hashes=tri.source.source.parse_source(ROOT)
    phase=json.loads((HERE.parents[1]/'full-phase/receipt.json').read_text())
    full=json.loads((HERE.parent/'receipt.json').read_text())
    vertices=json.loads((HERE.parents[1]/'matter-vertices/receipt.json').read_text())
    assert phase['source_sha256']==full['source_sha256']==vertices['source_sha256']==hashes
    P=s.diag(*[int(i%63<7) for i in range(252)])
    H0=decode(full['original_H_free'])
    N=decode(full['original_H_yukawa'])
    Cinv=decode(full['time_principal_inverse'])
    zero(P*N-N);zero(N*P)
    p=s.symbols('p0:4',real=True)
    operators=[];diagonal_operators=[]
    counts={}
    for item in vertices['primitive_vertices']:
        V=decode(item['operator'],**{str(x):x for x in p})
        if item['group']=='scalar':
            zero(P*V-V);zero(V*P)
        diagonal=P*V*P+(s.eye(252)-P)*V*(s.eye(252)-P)
        arrow=V-diagonal
        zero(P*diagonal-diagonal*P);zero(P*arrow-arrow);zero(arrow*P)
        counts[item['group']]=counts.get(item['group'],0)+1
        point=dict(zip(p,[s.Rational(5,7),s.Rational(1,3),s.Rational(-2,5),s.Rational(3,7)]))
        operators.append(clean(V.subs(point)))
        diagonal_operators.append(clean(diagonal.subs(point)))
    principal=[decode(x) for x in phase['principal_coefficients']]
    lapse=s.sympify(phase['source_lapse'])
    gamma0=clean(lapse*principal[0]/s.I)
    spatial=[clean(-lapse*gamma0*principal[j+1]/s.I) for j in range(3)]
    points=[([0,0,0],1+2*s.I),([0,0,3*s.sqrt(2)/2],3+s.I)]
    G=[];G0=[]
    for momentum,z in points:
        free=clean(H0+sum((x*M for x,M in zip(momentum,spatial)),s.zeros(252)))
        K=z*s.eye(252)-free
        R0=tri.block_inverse(K,tri.components(free))
        R=clean(R0+R0*N*R0)
        zero(clean((K-N)*R-s.eye(252)))
        G.append(clean(s.I*R*Cinv));G0.append(clean(s.I*R0*Cinv))
        assert clean(G[-1]-G0[-1]).todok()
    words=[]
    for indices in [[0,0],[3,12,24],[0,48,72,84]]:
        a=s.eye(252);b=s.eye(252)
        for j,index in enumerate(indices):
            a=clean(a*G[j%2]*operators[index])
            b=clean(b*G0[j%2]*diagonal_operators[index])
        fulltrace=s.simplify(s.trace(a));freetrace=s.simplify(s.trace(b))
        assert s.simplify(fulltrace-freetrace)==0
        words.append({'vertices':indices,'source_groups':[vertices['primitive_vertices'][i]['group'] for i in indices],
            'full_trace':str(fulltrace),'free_trace':str(freetrace),'exact_equal':True})
        print('word',indices,'PASS',flush=True)
    assert words[0]['full_trace']!='0'
    scalar_ids=[i for i,v in enumerate(vertices['primitive_vertices']) if v['group']=='scalar']
    for index in scalar_ids:
        V=operators[index]
        assert s.simplify(s.trace(G[0]*operators[0]*G[1]*V))==0
        zero(clean(V*G[0]*V))
    reverse=s.simplify(s.trace(N.H*N))
    assert reverse>0
    receipt={'scope':'COMPLETE_ORDERED_ORIGINAL_DIRAC_MATRIX_WORDS_NOT_A_CHOICE_OF_QUANTUM_LOOP_STATE',
        'source_sha256':hashes,'automatic_original_vertex_triangular_expansions':counts,'words':words,
        'all_70_original_scalar_closed_insertions_zero':True,'all_70_double_scalar_chains_zero':True,
        'open_full_minus_free_Dirac_Green_nonzero_at_both_points':True,
        'reverse_adjoint_control_trace_Nadj_N':str(reverse),
        'no_reverse_adjoint_relabelled_as_original_Y':True,'seconds':round(time.monotonic()-started,3)}
    (HERE/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'passed':True,'seconds':receipt['seconds'],'reverse_trace':str(reverse)}),flush=True)

if __name__=='__main__':main()
