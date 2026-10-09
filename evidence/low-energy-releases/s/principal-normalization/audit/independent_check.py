#!/usr/bin/env python3
"""Independent source-action, auxiliary elimination and clock audit.

The candidate is not imported. The gauge action is differentiated before
eliminating B, its raw H289 Schur block is checked, and the clock change is
performed on the curvature one-form and integration density separately.
"""
from __future__ import annotations

import argparse
import importlib.util
import itertools
import json
from pathlib import Path
import re
import time
import sympy as s


def clean(matrix):return s.SparseMatrix(matrix).applyfunc(s.expand)


def equal(left,right):
    assert left.shape==right.shape
    assert all(s.simplify(value)==0 for value in s.SparseMatrix(left-right).todok().values())


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,required=True)
    root=parser.parse_args().root.resolve();started=time.monotonic()
    base=root/'Verification/physics/low-energy-phenomenology'
    core=root/'Lean/SaturationMonoid/PhysicsCore'
    directory=base/'principal-normalization'
    candidate=json.loads((directory/'receipt.json').read_text())
    assert candidate==json.loads(Path('/tmp/principal-normalization-audit.json').read_text())
    active=json.loads((base/'active-gauge/receipt.json').read_text())
    phase=json.loads((base/'full-phase/receipt.json').read_text())
    matter=json.loads((base/'matter-modes/source.json').read_text())
    vertices=json.loads((base/'matter-vertices/receipt.json').read_text())
    scalar=json.loads((base/'scalar-exchange/receipt.json').read_text())
    weak=json.loads((base/'weak-exchange/spatial/receipt.json').read_text())
    p=s.symbols('p0:4',real=True);nu=s.symbols('nu',real=True)
    u,*r=s.symbols('u r1 r2 r3',real=True)
    lam,k=s.symbols('lam k',real=True)
    symbols={str(x):x for x in [*p,nu,u,*r,lam,k]}
    def decode(record):
        return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(value,locals=symbols)
            for i,j,value in record['entries']})
    def polynomial(record,size,degree=None):
        result=s.MutableSparseMatrix(size,size,{})
        for i,j,powers,value in record:
            if degree is None or sum(powers)==degree:
                result[i,j]+=s.sympify(value)*s.prod(x**power for x,power in zip(p,powers))
        return clean(result)
    n=s.sqrt(s.Rational(54,125));sigma=s.Rational(1,2)
    assert n==s.sympify(active['source_lapse'])==s.sympify(candidate['source_lapse'])
    assert sigma==s.sympify(active['source_coupling'])==s.sympify(candidate['source_sigma'])
    # Recover the original oriented pairs, Hodge and wedge, including the 31 sign.
    text=(core/'PointwiseDiracSpinConnectionLift.lean').read_text()
    first=[int(x) for x in re.search(r'def lorentzBivectorFirst.*?!\[(.*?)\]',text,re.S).group(1).split(',')]
    second=[int(x) for x in re.search(r'def lorentzBivectorSecond.*?!\[(.*?)\]',text,re.S).group(1).split(',')]
    pairs=list(zip(first,second));assert pairs==[(0,1),(0,2),(0,3),(2,3),(3,1),(1,2)]
    text=(core/'RawLorentzianMetricHodgeRecovery.lean').read_text()
    literal=re.search(r'def lorentzianCoframeHodge.*?toFun := fun ω => !\[(.*?)\]',text,re.S).group(1)
    Hodge=s.MutableSparseMatrix(6,6,{})
    for i,value in enumerate(literal.split(',')):
        match=re.fullmatch(r'\s*(-?)ω (\d)\s*',value);assert match
        Hodge[i,int(match[2])]=-1 if match[1] else 1
    text=(core/'StageNineTopologicalFourFormPairing.lean').read_text()
    complement=[int(x) for x in re.search(r'def twoFormComplement.*?!\[(.*?)\]',text,re.S).group(1).split(',')]
    W=s.SparseMatrix(6,6,{(i,j):1 for i,j in enumerate(complement)})
    lapse,coupling=s.symbols('lapse coupling',positive=True)
    e=s.diag(lapse,1,1,1)
    exterior=s.Matrix(6,6,lambda i,j:e[pairs[i][0],pairs[j][0]]*e[pairs[i][1],pairs[j][1]]-
        e[pairs[i][0],pairs[j][1]]*e[pairs[i][1],pairs[j][0]])
    star=exterior.inv()*Hodge*exterior
    equal(star*star,-s.eye(6));equal((W*star).T,W*star)
    expected_star=s.SparseMatrix.vstack(s.SparseMatrix.hstack(s.zeros(3),s.eye(3)/lapse),
        s.SparseMatrix.hstack(-lapse*s.eye(3),s.zeros(3)))
    equal(star,expected_star)
    hodge_source=(core/'StageNineGlobalIntegratedAction.lean').read_text()
    assert '(inverseCoframeTwoFormLinear coframe).comp' in hodge_source
    assert '(coframeTwoFormLinear coframe))' in hodge_source
    action_source=(core/'StageNineFormNativeMotherAction.lean').read_text()
    assert 'generatedTwoFormWedgeCoefficient pairing auxiliary curvature -' in action_source
    assert '(1 / 2 : ℝ) *' in action_source
    repaired_source=(core/'StageNineDiracDualFormNativeMotherAction.lean').read_text()
    assert 'generatedFormNativeGaugeDensityAtBoundary boundary field +' in repaired_source
    f=s.Matrix(s.symbols('f0:6',real=True));aux=s.Matrix(s.symbols('b0:6',real=True))
    action=(aux.T*W*f)[0]-coupling*s.Rational(1,2)*(aux.T*W*star*aux)[0]
    Hessian_B=s.hessian(action,aux)
    mixed=s.Matrix([s.diff(action,z) for z in aux]).jacobian(f)
    equal(Hessian_B,-coupling*W*star);equal(mixed,W)
    solution=clean(-Hessian_B.inv()*mixed*f)
    equal(solution,-star*f/coupling)
    reduced=s.expand(action.subs(dict(zip(aux,solution)),simultaneous=True))
    electric=sum(f[i]**2 for i in range(3));magnetic=sum(f[i]**2 for i in range(3,6))
    assert s.simplify(reduced-lapse*electric/(2*coupling)+magnetic/(2*coupling*lapse))==0
    curvature_hessian=s.hessian(reduced,f)
    equal(curvature_hessian,s.diag(*([lapse/coupling]*3+[-1/(coupling*lapse)]*3)))
    assert clean(Hessian_B*(star*f/coupling)+mixed*f)!=s.zeros(6,1)
    print('PASS actual oriented Hodge, original BF-minus-half-constitutive action, B=-star F/sigma and exact reduced E/B factors',flush=True)

    fundamental={}
    for group in ((0,1,2),(3,4)):
        for a,b in itertools.combinations(group,2):
            fundamental[f'A{a}{b}']=s.SparseMatrix(7,7,{(a,b):1,(b,a):-1})
            fundamental[f'S{a}{b}']=s.SparseMatrix(7,7,{(a,b):s.I,(b,a):s.I})
        for a in group[:-1]:
            fundamental[f'D{a}-{group[-1]}']=s.SparseMatrix(7,7,{(a,a):s.I,(group[-1],group[-1]):-s.I})
    fundamental['Y']=s.diag(0,0,0,0,0,s.I,-s.I)
    assert list(fundamental)==active['native_P286_labels']
    matrices=list(fundamental.values())
    # Direct sum of the original three pairings; do not edit a mother Gram entry.
    native=s.Matrix(12,12,lambda i,j:-s.re(s.trace(matrices[i][:3,:3]*matrices[j][:3,:3])+
        s.trace(matrices[i][3:5,3:5]*matrices[j][3:5,3:5])+matrices[i][5,5]*matrices[j][5,5]))
    mother=s.Matrix(12,12,lambda i,j:-s.re(s.trace(matrices[i]*matrices[j])))
    equal(native,decode(candidate['native_pairing']))
    assert native[11,11]==1 and mother[11,11]==2
    assert native.eigenvals()=={s.Integer(2):9,s.Integer(1):2,s.Integer(3):1}
    fields=active['fields']
    gauge=[i for i,row in enumerate(fields) if row['group']=='gauge_A']
    bfields=[i for i,row in enumerate(fields) if row['group']=='gauge_B']
    assert [fields[i]['coordinate'] for i in gauge]==[[mu,a] for mu in range(4) for a in range(12)]
    assert [fields[i]['coordinate'] for i in bfields]==[[pair,a] for pair in range(6) for a in range(12)]
    curl=s.MutableSparseMatrix(6,4,{})
    for row,(a,b) in enumerate(pairs):curl[row,b]=p[a];curl[row,a]=-p[b]
    physical={lapse:n,coupling:sigma}
    reduced_curvature=curvature_hessian.subs(physical)
    spacetime=clean(-curl.T*reduced_curvature*curl)
    equal(spacetime,decode(candidate['source_spacetime_factor']))
    equal(spacetime*s.Matrix(p),s.zeros(4,1))
    generated=s.kronecker_product(spacetime,native)
    original121=polynomial(active['primitive_121_Fourier_Jacobi_entries'],121)
    original_principal=polynomial(active['primitive_121_Fourier_Jacobi_entries'],121,2).extract(gauge,gauge)
    equal(generated,original_principal)
    equal(generated,decode(candidate['all48_gauge_principal_Hessian']))
    original289=polynomial(active['Fourier_Jacobi_entries'],289)
    raw0=polynomial(active['Fourier_Jacobi_entries'],289,0)
    raw1=polynomial(active['Fourier_Jacobi_entries'],289,1)
    raw2=polynomial(active['Fourier_Jacobi_entries'],289,2)
    BB=raw0.extract(bfields,bfields)
    expected_BB=s.kronecker_product(Hessian_B.subs(physical),native)
    equal(BB,expected_BB)
    BBinv=s.kronecker_product(Hessian_B.subs(physical).inv(),native.inv())
    equal(BB*BBinv,s.eye(72));equal(BBinv*BB,s.eye(72))
    BA=raw1.extract(bfields,gauge);AB=raw1.extract(gauge,bfields)
    equal(BA,s.kronecker_product(W*curl,native))
    equal(AB,-s.kronecker_product(curl.T*W,native))
    equal(raw2.extract(gauge,gauge),s.zeros(48))
    equal(-AB*BBinv*BA,generated)
    monomials=sum(len(s.Poly(value,*p).terms()) for value in generated.todok().values())
    assert len(generated.todok())==224 and monomials==336
    print('PASS direct native pairing, actual72 auxiliary inverse and all48 source principal rows/columns (336 coefficients)',flush=True)

    # The same fixed-background action is rewritten; N is not reset to one.
    clock_map=s.diag(lapse,1,1,1)
    curl_tau=curl.subs(p[0],nu)
    equal(curl.subs(p[0],lapse*nu)*clock_map,s.diag(lapse,lapse,lapse,1,1,1)*curl_tau)
    proper_curvature=s.diag(*([lapse*lapse/coupling]*3+[-1/(coupling*lapse*lapse)]*3))
    proper_generated=clean((-curl_tau.T*proper_curvature*curl_tau).subs(physical))
    proper_congruence=clean((clock_map*spacetime.subs(p[0],lapse*nu)*clock_map/lapse).subs(lapse,n))
    equal(proper_generated,proper_congruence)
    equal(proper_generated,decode(candidate['proper_time_spacetime_factor']))
    inverse_e=s.simplify(n*n/sigma);inverse_b=s.simplify(1/(sigma*n*n))
    assert inverse_e==s.Rational(108,125) and inverse_b==s.Rational(125,27)
    assert s.simplify(inverse_b/inverse_e)==1/n**4
    for key,value in [('electric_inverse_coefficient',inverse_e),('magnetic_inverse_coefficient',inverse_b),
        ('electric_squared_coupling_in_native_pairing',1/inverse_e),('magnetic_squared_coupling_in_native_pairing',1/inverse_b)]:
        assert s.sympify(candidate[key])==value
    # Actual metric fixes proper clock on the background worldlines.
    metric=e.T*s.diag(-1,1,1,1)*e
    assert metric[0,0]==-lapse*lapse and s.sqrt(-metric[0,0])==lapse
    wrong_reset=clean(-curl_tau.T*(curvature_hessian.subs({lapse:1,coupling:sigma}))*curl_tau)
    assert wrong_reset!=proper_generated
    print('PASS separate A_tau=A_t/N, derivative p0=N*nu and density dt=d_tau/N transformations; proper E/B inverse pair',flush=True)

    gamma=[]
    text=(core/'DiracCliffordRepresentation.lean').read_text()
    for name in ('Zero','One','Two','Three'):
        literal=re.search(r'def diracGamma'+name+r'\s*:.*?:=\s*!!\[(.*?)\]',text,re.S).group(1)
        gamma.append(s.SparseMatrix([[s.sympify(v.strip().replace('Complex.I','I')) for v in row.split(',')]
            for row in literal.split(';')]))
    Gamma=[s.kronecker_product(g,s.eye(63)) for g in gamma]
    C=[s.I*Gamma[mu]/(n if mu==0 else 1) for mu in range(4)]
    for mu in range(4):equal(C[mu],decode(phase['principal_coefficients'][mu]))
    dirac=sum((p[mu]*C[mu] for mu in range(4)),s.zeros(252))
    characteristic=p[0]**2/n**2-sum(x*x for x in p[1:])
    equal(dirac*dirac,characteristic*s.eye(252))
    scalar_matrix=decode(scalar['normalized_full_scalar_operator'])
    scalar_principal=scalar_matrix.applyfunc(lambda value:sum(coefficient*s.prod(x**power for x,power in zip([u,*r],powers))
        for powers,coefficient in s.Poly(value,u,*r).terms() if sum(powers)==2))
    scalar_principal=clean(scalar_principal.subs({u:p[0]/(n*s.sqrt(2)),**{r[j]:p[j+1]/s.sqrt(2) for j in range(3)}}))
    equal(scalar_principal,characteristic*s.eye(70))
    equal(scalar_principal,decode(candidate['actual_all70_scalar_principal']))
    assert s.expand(s.sympify(candidate['matter_principal_square'],locals=symbols)-characteristic)==0
    plane={p[0]:lam,p[1]:0,p[2]:0,p[3]:s.I*k}
    transverse_polynomial=-4*n*(lam*lam+k*k/(n*n)-s.Rational(1,2))
    weak_consumers=[]
    for label in ('A34','S34'):
        generator=list(fundamental).index(label)
        transverse=s.SparseMatrix(121,2,{(gauge[12+generator],0):1,(gauge[24+generator],1):1})
        equal(original121.subs(plane)*transverse,transverse_polynomial*transverse)
        complete=s.MutableSparseMatrix(289,2,{})
        complete[:121,:]=transverse
        response=-BBinv*original289.extract(bfields,range(121)).subs(plane)*transverse
        for i,field in enumerate(bfields):complete[field,:]=response[i,:]
        forcing=s.MutableSparseMatrix(289,2,{})
        forcing[:121,:]=transverse_polynomial*transverse
        equal(original289.subs(plane)*complete,forcing)
        weak_consumers.append(label)
    stored_weak=decode(weak['weak_four_by_four_operator']).subs({s.Symbol('k1'):0,s.Symbol('k2'):0,s.Symbol('k3'):k})
    T=s.SparseMatrix(4,2,{(1,0):1,(2,1):1})
    equal(stored_weak*T,transverse_polynomial*T)
    # The principal gradient null vector is not a full background symmetry.
    weak_index=list(fundamental).index('A34')
    gradient=s.MutableSparseMatrix(121,1,{})
    for mu in range(4):gradient[gauge[12*mu+weak_index],0]=p[mu]
    assert clean(original121*gradient)!=s.zeros(121,1)
    ratio=1/n**2
    assert ratio==s.Rational(125,54)==s.sympify(candidate['gauge_transverse_over_matter_speed'])
    assert s.simplify((1/n)/n)==ratio
    print('PASS all252 Dirac and70 scalar principals; both exact weak transverse channels lifted to all289 original rows',flush=True)

    spec=importlib.util.spec_from_file_location('certified_bit_exterior',base/'mixed-symbol/audit/independent_check.py')
    helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
    native_weak=fundamental['A34']
    rho=s.kronecker_product(s.eye(4),s.diag(*[helper.exterior(native_weak,degree) for degree in (6,2,4)]))
    V=clean(n*C[1]*rho)
    saved=next(item for item in vertices['primitive_vertices'] if item['group']=='gauge_A' and item['coordinate']==[1,weak_index])
    equal(V,decode(saved['operator']))
    S=s.kronecker_product(gamma[0]*s.diag(-1,-1,1,1),s.eye(63))
    F=decode(matter['source_isometry'])
    current=clean(F.H*(s.sqrt(2)*(S*V+V.H*S)/2)*F)
    equal(current.H,current)
    witness=candidate['free_transverse_current_nonzero_witness']
    i,j=witness['row'],witness['column']
    assert current[i,j]==s.sympify(witness['value'])!=0
    vector=s.zeros(216,1);vector[i]=1/s.sqrt(2);vector[j]=s.I/s.sqrt(2)
    psi=F*vector;dual=s.sqrt(2)*psi.H*S
    equal(psi.H*psi,s.ones(1,1))
    value=s.simplify(s.re((dual*V*psi)[0]))
    assert value!=0 and value==s.simplify((vector.H*current*vector)[0])
    assert clean(s.kronecker_product(spacetime,mother)-generated)!=s.zeros(48)
    wrong_action=(aux.T*W*f)[0]-coupling*(aux.T*W*star*aux)[0]
    wrong_aux=-s.hessian(wrong_action,aux).inv()*mixed*f
    wrong_reduced=s.expand(wrong_action.subs(dict(zip(aux,wrong_aux)),simultaneous=True))
    assert s.simplify(wrong_reduced-reduced/2)==0
    wrong_principal=clean(-curl.T*s.hessian(wrong_reduced,f).subs(physical)*curl)
    equal(wrong_principal,spacetime/2)
    assert wrong_principal!=spacetime
    print('PASS original free-free spatial weak vertex and explicit unit prepared source current',value,flush=True)
    output={'status':'PASS','frozen_replay_identical':True,
        'actual_Hodge':'(E,B) -> (B/N,-N E)','source_auxiliary_solution':'Baux=-star(F)/sigma',
        'native_pairing_spectrum':{'1':2,'2':9,'3':1},'native_Y_norm':1,'mother_Y_norm':2,
        'source_gauge_auxiliary_inverse_dimension':72,'principal_matrix_shape':[48,48],
        'principal_nonzero_entries':224,'principal_exact_monomials':monomials,
        'reduced_principal_from_raw_H289':True,'full_proper_clock_matrix_congruence':True,
        'inverse_electric':str(inverse_e),'inverse_magnetic':str(inverse_b),
        'matter_scalar_characteristic':str(characteristic),'source_weak_full289_channels':weak_consumers,
        'exact_weak_transverse_operator':str(transverse_polynomial),
        'coordinate_characteristic_speeds':{'matter_scalar':str(n),'weak_transverse':str(1/n)},
        'proper_characteristic_speeds':{'matter_scalar':'1','weak_transverse':str(ratio)},
        'weak_free_free_vertex_witness':witness,'actual_unit_prepared_weak_current':str(value),
        'negative_controls':['wrong_B_auxiliary_sign','replace_native_Y_by_mother_trace',
            'omit_action_quadratic_half','reset_lapse_after_fixed_action_clock_rewrite',
            'extend_principal_gradient_null_to_full_background_operator'],
        'full_LSZ_physical_beta_or_empirical_particle_identified':False,
        'elapsed_seconds':round(time.monotonic()-started,3)}
    (directory/'audit/independent-receipt.json').write_text(json.dumps(output,indent=2)+'\n')
    print('PASS complete independent principal normalization audit',output['elapsed_seconds'],'s',flush=True)


if __name__=='__main__':
    main()
