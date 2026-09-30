#!/usr/bin/env python3
"""Source zero modes, fixed-graph congruence jets and complete-source characteristics."""
from ast import literal_eval
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[5]
BASE=ROOT/'Verification/physics/low-energy-phenomenology'
u,q,t,r,slow=s.symbols('u q t r slow',real=True)
START=time.monotonic()


@lru_cache(None)
def norm(v): return s.cancel(s.expand(v))


def clean(M): return s.SparseMatrix(M).applyfunc(norm)
def zero(M):
    rest=clean(M).todok()
    assert not rest,list(rest.items())[:3]
def decode(v): return s.SparseMatrix(*v['shape'],{(i,j):s.sympify(x,locals={'u':u,'q':q,'slow':slow}) for i,j,x in v['entries']})
def encode(M): return {'shape':list(M.shape),'entries':[[int(i),int(j),str(v)] for (i,j),v in clean(M).todok().items()]}
def part(M,n):
    return clean(M).applyfunc(lambda v: sum(c*u**a*q**b for (a,b),c in s.Poly(v,u,q).terms() if a+b==n))
def cut(M): return clean(sum((part(M,n) for n in range(3)),s.zeros(*M.shape)))
def minimum(M): return min(a+b for v in clean(M).todok().values() for (a,b),c in s.Poly(v,u,q).terms() if c)


def main():
    actual=json.loads((BASE/'active-gauge/receipt.json').read_text())
    quotient=json.loads((BASE/'active-gauge/quotient.json').read_text())
    symmetry=json.loads((BASE/'active-gauge/symmetries.json').read_text())
    propagation=json.loads((BASE/'active-gauge/propagation.json').read_text())
    old=json.loads((HERE.parents[1]/'boson-effective/receipt.json').read_text())
    back=json.loads((HERE.parents[1]/'boson-effective/low-readback-receipt.json').read_text())
    frozen=json.loads((HERE.parent/'receipt.json').read_text())
    direct=json.loads((HERE.parent/'direct-receipt.json').read_text())
    modes=json.loads((HERE.parent/'modes-receipt.json').read_text())
    prop=json.loads((HERE.parent/'propagation-receipt.json').read_text())
    for path,digest in actual['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    N=s.sympify(actual['source_lapse']); spin=s.sqrt(2)
    retained=old['original_retained103']; scales=list(map(s.sympify,old['normalized_field_scaling']))
    lam,k=s.symbols('lam k',real=True)
    K=clean(s.SparseMatrix(103,103,{(i,j):s.sympify(v.replace('lambda','lam'),locals={'lam':lam,'k':k}).subs(
        {lam:N*spin*u,k:spin*q})*scales[i]*scales[j]/N for i,j,v in quotient['quotient_operator_103_by_103']}))
    K61=clean(sum((decode(value)*u**literal_eval(power)[0]*q**literal_eval(power)[1]
        for power,value in old['local61_coefficients_degree2'].items()),s.zeros(61)))
    K610=K61.subs({u:0,q:0})
    # Generate the graph from a complete nullspace, rather than supply the graph or its Schur zero.
    raw_null=s.Matrix.hstack(*K610.nullspace())
    assert raw_null.cols==5
    lights=list(frozen['light5_local61_indices']); heavies=[i for i in range(61) if i not in lights]
    E61=clean(raw_null*raw_null[lights,:].inv())
    zero(K610*E61); zero(E61[lights,:]-s.eye(5))
    A56=K610.extract(heavies,heavies); G56=clean(A56.inv(method='DM'))
    zero(A56*G56-s.eye(56)); zero(G56*A56-s.eye(56))
    zero(E61-decode(frozen['true_zero_graph61']))
    bare61=s.SparseMatrix(61,5,{(i,j):1 for j,i in enumerate(lights)})
    bare_residual=clean(K610*bare61); assert bare_residual.todok()
    print('PASS true nullspace graph, source56 two-sided inverse, and rejected bare coordinate axes',flush=True)

    # Rebuild all five original modes from actual SpinPair/Gamma5 parameter paths.
    core=ROOT/'Lean/SaturationMonoid/PhysicsCore'
    text=(core/'Stage9C/Material/SpinPair/Spinor.lean').read_text()
    match=re.search(r'def spinPairCoefficients.*?:=\s*!!\[(.*?)\]',text,re.S);assert match
    upper,lower=s.symbols('upper lower',real=True)
    coefficient=s.Matrix([[s.sympify(v,locals={'upper':upper,'lower':lower}) for v in row.split(',')]
        for row in match.group(1).split(';')])
    prepared=s.Matrix(list(coefficient.subs({upper:1,lower:1}).row_join(s.zeros(4,1))))
    zero(prepared-s.Matrix(list(map(s.sympify,actual['actual_background']['primal_H']))))
    match=re.search(r'def diracGammaFive.*?:=\s*Matrix.diagonal\s*!\[(.*?)\]',
        (core/'DiracCliffordRepresentation.lean').read_text(),re.S);assert match
    signs=list(map(s.sympify,match.group(1).split(',')))
    eps=s.symbols('eps',real=True)
    axial=s.kronecker_product(s.diag(*[s.exp(-eps*v) for v in signs]),s.eye(3))
    phase=s.kronecker_product(s.diag(*[s.exp(-s.I*eps*v) for v in signs]),s.eye(3))
    dual=spin*prepared.T
    paths=[((1+eps)*prepared,dual/(1+eps)),(s.exp(s.I*eps)*prepared,s.exp(-s.I*eps)*dual),
        (axial*prepared,dual*axial),(phase*prepared,dual*phase),(prepared,(1+s.I*eps)*dual)]
    Z=s.zeros(289,5)
    for col,(primal,right) in enumerate(paths):
        vectors={'primal_H':primal.diff(eps).subs(eps,0),'dual_H':right.diff(eps).subs(eps,0)}
        for row,field in enumerate(actual['fields']):
            if field['group'] in vectors:
                realpart,sp,color=field['coordinate']
                Z[row,col]=(s.re if realpart==0 else s.im)(vectors[field['group']][3*sp+color])
    zero(Z-decode(modes['source_zero_modes_289']))
    Q0=s.SparseMatrix(103,112,{(i,j):s.sympify(v.replace('lambda','lam'),locals={'lam':lam,'k':k}).subs({lam:0,k:0})
        for i,j,v in quotient['quotient_readback_103_by_112']})
    coordinate=clean(s.diag(*[1/v for v in scales])*Q0*Z[9:121,:])
    light103=[retained.index(i) for i in frozen['light5_source_indices']]
    heavy103=[i for i in range(103) if i not in light103]
    chart=coordinate[light103,:]; determinant=norm(chart.det());assert determinant==4
    E103=clean(coordinate*chart.inv())
    K0=K.subs({u:0,q:0});zero(K0*E103);zero(E103[light103,:]-s.eye(5))
    A98=K0.extract(heavy103,heavy103);G98=clean(A98.inv(method='DM'))
    zero(A98*G98-s.eye(98));zero(G98*A98-s.eye(98))
    zero(chart-decode(modes['original_modes_in_light5']))
    print('PASS literal original five primal/independent-dual mode paths, faithful full graph and det4 chart',flush=True)

    # Fixed zero-graph congruence derives the 2jet without the candidate's recursive writeback.
    def feshbach(source,E,heavy,G0):
        linear=part(source,1); quadratic=part(source,2)
        left=clean(E.T*linear[:,heavy]);right=clean(linear[heavy,:]*E)
        first=clean(E.T*linear*E)
        second=clean(E.T*quadratic*E-left*G0*right)
        return clean(first+second)
    S61=feshbach(K61,E61,heavies,G56)
    S103=feshbach(K,E103,heavy103,G98)
    zero(S61-S103);zero(S103-decode(frozen['light5_degree2']))
    sourceS=clean(chart.T*S103*chart)
    zero(part(sourceS,1)-u*decode(modes['first_order_in_original_modes']))
    zero(part(sourceS,2)-decode(modes['second_order_in_original_modes']))
    # Generate the finite field jet from the fixed constant graph and source deltaK.
    K1=part(K,1);K2=part(K,2)
    V1=clean(-G98*K1[heavy103,:]*E103)
    V2=clean(-G98*K2[heavy103,:]*E103+G98*K1.extract(heavy103,heavy103)*G98*K1[heavy103,:]*E103)
    jet=E103.copy()
    for i,row in enumerate(heavy103):jet[row,:]+=V1[i,:]+V2[i,:]
    jet=clean(jet);zero(jet-decode(direct['direct103_field_jet']))
    momenta=[N*spin*u,0,0,s.I*spin*q]
    H=s.zeros(289,cls=s.SparseMatrix)
    for i,j,powers,value in actual['Fourier_Jacobi_entries']:
        H[i,j]+=s.sympify(value)*s.prod(p**a for p,a in zip(momenta,powers))
    H=clean(H)
    full=s.zeros(289,5,cls=s.SparseMatrix)
    for (i,j),value in jet.todok().items():full[retained[i],j]=scales[i]*value
    for step in reversed(actual['algebraic_Schur_steps']):
        values=s.zeros(289,5,cls=s.SparseMatrix)
        for i,j,powers,value in step['write_back_auxiliary_from_retained']:
            values[i,:]+=s.sympify(value)*s.prod(p**a for p,a in zip(momenta,powers))*full[j,:]
        for i in step['eliminated_fields']:full[i,:]=cut(values[i,:])
    full=clean(full);zero(full-decode(frozen['whole289_field_writeback_degree2']))
    zero(full.subs({u:0,q:0})*chart-Z)
    # Independent source injection: solve negative-momentum symmetry/Ward annihilators.
    T=s.zeros(112,9,cls=s.SparseMatrix)
    for i,j,powers,value in symmetry['source_symmetry_tangents_112']:
        T[i-9,j]+=s.sympify(value)*s.prod((-p)**a for p,a in zip(momenta,powers))
    T=clean(T);deleted=[i-9 for i in quotient['fixed_section_removed_original_fields']]
    selected=[i-9 for i in retained]
    raw=s.zeros(112,5,cls=s.SparseMatrix)
    for j,i in enumerate(light103):raw[retained[i]-9,j]=N/scales[i]
    missing=clean(-T.extract(deleted,range(9)).T.inv(method='DM')*T.extract(selected,range(9)).T*raw[selected,:])
    for row,i in enumerate(deleted):raw[i,:]=missing[row,:]
    zero(T.T*raw)
    broken=actual['Ward_constraint_elimination']['broken_parameter_columns'];Ward=s.zeros(121,9,cls=s.SparseMatrix)
    for i,j,powers,value in actual['source_primitive_gauge_tangent']:
        if i<121 and j in broken:Ward[i,broken.index(j)]+=s.sympify(value)*s.prod((-p)**a for p,a in zip(momenta,powers))
    Ward=clean(Ward);injection=s.zeros(289,5,cls=s.SparseMatrix);injection[9:121,:]=raw
    injection[:9,:]=clean(-Ward[:9,:].T.inv(method='DM')*Ward[9:,:].T*raw)
    zero(Ward.T*injection[:121,:]);zero(injection-decode(frozen['whole289_source_injection']))
    residual=clean(H*full-injection*S103)
    zero(cut(residual));assert minimum(residual)==3
    zero(residual-decode(frozen['whole289_exact_remainder']))
    print('PASS independent fixed-graph Feshbach jets, true all289 field return and independently constrained source injection',flush=True)

    # Full103 polynomial factors: multiply finite power-series coefficients, retaining
    # all lower orders instead of supplying their vanishing or a lowest-term formula.
    def series_product(weight,limit):
        output=[s.S.One]+[s.S.Zero]*limit
        for block in propagation['blocks']:
            output=[v*s.sympify(block['constant']) for v in output]
            for factor in block['factors']:
                poly=s.Poly(s.sympify(factor['polynomial'],locals={'u':u,'q':q}).subs({u:r*t**weight,q:t}),t)
                coefficients=[poly.nth(i) for i in range(limit+1)]
                for _ in range(factor['multiplicity']):
                    output=[s.expand(sum(output[j]*coefficients[i-j] for j in range(i+1))) for i in range(limit+1)]
        return output
    det98=norm(A98.det(method='domain-ge'));assert det98!=0
    ray=series_product(1,8);weighted=series_product(2,10)
    assert all(v==0 for v in ray[:8]) and all(v==0 for v in weighted[:10])
    raycoeff=s.factor(ray[8]/det98*determinant**2)
    weightedcoeff=s.factor(weighted[10]/det98*determinant**2)
    expect8=s.Rational(655360,537273)*r*r*(5+3*r*r)*(55+67*r*r)*(125-162*r*r)
    expect10=s.Rational(512000000,439587)*(36*r*r+25)
    zero(s.Matrix([raycoeff-expect8,weightedcoeff-expect10]))
    determinantS=s.factor(sourceS.det(method='domain-ge'))
    zero(s.Matrix([s.Poly(s.expand(determinantS.subs({u:r*t,q:t})),t).nth(8)-raycoeff,
        s.Poly(s.expand(determinantS.subs({u:r*t*t,q:t})),t).nth(10)-weightedcoeff]))
    assert s.factor(determinantS.subs(u,0))!=0
    print('PASS full103 determinant series first orders8/10, with source chart factor16 and static nonzero slow scale',flush=True)

    # Check the factor product and the genuine inverse against an exact nonzero point.
    at={u:s.Rational(1,7),q:s.Rational(1,11)}
    Kv=clean(K.subs(at));Dv=Kv.extract(heavy103,heavy103)
    dm=DomainMatrix.from_Matrix(Dv,extension=True).to_field();di=dm.inv()
    assert dm.matmul(di)==DomainMatrix.eye(dm.shape,dm.domain)
    assert di.matmul(dm)==DomainMatrix.eye(dm.shape,dm.domain)
    actual_inverse=clean(di.to_Matrix())
    L=K1.extract(heavy103,heavy103);Q=K2.extract(heavy103,heavy103)
    inversejet=clean(G98-G98*L*G98+G98*L*G98*L*G98-G98*Q*G98)
    rv=clean(Dv*inversejet.subs(at)-s.eye(98))
    zero(actual_inverse-inversejet.subs(at)+actual_inverse*rv)
    assert clean(actual_inverse-inversejet.subs(at)).todok()
    exactS=clean(Kv.extract(light103,light103)-Kv.extract(light103,heavy103)*actual_inverse*Kv.extract(heavy103,light103))
    true_remainder=clean(exactS-S103.subs(at));assert true_remainder.todok()
    block_determinants=s.S.One;factor_product=s.S.One
    all_factors=[]
    for block in propagation['blocks']:
        ids=block['quotient_indices']
        block_matrix=DomainMatrix.from_Matrix(Kv.extract(ids,ids),extension=True).to_field()
        block_determinants*=block_matrix.domain.to_sympy(block_matrix.det())
        block_factor=s.sympify(block['constant'])
        for factor in block['factors']:
            polynomial=s.sympify(factor['polynomial'],locals={'u':u,'q':q})
            all_factors.append(polynomial)
            block_factor*=polynomial.subs(at)**factor['multiplicity']
        factor_product*=block_factor
    zero(s.Matrix([block_determinants-factor_product,
        block_determinants-dm.domain.to_sympy(dm.det())*exactS.det(method='domain-ge')]))
    slopes=[s.I*s.sqrt(s.Rational(5,3)),s.I*s.sqrt(s.Rational(55,67)),s.sqrt(s.Rational(125,162))]
    controls=[]
    for val in slopes+[s.Rational(5,6)*s.I/s.Integer(11)]:
        point={u:val/s.Integer(11),q:s.Rational(1,11)}
        assert all(s.simplify(polynomial.subs(point))!=0 for polynomial in all_factors)
        controls.append({str(key):str(value) for key,value in point.items()})
    print('PASS genuine source98 inverse and full103 determinant; finite source differs from 2jet and none of four leading rays is an exact zero line',flush=True)

    # Original g00 row and independent opposite-momentum source.
    e00=next(i for i,v in enumerate(actual['fields']) if v=={'group':'coframe','coordinate':[0,0]})
    reader61=clean(-2*N*decode(back['whole289_low_field_lift'])[e00,:])
    origin_contact=norm((reader61[:,heavies]*G56*reader61[:,heavies].T)[0]/N)
    zero(s.Matrix([origin_contact-18*N/125]))
    reader=clean(-2*N*full[e00,:]*chart)
    zero(reader-decode(modes['metric_reader_original_modes_degree2']))
    coreids=[0,1,3];rho=part(reader,1)[:,coreids]
    forcing=clean(rho.subs({u:-u,q:-q},simultaneous=True).T)
    zero(rho-s.Matrix([[0,0,-36*u/25]]));zero(forcing-s.Matrix([0,0,36*u/25]))
    corematrix=part(sourceS,2).extract(coreids,coreids)
    solution=clean(corematrix.inv(method='DM')*forcing)
    rayresponse=norm(origin_contact+(rho*solution)[0]/N)
    target=18*N*(297*u*u-125*q*q)/(125*(162*u*u-125*q*q))
    zero(s.Matrix([rayresponse-target]))
    wrong_leg=norm(origin_contact+(rho*corematrix.inv(method='DM')*rho.T)[0]/N)
    assert norm(wrong_leg-rayresponse)!=0 and norm(rayresponse-origin_contact)!=0
    real_slopes=[norm(N*N*v*v) for v in slopes]
    assert real_slopes==[-s.Rational(18,25),-s.Rational(594,1675),s.Rational(1,3)]
    quadratic_slope=norm((N*spin/2*5*s.I/6)**2);assert quadratic_slope==-s.Rational(3,20)
    result={'status':'PASS','source_hashes_checked':len(actual['source_sha256']),
        'source61_rank':56,'full103_rank_at_origin':98,'true_null_graph_full_dimension':5,
        'bare_coordinate_axis_residual_count':len(bare_residual.todok()),
        'source_modes_generated_from_actual_primitive_paths':True,'source_chart_determinant':str(determinant),
        'all289_origin_modes_recovered':True,'independent_2jet_method':'fixed zero-graph congruence and Feshbach second variation',
        'two_routes_61_and103_same':True,'all289_field_and_independent_source_injection':True,
        'full289_remainder_nonzero_entries':len(residual.todok()),'full289_remainder_minimum_degree':minimum(residual),
        'source_degree8_characteristic_on_ray':str(raycoeff),'source_degree10_characteristic':str(weightedcoeff),
        'original_full103_factors_rechecked_at_new_point':True,'genuine_inverse_differs_from_quadratic_jet':True,
        'genuine_light_kernel_differs_from_quadratic_jet':len(true_remainder.todok()),
        'finite_nonzero_source_points_on_leading_rays':controls,'g00_contact':str(origin_contact),
        'g00_first_reader':encode(rho),'g00_reverse_source':encode(forcing),'g00_leading_response':str(s.factor(rayresponse)),
        'wrong_same_sign_source_rejected':True,'clock_linear_lambda2_per_k2':list(map(str,real_slopes)),
        'clock_quadratic_lambda2_per_k4':str(quadratic_slope),'scope':'original axial source; exact low-momentum coefficients, not finite-momentum exact zero lines',
        'seconds':round(time.monotonic()-START,3)}
    (HERE/'independent-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)


if __name__=='__main__':main()
