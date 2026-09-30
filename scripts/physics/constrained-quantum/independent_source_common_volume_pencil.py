#!/usr/bin/env python3
"""Original-density audit of the full five-weight coframe dilation pencil.

No candidate constructor is imported. Independent original BF/Dirac readers,
all97 scalar divergence coefficients, and implicit Gauss jets generate the
full scaled action without crossing a coefficient-string boundary.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_joint_form_hamiltonian import (
    RawGaussSection, RawLiveCoefficients, HERE, ROOT, ROOT_ID, bindings, rational,
    eq, decode, encode, terms, current, state_encode, decoded_state, zero,
    state_equal, raw_gauge_coefficients, whole_action)
from independent_source_quantum_ordered_temporal import raw_coframe_family
from independent_source_scalar_form_hamiltonian import raw_coefficients
from independent_source_scalar_temporal_form import at, reclock_scalar
from independent_source_common_hamiltonian import raw_matter, original_inventory
from independent_source_full_quantum_adjoint import sparse, dual_pair
from independent_source_gauge_legendre import ETA, SIGMA

POWERS=(-3,-1,0,1,3)


def coefficient_audit(raw, e, cf, ys, scale, candidate):
    q=raw.q; change=dict(zip(q,(scale*z for z in q))); records=[]
    def homogeneous(name,matrix,degree,order=0):
        A=s.Matrix(matrix)
        eq(rational(A.subs(change,simultaneous=True)),scale**degree*A)
        # A separate infinitesimal readback pays the virial convention.
        eq(rational(sum((x*A.diff(x) for x in q),s.zeros(*A.shape))),degree*A)
        records.append({'coefficient':name,'degree':degree,'coframe_derivative_order':order,
            'operator_degree':degree-order,'nonzero_entries':len(A.todok())})
    homogeneous('coframe_principal',cf['K'],-1,2)
    homogeneous('coframe_live_drift',cf['drift'],-2,1)
    for j,M in enumerate(cf['M']): homogeneous('coframe_mixed_'+str(j),M,-2,1)
    homogeneous('coframe_onebody',cf['one_body'],-3)
    homogeneous('coframe_live_correction',cf['correction'],-3)
    # Build the ordered slots first, then compare the flattened current tensor.
    pair=s.MutableSparseMatrix.zeros(64,64)
    for (a,b),weight in cf['W'].todok().items():
        for (i,j),left in cf['J'][a].todok().items():
            for (k,l),right in cf['J'][b].todok().items(): pair[8*i+j,8*k+l]+=weight*left*right
    homogeneous('coframe_ordered_two_current',rational(pair),-3)
    homogeneous('coframe_volume_potential',[[cf['constant']]],3)
    metric=rational(e.det()*(e.T*ETA*e).inv())
    homogeneous('scalar_nested_momentum_weight',[[1/(2*metric[0,0])]],-3)
    homogeneous('scalar_ordered_shift_weights',rational(metric[0,1:]/metric[0,0]),-1)
    homogeneous('scalar_spatial_weights',rational(metric[1:,0]*metric[0,1:]/metric[0,0]-metric[1:,1:]),1)
    homogeneous('scalar_vacuum_potential_weight',[[e.det()]],3)
    # Four-index metric contraction, independently of the candidate Hodge API.
    gram=e.T*ETA*e; pairs=((0,1),(0,2),(0,3),(2,3),(3,1),(1,2))
    K=rational(s.Matrix(6,6,lambda i,j:-(gram[pairs[i][0],pairs[j][0]]*gram[pairs[i][1],pairs[j][1]]-
        gram[pairs[i][0],pairs[j][1]]*gram[pairs[i][1],pairs[j][0]])/(SIGMA*e.det())))
    eq(K.T,K)
    electric=K[:3,:3]; inverse=rational(electric.inv(method='DM')); eq(electric*inverse,s.eye(3))
    for name,A,degree in [('electric',electric,-1),('electric_inverse',inverse,1),
                         ('mixed',K[:3,3:],0),('magnetic',K[3:,3:],1)]:
        homogeneous('original_BF_'+name,A,degree)
    gamma=original_inventory()['gamma']; inverse_e=e.inv()
    D=[rational(s.I*e.det()*sum((inverse_e[mu,a]*gamma[a] for a in range(4)),s.zeros(4))) for mu in range(4)]
    Ei=D[0].inv(); eq(D[0]*Ei,s.eye(4))
    for i in (1,2,3): homogeneous('matter_spatial_'+str(i),rational(Ei*D[i]),-1)
    homogeneous('original_Yukawa_weight',rational(-s.I*e.det()*Ei),0)
    # Exact source family parameters are held fixed by the dilation. Their
    # derivatives therefore preserve each coefficient's degree as well.
    for A,degree in [(cf['K'],-1),(metric[0,1:]/metric[0,0],-1),(inverse,1),(-s.I*e.det()*Ei,0)]:
        for y in ys:
            derivative=rational(A.diff(y))
            eq(rational(derivative.subs(change,simultaneous=True)),scale**degree*derivative)
    assert records==candidate['generic_source_coefficient_laws']
    return records


def pairing_audit(section,raw,scale):
    m=s.Symbol('occupation_number',integer=True,nonnegative=True)
    z=s.Matrix(s.symbols('common_slice0:100',real=True))
    point=section.free_reader.T*z+section.reader.T*section.reader*section.source
    orbit=s.Matrix.hstack(*(T*point for T in section.T))
    determinant=s.factor((section.reader*orbit).det())
    rho=s.sign(section.source_minor.det())*determinant
    assert rho!=0
    assert all(s.diff(rho,z[i])==0 for i in range(6))
    # Native residual gauge generators fix all six coframe coordinates.
    for T in section.T:
        eq(T[:6,:],s.zeros(6,103)); eq(T[:,:6],s.zeros(103,6))
    q=raw.q; volume=q[0]*q[2]*q[5]; scaled=dict(zip(q,(scale*x for x in q)))
    zero(s.simplify(s.sqrt(volume).subs(scaled,simultaneous=True)-scale**s.Rational(3,2)*s.sqrt(volume)))
    for component in q:
        zero(s.simplify((component/volume**s.Rational(1,3)).subs(scaled,simultaneous=True)-component/volume**s.Rational(1,3)))
    exponent=s.Rational(3,2)*m+6
    zero(2*exponent-6-3*(m+2))
    zero(exponent-s.Rational(3,2)*(m+s.Rational(7,2))-s.Rational(3,4))
    # The radial generator also fixes the sign in i[D,H].
    r=s.Symbol('volume_radius',positive=True); f=s.Function('test')(r)
    zero(s.simplify((s.diff(scale**s.Rational(3,4)*f.subs(r,scale**s.Rational(3,2)*r),scale).subs(scale,1)-
        (s.Rational(3,2)*r*s.diff(f,r)+s.Rational(3,4)*f)).doit()))
    return {'native_residual_density':str(rho),'coframe_density_derivatives_all_zero':True,
        'occupation_exponent':str(exponent),'radial_exponent':'3/4',
        'generator':'D=-i*(3/2*r*partial_r+3/4); d/d(log lambda) U_lambda|1=iD',
        'native_all3_Gauss_generators_fix_coframe':True}


def split_state(state,scale):
    output={p:{} for p in POWERS}
    for word,expression in state.items():
        # Laurent coefficients by derivatives at zero of lambda^3 H, rather
        # than the candidate's term enumeration.
        polynomial=s.cancel(scale**3*expression)
        assert s.denom(polynomial).free_symbols.isdisjoint({scale})
        for k in range(7):
            coefficient=s.cancel(s.diff(polynomial,scale,k).subs(scale,0)/s.factorial(k))
            if coefficient:
                assert k-3 in POWERS
                output[k-3][word]=coefficient
        zero(polynomial-sum(scale**(p+3)*values.get(word,0) for p,values in output.items()))
    return output


def actual_audit(section,raw,e,cf,ys,scale,candidate):
    prior=json.loads((HERE/'source_common_temporal_form.json').read_text()); count=bindings(prior)
    saved=prior['actual_consumer']; target=candidate['actual_consumer']
    q=tuple(map(s.sympify,saved['q'])); clock=tuple(map(s.sympify,saved['time']))
    x,A=decode(saved['x61']),decode(saved['A36']); word=tuple(saved['input_CAR'])
    assert word==(144,396) and all(clock[1:])
    assert target['time_column']==list(map(str,clock)) and target['q']==list(map(str,q))
    eq(decode(target['x61']),x); eq(decode(target['A36']),A)
    gradient,Hessian=decode(saved['gradient100']),decode(saved['Hessian100'])
    point=s.Matrix(q).col_join(x).col_join(A.reshape(36,1))
    _,base=section.extension_jet(point,{word:1},{word:gradient},{word:Hessian})
    section.Gauss_checks(point,base)
    scale_pullback=s.diag(*([1/scale]*6+[1]*97))
    jets={w:[f,scale_pullback*g,scale_pullback*h*scale_pullback] for w,(f,g,h) in base.items()}
    scaled_point=s.Matrix([scale*t for t in q]).col_join(x).col_join(A.reshape(36,1))
    gauss=section.Gauss_checks(scaled_point,jets)
    assert target['Gauss']['all3_Gauss_values_zero'] and gauss['all3_original_Gauss_values_zero']
    assert target['Gauss']['all309_first_derivatives_of_Gauss_zero'] and gauss['all309_first_derivatives_of_Gauss_zero']
    assert target['Gauss']['all103_by103_Hessian_entries_retained']
    assert all(g.shape==(103,1) and h.shape==(103,103) for _,g,h in jets.values())
    original_sub={**dict(zip(raw.q,q)),**dict(zip(ys,clock))}
    scaled_sub={**dict(zip(raw.q,(scale*t for t in q))),**dict(zip(ys,clock))}
    ee=at(e,scaled_sub); cf_scaled={key:at(value,scaled_sub) for key,value in cf.items()}
    initial_scalar=raw_coefficients(section.native,at(e,original_sub),x,A)
    scalar=reclock_scalar(section.native,initial_scalar,ee,A)
    gauge=raw_gauge_coefficients(ee,A,section.native)
    connection=s.zeros(4,12); connection[1:,:]=A
    matter=raw_matter(ee,scalar['phi'],connection)
    inventory=original_inventory(); gamma=inventory['gamma']
    M=dual_pair(rational(-s.I*matter['E_inverse']*matter['lower']))
    rawY=sum(((scalar['phi'][j]+s.I*scalar['phi'][j+35])*inventory['scalar'][j] for j in range(35)),s.zeros(252))
    Y=dual_pair(sparse(s.kronecker_product(clock[0]*gamma[0],s.eye(63)))*sparse(rawY))
    assert scale not in Y.free_symbols
    M0=sparse(M-Y); eq(M0.H,M0)
    pieces,H0=whole_action(dict(coframe=cf_scaled,scalar=scalar,gauge=gauge,matter=M0),jets)
    pieces['matter_noY']=pieces.pop('matter_without_Lorentz')
    values={w:row[0] for w,row in jets.items() if row[0]}
    pieces['original_Y']=current(Y,values)
    assert pieces['original_Y']; assert terms([(1,pieces['original_Y']),(-1,current(Y.H,values))])
    allowed={'coframe':{-3,3},'scalar_form':{-3,-1,1,3},'gauge':{1},'matter_noY':{-1},'original_Y':{0}}
    component_weights={}
    for name,image in pieces.items():
        assert image
        component_weights[name]=split_state(image,scale)
        for degree,coefficient in component_weights[name].items():
            assert not coefficient or degree in allowed[name]
            state_equal(coefficient,decoded_state(target['original_component_weights'][name][str(degree)]))
    whole=terms((1,image) for image in pieces.values())
    weights=split_state(whole,scale)
    assert all(weights.values())
    for p,image in weights.items(): state_equal(image,decoded_state(target['full_H_weights'][str(p)]))
    state_equal(pieces['original_Y'],decoded_state(target['original_Y']))
    source_value={w:s.cancel(v.subs(scale,1)) for w,v in whole.items()}
    state_equal(source_value,decoded_state(saved['positive_H']))
    derivative={w:s.cancel(s.diff(v,scale).subs(scale,1)) for w,v in whole.items()}
    virial=terms((p,image) for p,image in weights.items())
    state_equal(derivative,virial); state_equal(virial,decoded_state(target['exact_dilation_derivative']))
    assert virial
    return {'source_binding_checks':count,'Gauss':gauss,'original_component_weights':
        {name:{str(p):state_encode(image) for p,image in row.items()} for name,row in component_weights.items()},
        'full_H_weights':{str(p):state_encode(image) for p,image in weights.items()},
        'original_Y':state_encode(pieces['original_Y']),'exact_dilation_derivative':state_encode(virial),
        'source_scale_one_readback':True,'all_five_weights_nonzero':True,'original_Y_differs_from_its_adjoint_on_actual_N2':True}


def main():
    started=time.monotonic(); path=HERE/'source_common_volume_pencil.json'
    candidate=json.loads(path.read_text()); count=bindings(candidate); assert candidate['root']==ROOT_ID
    section,raw=RawGaussSection(),RawLiveCoefficients()
    assert section.native.hashes==candidate['source_sha256']
    ys=(s.Symbol('quantum_n',positive=True),*s.symbols('quantum_b1:4',real=True))
    e,cf=raw_coframe_family(raw,ys); scale=s.Symbol('coframe_dilation',positive=True)
    generic=coefficient_audit(raw,e,cf,ys,scale,candidate)
    pairing=pairing_audit(section,raw,scale)
    print('PASS independent all-q/all-four-time dilation coefficients, native rho3 and exact radial unitary/generator sign',flush=True)
    actual=actual_audit(section,raw,e,cf,ys,scale,candidate)
    print('PASS complete raw Gauss/CAR action, all five original weights, non-Hermitian Y and exact weak virial',flush=True)
    files=[Path(__file__),path,HERE/'source_common_volume_pencil.py',HERE/'source_common_temporal_form.json']+[HERE/name for name in (
        'independent_source_joint_form_hamiltonian.py','independent_source_quantum_ordered_temporal.py',
        'independent_source_scalar_form_hamiltonian.py','independent_source_scalar_temporal_form.py',
        'independent_source_common_hamiltonian.py','independent_source_full_quantum_adjoint.py',
        'independent_source_quantum_gauss_section.py','independent_source_gauge_legendre.py')]
    result={'verdict':'CERTIFIED_ORIGINAL_COMMON_LOCAL_QUANTUM_FIVE_WEIGHT_UNITARY_COFRAME_DILATION_PENCIL',
        'root':ROOT_ID,'candidate_constructor_imported':False,'source_sha256':section.native.hashes,
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'source_binding_checks':count+actual['source_binding_checks'],
        'independent_method':'raw epsilon-Hessian/primary graph, four-index BF metric contraction, original Dirac density; complete97 scalar divergence and independent implicit103 Gauss jets; Laurent derivatives at zero; native residual determinant',
        'generic_source_coefficient_laws':generic,'native_pairing':pairing,'actual_consumer':actual,
        'exact_family':'U_lambda H U_lambda^-1=sum(p in {-3,-1,0,1,3}) lambda^p H_p',
        'exact_weak_virial':'i[D,H]=sum p H_p on the compact smooth common core; derivative is with respect to log(lambda)',
        'configuration_semantics':'Positive dilation of the six coframe configuration variables only; not a spacetime dilation.',
        'time_derivative_scope':'U_lambda is independent of the four temporal parameters, hence the exact homogeneous family differentiates to the same weights of each original F_a=-partial_y_a H.',
        'clock_solution_spectral_measure_or_lifetime_generated':False,'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'independent_source_common_volume_pencil.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS independent source common volume pencil',result['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__': main()
