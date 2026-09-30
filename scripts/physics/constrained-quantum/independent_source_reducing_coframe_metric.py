#!/usr/bin/env python3
"""Raw-BF audit of the source-normalized complete coframe Fock metric.

No new metric producer is imported. The original primary solve, epsilon
Hessian and live derivatives regenerate every coefficient. Formal adjoints
are collected by integration by parts, and literal differentiation of an
inverse half density checks the full two-particle CAR action.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_coframe_live_ordering import (
    RawLiveCoefficients, HERE, ROOT, ROOT_ID, FREE, rational, eq, full,
    polynomial_action, terms, current, state_encode)
from independent_source_gauge_legendre import bindings, decode, encode
from independent_source_gauss_quantum_current import decoded_state
from independent_source_gauss_section_measure import RawSectionMeasure


def zero(value): assert s.cancel(s.expand(value)) == 0

def state_equal(left, right): assert terms([(1,left),(-1,right)]) == {}


def coefficient_audit(raw, candidate, carrier):
    q,K=raw.q,raw.K
    eq(K,K.T);eq(K,K.conjugate())
    inverse=rational(K.inv(method='DM'));eq(K*inverse,s.eye(6));eq(inverse*K,s.eye(6))
    volume=q[0]*q[2]*q[5]
    gradient=s.Matrix([s.diff(volume,y)/volume for y in q])
    second=gradient.jacobian(q)
    drift=rational(s.I*raw.drift.T)
    divK=rational(s.Matrix([sum(s.diff(K[i,j],q[i])for i in range(6))for j in range(6)]))
    # Recover the number drift directly from the trace of the full spin8
    # anti-Hermitian mixed coefficient, before referring to a metric ansatz.
    t=rational(s.Matrix([s.trace(M.H-M)/(16*s.I)for M in raw.M]))
    hermitian=[]
    for j,M in enumerate(raw.M):
        eq(M.H-M,2*s.I*t[j]*s.eye(8))
        value=rational((M+M.H)/2)
        eq(value.H,value);eq(M,value-s.I*t[j]*s.eye(8))
        hermitian.append(value)
    eq(t,K*gradient);eq(drift-divK,2*t)
    eq(t,raw.N*s.Matrix(q)/(4*volume))
    # Kronecker rows are (i,k), columns(j,l), unlike the candidate's
    # flattened two-current-slot layout. Hermitian conjugation here checks
    # every original ordered normal-product coefficient at once.
    tensor=rational(sum((weight*s.kronecker_product(raw.J[a],raw.J[b])
                         for (a,b),weight in raw.W.todok().items()),s.zeros(64)))
    eq(tensor.H,tensor)
    assert len(tensor.todok())==candidate['source_metric_producer']['full_normal_current_tensor_nonzero_entries']
    eq(raw.one_body.H,raw.one_body);eq(raw.correction.H,raw.correction)
    zero(s.im(3*raw.e.det()))
    divM=rational(sum((M.diff(q[j])for j,M in enumerate(hermitian)),s.zeros(8)))
    contracted=rational(sum((gradient[j]*M for j,M in enumerate(hermitian)),s.zeros(8)))
    eq(divM,s.zeros(8));eq(contracted,s.zeros(8))
    for actual,saved in zip(hermitian,candidate['source_metric_producer']['Hermitian_mixed_matrices']):
        eq(actual,decode(saved,{str(v):v for v in q}))
    eq(t,decode(candidate['source_metric_producer']['mixed_scalar_anti_Hermitian_part'],{str(v):v for v in q}))

    number=s.Symbol('particle_number',integer=True,nonnegative=True)
    effective=drift+number*t
    # The first-order formal-adjoint equation uniquely generates d(log w).
    log_weight_gradient=rational(inverse*(effective-divK))
    eq(log_weight_gradient,(number+2)*gradient)
    for i in range(6):
        for j in range(6):zero(s.diff(log_weight_gradient[i],q[j])-s.diff(log_weight_gradient[j],q[i]))
    weight=volume**(number+2)
    for j in range(6):zero(s.diff(weight,q[j])/weight-log_weight_gradient[j])
    source=dict(zip(q,(raw.e0[i]for i in FREE)))
    assert s.simplify(weight.subs(source))==1
    assert all(q[j].is_positive for j in (0,2,5))

    # Full integration-by-parts coefficients in the generated weight.
    # Weighted divergence of K pays both the first-order and scalar terms;
    # weighted divergence of all Hermitian mixed currents is zero.
    first_adjoint=rational(-2*(divK+K*log_weight_gradient)+effective)
    eq(first_adjoint,-effective)
    second_div=sum(s.diff(s.diff(K[i,j],q[i]),q[j])+
        log_weight_gradient[j]*s.diff(K[i,j],q[i])+
        log_weight_gradient[i]*s.diff(K[i,j],q[j])+
        (s.diff(log_weight_gradient[i],q[j])+log_weight_gradient[i]*log_weight_gradient[j])*K[i,j]
        for i in range(6)for j in range(6))
    first_div=sum(s.diff(effective[j],q[j])+log_weight_gradient[j]*effective[j]for j in range(6))
    zero(first_div-second_div)
    eq(rational(divM+sum((log_weight_gradient[j]*M for j,M in enumerate(hermitian)),s.zeros(8))),s.zeros(8))
    alpha=(number+2)/2
    deltaV=s.cancel(alpha*(effective.T*gradient)[0]-alpha**2*(gradient.T*K*gradient)[0]+
        alpha*sum(K[i,j]*second[i,j]for i in range(6)for j in range(6)))
    zero(deltaV-3*raw.N*(number+2)*(number+4)/(16*volume))
    zero(deltaV-s.sympify(candidate['half_density_readback']['generated_real_shift'],locals={str(v):v for v in (*q,number)}))
    eq(effective-2*alpha*K*gradient,divK)
    for J in raw.J:
        A=full(J)
        for (i,j),value in A.todok().items():zero((carrier[i,i]-carrier[j,j])*value)
    for word in ((),(7,),(7,71),(7,71,134)):
        state_equal(current(s.eye(504),{word:1}),{word:s.Integer(len(word))})
    return {'volume':volume,'gradient':gradient,'second':second,'number':number,'weight':weight,
        'effective':effective,'t':t,'divK':divK,'hermitian':hermitian,'deltaV':deltaV,
        'report':{'source_fixed_time':list(map(str,raw.e0[:,0])),
            'raw_BF_primary_and_live_sixq_coefficients':True,'kinetic_two_sided_inverse':True,
            'full_spin8_mixed_scalar_antiadjoint_recovered_from_trace':encode(t),
            'whole_normal_product_Kronecker_tensor_Hermitian':True,'tensor_nonzero_entries':len(tensor.todok()),
            'onebody_live_correction_and_source_potential_Hermitian':True,
            'both_full_Hermitian_mixed_divergences_zero':True,
            'metric_from_formal_adjoint_equation':str(weight),
            'all_coframe_formal_adjoint_second_first_and_zeroth_coefficients_match':True,
            'positive_and_source_weight_one':'q0,q2,q5>0 implies v>0 and W_m>0; at the literal source all three diagonal q entries are1.',
            'uniqueness_scope':'Among coframe-only number-sector scalar weights, invertible K fixes dlogW and source normalization fixes its constant on the connected chart. The corresponding matrix transport has identity as its unique source-connected solution. Factors depending on scalar/gauge variables are not fixed by this calculation.',
            'generated_real_half_density_shift':str(deltaV),
            'all_original24_current_coefficients_preserve_the_source392_carrier':True}}


def actual_half_density(raw, coefficients, candidate, carrier):
    saved=candidate['actual_fullCAR_consumer']
    qpoint=tuple(map(s.sympify,saved['full_six_q_point']));word=tuple(saved['input_CAR']);number=len(word)
    assert all(carrier[j,j]==1 for j in word)
    data=raw.coefficients(qpoint)
    gradient=decode(saved['original_gradient']);Hessian=decode(saved['original_Hessian'])
    x=s.Matrix(s.symbols('audit_increment0:6',real=True));origin=dict.fromkeys(x,0)
    f=1+(gradient.T*x)[0]+(x.T*Hessian*x)[0]/2
    # Differentiate the actual local inverse half-density multiplier rather
    # than reuse the producer's pre-expanded product-rule jet formulas.
    v0=qpoint[0]*qpoint[2]*qpoint[5]
    volume=(qpoint[0]+x[0])*(qpoint[2]+x[2])*(qpoint[5]+x[5])
    alpha=s.Rational(number+2,2)
    transformed=(v0/volume)**alpha*f
    g=rational(s.Matrix([s.diff(transformed,y).subs(origin)for y in x]))
    h=rational(s.hessian(transformed,list(x)).subs(origin))
    eq(g,decode(saved['normalized_U_inverse_gradient']));eq(h,decode(saved['normalized_U_inverse_Hessian']))
    actual,pieces=polynomial_action(data,word,1,g,h)
    state_equal(actual,decoded_state(saved['actual_U_H_U_inverse_image']))
    C,_=polynomial_action(data,word,1,s.zeros(6,1),s.zeros(6))
    point=dict(zip(raw.q,qpoint));divK=coefficients['divK'].subs(point)
    shift=s.simplify(coefficients['deltaV'].subs(coefficients['number'],number).subs(point))
    scalar=-s.trace(data['K']*Hessian)-(divK.T*gradient)[0]+shift
    expected=terms([(1,C),(scalar,{word:1})]+[(-s.I*gradient[j],current(full(rational(M.subs(point))),{word:1}))
        for j,M in enumerate(coefficients['hermitian'])])
    state_equal(actual,expected)
    state_equal(expected,decoded_state(saved['independent_divergence_plus_Hermitian_current_image']))
    original,_=polynomial_action(data,word,1,gradient,Hessian)
    defect=terms([(1,actual),(-1,original)]);assert defect
    assert len(actual)>1 and all(len(w)==number and all(carrier[i,i]==1 for i in w)for w in actual)
    assert shift==s.sympify(saved['source_generated_real_potential_shift'])==144*s.sqrt(30)/385
    return {'literal_inverse_half_density_polynomial_differentiation':True,
        'independent_exterior_slot_CAR_and_whole_normal_products':True,
        'input_CAR':list(word),'full_output':state_encode(actual),
        'real_shift':str(shift),'original_and_conjugated_operators_differ':state_encode(defect),
        'whole_output_stays_in_the_generated392_carrier':True}


def measure_transport(raw, coefficients):
    measure=RawSectionMeasure();section=measure.section
    for L in section.T:eq(L[:6,:],s.zeros(6,103));eq(L[:,:6],s.zeros(103,6))
    alpha=section.source_minor.inv()*section.reader
    eq(alpha[:,:6],s.zeros(3,6))
    for q in raw.q:zero(s.diff(measure.density,q))
    v=s.Symbol('positive_volume',positive=True)
    m=s.Symbol('m',integer=True,nonnegative=True)
    W=lambda n:v**(n+2)
    U=lambda n:v**(1+n/2)
    zero(W(m-1)/W(m)-1/v)
    zero(U(m-1)*s.sqrt(v)/U(m)-1)
    zero(U(m+1)/(s.sqrt(v)*U(m))-1)
    zero(U(m)**2-W(m))
    return {'original_rho_remains_q_independent':True,
        'original_Gauss_group_and_extension_leave_all_sixq_unchanged':True,
        'number_sector_weight_and_half_density_commute_with_Gauss_and_reducing_projection':True,
        'actual_CAR_adjoint_and_isometric_readbacks':True,
        'pairing':'Integral rho(z) v(q)^(m+2) inner(f_m,g_m) dz on each number sector; U=v^(1+m/2) transports it to the existing rho pairing.',
        'other_operators':'Scalar/gauge operators differentiate x/A only and their CAR currents preserve Number. Thus W and U commute with them; their existing rho-adjoint conditions are transported, not established here.',
        'unchanged_authority':'The existing residual3 orbit density rho is retained. No Y-adjoint, independent normalization constant or full selfadjoint Hamiltonian is introduced.'}


def main():
    started=time.monotonic();path=HERE/'source_reducing_coframe_metric.json'
    candidate=json.loads(path.read_text());count=bindings(candidate);assert candidate['root']==ROOT_ID
    paid=['source_yukawa_reducing_carrier.json','independent_source_yukawa_reducing_carrier.json',
        'independent_source_coframe_live_ordering.json','independent_source_gauss_section_measure.json',
        'independent_source_quantum_gauss_section.json']
    records={name:json.loads((HERE/name).read_text())for name in paid}
    for value in records.values():count+=bindings(value)
    carrier=decode(records['source_yukawa_reducing_carrier.json']['generated_reducing_projector_real504'])
    eq(carrier,carrier.H);eq(carrier*carrier,carrier);assert s.trace(carrier)==392
    raw=RawLiveCoefficients()
    coefficients=coefficient_audit(raw,candidate,carrier)
    print('PASS raw full-sixq/spin8/normal-product formal adjoint and source-generated positive Fock metric',flush=True)
    actual=actual_half_density(raw,coefficients,candidate,carrier)
    print('PASS literal half-density differentiation and fullCAR coframe action with generated real DeltaV',flush=True)
    transport=measure_transport(raw,coefficients)
    paths=[Path(__file__),path,HERE/'source_reducing_coframe_metric.py',HERE/'independent_source_coframe_live_ordering.py',
        HERE/'independent_source_gauss_section_measure.py',HERE/'independent_source_quantum_gauss_section.py']+[HERE/name for name in paid]
    output={'verdict':'CERTIFIED_SOURCE_POSITIVE_COFRAME_FOCK_METRIC_AND_COMPLETE_FIXED_TIME_FORMAL_SYMMETRY',
        'root':ROOT_ID,'source_sha256':candidate['source_sha256'],
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths},
        'source_binding_checks':count,'new_metric_producer_imported':False,
        'complete_coefficients':coefficients['report'],'actual_fullCAR_readback':actual,'measure_and_other_components':transport,
        'certified_scope':'Literal fixed y_source=(N,0,0,0), every sixq point in the positive source chart, the complete coframe operator and its generated392 Fock consumer. Full scalar/gauge adjoint conditions remain separate.',
        'full_Hamiltonian_selfadjointness_propagator_spectrum_or_lifetime_generated':False,
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'independent_source_reducing_coframe_metric.json').write_text(json.dumps(output,separators=(',',':'))+'\n')
    print('PASS independent positive coframe Fock metric',output['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
