#!/usr/bin/env python3
"""Source-generated positive Fock metric for the complete live coframe operator.

The original mixed currents have a scalar anti-Hermitian part proportional
to particle number. The full formal-adjoint equation therefore generates
v^(2+Number), not only the vacuum weight v^2. No operator is symmetrized:
the original coframe Hamiltonian is retained, with its source-normalized
positive candidate pairing and exact half-density representation supplied.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from dynamic import HERE,ROOT,ROOT_ID,decode
from source_gauss_section_measure import SourceGaussSectionMeasure
from source_coframe_live_ordering import full,verify_jet_action
from source_coframe_legendre import rational
from source_lorentz_contact import equal,encode
from source_gauss_quantum_current import apply_superposition,weighted_sum,encode_state
from source_quantum_temporal_symbol import N


def zero(value): assert s.cancel(value)==0


def complete_coefficients(model):
    c=model.section.native.joint.coframe;q=c.q
    volume=q[0]*q[2]*q[5]
    g=s.Matrix([1/q[0],0,1/q[2],0,0,1/q[5]])
    Hessian=g.jacobian(q)
    K=c.K;D=rational(s.I*c.drift.T)
    divergence=rational(s.Matrix([sum(s.diff(K[i,j],q[i])for i in range(6))for j in range(6)]))
    t=rational(K*g)
    equal(rational(t-N*s.Matrix(q)/(4*volume)),s.zeros(6,1))
    equal(rational(D-divergence-2*t),s.zeros(6,1))
    hermitian=[]
    for j,M in enumerate(c.M):
        equal(rational(M.H-M-2*s.I*t[j]*s.eye(8)),s.zeros(8))
        Mh=rational(M+s.I*t[j]*s.eye(8))
        equal(Mh.H,Mh)
        hermitian.append(Mh)
    equal(rational(sum((hermitian[j].diff(q[j])for j in range(6)),s.zeros(8))),s.zeros(8))
    equal(rational(sum((g[j]*hermitian[j]for j in range(6)),s.zeros(8))),s.zeros(8))
    # All ordered normal-current coefficients, including the two independent
    # real branches and both current slots, are checked before any Fock state.
    flat=s.Matrix.hstack(*(J.reshape(64,1)for J in c.J))
    tensor=rational(flat*c.W*flat.T)
    transpose_indices=[8*j+i for i in range(8)for j in range(8)]
    adjoint=tensor.conjugate().extract(transpose_indices,transpose_indices)
    equal(rational(adjoint-tensor),s.zeros(64))
    equal(c.one_body.H,c.one_body);equal(c.correction.H,c.correction)
    m=s.Symbol('particle_number',integer=True,nonnegative=True)
    alpha=(m+2)/2
    effective_D=rational(D+m*t)
    equal(rational(effective_D-divergence-(m+2)*K*g),s.zeros(6,1))
    weight=volume**(m+2)
    for j in range(6):zero(s.diff(weight,q[j])/weight-(m+2)*g[j])
    source=dict(zip(q,(c.e0[j]for j in(5,9,10,13,14,15))))
    assert s.simplify(weight.subs(source))==1
    # Original coefficient-left operator conjugated by U=v^(1+m/2).
    # The result keeps every normal product and adds this real scalar term.
    potential=s.cancel(alpha*(effective_D.T*g)[0]-alpha**2*(g.T*K*g)[0]+
                       alpha*sum(K[i,j]*Hessian[i,j]for i in range(6)for j in range(6)))
    zero(potential-3*N*(m+2)*(m+4)/(16*volume))
    equal(rational(effective_D-2*alpha*K*g-divergence),s.zeros(6,1))
    return {'q':q,'volume':volume,'g':g,'Hessian':Hessian,'D':D,'divergence':divergence,
            't':t,'hermitian':hermitian,'tensor':tensor,'m':m,'alpha':alpha,
            'weight':weight,'effective_D':effective_D,'potential':potential}


def actual_half_density(model,coefficients):
    c=model.section.native.joint.coframe
    carrier=json.loads((HERE/'source_yukawa_reducing_carrier.json').read_text())
    P=decode(carrier['generated_reducing_projector_real504'])
    word=(7,71)
    assert all(P[i,i]==1 for i in word)
    q=(s.Rational(7,6),s.Rational(1,11),s.Rational(9,8),s.Rational(-1,13),s.Rational(1,17),s.Rational(11,10))
    data=c.coefficients(q);sub=dict(zip(c.q,q));m=len(word);alpha=s.Rational(m+2,2)
    g=coefficients['g'].subs(sub);d2=coefficients['Hessian'].subs(sub)
    gradient=s.Matrix([s.I*s.Rational(j+1,17)for j in range(6)])
    direction=s.Matrix([s.Rational(j%3-1,19)for j in range(6)])
    Hessian=direction*direction.T-s.eye(6)
    transformed_gradient=gradient-alpha*g
    transformed_Hessian=Hessian-alpha*(g*gradient.T+gradient*g.T)+alpha**2*g*g.T-alpha*d2
    direct=verify_jet_action(data,word,1,transformed_gradient,transformed_Hessian)
    actual={tuple(w):s.sympify(v)for w,v in direct['raw_nested_square']}
    zeroth=verify_jet_action(data,word,1,s.zeros(6,1),s.zeros(6))
    potential={tuple(w):s.sympify(v)for w,v in zeroth['raw_nested_square']}
    divergence=coefficients['divergence'].subs(sub)
    real_shift=s.simplify(coefficients['potential'].subs(coefficients['m'],m).subs(sub))
    scalar=-sum(v*Hessian[i,j]for(i,j),v in data['K'].todok().items())-(divergence.T*gradient)[0]+real_shift
    terms=[(1,potential),(scalar,{word:1})]
    for j,Mh in enumerate(coefficients['hermitian']):
        matrix=full(rational(Mh.subs(sub)))
        terms.append((-s.I*gradient[j],apply_superposition(matrix,{word:1})))
    expected=weighted_sum(terms)
    assert weighted_sum([(1,actual),(-1,expected)])=={}
    assert len(actual)>1 and all(len(w)==m and all(P[i,i]==1 for i in w)for w in actual)
    assert real_shift>0
    original=verify_jet_action(data,word,1,gradient,Hessian)
    old={tuple(w):s.sympify(v)for w,v in original['raw_nested_square']}
    assert weighted_sum([(1,actual),(-1,old)])
    return {'particle_number':m,'input_CAR':list(word),'full_six_q_point':list(map(str,q)),
        'wavepacket':'A compact smooth cutoff equal1 near the displayed q point times the polynomial jet 1+i ell.y+(direction.y)^2/2-|y|^2/2, tensor the displayed source CAR word; extend through the original Gauss section.',
        'original_gradient':encode(gradient),'original_Hessian':encode(Hessian),
        'normalized_U_inverse_gradient':encode(transformed_gradient),'normalized_U_inverse_Hessian':encode(transformed_Hessian),
        'actual_U_H_U_inverse_image':encode_state(actual),
        'independent_divergence_plus_Hermitian_current_image':encode_state(expected),
        'source_generated_real_potential_shift':str(real_shift),
        'full_CAR_output_remains_in_392_carrier':True,
        'original_operator_was_not_silently_replaced':True}


def Gauss_and_other_components(model):
    section=model.section
    equal(section.alpha[:,:6],s.zeros(3,6))
    for L in section.L:equal(L[:6,:],s.zeros(6,103));equal(L[:,:6],s.zeros(103,6))
    for j in range(6):zero(s.diff(model.rho,model.coordinates[j]))
    # Every scalar/gauge/matter current is number-preserving. The extra
    # q/number metric commutes with their boson derivatives and CAR factors;
    # this transports their existing adjoint conditions, it does not prove them.
    return {'Gauss_extension_restriction_commute_with_candidate_metric_and_half_density':True,
        'source_local_positive_candidate_pairing':'sum_over_CAR_words s Integral rho(z)*v(q)^(2+card(s))*conj(f_s(z))*g_s(z) dz',
        'positive_source_normalization':'v>0 in the original coframe chart; all finitely many CAR weights are strictly positive and equal1 at the source coframe. No independent normalization factor is supplied.',
        'metric_on_number_sector':'W_m=v^(m+2) I; equivalently W=v^2 Gamma(v I) on the algebraic Fock carrier.',
        'full_Fock_positivity':'Different particle-number sectors remain orthogonal, and each sector has a positive scalar metric. The generated392 projection and original group action commute with it.',
        'same_Hamiltonian_half_density':'U_m=v^(1+m/2) is an isometry from the candidate rho*W pairing to the existing rho pairing and preserves compact support; the actual operator readback is U Hcoframe U^-1.',
        'CAR_adjoint_readback':'In the candidate metric the adjoint of an original annihilator is v^-1 times the original creation operator. The source-normalized annihilator sqrt(v)*a and creator v^-1/2*a_dagger satisfy CAR and are mutual adjoints; U carries them to the original orthonormal CAR representation.',
        'other_component_transport':'Scalar/gauge operators differentiate x/A only and preserve particle number, so W and U commute with them. Their formal-adjoint conditions under rho are therefore unchanged, not newly proved.',
        'full12_orbit_measure_responsibility':'The existing rho is the residual3 orbit Jacobian. Formal symmetry of the whole broken9 scalar/Gauss operator, possible determinant/connection contributions from the full12 source quotient, and global quantum completion retain their own source responsibilities.',
        'old_rho_authority_replaced':False,'Yukawa_adjoint_added':False}


def main():
    started=time.monotonic();model=SourceGaussSectionMeasure()
    coefficients=complete_coefficients(model)
    print('PASS all generic live coframe current/kinetic/normal-product adjoints and source positive metric v^(2+Number)',flush=True)
    actual=actual_half_density(model,coefficients)
    print('PASS actual full two-particle CAR coframe action and source half-density divergence readback with generated real potential',flush=True)
    scope=Gauss_and_other_components(model)
    paths=[HERE/name for name in('source_reducing_coframe_metric.py','source_reducing_quantum_adjoint.json',
        'source_yukawa_reducing_carrier.json','source_coframe_live_ordering.py','source_coframe_live_ordering.json',
        'source_gauss_section_measure.py','source_gauss_section_measure.json','source_quantum_gauss_section.py',
        'source_quantum_stabilizer.py','source_quantum_grade_structure.json')]
    output={'root':ROOT_ID,'scope':'SOURCE_NORMALIZED_POSITIVE_FOCK_METRIC_AND_COMPLETE_LIVE_COFRAME_FORMAL_SYMMETRY',
        'source_sha256':model.section.native.graph.common.source_hashes,
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths},
        'time_coframe_scope':'The literal fixed y_source=(N,0,0,0), with all six live q coordinates and the entire Fock carrier retained. Formal symmetry for arbitrary four-time parameters is not asserted here.',
        'source_metric_producer':{'volume':str(coefficients['volume']),
            'vacuum_weight':'v^2','complete_Fock_weight':'v^(2+Number)',
            'mixed_scalar_anti_Hermitian_part':encode(coefficients['t']),
            'actual_full_spin8_identity':'M_r^dagger-M_r=2 i t_r I8, t=K grad(log v)=N q/(4v); dGamma(I504)=Number',
            'Hermitian_mixed_matrices':[encode(M)for M in coefficients['hermitian']],
            'whole_normal_current_tensor_adjoint_identity':'T_(ij,kl)=conjugate(T_(ji,lk)) for the complete64x64 spin tensor, before any CAR state or sector restriction',
            'full_normal_current_tensor_nonzero_entries':len(coefficients['tensor'].todok()),
            'live_current_correction_and_onebody_Hermitian':True,
            'whole_Hermitian_mixed_divergence_zero':True,'log_volume_contraction_of_whole_Hermitian_mixed_zero':True,
            'source_equation':'K grad(log w_m)=i drift +m*t-divK=(m+2)*K grad(log v)',
            'uniqueness':'K is invertible in the source chart. Among coframe-only positive weights on each fixed number sector, the equation fixes grad(log w_m); w_m(source)=1 gives w_m=v^(m+2). Within coframe-only number-sector matrix metrics, the first-order equation reduces after this scalar weight to unitary-connection transport with source matrix I; I is its unique source-connected solution. This is not uniqueness of the full measure: allowing x/A dependence permits additional factors independent of q, whose source responsibility is unchanged.',
            'matrix_metric_transport':'2 sum_i K_ij partial_i G=2(D_j-divK_j)G+i G M_j-i M_j^dagger G. On number m, after G=v^(m+2) Gtilde this is 2K partial Gtilde=i[Gtilde,Mh]; initial I transports to I.'},
        'complete_operator_symmetry':'On each fixed number sector and the original compact smooth q chart, Hcoframe=-K:partial^2-(D+m*t).partial-i dGamma(Mh).partial+C. The weight divergence equals D+m*t; Mh is Hermitian with weighted divergence0; the full C (normal-current quartic, onebody, live correction and source potential) is Hermitian. Integration by parts therefore proves the full original coframe operator formally symmetric in rho*v^(m+2), for every state in the generated392 Fock carrier.',
        'half_density_readback':{'operator':'U Hcoframe U^-1=-partial_i(Kij partial_j)-i dGamma(Mh_j) partial_j+C+DeltaV',
            'U':'v^(1+Number/2)','generated_real_shift':str(coefficients['potential']),
            'all_original_normal_products_and_current_coefficients_retained':True},
        'actual_fullCAR_consumer':actual,'pairing_and_other_components':scope,
        'closed_selfadjoint_full_Hamiltonian_propagator_spectrum_or_lifetime_generated':False,
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'source_reducing_coframe_metric.json').write_text(json.dumps(output,separators=(',',':'))+'\n')
    print('PASS source positive coframe Fock metric',output['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
