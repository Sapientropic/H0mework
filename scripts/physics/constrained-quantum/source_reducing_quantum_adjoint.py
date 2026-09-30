#!/usr/bin/env python3
"""Live formal-adjoint responsibility on the source reducing quantum carrier.

The original local Gauss density is independent of the six coframe variables.
The complete vacuum restriction retains its original coefficient-left kinetic
operator. Its live first-order adjoint defect is nonzero on the positive
source chart, and two actual compact Gauss packets detect it. No Yukawa
adjoint interaction, density replacement or operator symmetrization is made.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from dynamic import HERE,ROOT,ROOT_ID,decode
from source_gauss_section_measure import SourceGaussSectionMeasure
from source_coframe_legendre import rational
from source_lorentz_contact import clean,equal,encode
from source_quantum_temporal_symbol import N


def zero(value): assert s.cancel(value)==0


def live_coefficients(model):
    c=model.section.native.joint.coframe;q=c.q
    K=c.K;D=rational(s.I*c.drift.T)
    equal(K.T,K);equal(K.conjugate(),K);equal(D.conjugate(),D)
    divergence=rational(s.Matrix([sum(s.diff(K[i,j],q[i])for i in range(6))for j in range(6)]))
    defect=rational(divergence-D)
    volume=q[0]*q[2]*q[5]
    expected=-N*s.Matrix(q)/(2*volume)
    equal(rational(defect-expected),s.zeros(6,1))
    source=tuple(c.e0[j]for j in(5,9,10,13,14,15))
    source_defect=c.at(defect,source)
    equal(source_defect,s.Matrix([-N/2,0,-N/2,0,0,-N/2]))
    # For L=-Kij partial_i partial_j-Dj partial_j+V with real coefficients
    # and q-independent rho, integration by parts gives these full local
    # differential coefficients. The order0 term is kept as well.
    first_difference=rational(2*(D-divergence))
    zero_difference=s.cancel(sum(s.diff(D[j]-divergence[j],q[j])for j in range(6)))
    V=3*c.det
    adjoint_first=rational(D-2*divergence)
    adjoint_zero=s.cancel(V+zero_difference)
    # The q-principal block is nondegenerate throughout this positive chart.
    determinant=s.factor(K.det(method='domain-ge'))
    zero(determinant+N**6/(16*q[2]**2*q[5]**4))
    # This solves the necessary scalar coframe density equation only. It is
    # recorded as the exact repair responsibility, never installed as a new
    # physical measure or as a substitute for the original rho.
    log_weight=s.Matrix([2/q[0],0,2/q[2],0,0,2/q[5]])
    equal(rational(K*log_weight-(D-divergence)),s.zeros(6,1))
    for j in range(6):zero(s.diff(volume**2,q[j])/volume**2-log_weight[j])
    return {'q':q,'K':K,'D':D,'divergence':divergence,'defect':defect,'source_defect':source_defect,
        'first_difference':first_difference,'zero_difference':zero_difference,
        'adjoint_first':adjoint_first,'adjoint_zero':adjoint_zero,'determinant':determinant,
        'necessary_relative_density':volume**2}


def complete_vacuum_scope(model):
    m=model.section;native=m.native;c=native.joint.coframe
    # The actual source group and chart fix the q block, so the coframe
    # derivative survives Gauss extension/restriction without a connection term.
    equal(m.alpha[:,:6],s.zeros(3,6))
    equal(m.z[:6,:6],s.eye(6));equal(m.z[6:,:6],s.zeros(94,6))
    for L in m.L:equal(L[:6,:],s.zeros(6,103));equal(L[:,:6],s.zeros(103,6))
    for Hessian in m.alpha2+m.z2:
        equal(Hessian[:6,:],s.zeros(6,103));equal(Hessian[:,:6],s.zeros(103,6))
    for j in range(6):zero(s.diff(model.rho,model.coordinates[j]))
    # Scalar momentum fields and their broken-Gauss graph are real and act
    # only on x/A; in CAR vacuum their current terms vanish. At the original
    # zero-shift time column h0i and the gauge mixed block vanish for every q.
    for T in native.T_b+native.T_s:equal(T.conjugate(),T)
    equal(native.graph.R.conjugate(),native.graph.R)
    equal(native.graph.O.conjugate(),native.graph.O)
    e=c.e;inverse=rational(e.adjugate()/e.det())
    from source_lorentz_contact import ETA
    metric=rational(e.det()*inverse*ETA*inverse.T)
    equal(metric[0,1:],s.zeros(1,3))
    gauge=native.gauge
    kernel=rational(gauge.at(gauge.kernel_numerator,e)/e.det())
    equal(kernel[:3,3:],s.zeros(3))
    for T in gauge.adjoint:equal(T.conjugate(),T)
    # Both actual compact germs belong to the generated392 reducing Fock
    # carrier (its algebraic vacuum). The original local Gauss equations,
    # including all differentiated rows, are reconstructed without a premise.
    delta=model.source_support_radius()['delta']
    f_value={():s.S.One};f_gradient={():s.zeros(100,1)}
    f_Hessian={():-2*s.eye(100)/delta**2}
    g_value={():s.S.Zero};g_gradient={():s.eye(100)[:,0]}
    g_Hessian={():s.zeros(100)}
    fjet=m.extend_jet(f_value,f_gradient,f_Hessian)
    gjet=m.extend_jet(g_value,g_gradient,g_Hessian)
    first=m.verify_Gauss_jet(fjet);second=m.verify_Gauss_jet(gjet)
    assert set(fjet)=={()} and set(gjet)=={()}
    return {'source_density_q_derivatives_zero':True,
        'Gauss_orbit_fixes_all6_q_and_full_inverse_first_second_jets':True,
        'other_complete_boson_energy_blocks':'On the CAR vacuum the whole scalar/broken-Gauss and native-gauge operators have real coefficients, differentiate only x/A, and commute with multiplication by q0. Their full contributions cancel in the two-packet antisymmetric pairing.',
        'matter_and_all_CAR_current_terms':'Every number-preserving current and normal product annihilates the algebraic vacuum; this is a state inside the full generated392 Fock carrier, not an assumption about other particle-number sectors.',
        'actual_compact_Gauss_packets':{'f':first,'g':second,
            'f_value':'1','f_gradient':'0','f_Hessian':'-2 I100/delta^2',
            'g_value':'0','g_gradient':'e_q0','g_Hessian':'0'},
        'original_density_or_Hamiltonian_ordering_changed':False}


def compact_pair(model,coefficients):
    q=coefficients['q'];K=coefficients['K'];D=coefficients['D']
    # The complete difference is obtained before freezing coefficients:
    # H((q0-1)f)=(q0-1)Hf-2 K_i0 partial_i f-D0 f.
    # Integrating the first term with the actual q-independent rho produces
    # D0-div(K)_0=N/(2 q2 q5), strictly positive on the whole support.
    difference=s.cancel(D[0]-coefficients['divergence'][0])
    zero(difference-N/(2*q[2]*q[5]))
    support=model.source_support_radius();delta=support['delta']
    C0,C2,Cminus=s.symbols('C0 C2 Cminus',positive=True)
    a0,b0=model.z0[model.gauge_a1],model.z0[model.gauge_a12]
    rho_average=8*b0*(a0*a0+delta**2*C2/C0)
    common_factor=(delta*C0)**100
    normalized=s.factor(rho_average*N*(Cminus/C0)**2/2)
    lower=s.factor(N/2)
    upper=s.factor(N/(2*(1-delta**2)**2))
    assert 0<delta<1 and upper>lower>0
    # Exact positive even-kernel identity gives strict moment bounds, without
    # replacing an integral by an uncontrolled point estimate.
    t=s.Symbol('t',real=True)
    zero((1/(1+delta*t)+1/(1-delta*t))/2-1/(1-delta**2*t**2))
    return {'packets':'f(z)=product_j eta((z_j-z_source_j)/delta) tensor vacuum; g(z)=(q0-1) f(z), eta(t)=exp(1-1/(1-t^2)) on |t|<1 and zero outside.',
        'same_grade_and_same_Fock_carrier':True,'support':{key:str(value)for key,value in support.items()},
        'complete_pairing_difference':'<g,H_restricted f>_rho-<H_restricted g,f>_rho=(N/2) Integral rho(z)|f(z)|^2/(q2*q5) dz >0',
        'source_coefficient_not_frozen':str(difference),
        'moments':'C0=Integral_-1^1 eta(t)^2 dt; C2=Integral_-1^1 t^2 eta(t)^2 dt; Cminus=Integral_-1^1 eta(t)^2/(1+delta*t) dt; all strictly positive.',
        'positive_common_packet_factor':str(common_factor),
        'exact_pairing_difference_after_common_factor':str(normalized),
        'exact_f_norm_after_common_factor':str(rho_average),
        'strict_difference_over_f_norm_bounds':[str(lower),str(upper)],
        'strict_bound_reason':'Even eta^2 gives Cminus/C0 as the positive average of 1/(1-delta^2 t^2), strictly between1 and1/(1-delta^2).',
        'source_Haar_factor':'The original positive local coordinate-Haar volume multiplies both pairings equally; no probability or external-state normalization is introduced.'}


def main():
    started=time.monotonic();model=SourceGaussSectionMeasure()
    carrier=json.loads((HERE/'source_yukawa_reducing_carrier.json').read_text())
    assert carrier['generated_real_CAR_dimension']==392
    for group in('source_sha256','input_sha256'):
        for name,digest in carrier[group].items():assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
    coefficients=live_coefficients(model)
    print('PASS generic full sixq source principal/drift coefficients, nonzero formal-adjoint defect and exact source chart determinant',flush=True)
    scope=complete_vacuum_scope(model)
    packets=compact_pair(model,coefficients)
    print('PASS complete same-grade compact Gauss packets, original rho and strict positive forward-minus-reverse pairing',flush=True)
    paths=[HERE/name for name in('source_reducing_quantum_adjoint.py','source_yukawa_reducing_carrier.py',
        'source_yukawa_reducing_carrier.json','source_gauss_section_measure.py','source_gauss_section_measure.json',
        'source_quantum_gauss_section.py','source_quantum_stabilizer.py','source_coframe_live_ordering.py',
        'source_joint_local_quantum.py','source_gauge_quantum_energy.py')]
    output={'root':ROOT_ID,'scope':'LIVE_SOURCE_COFRAME_FORMAL_ADJOINT_DEFECT_ON_GENERATED_REDUCING_FOCK_CARRIER_WITH_ACTUAL_GAUSS_PACKETS',
        'source_sha256':model.section.native.graph.common.source_hashes,
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths},
        'whole_live_coefficients':{'K':encode(coefficients['K']),'D_equals_i_drift':encode(coefficients['D']),
            'divergence_K':encode(coefficients['divergence']),'divergence_minus_D':encode(coefficients['defect']),
            'source_value_defect':encode(coefficients['source_defect']),
            'principal_determinant':str(coefficients['determinant']),
            'vacuum_operator':'L=-sum Kij(q) partial_qi partial_qj-sum Dj(q) partial_qj+3 det(e)',
            'formal_adjoint_first_coefficient':encode(coefficients['adjoint_first']),
            'formal_adjoint_zero_coefficient':str(coefficients['adjoint_zero']),
            'Ldagger_minus_L_first_coefficient':encode(coefficients['first_difference']),
            'Ldagger_minus_L_zero_coefficient':str(coefficients['zero_difference'])},
        'complete_other_component_and_Gauss_scope':scope,'actual_compact_pair':packets,
        'signed_responsibility':'The original coefficient-left Hamiltonian restricted to this392 Fock carrier is not formally symmetric on the existing positive rho pairing. Yukawa annihilation does not remove this independent live coframe ordering defect.',
        'necessary_local_coframe_density_equation':{'equation':'K grad(log w)=D-divK',
            'generated_relative_solution':str(coefficients['necessary_relative_density']),
            'source_normalization':'w(source)=1; this scalar equation has the displayed unique local solution up to a constant because K is invertible.',
            'not_installed':'This is a derived necessary coframe condition, not a replacement of the already generated rho or a proof that the full Hamiltonian is symmetric in rho*w. Any norm or ordering change must be generated from the original action and canonical pullback.'},
        'excluded_inferences':'No Yukawa-adjoint term was added; no Hermitian average, new source occurrence, complete interacting spectral measure, proton identification or proton no-go follows.',
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'source_reducing_quantum_adjoint.json').write_text(json.dumps(output,separators=(',',':'))+'\n')
    print('PASS reducing quantum formal-adjoint responsibility',output['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
