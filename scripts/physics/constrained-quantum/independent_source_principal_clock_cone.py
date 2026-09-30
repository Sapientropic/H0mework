#!/usr/bin/env python3
"""Independent original-density/Gauss audit of the principal clock cone.

The native BF electric Hessian is inverted before contraction with the
independently generated implicit Gauss cotangent map. The complete original
four-energy zero-value/zero-gradient germ reads its scalar Fock principal
symbol. No principal covector is used as an external-leg momentum.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_joint_form_hamiltonian import (
    RawGaussSection,RawLiveCoefficients,HERE,ROOT,ROOT_ID,bindings,rational,
    eq,decode,encode,whole_action,raw_gauge_coefficients,terms,state_encode,
    decoded_state,state_equal)
from independent_source_scalar_form_hamiltonian import raw_coefficients
from independent_source_quantum_ordered_temporal import raw_coframe_family
from independent_source_scalar_temporal_form import at
from independent_source_common_hamiltonian import raw_matter
from independent_source_full_quantum_adjoint import dual_pair
from independent_source_gauge_legendre import ETA,SIGMA


def zero(value): assert s.factor(s.cancel(value))==0,value


def decoded_time_state(rows,ys):
    return {tuple(word):s.sympify(value,locals={str(v):v for v in ys}) for word,value in rows}


def positive_minors(A):
    assert A.T==A
    values=[s.factor(A[:j,:j].det()) for j in range(1,A.rows+1)]
    assert all(value>0 for value in values)
    return list(map(str,values))


def generic_clock(candidate):
    n=s.Symbol('n',positive=True);b=s.Matrix(s.symbols('b1:4',real=True));a=s.Symbol('a0_2',positive=True)
    S=s.Matrix([[s.Symbol('S00'),s.Symbol('S01'),s.Symbol('S02')],
        [s.Symbol('S01'),s.Symbol('S11'),s.Symbol('S12')],
        [s.Symbol('S02'),s.Symbol('S12'),s.Symbol('S22')]])
    T=s.trace(S);delta=n*n-(b.T*b)[0];C=T*s.eye(3)-S
    H=n*a+T/(2*n)+(b.T*C*b)[0]/(2*n*delta)
    zero(H-(n*a+(n*n*T-(b.T*S*b)[0])/(2*n*delta)))
    y=s.Matrix([n,*b]);F=-s.Matrix([s.diff(H,z) for z in y])
    zero((b.T*F[1:,:])[0]+n*(b.T*C*b)[0]/delta**2)
    origin=dict.fromkeys(b,0);eq(F.subs(origin),s.Matrix([-a+T/(2*n*n),0,0,0]))
    J=F.jacobian(y).subs(origin);expected=s.diag(-T/n**3,*[0]*3);expected[1:,1:]=-C/n**3
    eq(J,expected);zero(J.det()-T*C.det()/n**12)
    sym={str(v):v for v in [*y,a,*set(S)]}
    zero(H-s.sympify(candidate['complete_principal_H'],locals=sym))
    eq(F,decode(candidate['all4_original_principal_forces'],sym))
    eq(J,decode(candidate['source_root_Jacobian'],sym))
    zero(J.det()-s.sympify(candidate['Jacobian_determinant'],locals=sym))
    # For a native Gram S>=0, trS I-S>0 iff at least two Gram
    # eigenvalues are positive; the displayed elementary-symmetric minors
    # also retain the degenerate rank-one exclusion explicitly.
    lam=s.symbols('lambda0:3',nonnegative=True)
    eig=s.diag(*lam);complement=s.trace(eig)*s.eye(3)-eig
    eq(complement,s.diag(lam[1]+lam[2],lam[0]+lam[2],lam[0]+lam[1]))
    assert complement.subs({lam[0]:1,lam[1]:0,lam[2]:0}).det()==0
    assert complement.subs({lam[0]:1,lam[1]:1,lam[2]:0}).det()>0
    return {'original_four_forces_and_Jacobian':True,
        'exact_future_branch_identity':str(s.factor((b.T*F[1:,:])[0])),
        'unique_future_timelike_root':'b=0 and n=positive sqrt(trace(S2)/(2*a0_2)) on a0_2>0 and trace(S2)I-S2>0.',
        'native_Gram_rank_two_suffices_and_rank_one_excluded':True,
        'global_timelike_scope':'C>0 makes b.F_b strictly negative for b!=0 throughout n>|b|; the remaining positive-n scalar equation has exactly one solution.'}


def original_coefficients(section,raw,ys):
    n,*bs=ys;b=s.Matrix(bs);q=s.Matrix(raw.q)
    L=s.Matrix([[q[0],0,0],[q[1],q[2],0],[q[3],q[4],q[5]]]);v=L.det()
    e=s.zeros(4);e[:,0]=s.Matrix(ys);e[1:,1:]=L
    metric=rational(e.det()*e.inv()*ETA*e.inv().T);zero(metric[0,0]+v/n)
    g=e.T*ETA*e
    electric=s.Matrix(3,3,lambda i,j:-(g[0,0]*g[i+1,j+1]-g[0,j+1]*g[i+1,0])/(SIGMA*e.det()))
    delta=n*n-(b.T*b)[0]
    inverse=SIGMA*v/(n*delta)*L.inv()*(n*n*s.eye(3)-b*b.T)*L.inv().T
    eq(rational(electric*inverse),s.eye(3));eq(rational(inverse*electric),s.eye(3))
    ee,cf=raw_coframe_family(raw,ys);eq(ee,e)
    eq(rational(cf['K']/n),rational(raw.K/raw.N))
    for shift in bs:eq(cf['K'].diff(shift),s.zeros(6))
    return e,cf,{'raw_BF_electric_Hessian_two_sided_inverse_all_q_and_time':True,
        'all_q_and_time_scalar_h00_equals_minus_volume_over_n':True,
        'all_q_and_time_coframe_quadratic_is_n_times_K0':True,
        'full_Fock_principal_scope':'Every original second derivative multiplies the identity on the complete occupation carrier: coframe currents, scalar currents, Gauss connections and all adjoint corrections multiply only the zero/first jets; original matter/Y are order zero.'}


def source_factors(section,raw,saved):
    source=section.source;geo=section.implicit_jets(source)
    positive_minors(section.native.Gram.inv())
    pull=rational(geo['tangent'].T*section.free_reader.T)
    eq(geo['V'].T*pull,s.zeros(3,100))
    q=tuple(source[:6,0]);x=source[6:67,:];A=source[67:,:].reshape(3,12)
    assert list(map(str,q))==saved['q'];eq(x,decode(saved['x61']));eq(A,decode(saved['A36']))
    e=raw.at(raw.e,q);scalar=raw_coefficients(section.native,e,x,A)
    scalar_factor=rational(scalar['a']*pull[6:,:]);gauge_factor=pull[67:,:]
    K0=raw.at(raw.K/raw.N,q);volume=s.prod(q[j] for j in (0,2,5))
    a0=rational(pull[:6,:].T*K0*pull[:6,:]-scalar_factor.T*scalar_factor/(2*volume))
    for name,M in [('coframe_K0',K0),('scalar_factor70x100',scalar_factor),('gauge_factor36x100',gauge_factor),
                   ('a0_matrix100',a0),('native_inverse_Gram',section.native.Gram.inv())]:eq(M,decode(saved[name]))
    return dict(q=q,x=x,A=A,pull=pull,scalar=scalar,scalar_factor=scalar_factor,gauge_factor=gauge_factor,
        K0=K0,a0=a0,volume=volume,point=source,geo=geo)


def cotangent_values(section,raw,f,p):
    momentum=f['pull']*p;P=(f['gauge_factor']*p).reshape(3,12)
    G=section.native.Gram.inv();electric=rational(P*G*P.T)
    q=f['q'];L=s.Matrix([[q[0],0,0],[q[1],q[2],0],[q[3],q[4],q[5]]])
    S=rational(SIGMA*f['volume']*L.inv().T*electric*L.inv())
    a0=s.factor((p.T*f['a0']*p)[0]);T=s.trace(S)
    eq(f['geo']['V'].T*momentum,s.zeros(3,1))
    # The original nine broken rows, before returning to the61 scalar slice.
    pi_phi=f['scalar_factor']*p
    for rho,ad in zip(section.native.rhob,section.native.adb):
        gauge=sum((ad*f['A'][i,:].T).dot(momentum[67+12*i:79+12*i,:]) for i in range(3))
        zero((rho*section.native.v).dot(pi_phi)+gauge)
    return momentum,P,electric,S,a0,T


def candidate_witness(section,raw,f,saved):
    p=decode(saved['canonical_p100']);momentum,P,electric,S,a0,T=cotangent_values(section,raw,f,p)
    assert positive_minors(S)==saved['S2_positive_leading_minors']
    assert positive_minors(T*s.eye(3)-S)==saved['traceS2_identity_minus_S2_positive_minors']
    for name,M in [('ambient_p103',momentum),('original_electric_momentum3x12',P),
                   ('original_electric_Gram',electric),('source_S2',S)]:eq(M,decode(saved[name]))
    loss=s.factor((f['scalar_factor']*p).dot(f['scalar_factor']*p)/(2*f['volume']))
    pr2=s.factor((2*f['q'][0]*p[0])**2/f['volume'])
    zero(loss-s.sympify(saved['source_scalar_loss']));zero(pr2-s.sympify(saved['source_radial_momentum_squared']))
    zero(a0-s.sympify(saved['source_a0_2']));zero(T-s.sympify(saved['source_traceS2']))
    assert a0>0 and pr2>0 and P.rank()==3
    zero(T/(2*a0)-raw.N**2)
    for j in (0,2,5):zero(p[j]-s.sqrt(f['volume']*pr2)/(2*f['q'][j]))
    return p,{'original_broken9_and_residual3_Gauss_principal_rows_zero':True,
        'source_a0_2':str(a0),'source_S2':encode(S),'source_radial_momentum_squared':str(pr2),
        'source_clock_squared':str(T/(2*a0)),'original_electric_rank':P.rank(),
        'actual_positive_clock_is_source_lapse':True}


def second_witness(section,raw,f):
    p=s.zeros(100,1)
    for ambient in (80,93):p[section.free.index(ambient)]=1
    _,P,_,S,a,T=cotangent_values(section,raw,f,p)
    eq(S,s.eye(3)/4);zero(a+s.Rational(9,200));assert P.rank()==3
    pr2=s.factor(s.Rational(16,3)*(T/(2*raw.N**2)-a));assert pr2==s.Rational(3287,675)
    for j in (0,2,5):p[j]=s.sqrt(pr2)/2
    _,_,_,S,a,T=cotangent_values(section,raw,f,p)
    assert a==s.Rational(125,144);zero(T/(2*a)-raw.N**2)
    return {'independent_ambient_free_gauge_coordinates':[80,93],
        'canonical_p100':encode(p),'source_S2':encode(S),'positive_complement':encode(T*s.eye(3)-S),
        'original_scalar_a0_2':'-9/200','source_radial_momentum_squared':str(pr2),'source_total_a0_2':str(a),
        'original_electric_rank':3,'same_source_clock':str(raw.N)}


def original_action(section,raw,f,e,cf,ys,p,saved,witness):
    qpoint=dict(zip(raw.q,f['q']));ee=at(e,qpoint)
    data={'coframe':{k:at(v,qpoint) for k,v in cf.items()},
        'scalar':raw_coefficients(section.native,ee,f['x'],f['A']),
        'gauge':raw_gauge_coefficients(ee,f['A'],section.native)}
    connection=s.zeros(4,12);connection[1:,:]=f['A']
    matter=raw_matter(ee,data['scalar']['phi'],connection)
    data['matter']=dual_pair(rational(-s.I*matter['E_inverse']*matter['lower']))
    word=tuple(saved['input_CAR']);assert word==(144,396)
    _,jets=section.extension_jet(f['point'],{word:0},{word:s.zeros(100,1)},{word:-p*p.T})
    assert set(jets)=={word};value,gradient,Hessian=jets[word]
    assert value==0 and not gradient.todok();eq(Hessian,-(f['pull']*p)*(f['pull']*p).T)
    gauss=section.Gauss_checks(f['point'],jets)
    pieces,result=whole_action(data,jets);pieces['matter_noY']=pieces.pop('matter_without_Lorentz')
    for name,image in pieces.items():state_equal(image,decoded_time_state(saved['four_original_component_images'][name],ys))
    state_equal(result,decoded_time_state(saved['original_full_H2_image'],ys))
    assert pieces['matter_noY']=={} and all(pieces[name] for name in ('coframe','scalar_form','gauge'))
    _,_,_,S,a,T=cotangent_values(section,raw,f,p);n,*bs=ys;b=s.Matrix(bs)
    expected=n*a+(n*n*T-(b.T*S*b)[0])/(2*n*(n*n-(b.T*b)[0]))
    state_equal(result,{word:expected})
    force=-s.Matrix([s.diff(expected,v) for v in ys]);at_source=dict(zip(ys,(raw.N,0,0,0)))
    eq(rational(force.subs(at_source)),s.zeros(4,1))
    J=rational(force.jacobian(s.Matrix(ys)).subs(at_source))
    eq(J,decode(witness['actual_four_force_Jacobian']));zero(J.det()-s.sympify(witness['actual_Jacobian_determinant']))
    positive_minors(-J)
    return {'original_four_energy_images':{name:state_encode(value) for name,value in pieces.items()},
        'actual_symbolic_four_time_principal':str(s.factor(expected)),'Gauss':gauss,
        'original_all_four_forces_at_source_clock':encode(rational(force.subs(at_source))),
        'force_Jacobian':encode(J),'force_Jacobian_positive_determinant':str(s.factor(J.det())),
        'whole_original_principal_is_scalar_without_CAR_projection':True,
        'zero_value_gradient_germ_removes_no_second_order_term':True}


def poisson_readback(raw,f,p,candidate,section):
    q=s.Matrix(raw.q);v=q[0]*q[2]*q[5];r=s.sqrt(v);dr=s.Matrix([s.diff(r,z) for z in q]);K=raw.K/raw.N
    eq(rational(K*dr-q/(8*r)),s.zeros(6,1))
    _,_,E,_,_,_=cotangent_values(section,raw,f,p)
    L=s.Matrix([[q[0],0,0],[q[1],q[2],0],[q[3],q[4],q[5]]])
    T=s.factor(SIGMA*v*s.trace(L.inv().T*E*L.inv()))
    zero(sum(q[j]*s.diff(T,q[j]) for j in range(6))-T)
    # Differentiate in independent canonical p_q before restricting to the
    # two radial covectors; differentiating p_r dr(q) prematurely is wrong.
    covector=s.Matrix(s.symbols('canonical_pq0:6',real=True));pr=s.Symbol('p_r',real=True)
    a=(covector.T*K*covector)[0]
    bracket=-sum(s.diff(a,covector[j])*s.diff(T,q[j]) for j in range(6))
    radial=s.factor(bracket.subs(dict(zip(covector,pr*dr))))
    zero(radial+pr*T/(4*r))
    actual=s.factor(radial.subs({**dict(zip(q,f['q'])),pr:2*f['q'][0]*p[0]/s.sqrt(f['volume'])}))
    assert actual!=0;zero(actual-s.sympify(candidate['source_positive_radial_value']))
    zero(2*actual-s.sympify(candidate['full_a0_traceS_odd_radial_difference']))
    return {'independent_canonical_derivatives_before_radial_restriction':True,
        'generic_radial_bracket':str(radial),'source_value':str(actual),
        'two_source_rays_odd_difference':str(2*actual),
        'noncommuting_source_requirement':'Other pieces have no coframe covector and hence even dependence on this radial sign. At least one full canonical bracket is nonzero; order1/0 terms cannot cancel the order3 commutator symbol.',
        'commuting_quantum_square_root_not_installed':True}


def main():
    started=time.monotonic();path=HERE/'source_principal_clock_cone.json';candidate=json.loads(path.read_text())
    count=bindings(candidate);assert candidate['root']==ROOT_ID
    paid=('independent_source_common_weyl_symbol','independent_source_common_temporal_form',
          'independent_source_coframe_volume_shape','independent_source_temporal_cone_resolvent')
    for name in paid:
        receipt=json.loads((HERE/(name+'.json')).read_text());count+=bindings(receipt);assert receipt['root']==ROOT_ID
    laws=generic_clock(candidate['generic_clock_laws']);section,raw=RawGaussSection(),RawLiveCoefficients()
    assert section.native.hashes==candidate['source_sha256']
    ys=(s.Symbol('quantum_n',positive=True),*s.symbols('quantum_b1:4',real=True))
    e,cf,coverage=original_coefficients(section,raw,ys)
    f=source_factors(section,raw,candidate['original_source_factors'])
    p,witness=candidate_witness(section,raw,f,candidate['actual_source_cotangent_witness'])
    extra=second_witness(section,raw,f)
    print('PASS independent original BF/scalar/coframe factors, all12 principal Gauss rows and two actual rank3 cone witnesses',flush=True)
    actual=original_action(section,raw,f,e,cf,ys,p,candidate['actual_four_energy_principal_action'],candidate['actual_source_cotangent_witness'])
    poisson=poisson_readback(raw,f,p,candidate['canonical_Moyal_consumer'],section)
    assert candidate['complete_quantum_clock_or_spectral_measure_generated'] is False
    files=[Path(__file__),path,HERE/'source_principal_clock_cone.py']+[HERE/name for name in (
        'independent_source_joint_form_hamiltonian.py','independent_source_quantum_gauss_section.py',
        'independent_source_coframe_live_ordering.py','independent_source_scalar_form_hamiltonian.py',
        'independent_source_quantum_ordered_temporal.py','independent_source_gauge_legendre.py',
        'independent_source_common_hamiltonian.py')]+[HERE/(name+'.json') for name in paid]
    output={'verdict':'CERTIFIED_SOURCE_GENERATED_PRINCIPAL_CLOCK_CONE_AND_UNIQUE_GLOBAL_FUTURE_ROOT',
        'root':ROOT_ID,'source_sha256':candidate['source_sha256'],
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'source_binding_checks':count,'candidate_constructor_imported':False,
        'independent_method':'Original four-index BF electric inverse, raw epsilon/coframe principal, original scalar momentum graph, implicit Gauss cotangent pullback, complete original all-time four-energy quadratic germ; canonical derivatives before radial restriction.',
        'original_quadratic_order_coverage':coverage,'generic_clock_laws':laws,
        'actual_candidate_source_witness':witness,'independent_second_source_witness':extra,
        'actual_original_four_energy_consumer':actual,'canonical_Moyal_consumer':poisson,
        'scope':'The generated open domain lies in the original configuration cotangent bundle. Its unique future timelike principal clock and nonzero canonical Moyal obligation are source-generated; no external-leg momentum, complete quantum clock, spectral pole or proton identification is inferred.',
        'complete_quantum_clock_spectrum_or_lifetime_generated':False,
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'independent_source_principal_clock_cone.json').write_text(json.dumps(output,separators=(',',':'))+'\n')
    print('PASS independent principal clock cone',output['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
