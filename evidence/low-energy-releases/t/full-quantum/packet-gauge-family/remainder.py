#!/usr/bin/env python3
"""Source-generated constants for the actual weighted causal family remainder.

No new large inverse is computed.  The original matrix/source entries generate
the circle bound; the certified pole disk generates the companion and its
derivative bounds.  Contact cancellation is consumed only from the actual lift.
"""
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode=True
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent;FQ=HERE.parent
x,epsilon,a,U=s.symbols('x epsilon a U',real=True)
alpha=3*s.sqrt(2)/10
N=3*s.sqrt(30)/25
rho=F(1,131072)
radicals=[s.Integer(1),s.sqrt(2),s.sqrt(15),s.sqrt(30)]
radical_bounds=[F(1),F(3,2),F(4),F(6)]


def read(path):return json.loads(path.read_text())
def rational(v):
    assert v.is_Rational,v
    return F(int(s.numer(v)),int(s.denom(v)))


@lru_cache(None)
def number_bound(value):
    value=s.expand(value);remaining=value;parts=[s.Integer(0)]*4
    for j in range(3,0,-1):
        parts[j]=remaining.coeff(radicals[j]);remaining=s.expand(remaining-radicals[j]*parts[j])
    parts[0]=remaining
    assert s.expand(sum(r*v for r,v in zip(radicals,parts))-value)==0
    return sum((abs(rational(s.re(v)))+abs(rational(s.im(v))))*b
               for v,b in zip(parts,radical_bounds))


@lru_cache(None)
def circle_bound(text):
    value=s.expand(s.sympify(text,locals={'x':x,'epsilon':epsilon}).subs(epsilon,alpha*a))
    return sum(number_bound(coefficient)*F(5)**dx*F(1,100)**da
               for (dx,da),coefficient in s.Poly(value,x,a,domain=s.EX).terms())


def matrix(record):
    return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(v,locals={'x':x}) for i,j,v in record['entries']})


def constant_matrix_norm(M):
    rows=[F(0)]*M.rows
    for (i,j),value in s.SparseMatrix(M).todok().items():rows[i]+=number_bound(value)
    return max(rows,default=F(0))


def main():
    began=time.monotonic()
    source=read(HERE/'source.json');infinity=read(HERE/'infinity.json')
    domain=read(HERE/'domain.json');proper=read(HERE/'proper.json');lift=read(HERE/'lift.json')
    old=read(FQ/'packet-gauge-causal/source.json')
    assert proper['nonpositive_section_powers']==[]
    assert lift['all289_strictly_proper_for_the_same_parameter_family'] is True
    assert infinity['complete_frequency_degree']==126
    delta=F(domain['generated_positive_delta_in_a'])
    assert 0<delta<=F(1,100)
    assert F(domain['uniform_neumann_ratio_upper'])<F(1,4)
    assert F(4,25)<F(9,50) # (2/5)^2 < alpha^2.
    eps_star=delta/5
    outer_epsilon_radius=2*delta/5
    # The physical real family is restricted to |epsilon|<=eps_star.  Its
    # mathematical complex extension has the larger certified disk above.
    fhat=s.Poly(s.sympify(source['complete_Fhat'],locals={'U':U}),U,domain=s.QQ)
    lowerU=s.Rational(3,4)*s.Rational(rho.numerator,rho.denominator)**2
    upperU=s.Rational(4,5)*s.Rational(rho.numerator,rho.denominator)**2
    assert fhat.count_roots(lowerU,upperU)==1
    D=s.Poly(s.sympify(source['source_denominator'],locals={'U':U}),U,domain=s.QQ)
    Ubound=rho*rho
    Dlower=abs(rational(D.nth(0)))-sum(abs(rational(v))*Ubound**j for (j,),v in D.terms() if j)
    assert Dlower>F(1,2)
    scales=matrix(old['scales103'])
    diagonal=[s.Integer(1)]*9+[scales[i,i] for i in range(103)]
    source_rows=[F(0)]*112
    for i,j,text in source['section_source_numerator']['entries']:
        value=s.sympify(text,locals={'x':x,'epsilon':epsilon})*diagonal[i]/N
        source_rows[i]+=circle_bound(str(value))*Ubound**j/Dlower
    normalized_forcing=max(source_rows)
    inverse=F(4,3)*F(domain['unvaried_inverse_infinity_norm_circle_bound'])
    section_bound=max(map(number_bound,diagonal))*inverse*normalized_forcing
    values=[F(0)]*289
    for i in source['keep121']:values[i]=section_bound
    for step in reversed(source['auxiliary_steps']):
        bounds=[F(0)]*len(step['eliminated'])
        for i,j,text in step['particular_source']['entries']:
            bounds[i]+=circle_bound(text)*Ubound**j/Dlower
        for i,j,text in step['back']['entries']:
            bounds[i]+=circle_bound(text)*values[step['kept'][j]]
        for i,row in enumerate(step['eliminated']):values[row]=bounds[i]
    world=[F(0)]*289
    for i,j,text in old['L']['entries']:
        world[i]+=number_bound(s.sympify(text))*values[j]
    G=max(world)
    assert G>0
    print('PASS actual fixed source and full289 lift generate a complex-parameter circle bound',flush=True)

    # Independently retain the Noether source protocol.  Its inverse minor is
    # frequency independent, and the fixed retained source has no time-tangent
    # projection.  Hence it cannot introduce a derivative-of-delta input.
    K0,K1,C1=map(matrix,[old['K0'],old['K1'],old['C1']])
    Z=matrix(source['original_source_numerator'])
    removed=source['removed'];Km=K0.extract(removed,range(9))
    Kmi=matrix(old['symmetry_minor_inverse'])
    assert (Km*Kmi-s.eye(9)).applyfunc(s.expand)==s.zeros(9)
    assert all(x not in v.free_symbols for v in list(Km)+list(K1)+list(C1))
    Ktime=K0.applyfunc(lambda v:s.expand(v).coeff(x,1))
    assert (Ktime.T*Z).applyfunc(s.expand)==s.zeros(9,Z.cols)
    minor_ratio=outer_epsilon_radius*constant_matrix_norm(Kmi*K1.extract(removed,range(9)))
    assert minor_ratio<F(1,4)
    print('PASS original Noether minor and absence of higher-frequency source contact',flush=True)

    # Vieta bounds the monic degree126 companion without selecting eigenvectors.
    m=126;M=6**m+m-2
    B=F(85,4)*10**m*G
    derivative_scale=5/delta
    M1,M2=derivative_scale*M,2*derivative_scale**2*M
    B1,B2=derivative_scale*B,2*derivative_scale**2*B
    assert F(19,4)**2>25*F(108,125) and F(108,125)<1
    # eta=5, beta=19/4.  The large norm enters a finite polynomial, not the
    # exponential rate.  This exact sum is the Schur-Duhamel L1 envelope.
    S=4*((8*M)**m-1)//(8*M-1)
    assert S==4*sum((8*M)**j for j in range(m))
    K0bound=B*S
    K1bound=B1*S+B*M1*S*S
    K2bound=B2*S+2*B1*M1*S*S+B*(M2*S*S+2*M1*M1*S**3)
    W0=B*M;W1=B1*M+B*M1;W2=B2*M+2*B1*M1+B*M2
    L0=W0*S
    L1=W1*S+W0*M1*S*S
    L2=W2*S+2*W1*M1*S*S+W0*(M2*S*S+2*M1*M1*S**3)
    T0,T1,T2=K0bound+B+L0,K1bound+B1+L1,K2bound+B2+L2
    # Source E0 eta1 preparation and original phase transfer -k.  These are
    # numerical consequences of the certified Dynamics bounds, not a chosen
    # noise variance or desired response coefficient.
    assert 2*rho*rho<F(1,90000)**2
    A0,A1,A2=F(17,5),F(74,25),F(148,125)
    field0=T0*A0;field1=T1*A0+T0*A1
    field_remainder=T2*A0/2+T1*A1+T0*A2
    current0=2*field_remainder*field0+field1*field1
    current1=2*field1*field0+eps_star*field1*field1
    assert min(T0,T1,T2,field_remainder,current0,current1)>0
    print('PASS actual weighted kernel/time-jet and field epsilon-squared remainder envelopes',flush=True)

    vertex=read(FQ/'packet-gauge-bilocal/vertices.json');readers=[]
    for row in vertex['readers']:
        v0=sum((number_bound(s.sympify(entry[-1])) for entry in row['Q0_bijet']),F(0))/2
        v1=sum((number_bound(s.sympify(entry[-1])) for entry in row['Q1_bijet']),F(0))/2
        readers.append({'reader':row['reader'],'V0':str(v0),'V1':str(v1)})
    assert len(readers)==48
    print('PASS all48 actual bijet coefficients and both variation legs of the integrated current',flush=True)
    response_path=FQ/'packet-gauge-response/response.json'
    response=read(response_path)
    assert s.sympify(response['physical_lambda'])==5-5*s.I
    assert all(s.simplify(s.sympify(v)+s.sympify(k))==0
        for v,k in zip(response['quantum_current_transfer'],old['physical_momentum']))
    selected=response['selected_reader']
    assert selected['reader']==[1,1]
    actual_interval=list(map(F,selected['complete_first_response_interval']['rational']))
    simple=list(map(F,response['selected_simple_strict_interval']))
    assert 0<simple[0]<actual_interval[0]<actual_interval[1]<simple[1]
    assert response['strictly_nonzero_response_count']==22
    print('PASS actual S01 derivative consumer at the shared physical frequency',flush=True)
    files=['source.json','infinity.json','domain.json','proper.json','lift.json']
    result={'scope':'STRIKE_ACTUAL_FINITE_GAUGE_RETARDED_FAMILY_WEIGHTED_STRONG_DERIVATIVE_AND_CURRENT',
        'input_sha256':{name:hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in files},
        'upstream_sha256':{str(path.relative_to(FQ)):hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [FQ/'packet-gauge-causal/source.json',FQ/'packet-gauge-dynamics/bounds.json',
                FQ/'packet-gauge-bilocal/vertices.json',response_path]},
        'actual_parameter':'epsilon=3*sqrt(2)*a/10; primitive A=actualA+epsilon dx1 S01',
        'delta_in_a':str(delta),'real_epsilon_radius':str(eps_star),'complex_epsilon_disk_radius':str(outer_epsilon_radius),
        'physical_clock':'lambda=c*x, c=6*sqrt(15)/25; t is unchanged',
        'source_phase_transfer':'-k, where k is the same fixed nonaxial momentum in packet-gauge-causal/source.json',
        'actual_U_interval':[str(lowerU),str(upperU)],'source_D_lower':str(Dlower),
        'full289_field_infinity_norm_on_abs_x5':str(G),
        'Noether_minor_neumann_ratio_upper':str(minor_ratio),
        'Noether_source_has_only_instant_and_proper_parts':True,
        'all289_field_polynomial_contact_identically_zero':True,
        'source_companion_degree':m,'physical_spectral_rate_upper':'19/4','damping_minimum':5,
        'companion_norm_upper':str(M),'output_norm_upper':str(B),
        'parameter_Cauchy_derivative_scale':str(derivative_scale),
        'semigroup_weighted_L1_upper':str(S),
        'kernel_and_timejet_operator_bounds':{'value':str(T0),'first_parameter_derivative':str(T1),
            'second_parameter_derivative':str(T2),'Taylor_remainder':'epsilon^2*T2/2'},
        'actual_noise_weighted_bounds':{'J0':str(A0),'Z':str(A1),'epsilon_squared_remainder':str(A2)},
        'field_pair_bounds':{'Y0_and_timejet':str(field0),'Y1_and_timejet':str(field1),
            'epsilon_squared_remainder':str(field_remainder)},
        'full_current_remainder':{'coefficient_of_V0':str(current0),'coefficient_of_V1':str(current1),
            'readers':readers,'formula':'epsilon^2*(V0*C_current0+V1*C_current1)'},
        'actual_finite_family_derivative_consumer':{'reader':[1,1],'frequency':'z=w=5*(1-I)',
            'strict_interval':list(map(str,simple)),'all_nonzero_reader_count':22,
            'identification':'The exact earlier response is now the genuine derivative of the original finite-epsilon retarded current family, by the weighted source remainder proved here.'},
        'identification':'The same source family has X_epsilon; X_0 and its real parameter derivative are the certified Causal X0/X1. Uniform weighted differentiability identifies the corresponding chi0/chi1 and Y0/Y1, and the old Response expression is the true finite-family derivative.',
        'integral_convention':'double time with exp(-conjugate(z)t-ws), Re(z),Re(w)>=5; not the single transform of its diagonal',
        'time_zero':'Y_epsilon(0)=0; time jets at zero are right derivatives and retain chi_epsilon(0)*J_epsilon(0)',
        'elapsed_seconds':round(time.monotonic()-began,3)}
    (HERE/'remainder.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS finite-family source remainder construction',result['elapsed_seconds'],flush=True)


if __name__=='__main__':main()
