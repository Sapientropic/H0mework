#!/usr/bin/env python3
"""Independent original scalar energy and global momentum-growth audit.

Coefficient norm bounds carry explicit weighted-Cauchy positive-square
certificates. The all-order flow implication is an analytic Gronwall/VoC
argument, separate from the exact matrix identities and from Lean theorems.
"""
from __future__ import annotations

import hashlib
import itertools
import json
from pathlib import Path
import time

import sympy as s

from independent_spectral_splice import ROOT_ID, clean, equal, source

HERE=Path(__file__).resolve().parent
BASE=HERE.parent
ROOT=HERE.parents[3]
K=s.symbols('k1:4',real=True)


def read(path): return json.loads(path.read_bytes())


def decode(record):
    return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(value,locals={str(k):k for k in K})
        for i,j,value in record['entries']})


def encode(value):
    return {'shape':list(value.shape),'entries':[[i,j,str(s.expand(v))]
        for (i,j),v in sorted(s.SparseMatrix(value).todok().items())]}


def zero(rows,columns=None): return s.SparseMatrix.zeros(rows,rows if columns is None else columns)


def bindings(record):
    count=0
    for key in ('source_sha256','input_sha256'):
        for name,digest in record.get(key,{}).items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
            count+=1
    return count


def realify(value):
    return clean(s.SparseMatrix.vstack(s.SparseMatrix.hstack(value.applyfunc(s.re),-value.applyfunc(s.im)),
        s.SparseMatrix.hstack(value.applyfunc(s.im),value.applyfunc(s.re))))


def weighted_Cauchy(value):
    """Generate b^2 I-M* M as a nonnegative diagonal plus positive rank-one terms."""
    entries=value.todok()
    magnitude={ij:s.simplify(s.sqrt(s.re(v)**2+s.im(v)**2)) for ij,v in entries.items()}
    assert all(v.is_positive for v in magnitude.values())
    rows=[sum(v for (i,j),v in magnitude.items() if i==r) for r in range(value.rows)]
    columns=[sum(v for (i,j),v in magnitude.items() if j==c) for c in range(value.cols)]
    rmax,cmax=s.simplify(s.Max(*rows)),s.simplify(s.Max(*columns))
    assert all(s.simplify(rmax-v).is_nonnegative for v in rows)
    assert all(s.simplify(cmax-v).is_nonnegative for v in columns)
    square=s.simplify(rmax*cmax)
    diagonal=[s.simplify(square-sum(rows[i]*magnitude.get((i,j),0) for i in range(value.rows)))
        for j in range(value.cols)]
    assert all(v.is_nonnegative for v in diagonal)
    certificate=s.MutableSparseMatrix.diag(*diagonal)
    pairs=[]
    for i in range(value.rows):
        support=sorted(j for ii,j in entries if ii==i)
        for j,ell in itertools.combinations(support,2):
            a,b=magnitude[i,j],magnitude[i,ell]
            vector=s.SparseMatrix(value.cols,1,{(j,0):s.conjugate(value[i,j])/a,
                (ell,0):-s.conjugate(value[i,ell])/b})
            weight=s.simplify(a*b)
            assert weight.is_positive
            certificate+=weight*vector*vector.H
            pairs.append({'row':i,'weight':str(weight),'vector':encode(vector)})
    equal(square*s.eye(value.cols)-value.H*value,certificate)
    return s.simplify(s.sqrt(square)),{'shape':list(value.shape),'row_max':str(rmax),
        'column_max':str(cmax),'operator_bound_squared':str(square),
        'positive_diagonal_remainder':[str(v) for v in diagonal],
        'positive_rank_one_terms':pairs,
        'exact_identity':'b^2 I-M^* M=diag(nonnegative remainder)+sum positive_weight*v*v^*'}


def main():
    started=time.monotonic()
    candidate_path=HERE/'scalar_momentum_energy.json'
    candidate=read(candidate_path)
    assert candidate['root']==ROOT_ID
    count=bindings(candidate)
    canonical_path=HERE/'scalar_canonical_phase.json'
    pair_path=HERE/'scalar_joint_hamiltonian.json'
    bounds_path=HERE/'independent_scalar_dyson_bounds.json'
    canonical,pair,bounds=map(read,(canonical_path,pair_path,bounds_path))
    for record in (canonical,pair,bounds): count+=bindings(record)
    active_path=BASE/'active-gauge/receipt.json'
    active=read(active_path)
    _,vacuum,degrees,hashes=source.parse_source(ROOT)
    assert hashes==candidate['source_sha256']==canonical['source_sha256']
    background=active['actual_background']
    coframe=s.Matrix(background['coframe']).applyfunc(s.sympify)
    N=s.simplify(coframe.det())
    assert N==s.sympify(candidate['source_lapse']) and N.is_positive
    equal(coframe,s.diag(N,1,1,1))
    metric=clean(coframe.inv()*s.diag(-1,1,1,1)*coframe.inv().T)
    assert s.simplify(N*metric[0,0]+1/N)==0
    # Rebuild the scalar gauge representation and orbit directly from the
    # original exterior generators, independently of the projected receipt.
    four_words=list(itertools.combinations(range(7),4))
    vacuum_vector=s.Matrix([vacuum.get(word,0) for word in four_words])
    rho=[];orbit=[]
    for _,imaginary,generator in source.generators([(0,1,2),(3,4)]):
        action=(s.I if imaginary else 1)*s.Matrix(source.exterior_action(generator,4))
        rho.append(realify(action))
        v=action*vacuum_vector
        orbit.append(s.SparseMatrix.vstack(v.applyfunc(s.re),v.applyfunc(s.im)))
    J=s.SparseMatrix.hstack(*orbit)[:,active['J_independent_columns']]
    P=clean(s.eye(70)-J*(J.T*J).inv()*J.T)
    equal(P,decode(canonical['projector61']));equal(P*P,P);equal(P.H,P)
    gauge=s.Matrix(background['gauge_connection']).applyfunc(s.sympify)
    connection=[clean(sum((gauge[mu,a]*rho[a] for a in range(12)),zero(70))) for mu in range(4)]
    equal(connection[0],zero(70))
    for A in connection: equal(A.H,-A)
    derivative=[zero(70),*[s.I*k*s.eye(70) for k in K]]
    raw_L=clean(-2*s.eye(70)-sum((metric[mu,nu]*(derivative[mu]+connection[mu])*
        (derivative[nu]+connection[nu]) for mu,nu in itertools.product(range(4),repeat=2)),zero(70)))
    equal(raw_L,decode(canonical['scalar_L']));equal(raw_L*P,P*raw_L)
    L=clean(P*raw_L*P)
    M0=clean(L.subs(dict.fromkeys(K,0)))
    linear=[clean(L.diff(k).subs(dict.fromkeys(K,0))) for k in K]
    radius2=sum(k*k for k in K)
    equal(L,radius2*P+M0+sum((k*M for k,M in zip(K,linear)),zero(70)))
    for M in (L,M0,*linear): equal(M.H,M);equal(P*M*P,M)
    equal(M0,decode(candidate['projected_constant']))
    for actual,saved in zip(linear,candidate['projected_linear']): equal(actual,decode(saved))
    norm_certificates={}
    b0,norm_certificates['M0']=weighted_Cauchy(M0)
    bj=[]
    for j,M in enumerate(linear):
        bound,cert=weighted_Cauchy(M);bj.append(bound);norm_certificates['M'+str(j+1)]=cert
    assert b0==s.sympify(candidate['constant_norm_bound'])==2
    assert bj==list(map(s.sympify,candidate['linear_norm_bounds']))==[3*s.sqrt(2)/5]*3
    shift=s.simplify(1+b0+sum(b*b for b in bj)/2)
    assert shift==s.sympify(candidate['energy_shift_a'])==s.Rational(102,25)
    r=s.symbols('r1:4',nonnegative=True)
    lower=sum(x*x for x in r)-sum(x*b for x,b in zip(r,bj))-b0+shift
    equal_squares=1+sum(x*x for x in r)/2+sum((x-b)**2 for x,b in zip(r,bj))/2
    assert s.expand(lower-equal_squares)==0
    upper=s.simplify(1+shift+b0+sum(bj))
    assert upper==s.sympify(candidate['energy_upper_C']) and upper.is_positive
    # Exact certificate for the claimed common upper coefficient: replace
    # each |k_j| by (1+k_j^2)/2, then the remaining constant and coefficients
    # in C(1+|k|^2)-the_upper_polynomial are nonnegative.
    comparison=upper*(1+sum(x*x for x in r))-(sum(x*x for x in r)+shift+b0+
        sum(b*(1+x*x)/2 for b,x in zip(bj,r)))
    assert all(s.simplify(c).is_nonnegative for _,c in s.Poly(comparison,*r).terms())
    assert s.simplify(upper-1).is_nonnegative
    print('PASS raw source principal/linear/constant scalar symbol and explicit positive-square coefficient norm certificates',flush=True)

    R=P[:,canonical['canonical_coordinate_pivots']]
    gram=clean(R.T*R);D=clean(R*gram.inv())
    T=clean(s.diag(R,D));S=clean(s.diag(D.T,R.T))
    equal(S*T,s.eye(122));equal(T*S,s.diag(P,P))
    A=clean(s.SparseMatrix.vstack(s.SparseMatrix.hstack(zero(70),-N*P),
        s.SparseMatrix.hstack(N*L,zero(70))))
    Ac=clean(S*A*T)
    equal(Ac,decode(canonical['canonical_generator']))
    Kenergy=clean(L+shift*P)
    E=s.diag(Kenergy,P)
    offdiag=s.SparseMatrix.vstack(s.SparseMatrix.hstack(zero(70),P),
        s.SparseMatrix.hstack(P,zero(70)))
    equal(A.H*E+E*A,-N*shift*offdiag)
    Ec=clean(T.H*E*T)
    equal(Ac.H*Ec+Ec*Ac,-N*shift*T.H*offdiag*T)
    sb,norm_certificates['S']=weighted_Cauchy(S)
    tb,norm_certificates['T']=weighted_Cauchy(T)
    condition=s.simplify(sb*tb)
    assert condition==s.sympify(candidate['canonical_frame_condition_bound'])==4
    C=s.simplify(condition*s.sqrt(upper));beta=s.simplify(N*shift/2)
    assert s.simplify(C-s.sympify(candidate['canonical_flow_constant_C']))==0
    assert beta==s.sympify(candidate['coordinate_time_growth_beta'])
    assert s.simplify(beta/N-shift/2)==0
    # |E'| <= N a E follows from 2 uv <= u^2+v^2 <= E on P61.
    u,v=s.symbols('u v',nonnegative=True)
    assert s.expand(u*u+v*v-2*u*v-(u-v)**2)==0
    print('PASS unchanged original140 and canonical122 energy derivative, full source S/T comparison and proper clock',flush=True)

    plus=s.SparseMatrix(122,244,{
        **{(j,j):1/s.sqrt(2) for j in range(61)},**{(j,j+61):s.I/s.sqrt(2) for j in range(61)},
        **{(j+61,j+122):1/s.sqrt(2) for j in range(61)},**{(j+61,j+183):s.I/s.sqrt(2) for j in range(61)}})
    U=s.SparseMatrix.vstack(plus,plus.conjugate())
    equal(U,decode(candidate['real244_unitary_conjugate_identity']))
    equal(U.H*U,s.eye(244));equal(U*U.H,s.eye(244))
    pair_A=decode(pair['real_phase_generator'])
    equal(U*pair_A*U.H,s.diag(Ac,Ac.subs(dict(zip(K,[-k for k in K])),simultaneous=True)))
    equal(decode(pair['zero_mode']['generator']),Ac.subs(dict.fromkeys(K,0)))
    derivative1=s.simplify(condition*N*(2+s.Max(*bj)))
    derivative2=s.simplify(2*condition*N)
    assert s.simplify(derivative1-s.sympify(candidate['first_generator_derivative_constant']))==0
    assert derivative2==s.sympify(candidate['second_generator_derivative_constant'])
    for i in range(3):
        lower_derivative=2*K[i]*P+linear[i]
        ambient_derivative=s.SparseMatrix.vstack(s.SparseMatrix.hstack(zero(70),zero(70)),
            s.SparseMatrix.hstack(N*lower_derivative,zero(70)))
        equal(Ac.diff(K[i]),S*ambient_derivative*T)
        for j in range(3):
            second=s.SparseMatrix.vstack(s.SparseMatrix.hstack(zero(70),zero(70)),
                s.SparseMatrix.hstack((2*N*P if i==j else zero(70)),zero(70)))
            equal(Ac.diff(K[i],K[j]),S*second*T)
            for k in K: equal(Ac.diff(K[i],K[j],k),zero(122))
    print('PASS complete real244 Fourier-pair unitary, true zero122 and exact first/second generator derivatives at every momentum',flush=True)

    source_paths=[candidate_path,HERE/'scalar_momentum_energy.py',canonical_path,pair_path,bounds_path,
        active_path,BASE/'exact_readout.py',HERE/'independent_spectral_splice.py',
        HERE/'independent_scalar_momentum_energy.py']
    result={'verdict':'CERTIFIED_SOURCE_SCALAR_GLOBAL_ENERGY_AND_SCHWARTZ_MULTIPLIER_BOUNDS',
        'root':ROOT_ID,'source_sha256':hashes,
        'input_sha256':{str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in source_paths},
        'candidate_constructor_or_norm_function_imported':False,
        'algorithm':'original coframe/exterior scalar density; full symbolic principal coefficient; explicit weighted-Cauchy Gram decompositions of b^2 I-M^*M; scalar completed squares; unchanged physical generator energy identity; original R/dual-D phase frames; exact unitary pair and generator derivatives',
        'source_binding_checks':count,'principal_coefficient':1,
        'coefficient_norm_certificates':norm_certificates,
        'source_norm_bounds':{'constant':str(b0),'linear':list(map(str,bj))},
        'comparison_energy_shift':str(shift),'canonical_frame_condition':str(condition),
        'canonical_flow_C':str(C),'coordinate_time_beta':str(beta),
        'energy_domain':'P61 phi=phi and P61 Pi=Pi; the comparison energy controls the original projected scalar field/momentum, then the source S/T frames transport the estimate to122 canonical coordinates',
        'lower_bound':'L+aP >= (1+|k|^2/2)P for every real k, by exact three-square completion and certified Hermitian coefficient norm bounds',
        'upper_bound':'L+aP <= energy_upper_C (1+|k|^2)P on the source range',
        'unchanged_source_energy_identity':'A^* E+E A=-N a [[0,P],[P,0]], hence Eprime=-2 N a Re<Pi,phi> and |Eprime|<=N a E',
        'global_flow':'||exp(t Ac(k))|| <= C sqrt(1+|k|^2) exp(beta |t|), and the same bound for the actual unit-normalized244 pair',
        'proper_clock':'tau=N t, so beta |t|=a |tau|/2; no N sqrt2 substitution',
        'all_order_derivative_argument':{'source_generator_degrees':'momentum degree2; first derivatives bounded byD1(1+|k|), second byD2, higher derivatives exactly0',
            'D1':str(derivative1),'D2':str(derivative2),
            'strengthened_induction':'for |t|<=T, ||partial_k^alpha exp(tAc)||<=Cr(T)(1+|k|)^(2r+1) exp(beta |t|), r=|alpha|',
            'recurrence':'C0=C; Cr(T)=C T [r D1 C_(r-1)(T)+r(r-1)/2 D2 C_(r-2)(T)], C_(-1)=0',
            'time_weight':'in the Volterra integral between0 andt, |t-s|+|s|=|t|; this prevents multiplying two independent exp(beta T) bounds',
            'momentum_weight':'first derivative contributions have degree2r+1; second derivative contributions have degree2r-2<=2r+1',
            'Schwartz_seminorm':'p_(m,alpha)(E_t f) <= sum_(beta<=alpha) C_(beta,T) p_(m+2|beta|+1,alpha-beta)(f)',
            'proof_status':'independent Gronwall and variation-of-constants mathematical audit from the exact matrix certificates; not a Lean analytic theorem'},
        'continuous_kappa_gate_reduction':'fixed-time free source phase and its momentum derivatives have polynomial growth globally, so they act continuously on spatial Schwartz test data; no transfer-radius cutoff is needed',
        'whole_spacetime_temperedness_claimed':False,
        'time_test_scope':'compact-time tests or an appropriate exponential-time weight; low-momentum source growth is retained',
        'physical_action_or_mass_shifted':False,'positive_comparison_energy_identified_as_physical_Hilbert_state':False,
        'continuous_unsmeared_interaction_or_UV_completion_constructed':False,
        'formal_Lean_energy_inequality_installed':False,
        'full_four_block_spectral_measure_or_lifetime_claimed':False,
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'independent_scalar_momentum_energy.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS independent source scalar global momentum energy audit',result['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':
    main()
