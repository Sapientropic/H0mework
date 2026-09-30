#!/usr/bin/env python3
"""Independent ordered-resolvent and raw four-energy Gauss-jet audit.

Free Jordan words are expanded before spherical integration. Sylvester
identities are checked as triangular matrices on all interleaved words;
physical jets are coefficient convolutions of an affine original Yukawa
polynomial, then lifted by the independently derived implicit Gauss section.
"""
from __future__ import annotations

from collections import defaultdict
from functools import lru_cache
from itertools import product
from math import factorial
import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_joint_form_hamiltonian import (
    RawGaussSection, RawLiveCoefficients, HERE, ROOT, ROOT_ID, bindings,
    decode, encode, eq, rational, build_operators, whole_action, state_encode,
    decoded_state, state_equal, terms)
from independent_source_common_hamiltonian import original_inventory
from independent_source_full_quantum_adjoint import dual_pair, sparse
from independent_source_gauss_quantum_current import apply_state, add_terms

ORDER = 3
ELL = s.symbols('l0:4')
ZERO = (0, 0, 0, 0)


def zero(value): assert s.cancel(value) == 0, value


def word_product(left, right):
    out = defaultdict(lambda: s.S.Zero)
    for (w, a), c in left.items():
        for (v, b), d in right.items():
            if len(w)+len(v) <= ORDER:
                out[w+v, tuple(x+y for x,y in zip(a,b))] += c*d
    return {k:v for k,v in out.items() if v}


@lru_cache(None)
def token_expansion(token):
    if token == 'R':
        return {(w, tuple(w.count(j) for j in range(4))): s.Integer((-1)**len(w))
                for k in range(ORDER+1) for w in product(range(4), repeat=k)}
    j = int(token[1:]); result = {((j,), ZERO): s.S.One}
    if j == 0: result[(), ZERO] = s.S.One
    return result


@lru_cache(None)
def chain_expansion(chain):
    if not chain: return {((), ZERO): s.S.One}
    return word_product(chain_expansion(chain[:-1]), token_expansion(chain[-1]))


@lru_cache(None)
def sphere_radial(exponents):
    # l0=1; li=-r wi. Angular monomial integrals are independently
    # obtained by the Dirichlet(1/2,1/2,1/2) beta-moment formula.
    spatial = exponents[1:]
    if any(k % 2 for k in spatial): return s.S.Zero
    m = sum(spatial)
    angular = s.gamma(s.Rational(3,2))/s.gamma(s.Rational(m+3,2))
    angular *= s.prod(s.gamma(s.Rational(k+1,2))/s.gamma(s.Rational(1,2)) for k in spatial)
    return s.simplify((-1)**m*angular/(m+2))


def expand_integrand(rows, expected_degree, integrate):
    out = defaultdict(lambda: s.S.Zero)
    for row in rows:
        chain = tuple(row['word'])
        assert sum(1 if token.startswith('J') else -1 for token in chain) == expected_degree
        coeff = s.Poly(s.sympify(row['coefficient'], locals=dict(zip(map(str,ELL),ELL))), *ELL)
        for powers, scalar in coeff.terms():
            for (word, monomial), value in chain_expansion(chain).items():
                ell = tuple(a+b for a,b in zip(powers,monomial))
                if integrate: moment = sphere_radial(ell)
                else:
                    assert ell == ZERO
                    moment = s.S.One
                out[word] += scalar*value*moment
    return {w:s.factor(c) for w,c in out.items() if s.factor(c)}


def scalar_integrand(rows, y):
    L = sum(a*b for a,b in zip(ELL,y))
    return s.factor(sum(s.sympify(row['coefficient'], locals=dict(zip(map(str,ELL),ELL))) *
        s.prod(1/L if token=='R' else y[int(token[1:])] for token in row['word']) for row in rows))


def ordered_cone_audit(saved):
    n = s.Symbol('n', positive=True); b = s.symbols('b1:4', real=True); y = (n,*b)
    delta = n*n-sum(v*v for v in b); denominator = n*delta
    pairs = ((0,0),(1,1),(2,2),(0,1),(0,2),(1,2))
    original = [*y, *[(n*n-b[i]*b[j])/(2*denominator) if i==j else -b[i]*b[j]/denominator for i,j in pairs],
                *[-v/delta for v in b]]
    source_symbols = dict(zip(map(str,y),y))
    for value, actual in zip(saved['original_thirteen_coefficients'], original): zero(s.sympify(value,locals=source_symbols)-actual)
    origin = [s.Rational(9,5),0,0,0,*[s.Rational(324,625)]*3,*[0]*6]
    zero(s.sympify(saved['original_source_seed'],locals=source_symbols)-sum(a*c for a,c in zip(origin,original)))
    # Integrate the exact commutative resolvent first, without a germ
    # expansion. Rotational invariance reduces the sphere to its polar axis.
    z = s.Symbol('z', positive=True); r = s.Symbol('r', positive=True); u=s.Symbol('u', real=True)
    angular_primitive = 1/(4*r*z*(n-r*z*u)**2)
    zero(s.diff(angular_primitive,u)-(n-r*z*u)**-3/2)
    angular = s.factor(angular_primitive.subs(u,1)-angular_primitive.subs(u,-1))
    zero(angular-n/(n*n-r*r*z*z)**2)
    radial_primitive = 1/(z*z*(n*n-r*r*z*z))
    zero(s.diff(radial_primitive,r)-2*r/(n*n-r*r*z*z)**2)
    exact = s.factor(n*(radial_primitive.subs(r,1)-radial_primitive.subs(r,0)))
    zero(exact-1/(n*(n*n-z*z)))
    L=sum(a*c for a,c in zip(ELL,y)); base=1/L
    for a in range(4):
        for c in range(a,4):
            row=saved['T_integrands'][str((a,c))]
            zero(scalar_integrand(row,y)-s.diff(base,ELL[a],ELL[c]))
            for j in range(4):
                row=saved['original_F_integrands'][str((a,c,j))]
                zero(scalar_integrand(row,y)+s.diff(s.diff(base,ELL[a],ELL[c]),y[j]))
    counts=[0,0]
    at={n:1,**dict.fromkeys(b,0)}
    weights=saved['ordered_weight_integrands']; forces=saved['ordered_original_force_weight_integrands']
    assert len(weights)==13 and len(forces)==4 and all(len(row)==13 for row in forces)
    for equation in range(-1,4):
        for j, value in enumerate(original):
            expression=value if equation<0 else -s.diff(value,y[equation])
            degree=(1 if j<4 else -1)-(equation>=0)
            rows=weights[j] if equation<0 else forces[equation][j]
            polynomial=expand_integrand(rows,degree,j>=4)
            zero(sum(v*s.diff(expression,v) for v in y)-degree*expression)
            for k in range(4):
                for word in product(range(4),repeat=k):
                    expected=expression
                    for letter in word: expected=s.diff(expected,y[letter])
                    expected=s.factor(expected.subs(at)/factorial(k))
                    zero(polynomial.get(word,0)-expected)
                    counts[equation>=0]+=1
    return {'all_original_thirteen_weights_and_four_original_forces':True,
        'exact_timelike_cone_integral':str(exact),
        'ordered_weight_coefficients':counts[0], 'ordered_force_coefficients':counts[1],
        'symbolic_lapse_restored_by_exact_homogeneity':True,
        'independent_method':'Expand every resolvent chain in free ordered Jordan words, integrate each ell monomial by Dirichlet beta moments, then compare original source derivatives; exact polar integration pays the untruncated commutative coefficients.',
        'analytic_scope':'Operator integrals additionally consume the common relative-form domains of every nested R and J and angular integrability; no full quantum clock is supplied.'}


def decode_words(rows, symbols=None):
    return {tuple(row['word']):s.sympify(row['coefficient'],locals=symbols or {}) for row in rows}


def sylvester_audit(saved):
    n=s.Symbol('n',positive=True); alpha,beta=s.symbols('alpha beta'); t=s.Symbol('t',nonnegative=True)
    symbols={'n':n,'alpha':alpha,'beta':beta}
    words=[('Y',)*left+('X',)+('Y',)*right for total in range(3) for left in range(total+1) for right in [total-left]]
    index={word:i for i,word in enumerate(words)}; Q=s.zeros(6)
    for j,w in enumerate(words):
        for k,c in [(1,alpha),(2,beta)]:
            for out in [('Y',)*k+w,w+('Y',)*k]:
                if out in index: Q[index[out],j]+=c/2
    assert Q**3==s.zeros(6) and Q**2!=s.zeros(6)
    S=n*s.eye(6)+Q; inverse=S.inv(method='DM'); unit=s.eye(6)[:,0]
    eq(S*inverse,s.eye(6)); eq(inverse*S,s.eye(6))
    expected=decode_words(saved['N2_inverse_with_arbitrary_grade0_X'],symbols)
    column=inverse*unit
    assert all(s.factor(column[j]-expected.get(w,0))==0 for j,w in enumerate(words))
    for m in (1,2,3):
        actual=decode_words(saved['N2_inverse_powers'][str(m)],symbols); column=inverse**m*unit
        assert all(s.factor(column[j]-actual.get(w,0))==0 for j,w in enumerate(words))
        laplace=sum(((-1)**k*s.factorial(m+k-1)*Q**k/(s.factorial(m-1)*s.factorial(k)*n**(m+k)) for k in range(3)),s.zeros(6))
        eq(laplace,inverse**m)
    E=s.eye(6)-t*Q+t*t*Q**2/2
    eq(s.diff(E,t)+Q*E,s.zeros(6)); z=s.Symbol('s',nonnegative=True)
    eq(E.subs(t,t+z),E*E.subs(t,z))
    assert expected[('Y','X','Y')]!=0
    return expected, {'all_six_interleavings_checked_by_triangular_matrix_inverse':True,
        'left_and_right_Sylvester_inverse':True,'inverse_powers_checked':[1,2,3],
        'finite_semigroup_equation_and_composition':True,
        'nonzero_interleaved_Y_X_Y_coefficient':str(expected[('Y','X','Y')]),
        'all_particle_sector_extension':'Original strict positive grade makes the Neumann and semigroup sums terminate on each finite sector; a non-scalar grade-zero S0 inverse is still a consumed premise, with all S0 inverses retained in order.',
        'full_nonHermitian_Y_clock_not_replaced_by_positive_clock':True}


def positive_form_audit(saved):
    lam,mu,eta=s.symbols('lambda mu eta',positive=True); t=s.Symbol('t',nonnegative=True)
    k=2*s.sqrt(lam*mu)/(lam+mu)
    zero(s.sympify(saved['spectral_kernel'].replace('lambda','lam'),locals={'lam':lam,'mu':mu})-k)
    zero(s.integrate(lam*s.exp(-2*t*lam),(t,0,s.oo))-s.Rational(1,2))
    gram=2*s.sqrt(lam*mu)*s.exp(-t*(lam+mu))*(1-s.exp(-2*eta*t))
    integral=s.integrate(gram,(t,0,s.oo)); diagonal=eta/(lam+eta)
    zero(integral-s.sympify(saved['positive_regularizer_difference_Gram_kernel'].replace('lambda','lam'),locals={'lam':lam,'mu':mu,'eta':eta}))
    zero(integral.subs(mu,lam)-diagonal); zero(s.limit(diagonal,eta,0,dir='+'))
    zero((lam+mu)*k/2-s.sqrt(lam*mu))
    return {'exact_spectral_energy_identity_and_weak_Sylvester_kernel':True,
        'regularizer_difference_positive_Gram_factorization':str(gram),
        'regularizer_Gram_diagonal':str(diagonal),
        'strong_convergence_bound':'||difference v|| <= M ||sqrt(eta/(C+eta)) v||, from the bilinear Gram estimate and contraction norm of sqrt(eta/(C+eta)); injectivity gives strong convergence.',
        'scope':'Conditional analytic construction for an actual positive injective self-adjoint C and its C-relative bounded form; the actual full-Y clock and all nested cone domains are not assumed generated.'}


def polynomial_times_affine(poly, matrices):
    out={}
    for a,A in matrices.items():
        for b,state in poly.items():
            exponent=tuple(sorted(a+b))
            if len(exponent)>2:continue
            out[exponent]=add_terms([(1,out.get(exponent,{})),(1,apply_state(A,state))])
    return {a:row for a,row in out.items() if row}


def polynomial_jet(poly):
    words=set().union(*(set(state) for state in poly.values())) if poly else set()
    values={word:poly.get((),{}).get(word,0) for word in words}
    gradients={word:s.zeros(100,1) for word in words}; Hessians={word:s.zeros(100) for word in words}
    for exponent,state in poly.items():
        if len(exponent)==1:
            for word,c in state.items():gradients[word][exponent[0]]=c
        elif len(exponent)==2:
            i,j=exponent
            for word,c in state.items():
                Hessians[word][i,j]=Hessians[word][j,i]=c*(2 if i==j else 1)
    return values,gradients,Hessians


def actual_consumer(saved,inverse,source_hashes):
    section,raw=RawGaussSection(),RawLiveCoefficients(); inventory=original_inventory()
    assert section.native.hashes==source_hashes
    q=tuple(map(s.sympify,saved['q'])); x,A=decode(saved['x61']),decode(saved['A36'])
    point=s.Matrix(q).col_join(x).col_join(A.reshape(36,1)); eq(point,section.source)
    N=raw.N; assert list(map(s.sympify,saved['source_time']))==[N,0,0,0]
    data=build_operators(section,raw,q,x,A)
    F=sparse(s.kronecker_product(N*inventory['gamma'][0],s.eye(63)))
    original=[dual_pair(F*sparse(v)*(1 if j<35 else s.I)) for j,v in enumerate(inventory['scalar']*2)]
    phi=section.native.v+section.native.R*x
    Y=sparse(sum((v*p for v,p in zip(original,phi) if p),s.zeros(504)))
    eq(Y,decode(saved['original_full504_Y'])); data['matter']=sparse(data['matter']-Y)
    matrices={():Y}
    for j in range(61):
        dY=sparse(sum((original[i]*section.native.R[i,j] for i in range(70) if section.native.R[i,j]),s.zeros(504)))
        if dY.todok():matrices[(6+j,)]=dY
    assert len(matrices)-1==saved['source_Y_derivative_count']==61
    word=tuple(saved['input_CAR']); assert word==(144,396)
    g,H=decode(saved['gradient100']),decode(saved['Hessian100'])
    base={():{word:s.S.One}}
    for (j,_),c in g.todok().items():base[(j,)]={word:c}
    for (j,k),c in H.todok().items():
        if j<=k:base[j,k]={word:c/(2 if j==k else 1)}
    polynomials=[base]
    for _ in range(3):polynomials.append(polynomial_times_affine(polynomials[-1],matrices))
    assert polynomials[1] and polynomials[2] and not polynomials[3]
    images=[]; components=[]; counts=[]; gauss=[]
    for power,poly in enumerate(polynomials[:3]):
        values,gradients,Hessians=polynomial_jet(poly)
        _,jet=section.extension_jet(point,values,gradients,Hessians)
        gauss.append(section.Gauss_checks(point,jet)); counts.append(len(jet))
        pieces,image=whole_action(data,jet); pieces['matter_noY']=pieces.pop('matter_without_Lorentz')
        state_equal(image,decoded_state(saved['full_H0_on_Y_power_sections'][power]))
        for name,result in pieces.items():state_equal(result,decoded_state(saved['four_original_H0_components'][power][name]))
        images.append(image); components.append(pieces)
        print('PASS independent raw four energies on Y^'+str(power)+' polynomial, '+str(len(jet))+' implicit Gauss jet words',flush=True)
    frozen=polynomial_times_affine(base,{():Y})
    _,frozenjet=section.extension_jet(point,*polynomial_jet(frozen))
    _,frozenimage=whole_action(data,frozenjet)
    derivative_defect=terms([(1,images[1]),(-1,frozenimage)])
    assert derivative_defect
    state_equal(derivative_defect,decoded_state(saved['deleting_actual_Y_derivatives_defect']))
    @lru_cache(None)
    def image(w):
        assert w.count('X')==1
        split=w.index('X'); k=len(w)-split-1
        if k>=3:return {}
        out=images[k]
        for _ in range(split):out=apply_state(Y,out)
        return out
    n=s.Symbol('n',positive=True); alpha,beta=s.symbols('alpha beta'); a0=s.Rational(9,5)
    sub={n:N,alpha:-1/(2*a0),beta:3/(8*N*a0*a0)}
    coefficients={w:s.factor(c.subs(sub)) for w,c in inverse.items()}
    output=terms((c,image(w)) for w,c in coefficients.items())
    state_equal(output,decoded_state(saved['exact_Sylvester_inverse_H0']))
    C={():N,('Y',):sub[alpha],('Y','Y'):sub[beta]}
    residual=[]
    for prefix,c in C.items():
        for w,d in coefficients.items():residual.extend([(c*d/2,image(prefix+w)),(c*d/2,image(w+prefix))])
    residual=terms([*residual,(-1,images[0])]); assert not residual
    interleaved=image(('Y','X','Y')); assert interleaved
    state_equal(interleaved,decoded_state(saved['Y_H0_Y']))
    return {'independent_raw_70_Y_and_61_affine_derivatives':True,
        'implicit_Gauss_jet_word_counts':counts,'actual_Gauss_checks':gauss,
        'four_original_energy_components':[{k:state_encode(v) for k,v in row.items()} for row in components],
        'full_H0_on_Y_power_sections':[state_encode(v) for v in images],
        'Y_cubic_entire_second_jet_zero':True,'Y_H0_Y':state_encode(interleaved),
        'deleting_actual_Y_derivatives_defect':state_encode(derivative_defect),
        'exact_Sylvester_inverse_H0':state_encode(output),'actual_Sylvester_residual':state_encode(residual),
        'independent_method':'Exterior-slot CAR on a truncated commuting Taylor polynomial, coefficient convolution before independent implicit Gauss differentiation, then original coframe/gauge density and scalar adjoint-form action.',
        'scope':'Actual common source-point two-jet readback of full unbounded H0 on compact smooth sections, not an integrated norm, positive full-Y clock, or spectral pole.'}


def specialization_audit(saved,previous,N):
    a=s.Rational(9,5); eps,Y=s.symbols('epsilon Y')
    clock=N*(1-eps*Y/(2*N*a)+3*(eps*Y)**2/(8*N*N*a*a))
    energy=2*a*N+eps*Y-(eps*Y)**2/(4*N*a)
    zero(s.sympify(saved['N2_clock'])-clock); zero(s.sympify(saved['N2_energy'])-energy)
    assert s.Poly(s.expand(clock*clock*(a+eps*Y/N)-a*N*N),Y).nth(0)==0
    for k in (1,2):
        zero(s.Poly(s.expand(clock*clock*(a+eps*Y/N)-a*N*N),Y).nth(k))
        d=sum(s.sympify(row['coefficient'])/N**k for row in previous['full_original_Y']['time_coefficients'][0][k] if row['word']==[13]*k)
        e=sum(s.sympify(row['coefficient'])/N**k for row in previous['full_original_Y']['energy_coefficients'][k] if row['word']==[13]*k)
        zero(s.expand(clock).coeff(Y,k).coeff(eps,k)-d);zero(s.expand(energy).coeff(Y,k).coeff(eps,k)-e)
    return {'exact_quotient_clock_equation_and_previous_coefficients':True,
        'actual_physical_sector_asserted':False,'pure_Y_scope':saved['scope']}


def main():
    started=time.monotonic(); path=HERE/'source_temporal_cone_resolvent.json'
    candidate=json.loads(path.read_text()); count=bindings(candidate); assert candidate['root']==ROOT_ID
    paid=('independent_source_canonical_star_temporal_reduction','source_canonical_star_temporal_reduction',
          'independent_source_common_temporal_form','independent_source_quantum_grade_structure',
          'independent_source_yukawa_reducing_carrier')
    records={name:json.loads((HERE/(name+'.json')).read_text()) for name in paid}
    for record in records.values():count+=bindings(record);assert record['root']==ROOT_ID
    cone=ordered_cone_audit(candidate['exact_source_coefficient_map'])
    inverse,grade=sylvester_audit(candidate['finite_source_grade_inverse'])
    analytic=positive_form_audit(candidate['positive_injective_form_inverse'])
    N=s.sympify(candidate['exact_source_coefficient_map']['source_lapse'])
    specialization=specialization_audit(candidate['formal_coefficient_specialization'],records['source_canonical_star_temporal_reduction'],N)
    print('PASS independent free ordered cone weights/forces, finite Sylvester matrix inverse and positive relative-form kernel',flush=True)
    actual=actual_consumer(candidate['actual_unbounded_H0_consumer'],inverse,candidate['source_sha256'])
    assert candidate['full_grade_zero_quantum_clock_generated'] is False
    assert candidate['lifetime_status']=='SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED'
    paths=[Path(__file__),path,HERE/'source_temporal_cone_resolvent.py',
        HERE/'independent_source_joint_form_hamiltonian.py',HERE/'independent_source_gauss_quantum_current.py',
        HERE/'independent_source_quantum_gauss_section.py',HERE/'independent_source_common_hamiltonian.py',
        HERE/'independent_source_full_quantum_adjoint.py']+[HERE/(name+'.json') for name in paid]
    out={'verdict':'CERTIFIED_EXACT_SOURCE_CONE_COEFFICIENTS_AND_FINITE_GRADE_SYLVESTER_LIFTING',
        'root':ROOT_ID,'source_sha256':candidate['source_sha256'],
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks':count,'candidate_constructor_imported':False,
        'exact_ordered_cone':cone,'finite_grade_Sylvester_inverse':grade,
        'positive_injective_relative_form_inverse':analytic,'pure_Y_coefficient_specialization':specialization,
        'actual_original_four_energy_consumer':actual,
        'full_grade_zero_quantum_clock_or_nested_domain_or_spectrum_generated':False,
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'independent_source_temporal_cone_resolvent.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('PASS independent temporal cone resolvent',out['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
