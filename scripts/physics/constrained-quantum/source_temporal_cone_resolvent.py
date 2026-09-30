#!/usr/bin/env python3
"""Exact cone coefficients and finite positive-grade source Sylvester lifting.

The angular inverse is an ordered operator expression, not substitution of
commuting clock values. The actual compact source core permits unbounded H0
insertions. Existence of its full grade-zero quantum clock remains a distinct
operator equation; the pure-Y calculation is a coefficient specialization.
"""
from __future__ import annotations

from functools import lru_cache
from itertools import product, combinations_with_replacement
from math import factorial
import hashlib
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID, decode
from source_canonical_star_temporal_reduction import bound
from source_quantum_ordered_temporal import OrderedTemporalCoefficients
from source_quantum_temporal_symbol import N, SYM
from source_common_temporal_form import SourceCommonTemporalForm
from source_full_quantum_adjoint import split_matter
from source_quantum_grade_structure import matrix_grade, state_grade
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state
from source_lorentz_contact import clean, equal, encode, GAMMA
from source_coframe_legendre import rational


def encode_words(poly):
    return [{'word': list(word), 'coefficient': str(s.factor(value))}
            for word, value in sorted(poly.items()) if value]


def add(*rows):
    out = {}
    for row in rows:
        for w, c in row.items(): out[w] = out.get(w, 0)+c
    return {w: s.factor(c) for w, c in out.items() if s.factor(c)}


def scale(c, row):
    return {w: s.factor(c*v) for w, v in row.items() if c*v}


def mul(left, right, grade_cap=None):
    return add(*[{u+v: a*b} for u, a in left.items() for v, b in right.items()
                 if grade_cap is None or (u+v).count('Y') <= grade_cap])


def cone_expression(a, b, derivative=None):
    """Integrand of R_D[y_a y_b/P] or its original -partial_y force.

    Word order means composition of superoperators from left to right. R is
    (sum l_a J_a)^-1, J_a X=(C_a X+X C_a)/2, l=(1,-r omega).
    """
    ell = s.symbols('l0:4')
    row = add({('R', 'J'+str(a), 'R', 'J'+str(b), 'R'): 1},
              {('R', 'J'+str(b), 'R', 'J'+str(a), 'R'): 1})
    if derivative is None: return row
    result = []
    for word, coefficient in row.items():
        for j, token in enumerate(word):
            if token == 'R':
                result.append({word[:j]+('R', 'R')+word[j+1:]: coefficient*ell[derivative]})
            elif token == 'J'+str(derivative):
                result.append({word[:j]+word[j+1:]: -coefficient})
    return add(*result)


def exact_cone_coefficients():
    raw = OrderedTemporalCoefficients(); n, *b = raw.y
    ell = s.symbols('l0:4'); r = s.Symbol('r'); omega = s.symbols('omega1:4')
    clock = s.Symbol('N', positive=True); delta = n*n-sum(v*v for v in b)
    z = s.Symbol('z', positive=True); t = s.Symbol('t', real=True)
    anti = 1/(4*z*(n-z*t)**2)
    assert s.factor(s.diff(anti,t)-1/(2*(n-z*t)**3)) == 0
    assert s.factor(anti.subs(t,1)-anti.subs(t,-1)-n/(n*n-z*z)**2) == 0
    radial = r*r/(n*(n*n-r*r*z*z))
    assert s.factor(s.diff(radial,r)-2*r*n/(n*n-r*r*z*z)**2) == 0
    assert s.factor(radial.subs(r,1)-1/(n*(n*n-z*z))) == 0

    @lru_cache(None)
    def average(expression):
        expression = s.expand(expression.subs(dict(zip(ell,(1,*[-r*w for w in omega])))))
        value = 0
        for exponents, c in s.Poly(expression,r,*omega).terms():
            er, *eu = exponents
            if any(k%2 for k in eu): continue
            value += c*s.prod(s.factorial2(k-1) for k in eu)/s.factorial2(sum(eu)+1)/(er+2)
        return s.factor(value)

    @lru_cache(None)
    def taylor(expression, word):
        for j in word: expression = s.diff(expression,raw.y[j])
        return s.factor(expression.subs(dict(zip(raw.y,(clock,0,0,0))))/factorial(len(word)))

    words = [w for k in range(4) for w in product(range(4), repeat=k)]
    coefficients = forces = 0
    for a, c in combinations_with_replacement(range(4), 2):
        expression = raw.y[a]*raw.y[c]/(n*delta)
        for word in words:
            k = len(word); monomial = s.prod(ell[j] for j in word)
            R = (-1)**k*monomial/(clock*ell[0])**(k+1)
            assert s.factor(average(s.diff(R,ell[a],ell[c]))-taylor(expression,word)) == 0
            coefficients += 1
            for j in range(4):
                R2 = (-1)**k*(k+1)*ell[j]*monomial/(clock*ell[0])**(k+2)
                assert s.factor(average(s.diff(R2,ell[a],ell[c]))-taylor(-s.diff(expression,raw.y[j]),word)) == 0
                forces += 1
    mapped = [*raw.y]
    for i,j in SYM:
        mapped.append((raw.y[0]**2-raw.y[i+1]**2)/(2*n*delta) if i==j
                      else -raw.y[i+1]*raw.y[j+1]/(n*delta))
    mapped += [-n*v/(n*delta) for v in b]
    assert all(s.factor(a-b) == 0 for a,b in zip(mapped,raw.coefficients))
    weights=[{('J'+str(a),):s.S.One} for a in range(4)]
    force_weights=[[{():-s.S.One} if a==j else {} for a in range(4)] for j in range(4)]
    for i,j in SYM:
        weights.append(scale(s.Rational(1,2),add(cone_expression(0,0),scale(-1,cone_expression(i+1,i+1))))
                       if i==j else scale(-1,cone_expression(i+1,j+1)))
        for k in range(4):
            force_weights[k].append(scale(s.Rational(1,2),add(cone_expression(0,0,k),scale(-1,cone_expression(i+1,i+1,k))))
                                    if i==j else scale(-1,cone_expression(i+1,j+1,k)))
    weights += [scale(-1,cone_expression(0,i+1)) for i in range(3)]
    for k in range(4):force_weights[k] += [scale(-1,cone_expression(0,i+1,k)) for i in range(3)]
    return {'original_thirteen_coefficients': list(map(str,raw.coefficients)),
        'original_source_seed':str(raw.seed),
        'ordered_weight_integrands':[encode_words(w) for w in weights],
        'ordered_original_force_weight_integrands':[[encode_words(w) for w in row] for row in force_weights],
        'source_assembly':'Use the four affine J terms directly; integrate the nine rational integrands with r dr Avg_S2. Apply each resulting superoperator to its original full canonical grade0 atom plus its original seed coefficient times Id. Add the same first J0 applied to original Y/N. This generates R_D H and all four R_D F on any paid common resolvent/form domain; atom numbers are not canonical coordinates.',
        'source_lapse': str(N), 'source_denominator': str(n*delta),
        'normalized_identity': '1/[n(n^2-|b|^2)] = 2 integral_0^1 r dr average_S2 (n-r omega.b)^(-3)',
        'zero_shift_regular_radial_antiderivative': str(radial),
        'superoperators': 'C_a=c_a I+D_a; J_a(X)=(C_a X+X C_a)/2; l=(1,-r omega); R_l=(sum l_a J_a)^-1.',
        'quadratic_coefficient': 'T_ab=integral r dr average(R J_a R J_b R+R J_b R J_a R). The four linear weights are J_a; diagonal gauge weights (T_00-T_ii)/2, off diagonal -T_ij, cross -T_0i.',
        'T_integrands': {str((a,b)): encode_words(cone_expression(a,b)) for a,b in combinations_with_replacement(range(4),2)},
        'original_F_integrands': {str((a,b,j)): encode_words(cone_expression(a,b,j))
            for a,b in combinations_with_replacement(range(4),2) for j in range(4)},
        'derivative_convention': 'Differentiate c with D fixed: partial_cj R=-l_j R^2, partial_cj J_a=delta_aj Id. This is original -partial_y H before retraction, not a derivative in D and not trace stationarity.',
        'ordered_Jordan_moments_through_degree3': coefficients,
        'original_force_ordered_moments_through_degree3': forces,
        'moment_scope': 'Each ordered Jordan composition has its own checked coefficient, with symbolic N; substitution of the previously generated noncommuting D series preserves the equality.',
        'primary_graph_scope': 'These are the exact coefficient and original-force maps of the same inner primary graph. The full grade-zero clock solving all four forces and its closed operator domain are not assumed to exist.'}


def finite_grade_inverse():
    nn = s.Symbol('n', positive=True); alpha,beta = s.symbols('alpha beta')
    C = {():nn, ('Y',):alpha, ('Y','Y'):beta}; X = {('X',):1}
    R = {('Y',):alpha, ('Y','Y'):beta}
    def jordan(row): return scale(s.Rational(1,2),add(mul(R,row,2),mul(row,R,2)))
    powers = [X]
    for _ in range(3): powers.append(jordan(powers[-1]))
    assert not powers[3]
    inverse = add(*(scale((-1)**k/nn**(k+1),powers[k]) for k in range(3)))
    assert add(scale(s.Rational(1,2),add(mul(C,inverse,2),mul(inverse,C,2))),scale(-1,X)) == {}
    t = s.Symbol('t', nonnegative=True)
    exponential = add(*(scale((-t)**k/factorial(k),powers[k]) for k in range(3)))
    derivative = {w:s.diff(c,t) for w,c in exponential.items()}
    assert not add(derivative,jordan(exponential))
    inverses = {}
    for m in (1,2,3):
        row = add(*(scale((-1)**k*s.binomial(m+k-1,k)/nn**(m+k),powers[k]) for k in range(3)))
        for k in range(3):
            assert s.integrate(t**(m+k-1)*s.exp(-nn*t),(t,0,s.oo))/factorial(m-1)/factorial(k) == s.binomial(m+k-1,k)/nn**(m+k)
        inverses[str(m)] = encode_words(row)
    return inverse, {'N2_C_clock': encode_words(C), 'N2_inverse_with_arbitrary_grade0_X':encode_words(inverse),
        'N2_inverse_powers': inverses,
        'core_semigroup': 'For C=N I+R with strictly positive source grade, exp(-t J_C)X=e^(-Nt) sum_{k=0}^{Nf-grade(X)} (-t)^k J_R^k(X)/k!. All products act on the same compact smooth Gauss core.',
        'core_inverse': 'J_C^-m X=sum_k (-1)^k binom(m+k-1,k) N^(-m-k) J_R^k(X). This is a finite exact operator identity on each original particle sector, with no smallness or bounded-X premise.',
        'actual_vector_bound': 'For each actual compact smooth f, ||J_C^-m X f|| <= sum_k binom(m+k-1,k) N^(-m-k)||J_R^k(X) f||; all norms are finite source-core graph seminorms.',
        'tail_bound': 'The k summand beyond T is bounded by ||J_R^k(X) f|| e^(-NT) (m+k-1)!/[k!(m-1)! N^(m+k)] sum_{j=0}^{m+k-1}(NT)^j/j!.',
        'general_grade_zero_lifting': 'Given an actual grade-preserving Sylvester inverse S0^-1 for C0 on the invariant source core, (S0+J_R)^-1 X=sum_k (-S0^-1 J_R)^k S0^-1 X. The sum terminates by the original source grade, retaining all intervening unbounded grade0 operators and derivative terms.',
        'particle_sector_scope': 'Every formula is exact on each finite particle sector and hence on the algebraic finite-particle compact source core. No uniform operator-norm bound across all particle numbers is asserted.',
        'grade_zero_premise': 'The last general lifting consumes a generated grade0 inverse; it does not provide the full source quantum clock or its inverse.'}


def specialization_readout(saved):
    eps = s.Symbol('epsilon'); yy = s.Symbol('Y'); a0=s.Rational(9,5)
    clock = N*sum(s.binomial(-s.Rational(1,2),k)*(eps*yy/(N*a0))**k for k in range(3))
    energy = 2*a0*N*sum(s.binomial(s.Rational(1,2),k)*(eps*yy/(N*a0))**k for k in range(3))
    def trunc(expr): return s.Poly(s.expand(expr),yy).terms()
    def quotient(expr): return s.factor(sum(c*yy**k[0] for k,c in trunc(expr) if k[0]<3))
    assert quotient(clock**2*(a0+eps*yy/N)-a0*N*N) == 0
    for k in range(1,3):
        D=sum(s.sympify(row['coefficient'])*N**(-k) for row in saved['full_original_Y']['time_coefficients'][0][k] if row['word']==[13]*k)
        E=sum(s.sympify(row['coefficient'])*N**(-k) for row in saved['full_original_Y']['energy_coefficients'][k] if row['word']==[13]*k)
        assert s.simplify(s.expand(clock).coeff(yy,k).coeff(eps,k)-D)==0
        assert s.simplify(s.expand(energy).coeff(yy,k).coeff(eps,k)-E)==0
    return {'scope':'SPECIALIZATION_OF_ORIGINAL_FORMAL_COEFFICIENT_ALGEBRA_NOT_AN_ASSERTED_PHYSICAL_SECTOR',
        'specialization':'Set the thirteen grade0 atom symbols to zero and retain original atom13=Y/N; no claim that these symbols vanish simultaneously in the actual source.',
        'N2_clock':str(s.expand(clock)), 'N2_energy':str(s.expand(energy)),
        'exact_quotient_clock_equation':True, 'previous_full_Y_D1_D2_and_E1_E2_recovered':True,
        'arbitrary_particle_number':'N(1+epsilon Y/(N a0))^(-1/2) and 2a0 N(1+epsilon Y/(N a0))^(1/2) are finite binomial polynomials modulo Y^(Nf+1), for every epsilon in this coefficient specialization.'}


def multiply_affine_jet(Y, dY, jet, keep_derivatives=True):
    result = {}
    def row(word):
        return result.setdefault(word, {'value':s.S.Zero,'gradient':s.zeros(100,1),'Hessian':s.zeros(100)})
    for word,item in jet.items():
        for out,c in apply_superposition(Y,{word:1}).items():
            target=row(out); target['value']+=c*item['value']
            target['gradient']+=c*item['gradient']; target['Hessian']+=c*item['Hessian']
        if not keep_derivatives: continue
        for j,derivative in dY.items():
            for out,c in apply_superposition(derivative,{word:1}).items():
                target=row(out); target['gradient'][j]+=c*item['value']
                for k,v in item['gradient'].todok().items():
                    target['Hessian'][j,k[0]]+=c*v; target['Hessian'][k[0],j]+=c*v
    answer={}
    for word,item in result.items():
        item={'value':s.factor(item['value']), 'gradient':rational(item['gradient']), 'Hessian':rational(item['Hessian'])}
        if item['value'] or item['gradient'].todok() or item['Hessian'].todok(): answer[word]=item
    return answer


def actual_core_consumer(inverse):
    model=SourceCommonTemporalForm(); section=model.section; native=model.native
    q=tuple(section.b0[:6,0]); x=section.b0[6:67,:]; A=section.b0[67:,:].reshape(3,12)
    data=model.coefficients((N,0,0,0),q,x,A); M0,Y=split_matter(data)
    common=native.graph.common; embedding=native.graph.R
    factor=s.SparseMatrix(s.kronecker_product(N*GAMMA[0],s.eye(63)))
    original=[]
    for j in range(70):
        block=clean(factor*s.SparseMatrix(common.yukawa_basis[j%35])*(1 if j<35 else s.I))
        original.append(s.SparseMatrix(s.diag(block,-block.conjugate())))
    phi=native.graph.constraints.vacuum+embedding*x
    equal(clean(sum((original[i]*phi[i] for i in range(70) if phi[i]),s.zeros(504))),Y)
    dY={}
    for j in range(61):
        derivative=clean(sum((original[i]*embedding[i,j] for i in range(70) if embedding[i,j]),s.zeros(504)))
        if derivative.todok(): matrix_grade(derivative,1); dY[6+j]=s.SparseMatrix(derivative)
    word=(144,396)
    g=s.zeros(100,1); g[0]=s.Rational(1,7); g[73]=s.Rational(1,13)
    for j in range(6,67):g[j]=s.I*s.Rational(j%7+1,31)
    H=s.zeros(100); H[0,0]=s.Rational(1,17); H[25,25]=-s.Rational(1,19); H[73,73]=s.Rational(1,23)
    slice_jet={word:{'value':s.S.One,'gradient':g,'Hessian':H}}
    slices=[slice_jet]
    for _ in range(3): slices.append(multiply_affine_jet(Y,dY,slices[-1]))
    assert slices[1] and slices[2] and not slices[3]
    images=[]; Gauss=[]; pieces=[]
    for k,local in enumerate(slices[:3]):
        jet=section.extend_jet({w:r['value'] for w,r in local.items()},
            {w:r['gradient'] for w,r in local.items()}, {w:r['Hessian'] for w,r in local.items()})
        Gauss.append(section.verify_Gauss_jet(jet))
        action=model.action(data,jet); images.append(action['H0']); pieces.append(action['pieces'])
        state_grade(images[-1],2,k)
        print('PASS actual full H0 on Y^'+str(k)+' Gauss section, '+str(len(jet))+' jet words',flush=True)
    frozen=multiply_affine_jet(Y,dY,slice_jet,keep_derivatives=False)
    frozenjet=section.extend_jet({w:r['value'] for w,r in frozen.items()},
        {w:r['gradient'] for w,r in frozen.items()}, {w:r['Hessian'] for w,r in frozen.items()})
    wrong=model.action(data,frozenjet)['H0']
    derivative_defect=weighted_sum([(1,images[1]),(-1,wrong)])
    assert derivative_defect, 'The actual scalar gradient must expose the differentiated original Y.'
    @lru_cache(None)
    def image(word):
        assert word.count('X')==1
        j=word.index('X'); right=len(word)-j-1
        if right>=3:return {}
        result=images[right]
        for _ in range(j):result=apply_superposition(Y,result)
        return result
    a0=s.Rational(9,5); alpha=-1/(2*a0); beta=3/(8*N*a0*a0)
    substitution={'n':N,'alpha':alpha,'beta':beta}
    Z={w:s.factor(c.subs({v:substitution[str(v)] for v in c.free_symbols})) for w,c in inverse.items()}
    C={():N,('Y',):alpha,('Y','Y'):beta}
    residual=add(scale(s.Rational(1,2),add(mul(C,Z),mul(Z,C))),{('X',):-1})
    actual_residual=weighted_sum((c,image(w)) for w,c in residual.items())
    assert not actual_residual
    interleaved=image(('Y','X','Y')); assert interleaved
    output=weighted_sum((c,image(w)) for w,c in Z.items())
    without_interleaved=weighted_sum((c,image(w)) for w,c in Z.items() if w!=('Y','X','Y'))
    assert weighted_sum([(1,output),(-1,without_interleaved)])
    return {'source_time':list(map(str,(N,0,0,0))), 'q':list(map(str,q)), 'x61':encode(x),'A36':encode(A),
        'input_CAR':list(word),'gradient100':encode(g),'Hessian100':encode(H),
        'source_Y_derivative_count':len(dY), 'original_full504_Y':encode(Y),
        'three_actual_Gauss_jets':Gauss,
        'full_H0_on_Y_power_sections':[encode_state(a) for a in images],
        'four_original_H0_components':[{k:encode_state(v) for k,v in row.items()} for row in pieces],
        'Y_H0_Y':encode_state(interleaved),'deleting_actual_Y_derivatives_defect':encode_state(derivative_defect),
        'exact_Sylvester_inverse_H0':encode_state(output),'Sylvester_residual':encode_state(actual_residual),
        'source_Y_cubic_full_twojet_zero':True,
        'scope':'Actual source-point fiber readback on smooth compact Gauss sections, using all four original H0 components and full504 CAR. H0 differentiates Y coefficients and every Gauss extension jet. No integrated norm or spectral pole is inferred.'}


def positive_injective_form_inverse():
    lam,mu,eta=s.symbols('lambda mu eta',positive=True)
    t=s.Symbol('t',nonnegative=True)
    kernel=2*s.sqrt(lam*mu)/(lam+mu)
    assert s.simplify(2*s.integrate(s.sqrt(lam*mu)*s.exp(-t*(lam+mu)),(t,0,s.oo))-kernel)==0
    assert s.simplify((lam+mu)*kernel/2-s.sqrt(lam*mu))==0
    difference=2*s.sqrt(lam*mu)*(1/(lam+mu)-1/(lam+mu+2*eta))
    assert s.simplify(2*s.integrate(s.sqrt(lam*mu)*s.exp(-t*(lam+mu))*(1-s.exp(-2*eta*t)),(t,0,s.oo))-difference)==0
    assert s.factor(difference.subs(mu,lam)-eta/(lam+eta))==0
    return {'premise':'C is an actual positive injective self-adjoint clock on the source Hilbert space; h(u,v)=<C^(1/2)u,B C^(1/2)v> with bounded B and ||B||<=M. C and this relative form bound must be generated from the source, not postulated as completed time reduction.',
        'producer':'<u,R_C(h)v>=2 integral_0^infinity h(e^(-tC)u,e^(-tC)v) dt. The spectral energy identity integral ||C^(1/2)e^(-tC)u||^2 dt=||u||^2/2 gives absolute convergence and ||R_C(h)||<=M, without a uniform positive gap or bounded h.',
        'weak_equation':'For u,v in Dom(C), [<Cu,R_C(h)v>+<u,R_C(h)Cv>]/2=h(u,v), by integration of the derivative of the semigroup pairing.',
        'regularizer':'Replace C by C+eta I in the semigroup while keeping h fixed. For every u,v, |<u,(R_C(h)-R_(C+eta)(h))v>|<=M ||[eta(C+eta)^-1]^(1/2)u|| ||[eta(C+eta)^-1]^(1/2)v||. Injectivity and the uniform bound imply strong convergence as eta decreases to0.',
        'spectral_kernel':str(kernel),
        'positive_regularizer_difference_Gram_kernel':str(s.factor(difference)),
        'Gram_diagonal':str(eta/(lam+eta)),
        'nested_cone_scope':'Each further R or J insertion in the exact cone expression needs its corresponding relative form domain and integrability in r,omega. The single-inverse construction does not silently supply these or an actual solution of the four clock equations. This self-adjoint positive-C argument is not applied to the non-Hermitian full original Y clock; its positive-grade extension uses the separate finite lifting.'}


def main():
    start=time.monotonic()
    deps=('source_canonical_star_temporal_reduction','independent_source_canonical_star_temporal_reduction',
        'source_common_temporal_form','independent_source_common_temporal_form',
        'source_common_weyl_symbol','independent_source_common_weyl_symbol',
        'source_full_quantum_adjoint','independent_source_full_quantum_adjoint',
        'source_quantum_grade_structure','source_yukawa_reducing_carrier')
    saved={name:bound(name) for name in deps}
    cone=exact_cone_coefficients(); print('PASS all13 exact cone coefficient maps, 850 ordered moments and3400 original force moments',flush=True)
    inverse,grade=finite_grade_inverse(); specialization=specialization_readout(saved['source_canonical_star_temporal_reduction'])
    print('PASS finite source grade Sylvester inverse, semigroup and coefficient specialization',flush=True)
    actual=actual_core_consumer(inverse)
    files=[HERE/(name+'.json') for name in deps]+[HERE/name for name in (
        'source_temporal_cone_resolvent.py','source_common_temporal_form.py','source_full_quantum_adjoint.py',
        'source_quantum_gauss_section.py','source_scalar_form_hamiltonian.py','source_quantum_ordered_temporal.py')]
    files += [HERE/name for name in ('FockFilteredWords.lean','FockRaisingTensor.lean','FockRaising.lean')]
    out={'root':ROOT_ID,'scope':'EXACT_SOURCE_TEMPORAL_CONE_COEFFICIENT_MAP_AND_FINITE_POSITIVE_GRADE_SYLVESTER_LIFTING',
        'source_sha256':saved['source_common_temporal_form']['source_sha256'],
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'exact_source_coefficient_map':cone,'finite_source_grade_inverse':grade,
        'formal_coefficient_specialization':specialization,'actual_unbounded_H0_consumer':actual,
        'positive_injective_form_inverse':positive_injective_form_inverse(),
        'full_grade_zero_quantum_clock_generated':False,
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-start,3)}
    (HERE/'source_temporal_cone_resolvent.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('PASS source temporal cone resolvent',out['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
