#!/usr/bin/env python3
"""PBW audit of the original four-primary-pair canonical graph reduction.

Normal Heisenberg products, pi eta = eta pi - i, replace the candidate's
Moyal multiplier. Finite normal-to-Weyl contractions are performed only at
readback. All physical coefficients remain noncommuting source-operator words.
"""
from __future__ import annotations

from functools import lru_cache
from math import factorial, comb
import hashlib
import itertools
import json
from pathlib import Path
import time
import sympy as s

from independent_source_coframe_live_ordering import (
    RawLiveCoefficients, HERE, ROOT, ROOT_ID, bindings, encode)
from independent_source_spatial_active_phase_splice import DOMAIN, field_number

ZERO = (0, 0, 0, 0)
II = field_number(s.I)
ORDER = 3


def collect(rows):
    out = {}
    for key, value in rows: out[key] = out.get(key, DOMAIN.zero)+value
    return {key: value for key, value in out.items() if value != DOMAIN.zero}


def plus(*polynomials): return collect((key, c) for p in polynomials for key, c in p.items())
def scaled(c, polynomial):
    c = c if isinstance(c, type(DOMAIN.one)) else field_number(c)
    return {key: c*v for key, v in polynomial.items() if c*v != DOMAIN.zero}


@lru_cache(None)
def contractions(left_pi, right_eta):
    result = []
    for k in itertools.product(*(range(min(a, b)+1) for a, b in zip(left_pi, right_eta))):
        c = (-II)**sum(k)
        for a, b, n in zip(left_pi, right_eta, k): c *= comb(a, n)*factorial(b)//factorial(b-n)
        result.append((k, c))
    return tuple(result)


def normal_product(left, right):
    groups = [[[] for _ in range(ORDER+1)] for _ in range(2)]
    for group, polynomial in zip(groups, (left, right)):
        for key, value in polynomial.items(): group[key[0]].append((key, value))
    rows = []
    for n in range(ORDER+1):
        for m in range(ORDER+1-n):
            for (_, a, b, w), value in groups[0][n]:
                for (_, c, d, v), coefficient in groups[1][m]:
                    for k, factor in contractions(b, c):
                        eta = tuple(a[i]+c[i]-k[i] for i in range(4))
                        pi = tuple(b[i]+d[i]-k[i] for i in range(4))
                        rows.append(((n+m, eta, pi, w+v), value*coefficient*factor))
    return collect(rows)


def normal_commutator(left, right): return plus(normal_product(left, right), scaled(-1, normal_product(right, left)))


def normal_weyl(polynomial, sign=1):
    """exp(sign*i/2 d_eta.d_pi); sign+ converts normal symbols to Weyl."""
    rows = []
    for (n, a, b, w), value in polynomial.items():
        for k in itertools.product(*(range(min(x, y)+1) for x, y in zip(a, b))):
            factor = (sign*II/2)**sum(k)
            for x, y, r in zip(a, b, k): factor *= comb(x, r)*factorial(y)//factorial(y-r)
            eta = tuple(a[i]-k[i] for i in range(4)); pi = tuple(b[i]-k[i] for i in range(4))
            rows.append(((n, eta, pi, w), value*factor))
    return collect(rows)


def readback(polynomial):
    rows = []
    for (n, a, b, w), value in polynomial.items():
        if a != b: continue
        factor = (II/2)**sum(a)
        for power in a: factor *= factorial(power)
        rows.append(((n, ZERO, ZERO, w), value*factor))
    return collect(rows)


def derivative(polynomial, j):
    rows = []
    for (n, a, b, w), c in polynomial.items():
        if a[j]:
            aa = list(a); aa[j] -= 1
            rows.append(((n, tuple(aa), b, w), c*a[j]))
    return collect(rows)


def free_letter(j): return {(0, ZERO, ZERO, (j,)): DOMAIN.one}
def eta(j): return {(0, tuple(int(i == j) for i in range(4)), ZERO, ()): DOMAIN.one}
def primary(j): return {(0, ZERO, tuple(int(i == j) for i in range(4)), ()): DOMAIN.one}
UNIT = {(0, ZERO, ZERO, ()): DOMAIN.one}


def generator(D): return scaled(-1, plus(*(normal_product(primary(j), D[j]) for j in range(4))))


def conjugate(D, polynomial, inverse=False):
    G = generator(D); out = term = polynomial
    for r in range(1, ORDER+1):
        term = scaled((II if inverse else -II)/r, normal_commutator(G, term))
        out = plus(out, term)
    return out


def retract(D, polynomial): return readback(conjugate(D, polynomial))
def lift(D, polynomial): return conjugate(D, polynomial, inverse=True)


def truncate_germ(polynomial):
    return {key: c for key, c in polynomial.items() if key[0]+sum(key[1]) <= ORDER}


def dagger(polynomial):
    # This mouth is used for retained coefficients (no eta/pi), so no normal
    # reordering is hidden in word reversal.
    out = []
    for (n, a, b, w), c in polynomial.items():
        assert a == b == ZERO
        reverse = tuple(14 if j == 13 else 13 if j == 14 else j for j in reversed(w))
        out.append(((n, ZERO, ZERO, reverse), field_number(s.conjugate(DOMAIN.to_sympy(c)))))
    return collect(out)


def coefficient(polynomial, n): return {key: c for key, c in polynomial.items() if key[0] == n}


def words(polynomial, degree):
    out = {}
    for (n, a, b, w), c in polynomial.items():
        assert a == b == ZERO
        if n == degree: out[w] = c
    return out


def original_family(yukawa):
    active = json.loads((HERE.parent/'active-gauge/receipt.json').read_text())
    N = s.sympify(active['actual_background']['coframe'][0][0])
    n = s.Symbol('native_n', positive=True); b = s.symbols('native_b0:3', real=True); y = (n, *b)
    at = dict(zip(y, (N, 0, 0, 0))); delta = n*n-sum(v*v for v in b)
    pairs = ((0,0),(1,1),(2,2),(0,1),(0,2),(1,2))
    weights = [*y, *[(n*n-b[i]*b[j])/(2*n*delta) if i == j else -b[i]*b[j]/(n*delta) for i,j in pairs],
               *[-v/delta for v in b]]
    origin = [s.Rational(9,5),0,0,0,*[s.Rational(324,625)]*3,*[0]*6]
    seed = sum(c*f for c,f in zip(origin, weights))
    polynomials = [s.Poly(s.cancel(2*n*delta*f), *y) for f in weights]
    monomials = sorted(set().union(*(set(p.monoms()) for p in polynomials)))
    assert s.Matrix([[p.coeff_monomial(m) for p in polynomials] for m in monomials]).rank() == 13
    J = s.Matrix(4,4,lambda i,j:-s.diff(seed,y[i],y[j]).subs(at))
    assert J == s.diag(-s.sqrt(30), *[-2*s.sqrt(30)/3]*3)
    assert all(s.simplify(s.diff(seed,v).subs(at)) == 0 for v in y)
    # One common Taylor jet is differentiated before germ truncation, so F
    # is the derivative of the original family, including the seed quartic.
    rows = []
    for a in itertools.product(range(5), repeat=4):
        if sum(a)>4: continue
        def taylor(f):
            for v, power in zip(y,a):
                if power: f=s.diff(f,v,power)/factorial(power)
            return field_number(s.simplify(f.subs(at)))
        c=taylor(seed)
        if c:rows.append(((0,a,ZERO,()),c))
        if sum(a)>=4:continue
        for j,f in enumerate(weights):
            c=taylor(f)
            if c:
                rows.append(((1,a,ZERO,(j,)),c))
                if j==0 and yukawa is not None: rows.append(((1,a,ZERO,(yukawa,)),c))
    full=collect(rows)
    # Primary evolution differentiates H before retraction, so its scalar
    # Taylor jet has one more eta degree than the energy readback needs.
    H=full;F=[truncate_germ(scaled(-1,derivative(full,j)))for j in range(4)]
    return N,J,H,F


def solve(H,F,J):
    D=[{}for _ in range(4)];stages=[]
    for n in range(1,ORDER+1):
        residual=[coefficient(retract(D,f),n)for f in F]
        for j in range(4):D[j]=plus(D[j],scaled(-1/J[j,j],residual[j]))
        for f in F:assert not {key:c for key,c in retract(D,f).items()if key[0]<=n}
        stages.append([len(words(p,n))for p in D])
    energy=retract(D,H)
    return D,energy,stages


def left_substitute(polynomial,D):
    answer={}
    for(n,a,b,w),c in polynomial.items():
        assert b==ZERO
        term={(n,ZERO,ZERO,w):c}
        for j,power in enumerate(a):
            for _ in range(power):term=normal_product(term,D[j])
        answer=plus(answer,term)
    return answer


def old_solve(H,F,J):
    D=[{}for _ in range(4)]
    for n in range(1,ORDER+1):
        r=[coefficient(left_substitute(f,D),n)for f in F]
        for j in range(4):D[j]=plus(D[j],scaled(-1/J[j,j],r[j]))
        for f in F:assert not {k:c for k,c in left_substitute(f,D).items()if k[0]<=n}
    return D,left_substitute(H,D)


def extension_consumers(D,H,F,energy):
    f,g=free_letter(1),free_letter(10)
    Lf,Lg=lift(D,f),lift(D,g)
    assert conjugate(D,Lf)==f and retract(D,Lf)==f
    assert normal_product(Lf,Lg)==lift(D,normal_product(f,g))
    assert retract(D,normal_commutator(Lf,H))==normal_commutator(f,energy)
    for row in F:assert not retract(D,normal_commutator(Lf,row))
    for j in range(4):
        assert retract(D,primary(j))=={}
        assert retract(D,eta(j))==D[j]
        for k in range(4):
            expected=scaled(s.I if j==k else 0,UNIT)
            assert normal_commutator(eta(j),primary(k))==expected
        assert retract(D,normal_product(eta(j),primary(j)))==scaled(s.I/2,UNIT)
    # The full mixed symbol keeps pi; normal/Weyl conversion checks the
    # claimed derivation before any retraction discards those components.
    mixed=normal_product(normal_product(eta(0),eta(1)),normal_product(primary(2),f))
    W=normal_weyl(mixed)
    actual=normal_weyl(scaled(-s.I,normal_commutator(generator(D),mixed)))
    expected={}
    for j in range(4):
        # D has no primary coordinates, so multiplying it by a Weyl symbol
        # needs only physical-word multiplication, with no temporal contraction.
        comm=plus(normal_product(D[j],W),scaled(-1,normal_product(W,D[j])))
        # primary(j) here is ordinary Weyl multiplication, not a star product.
        pi_times={}
        for(n,a,b,w),c in comm.items():
            bb=list(b);bb[j]+=1;pi_times[n,a,tuple(bb),w]=c
        dx=derivative(W,j)
        expected=plus(expected,scaled(s.I,pi_times),scaled(s.Rational(1,2),plus(normal_product(D[j],dx),normal_product(dx,D[j]))))
    assert actual==expected
    return {'all16_primary_CCR_checked':True,'normal_to_Weyl_derivation_with_nonzero_primary_terms':True,
            'U_L_identity':True,'R_L_identity':True,'L_preserves_actual_observable_product':True,
            'lifted_Heisenberg_identity':True,'all_four_lifted_secondary_commutators_zero':True,
            'R_is_not_an_arbitrary_product_homomorphism':True,'nonmultiplicative_value':'I/2',
            'lift_term_counts':[len(Lf),len(Lg)]}


def multiplier_consumer(D,H,F,J,energy):
    Lam=[{}for _ in range(4)];stages=[]
    def total():return plus(H,*(normal_product(primary(j),Lam[j])for j in range(4)))
    def rate(X):return retract(D,scaled(-s.I,normal_commutator(X,total())))
    for n in range(1,ORDER+1):
        residual=[coefficient(rate(f),n)for f in F]
        for j in range(4):Lam[j]=plus(Lam[j],scaled(-1/J[j,j],residual[j]))
        for f in F:assert not {key:c for key,c in rate(f).items()if key[0]<=n}
        stages.append([len(words(p,n))for p in Lam])
    assert retract(D,total())==energy
    for j in range(4):
        # This directly differentiates the retained H4 jet. In particular it
        # does not replace a failed primary commutator by the supplied F jet.
        assert rate(primary(j))==retract(D,F[j])=={}
        assert rate(eta(j))==Lam[j]
        assert Lam[j]==scaled(-s.I,normal_commutator(D[j],energy))
    f=free_letter(1)
    assert rate(lift(D,f))==scaled(-s.I,normal_commutator(f,energy))
    return Lam,{'multiplier_word_counts':stages,
        'original_primary_rates_computed_from_one_higher_H_jet':True,
        'all_four_original_primary_and_four_secondary_projected_rates_zero':True,
        'R_total_H_equals_energy':True,'all_four_time_updates_equal_intrinsic_D_commutator':True,
        'lifted_observable_total_H_dynamics':True}


def parse_series(rows):
    return collect(((n,ZERO,ZERO,tuple(row['word'])),field_number(s.sympify(row['coefficient'])))
                   for n,items in enumerate(rows)for row in items)


def encode_series(polynomial):
    return [[{'word':list(w),'coefficient':str(DOMAIN.to_sympy(c))}for w,c in sorted(words(polynomial,n).items())]
            for n in range(ORDER+1)]


def compare_branch(D,energy,Lam,branch):
    assert D==[parse_series(row)for row in branch['time_coefficients']]
    assert energy==parse_series(branch['energy_coefficients'])
    total=branch['original_total_Hamiltonian']
    assert Lam==[parse_series(row)for row in total['multiplier_coefficients']]


def raw_K2(candidate,J):
    raw=RawLiveCoefficients();q=raw.q;p=s.Matrix(s.symbols('audit_canonical_p0:6',real=True))
    Q=s.cancel((p.T*raw.K*p)[0]/raw.N);point=dict(zip(q,(1,0,1,0,0,1)))
    second=s.S.Zero
    for i in range(6):
        for j in range(6):
            second+=(s.diff(Q,q[i],p[j]).subs(point)*s.diff(Q,p[i],q[j]).subs(point)-
                     s.diff(Q,q[i],q[j]).subs(point)*s.diff(Q,p[i],p[j]).subs(point))/4
    matrix=s.hessian(s.expand(second),list(p))/2
    from independent_source_gauge_legendre import decode
    assert matrix==matrix.T
    assert all(s.simplify(v)==0 for v in -8*matrix-decode(candidate['Lambda2_quadratic_matrix']))
    correction=matrix/(2*J[0,0])
    assert all(s.simplify(v)==0 for v in correction-decode(candidate['K2_star_minus_commuting_quadratic_matrix']))
    assert s.simplify(matrix[0,0]-s.Rational(3,16))==0
    assert s.simplify(correction[0,0]+s.sqrt(30)/320)==0
    assert s.sympify(candidate['canonical_kappa0_squared_coefficient'])==correction[0,0]
    return {'raw_original_BF_all_sixq_bidifferential_rebuilt':True,
            'whole_six_by_six_quadratic_correction':encode(correction),
            'canonical_kappa0_squared_difference':str(correction[0,0]),
            'scope':'Exact degree2 coframe momentum coefficient on the original vacuum: only the lapse atom has q momenta, and cross contractions with the other original components cannot retain degree2. This compares canonical operator composition with commuting invariant substitution, not the two reduction rules.'}


def source_fock_audit(D,energy,D0,E0,candidate,N,source_hashes=None):
    from collections import Counter
    from independent_source_joint_temporal_rates import RawSource,clean,eq
    from independent_source_coframe_live_ordering import current,state_encode
    from independent_source_gauge_legendre import decode
    from independent_source_gauss_quantum_current import decoded_state
    def grade_series(polynomial):
        rows=[]
        for n in range(ORDER+1):
            coefficients=words(polynomial,n)
            assert all(len(w)==n and all(0<=a<=13 for a in w)for w in coefficients)
            counts=dict(sorted(Counter(w.count(13)for w in coefficients).items()))
            rows.append({'order':n,'word_count':len(coefficients),
                         'Y_grade_word_counts':{str(g):v for g,v in counts.items()},
                         **{'words_not_eliminated_by_N'+str(k)+'_grade_bound':sum(v for g,v in counts.items()if g<=k)for k in range(3)}})
        return rows
    stripped=lambda p:{key:c for key,c in p.items()if 13 not in key[3]}
    assert [stripped(d)for d in D]==D0 and stripped(energy)==E0
    time_grades=[grade_series(d)for d in D];energy_grades=grade_series(energy)
    assert time_grades==candidate['actual_time_word_grades']
    assert energy_grades==candidate['actual_energy_word_grades']
    # Evaluate the original native Hodge weights on the actual27 time columns.
    rows=[]
    for triple in itertools.product((-1,0,1),repeat=3):
        b=[N*s.Rational(i,4)for i in triple];delta=N*N-sum(v*v for v in b)
        assert delta>0
        pairs=((0,0),(1,1),(2,2),(0,1),(0,2),(1,2))
        row=[N,*b,*[(N*N-b[i]*b[j])/(2*N*delta)if i==j else -b[i]*b[j]/(N*delta)for i,j in pairs],*[-v/delta for v in b]]
        rows.append([s.simplify(v)for v in row])
    values=s.Matrix(rows);_,chosen=values.T.rref();assert len(chosen)==13
    minor=values[list(chosen),:];det=s.factor(minor.det());assert det!=0
    supplied=candidate['residual_Gauss']
    eq(minor,decode(supplied['original_time_evaluation_minor']));assert list(chosen)==supplied['original_time_evaluation_rows']
    assert det==s.sympify(supplied['determinant'])
    raw=RawSource()
    if source_hashes is not None: assert raw.hashes==source_hashes
    e=s.Matrix(raw.active['actual_background']['coframe']).applyfunc(s.sympify)
    E=s.kronecker_product(raw.principals(e)[0],s.eye(63))
    single=clean(-s.I*e.det()*E.inv()*raw.yukawa(raw.v))
    Y=clean(s.diag(single,-single.conjugate()));eq(Y*Y,s.zeros(504))
    weights=[int(j%63<7)for j in range(504)]
    for (i,j),c in Y.todok().items():assert (weights[i]-weights[j]-1)*c==0
    w=(144,396);initial={w:s.S.One}
    once=current(Y,initial);twice=current(Y,once);thrice=current(Y,twice)
    assert once and twice and not thrice
    assert twice=={(a,b):-2*N*N for a in(0,2)for b in(252,254)}
    for state,grade in ((initial,0),(once,1),(twice,2)):
        assert all(len(w)==2 and sum(weights[i]for i in w)==grade for w in state)
    grade2={w:c for w,c in words(energy,2).items()if w.count(13)==2};assert set(grade2)=={(13,13)}
    c=DOMAIN.to_sympy(grade2[(13,13)])
    image={w:s.simplify(c*v/N**2)for w,v in twice.items()}
    assert image=={(a,b):s.sqrt(30)/30 for a in(0,2)for b in(252,254)}
    norm=s.simplify(sum(s.conjugate(v)*v for v in image.values()));assert norm==s.Rational(2,15)
    assert {w for w in words(energy,3)if w.count(13)==3}=={(13,13,13)}
    assert s.simplify(DOMAIN.to_sympy(words(energy,3)[(13,13,13)])-s.sqrt(30)/216)==0
    saved=candidate['actual_N2_complement_consumer']
    for state,key in ((once,'original_Y_image'),(twice,'original_Y_squared_image'),(thrice,'original_Y_cubed_image'),(image,'new_E2_grade2_image')):
        assert state==decoded_state(saved[key])
    assert c==s.sympify(saved['new_E2_grade2_word_coefficient'])and norm==s.sympify(saved['Fock_norm_squared'])
    carrier=json.loads((HERE/'source_yukawa_reducing_carrier.json').read_text());bindings(carrier)
    projector=decode(carrier['generated_reducing_projector_real504'])
    eq(projector*projector,projector);eq(projector.H,projector);assert s.trace(projector)==392
    eq(Y*projector,s.zeros(504));eq(Y.H*projector,s.zeros(504))
    for word in initial|once|twice:
        for i in word:eq(projector[:,i],s.zeros(504,1))
    return {'all_actual_D_and_E_word_lengths_and_Y_grades':True,
            'removing_Y_words_equals_independently_solved_H0':True,
            'original_timelike13_coefficient_minor_rank':13,'determinant':str(det),
            'Gauss_consumer':'The already certified current form H0 and isolated Y commute with original Gs; the independently inverted13 real coefficient table extracts each atom. Finite words, pi/eta and the generated canonical graph therefore preserve that same Gauss section.',
            'original70_Y_and_density_principal_rebuilt':True,
            'actual_N2_grade2_image':state_encode(image),'fiber_CAR_norm_squared':str(norm),
            'original_Y_cubed_zero':True,'all_input_output_modes_in_P392_complement':True,
            'no_r_smaller_than_N_bound_or_proton_identification_inferred':True}


def main():
    started=time.monotonic();path=HERE/'source_canonical_star_temporal_reduction.json'
    candidate=json.loads(path.read_text());count=bindings(candidate);assert candidate['root']==ROOT_ID
    paid=('independent_source_common_weyl_symbol','independent_source_scalar_temporal_form',
          'independent_source_temporal_energy_adjoint','source_temporal_energy_adjoint',
          'independent_source_quantum_grade_structure','independent_source_yukawa_reducing_carrier',
          'source_yukawa_reducing_carrier','independent_source_quantum_stabilizer')
    records={name:json.loads((HERE/(name+'.json')).read_text())for name in paid}
    for record in records.values():count+=bindings(record);assert record['root']==ROOT_ID
    N,J,H0,F0=original_family(None);D0,E0,stages0=solve(H0,F0,J)
    assert all(dagger(v)==v for v in [*D0,E0])
    ext0=extension_consumers(D0,H0,F0,E0);Lam0,total0=multiplier_consumer(D0,H0,F0,J,E0)
    assert all(dagger(v)==v for v in Lam0)
    compare_branch(D0,E0,Lam0,candidate['H0'])
    print('PASS independent PBW H0 D/E/Lambda and original eight projected constraints, with H4 primary coverage',flush=True)
    _,_,H,F=original_family(13);D,E,stages=solve(H,F,J)
    ext=extension_consumers(D,H,F,E);Lam,total=multiplier_consumer(D,H,F,J,E)
    compare_branch(D,E,Lam,candidate['full_original_Y'])
    _,_,Hs,Fs=original_family(14);Ds,Es,_=solve(Hs,Fs,J);Lams,totals=multiplier_consumer(Ds,Hs,Fs,J,Es)
    assert Ds==[dagger(v)for v in D]and Es==dagger(E)and Lams==[dagger(v)for v in Lam]
    assert any(dagger(v)!=v for v in D)
    print('PASS independent originalY and sharp branches, all lifted dynamics and multiplier adjoint pairing',flush=True)
    _,old0=old_solve(H0,F0,J);_,old=old_solve(H,F,J)
    assert all(coefficient(old0,n)==coefficient(E0,n)and coefficient(old,n)==coefficient(E,n)for n in range(3))
    defect=plus(coefficient(old0,3),scaled(-1,coefficient(dagger(old0),3)))
    correction=plus(coefficient(E0,3),scaled(-1,coefficient(old0,3)))
    assert plus(correction,scaled(-1,dagger(correction)))==scaled(-1,defect)
    average=scaled(s.Rational(1,2),plus(coefficient(old0,3),coefficient(dagger(old0),3)))
    comparison=plus(coefficient(E0,3),scaled(-1,average));assert len(comparison)==240
    germ=records['source_temporal_energy_adjoint'];mixed={w:c for w,c in words(defect,3).items()if 0 in w}
    old_words={tuple(row['word']):field_number(s.sympify(row['coefficient']))for row in germ['formal_calculation']['actual_coframe_containing_terms']}
    assert mixed==old_words and len(mixed)==30
    values={tuple(row['word']):field_number(s.sympify(row['value']))for row in germ['actual_consumer']['individual_nested_word_values']}
    value=sum((c*values[w]for w,c in mixed.items()),DOMAIN.zero)
    assert value==field_number(6623*s.sqrt(30)/145673515584)
    actual=candidate['actual_K3_germ'];assert s.sympify(actual['old_K3_adjoint_difference'])==DOMAIN.to_sympy(value)
    assert s.sympify(actual['generated_correction_adjoint_difference'])==-DOMAIN.to_sympy(value)
    K2=raw_K2(candidate['actual_canonical_K2'],J)
    fock=source_fock_audit(D,E,D0,E0,candidate['source_Fock_consumer'],N,candidate['source_sha256'])
    print('PASS independent original canonical K2, actual K3 defect compensation and full-source Fock/Gauss consumers',flush=True)
    paths=[Path(__file__),path,HERE/'source_canonical_star_temporal_reduction.py',
           HERE/'independent_source_coframe_live_ordering.py',HERE/'independent_source_joint_temporal_rates.py',
           HERE/'independent_source_gauss_quantum_current.py',HERE.parent/'active-gauge/receipt.json']+[HERE/(name+'.json')for name in paid]
    output={'verdict':'CERTIFIED_CANONICAL_STAR_TEMPORAL_GRAPH_AND_ORIGINAL_TOTAL_H_CONSTRAINT_EVOLUTION_ORDER3',
            'root':ROOT_ID,'source_sha256':candidate['source_sha256'],
            'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths},
            'source_binding_checks':count,'candidate_constructor_imported':False,
            'independent_method':'PBW normal Heisenberg multiplication and finite normal-to-Weyl contractions; original H4 Taylor differentiated before truncation; independent J0 recursions for graph and total-H multipliers; all retained coefficients remain free source-operator words.',
            'H0':{'D_word_counts':stages0,'energy_word_counts':[len(words(E0,n))for n in range(4)],
                  'all_D_energy_multiplier_coefficients_Hermitian':True,'extended_algebra':ext0,'original_total_H':total0},
            'full_original_Y':{'D_word_counts':stages,'energy_word_counts':[len(words(E,n))for n in range(4)],
                  'all_D_energy_multiplier_coefficients_equal_candidate':True,'independent_sharp_branch_equals_full_word_adjoint':True,
                  'full_graph_Hermitian_assumed':False,'original_Y_kept_without_adding_Ydagger':True,
                  'extended_algebra':ext,'original_total_H':total,'sharp_original_total_H':totals},
            'same_current_form_atoms_K1_K2_equal_old_substitution':True,
            'K3_minus_old_Hermitian_average_free_word_count':240,
            'actual_old_30_word_Gauss_defect':str(DOMAIN.to_sympy(value)),
            'generated_correction_adjoint_defect':str(-DOMAIN.to_sympy(value)),
            'actual_new_K3_adjoint_defect':'0 by the complete generated word identity on the same original domain',
            'actual_canonical_K2':K2,'source_Fock_and_Gauss_consumer':fock,
            'scope':'All stated constraints, multiplication of lifted observables and dynamics are modulo epsilon^4. R is a graph retraction, not a homomorphism on arbitrary extended products. H0 and full-Y/sharp statements are distinct. The nonzero240-word comparison does not assert injectivity of actual operator evaluation.',
            'epsilon_one_sum_Hilbert_evolution_spectrum_or_lifetime_generated':False,
            'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'independent_source_canonical_star_temporal_reduction.json').write_text(json.dumps(output,separators=(',',':'))+'\n')
    print('PASS independent canonical star temporal reduction',output['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
