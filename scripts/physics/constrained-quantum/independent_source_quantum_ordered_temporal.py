#!/usr/bin/env python3
"""Independent ordered-word, original-family and positive-packet audit.

Candidate constructors are output oracles only. Independent epsilon-BF
matrices and literal polynomial differentiation rebuild their operator
values; a commutative Taylor expansion followed by noncommuting symbolic
substitution replaces the producer's word-series convolution.
"""
from __future__ import annotations

from functools import lru_cache
import hashlib
import itertools
from pathlib import Path
import json
import time
import sympy as s

from independent_source_quantum_temporal_symbol import (
    N, SYMMETRIC, original_hessian, geometric_load, original_density_ports,
    original_gamma, quotient_right_inverse, quotient_inverse)
from independent_source_gauss_section_measure import RawSectionMeasure
from independent_source_quantum_gauss_section import general_scalar_action
from independent_source_joint_local_quantum import (
    RawLiveCoefficients, HERE, BASE, ROOT, ROOT_ID, FREE, rational, eq, clean,
    terms, current, polynomial_action, raw_matter, original_inventory,
    bindings, decode, encode, state_encode)
from independent_source_gauss_quantum_current import decoded_state
from independent_source_gauge_legendre import ETA, W, SIGMA, hodge, matrix_coordinates
from source_quantum_ordered_temporal import OrderedTemporalCoefficients, SourceTemporalQuantumFamily
from source_gauss_section_measure import SourceGaussSectionMeasure
from source_spatial_active_phase_splice import field_element, DOMAIN


def zero(value): assert s.cancel(s.expand(value)) == 0

def state_equal(left, right): assert terms([(1, left), (-1, right)]) == {}


def independent_words(candidate):
    n = s.Symbol('independent_n', positive=True)
    b = s.symbols('independent_b1:4', real=True); ys = (n, *b)
    delta = n*n-sum(v*v for v in b)
    # Derive the six symmetric and three antisymmetric contractions from
    # the inverse of the original electric3 block at spatial L=I.
    e = s.eye(4); e[:, 0] = s.Matrix(ys)
    K = rational(-W*hodge(e)/SIGMA)
    inverse = rational(K[:3, :3].inv())
    C = rational(-inverse*K[:3, 3:])
    M = rational(K[3:, :3]*inverse*K[:3, 3:]-K[3:, 3:])
    coefficients = list(ys)
    for i, j in SYMMETRIC:
        coefficients.append(s.cancel(inverse[i, j] if i == j else 2*inverse[i, j]))
    # The atom already contains E/2; its coefficient is the full inverse.
    # The atom is Ct_21-Ct_12, then cyclically; no momenta are commuted.
    coefficients += [C[2, 1], C[0, 2], C[1, 0]]
    source = [s.Rational(9, 5), 0, 0, 0, *[s.Rational(324, 625)]*3, *[0]*6]
    seed = s.factor(sum(a*c for a, c in zip(source, coefficients)))
    source_point = dict(zip(ys, (N, 0, 0, 0)))
    seed_F = [-s.diff(seed, y) for y in ys]
    J = rational(s.Matrix(seed_F).jacobian(ys).subs(source_point))
    eq(s.Matrix(seed_F).subs(source_point), s.zeros(4, 1))
    eq(J, s.diag(-s.sqrt(30), *[-2*s.sqrt(30)/3]*3))
    atoms = s.symbols('audit_op0:14', commutative=False)
    letters = list(atoms[:13]); letters[0] += atoms[13]
    u = s.symbols('delta0:4', real=True); t = s.Symbol('t', real=True)
    epsilon = s.Symbol('word_epsilon', real=True)
    @lru_cache(maxsize=None)
    def taylor(expression, order):
        changed = expression.subs({y: source_point[y]+t*u[a] for a, y in enumerate(ys)}, simultaneous=True)
        expansion = s.series(changed, t, 0, order+1).removeO().expand().subs(t, 1)
        return s.Poly(expansion, *u)
    def substitute(polynomial, Y, degree):
        result = 0
        coefficients = [[s.expand(value).coeff(epsilon, n) for n in range(degree+1)] for value in Y]
        for powers, coefficient in polynomial.terms():
            slots = [a for a, power in enumerate(powers) for _ in range(power)]
            if not slots:
                if degree == 0: result += coefficient
                continue
            if len(slots) > degree: continue
            for composition in itertools.product(range(1, degree+1), repeat=len(slots)):
                if sum(composition) != degree: continue
                term = coefficient
                for a, n in zip(slots, composition): term *= coefficients[a][n]
                result += term
        return s.expand(result)
    def evaluate(Y, degree, equation=-1):
        seed_expr = seed if equation < 0 else seed_F[equation]
        value = substitute(taylor(seed_expr, degree), Y, degree)
        if degree:
            for coefficient, letter in zip(coefficients, letters):
                f = coefficient if equation < 0 else -s.diff(coefficient, ys[equation])
                value += letter*substitute(taylor(f, degree-1), Y, degree-1)
        return s.expand(value)
    Y = [s.S.Zero]*4; actual = [[{}] for _ in range(4)]
    def parse(expression):
        result = {}
        for term in s.Add.make_args(s.expand(expression)):
            commutative, ordered = term.args_cnc()
            coefficient = field_element(s.simplify(s.Mul(*commutative)))
            word = []
            for letter in ordered:
                if letter.is_Pow:
                    assert letter.exp.is_Integer and letter.exp >= 0
                    word.extend([atoms.index(letter.base)]*int(letter.exp))
                else: word.append(atoms.index(letter))
            word = tuple(word)
            result[word] = result.get(word, DOMAIN.zero)+coefficient
        return {word: value for word, value in result.items() if value}
    for degree in range(1, 4):
        residual = s.Matrix([evaluate(Y, degree, a) for a in range(4)])
        step = -J.inv()*residual
        for a in range(4):
            Y[a] = s.expand(Y[a]+epsilon**degree*step[a])
            actual[a].append(parse(step[a]))
        for a in range(4): assert evaluate(Y, degree, a) == 0
    energy = [parse(evaluate(Y, degree)) for degree in range(4)]
    oracle = OrderedTemporalCoefficients()
    produced, generated_energy, stages = oracle.generate(3)
    for a in range(4):
        for degree in range(4): assert actual[a][degree] == produced[a][degree]
    assert energy == generated_energy
    assert [len(v) for v in energy] == candidate['actual_energy_word_counts']
    assert stages == candidate['actual_stages']
    assert s.expand(atoms[0]*atoms[1]-atoms[1]*atoms[0]) != 0
    return energy, {'independent_method': 'Original native Hodge electric inverse; rational Taylor expansion with commuting delta variables; ordered noncommuting SymPy substitution and full4x4 Jacobian solve.',
        'all_temporal_words_through_order3_compared': [[len(v) for v in row] for row in actual],
        'all_energy_words_through_order3_compared': [len(v) for v in energy],
        'ordering_contract': 'Coefficient operators left; delta0,delta1,delta2,delta3 powers ordered. No inner differential-operator factors are commuted.'}


def raw_coframe_family(raw, ys):
    e = raw.e.copy(); e[:, 0] = s.Matrix(ys)
    transform = s.kronecker_product(e, s.eye(6))
    Hi = rational(transform.T*original_hessian(s.eye(4)).inv()*transform/e.det())
    eq(original_hessian(e)*Hi, s.eye(24))
    incoming = s.Matrix(4, 4, s.symbols('raw_time_e0:16', real=True))
    Gt = rational(geometric_load(incoming).xreplace(dict(zip(incoming, e)))[:, :16])
    R = quotient_right_inverse(e)
    Q = rational(R*quotient_inverse(e, e[:, 1:].T*ETA*e[:, 1:])*R.T)
    E, vertices = original_density_ports(e, original_gamma())
    J = [rational(s.diag(s.I*E.inv()*V, s.I*(E.inv()*V).conjugate())) for V in vertices]
    L = rational(raw.S*s.eye(24)[:6, :]+Gt.T*Hi)
    T = [rational(sum((L[i, a]*J[a] for a in range(24)), s.zeros(8))) for i in range(16)]
    weights = rational((L.T*Q*L+Hi)/2)
    output = {'A': raw.A, 'S': raw.S, 'Q': Q, 'Hinv': Hi, 'L': L, 'J': J, 'T': T,
        'K': rational(raw.A.T*Q*raw.A/2), 'W': weights, 'dA': [rational(raw.A.diff(q)) for q in raw.q],
        'dT': [[rational(Ti.diff(q)) for Ti in T] for q in raw.q],
        'M': [rational(sum(((raw.A.T*Q)[r, j]*T[j] for j in range(16)), s.zeros(8))) for r in range(6)],
        'one_body': rational(sum((v*J[a]*J[b] for (a,b),v in weights.todok().items()), s.zeros(8))),
        'drift': rational(-s.I*sum(((raw.A.T*Q)[r,j]*raw.A.diff(q)[j,:] for r,q in enumerate(raw.q) for j in range(16)),s.zeros(1,6))/2),
        'correction': rational(-s.I*sum(((raw.A.T*Q)[r,j]*T[j].diff(q) for r,q in enumerate(raw.q) for j in range(16)),s.zeros(8))/2),
        'constant': 3*e.det()}
    eq(rational(-s.I*e.det()*E.inv()), ys[0]*original_gamma()[0])
    return e, output


def generic_gauge_Gram_identity(e, ys):
    n, *boost = ys
    b = s.Matrix(boost); L = e[1:, 1:]; inverse_L = L.inv()
    delta = n*n-(b.T*b)[0]
    R = (n*n*s.eye(3)-b*b.T)/(2*n*delta)
    cross = s.Matrix([[0,-b[2],b[1]],[b[2],0,-b[0]],[-b[1],b[0],0]])
    metric = e.T*ETA*e
    pairs = ((0,1),(0,2),(0,3),(2,3),(3,1),(1,2))
    K = s.Matrix(6,6,lambda i,j: -(metric[pairs[i][0],pairs[j][0]]*metric[pairs[i][1],pairs[j][1]]-
        metric[pairs[i][0],pairs[j][1]]*metric[pairs[i][1],pairs[j][0]])/(SIGMA*e.det()))
    inverse = rational(L.det()*inverse_L*R*inverse_L.T)
    mixed = rational(-L.det()*inverse_L*cross*inverse_L.T/delta)
    eq(K[:3,:3]*inverse,s.eye(3)); eq(inverse*K[:3,:3],s.eye(3))
    eq(-inverse*K[:3,3:],mixed)
    eq(K[3:,:3]*inverse*K[:3,3:]-K[3:,3:],4*inverse)
    return {'all_sixq_and_fourtime_electric_inverse': True,
        'all_sixq_and_fourtime_magnetic_feedback_is_four_times_electric_inverse': True,
        'all_nine_S_and_d_Gram_atoms_reconstruct_original_gauge_form': True}


def actual_family(candidate, model):
    target = SourceTemporalQuantumFamily(model.section.native)
    raw = RawLiveCoefficients(); e, coefficients = raw_coframe_family(raw, target.y)
    def compare(left, right):
        if isinstance(left, list):
            assert len(left) == len(right)
            for a,b in zip(left,right): compare(a,b)
        elif isinstance(left,s.MatrixBase): eq(left,right)
        else: zero(left-right)
    for name,value in coefficients.items(): compare(value,target.cf[name])
    eq(e,target.e)
    gauge_generic = generic_gauge_Gram_identity(e, target.y)
    print('PASS raw generic all-sixq/fourtime coframe coefficients and original Hodge nine-atom identities', flush=True)
    native = RawSectionMeasure().native
    native.x_symbols=s.Matrix(s.symbols('audit_x0:61',real=True))
    phi=native.v+native.R*native.x_symbols
    native.Dsymbol=clean(native.O.T*s.Matrix.hstack(*(T*phi for T in native.rhob)))
    q=(s.Rational(7,6),s.Rational(1,11),s.Rational(9,8),-s.Rational(1,13),s.Rational(1,17),s.Rational(11,10))
    x=s.zeros(61,1);x[19]=s.Rational(1,101);x[4]=-s.Rational(1,109)
    A=model.section.A0.copy();A[0,2]+=s.Rational(1,31);A[1,7]-=s.Rational(1,37)
    time=(7*N/6,s.Rational(1,11),-s.Rational(1,13),s.Rational(1,17))
    at={**dict(zip(raw.q,q)),**dict(zip(target.y,time))}
    evalue=rational(e.subs(at))
    def evaluate(value):
        if isinstance(value,list):return [evaluate(v)for v in value]
        if isinstance(value,s.MatrixBase):return rational(value.subs(at))
        return s.cancel(value.subs(at))
    cf={name:evaluate(value)for name,value in coefficients.items()}
    sc=native.scalar_data(evalue,x,A)
    from independent_source_joint_local_quantum import gauge_coefficients
    gauge=gauge_coefficients(evalue,A,native.inventory)
    A4=s.zeros(4,12);A4[1:,:]=A
    matter=raw_matter(evalue,sc['phi'],A4)
    H=clean(-s.I*matter['E_inverse']*matter['lower']);CAR=clean(s.diag(H,-H.conjugate()))
    gradient=s.Matrix([s.I*s.Rational(j%7-3,53)for j in range(103)])
    v=s.Matrix([s.Rational(j%5-2,47)for j in range(103)]);Hessian=v*v.T-s.eye(103)
    checked=[]
    for word,f0 in (((144,396),s.S.One),((144,396),s.S.Zero),((0,),s.Rational(3,2))):
        coframe,_=polynomial_action(cf,word,f0,gradient[:6,:],Hessian[:6,:6])
        scalar=general_scalar_action(sc,word,f0,gradient[6:,:],Hessian[6:,6:])
        weight,shift=gauge['weight'],gauge['shift']
        gv=-s.trace(weight*Hessian[67:,67:])/2+s.I*(shift.T*weight*gradient[67:,:])[0]
        gv+=f0*(s.I*s.trace(weight*gauge['ds'])/2+(shift.T*weight*shift)[0]/2+gauge['potential'])
        expected={'coframe':coframe,'scalar':scalar,'gauge':{word:s.cancel(gv)},'matter_without_Lorentz':current(CAR,{word:f0})}
        _,parts,image=target.action(time,q,x,A,word,gradient,Hessian,f0)
        for name,value in expected.items(): state_equal(value,parts[name])
        state_equal(terms((1,value)for value in expected.values()),image)
        atoms,_=target.atoms_at(q,x,A,word,gradient,Hessian,f0)
        assert len(atoms)==14
        y=(s.Symbol('n',positive=True),*s.symbols('b1:4',real=True));n,*b=y;D=n*n-sum(v*v for v in b)
        f=[*y,*[(n*n-b[i]*b[j])/(2*n*D)if i==j else -b[i]*b[j]/(n*D)for i,j in SYMMETRIC],*[-v/D for v in b]]
        seed=sum(a*c for a,c in zip([s.Rational(9,5),0,0,0,*[s.Rational(324,625)]*3,*[0]*6],f))
        point=dict(zip(y,time))
        reassembled=terms([(seed.subs(point),{word:f0})]+[(value.subs(point),atoms[j])for j,value in enumerate(f)]+[(time[0],atoms[13])])
        state_equal(reassembled,image)
        if f0:
            separated=Hessian[6:,6:].copy();separated[:61,61:]=s.zeros(61,36);separated[61:,:61]=s.zeros(36,61)
            assert terms([(1,scalar),(-1,general_scalar_action(sc,word,f0,gradient[6:,:],separated))])
        checked.append({'CAR':list(word),'value':str(f0),'all_four_raw_components':True,'all14_atom_reconstruction':True})
        print('PASS raw four-energy/all14-atom consumer', word, 'value', f0, flush=True)
    return {'generic_all_four_time_coframe_coefficients_match_raw_epsilon_density':True,
        'all_inner_live_q_derivatives_and_both_current_slots_retained':True,
        'generic_original_gauge_Gram':gauge_generic,
        'independent_nonzero_q_x_A_time_fixture':{'q':list(map(str,q)),'time':list(map(str,time))},
        'arbitrary_jet_interface_focused_consumers':checked,
        'raw_scalar_gauge_cross_Hessian_omission_nonzero':True,
        'generic_operator_scope':'Four-time nongauge affinity and original gauge Gram identities supply the arbitrary smooth two-jet operator identity; concrete consumers above include values1,0,3/2 and different CAR grades.'}


def packets(candidate,energy):
    measure=RawSectionMeasure();m=measure.section;native=m.native
    basis=original_inventory()['scalar'];gamma=s.kronecker_product(original_gamma()[0],s.eye(63))
    def Y(phi):
        raw=sum(((phi[j]+s.I*phi[j+35])*basis[j]for j in range(35)),s.zeros(252))
        value=clean(N*gamma*raw)
        return clean(s.diag(value,-value.conjugate()))
    grade=s.diag(*[s.Integer(j%63<7)for j in range(504)])
    eq(grade.H,grade);eq(grade*grade,grade);assert s.trace(grade)==56
    for phi in [s.eye(70)[:,j]for j in range(70)]:eq(grade*Y(phi)-Y(phi)*grade,Y(phi))
    for Q in native.Qs+native.Qb+m.r:eq(grade*Q-Q*grade,s.zeros(504))
    Y0=Y(native.v);incoming=(144,396);unit={incoming:s.S.One}
    image=current(Y0,unit)
    expected=decoded_state(candidate['positive_pairing_consumer']['source_Y_image']);state_equal(image,expected)
    norm=lambda values:s.simplify(sum(s.conjugate(v)*v for v in values.values()))
    derivative=[current(Y(native.R[:,j]),unit)for j in range(61)]
    w0,w1=norm(image),s.simplify(sum(norm(value)for value in derivative))
    assert w0==s.Rational(216,125)and w1==s.Rational(351,50)
    twice=current(Y0,image);third=current(Y0,twice)
    assert len(twice)==4 and not third
    c=DOMAIN.to_sympy(energy[2][(13,13)])
    second=terms([(c/N**2,twice)])
    assert second=={(a,b):s.sqrt(30)/30 for a in (0,2)for b in (252,254)}
    state_equal(second,decoded_state(candidate['positive_pairing_consumer']['actual_second_order_grade2_image']))
    assert c==s.sympify(candidate['positive_pairing_consumer']['second_order_raising_word_coefficient'])
    for word in energy[3]:
        if word.count(13)>2: assert word==(13,13,13)and third=={}
    D0=native.Dsymbol.subs(dict.fromkeys(native.x_symbols,0))
    perturb=[rational(D0.inv()*native.Dsymbol.diff(x))for x in native.x_symbols]
    C=max(sum(abs(E[i,j])for E in perturb for j in range(9))for i in range(9))
    delta=s.cancel(1/(10*(1+C)))
    assert C==s.Rational(7,2)and delta==s.Rational(1,45)and delta*C<s.Rational(1,10)
    fgrad={incoming:s.zeros(100,1)};fH={incoming:-2*s.eye(100)/delta**2}
    ggrad,gH={},{}
    for word in set(image).union(*(set(value)for value in derivative)):
        ggrad[word]=s.zeros(100,1)
        for j,value in enumerate(derivative):ggrad[word][m.free.index(6+j)]=value.get(word,0)
        gH[word]=-2*s.eye(100)*image.get(word,0)/delta**2
    _,fj=m.extension_jet(m.source,unit,fgrad,fH)
    _,gj=m.extension_jet(m.source,image,ggrad,gH)
    fchecks=m.Gauss_checks(m.source,fj);gchecks=m.Gauss_checks(m.source,gj)
    for jets,weight in ((fj,0),(gj,1)):
        assert all(sum(j%63<7 for j in word)==weight for word in jets)
    r=s.Symbol('C2_over_C0',positive=True)
    a0,b0=m.source[68],m.source[79]
    assert delta<a0/2 and delta<b0/2
    u,v=s.symbols('packet_u packet_v',real=True)
    variables={a:m.source[67+j]for j,a in enumerate(measure.A)if isinstance(a,s.Symbol)}
    variables[measure.A[1]]=a0+delta*u;variables[measure.A[12]]=b0+delta*v
    density=s.Poly(s.expand(measure.density.subs(variables)),u,v)
    moments={0:1,1:0,2:r,3:0}
    mean=sum(coefficient*moments[power[0]]*moments[power[1]]for power,coefficient in density.terms())
    eq(s.Matrix([[mean]]),s.Matrix([[8*b0*(a0*a0+delta*delta*r)]]))
    forward=s.expand(mean*(w0+delta*delta*r*w1))
    saved=s.sympify(candidate['positive_pairing_consumer']['forward_pairing_after_common_factor'],locals={str(r):r})
    zero(forward-saved);assert all(value>0 for value in s.Poly(forward,r).all_coeffs())
    return {'original70_vertex_grade_laws_and_rank56_orthogonal_projection':True,
        'full_N2_source_Y_image':state_encode(image),'source_norm_squared':str(w0),'all61_derivative_norm_sum':str(w1),
        'second_order_grade2_image':state_encode(second),'three_raising_factors_zero_on_N2':True,
        'two_actual_full_Gauss_jets':[fchecks,gchecks],
        'source_support_radius':str(delta),'original_rho_pairing_polynomial':str(forward),
        'positive_common_factor':'(delta*C0)^100 with C0=Integral eta^2>0; C2=Integral t^2 eta^2>0; both are finite for the stated compact bump.',
        'actual_pairing_argument':'g=Y_slice*f; complete grade law gives <g,Hnative*f>=Integral rho ||Y_slice*f||^2>0 and <Hnative*g,f>=0. The varying original rho and all61 affine Yukawa derivatives were integrated by exact product-packet moments.',
        'scope':'Current fixed-time Hnative and formal coefficientK1 only. The complete summed reduced operator at epsilon1 is not inferred.'}


def main():
    started=time.monotonic();path=HERE/'source_quantum_ordered_temporal.json'
    candidate=json.loads(path.read_text());count=bindings(candidate)
    assert candidate['root']==ROOT_ID
    paid=['independent_source_quantum_temporal_symbol.json','independent_source_quantum_grade_structure.json',
        'independent_source_gauss_section_measure.json','independent_source_quantum_gauss_section.json']
    for name in paid:count+=bindings(json.loads((HERE/name).read_text()))
    energy,words=independent_words(candidate)
    print('PASS independent native-Hodge free-word temporal equations and energy through degree3',flush=True)
    model=SourceGaussSectionMeasure()
    family=actual_family(candidate,model)
    print('PASS independent original four-time differential/CAR family, all14 atoms and zero-value/mixed-jet controls',flush=True)
    packet=packets(candidate,energy)
    print('PASS independent original N2 Yukawa, full Gauss packets, positive integral and second/third raising consumers',flush=True)
    paths=[Path(__file__),path,HERE/'source_quantum_ordered_temporal.py',HERE/'independent_source_quantum_temporal_symbol.py',
        HERE/'independent_source_joint_local_quantum.py',HERE/'independent_source_coframe_live_ordering.py',
        HERE/'independent_source_quantum_gauss_section.py',HERE/'independent_source_gauss_section_measure.py']+[HERE/name for name in paid]
    output={'verdict':'CERTIFIED_ORIGINAL_FOUR_TIME_QUANTUM_FAMILY_AND_SPECIFIED_ORDERED_FORMAL_COEFFICIENTS',
        'root':ROOT_ID,'source_sha256':candidate['source_sha256'],
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths},
        'source_binding_checks':count,'candidate_code_used_only_as_comparison_oracle':True,
        'independent_ordered_coefficients':words,'original_family':family,'positive_pairing':packet,
        'certified_scope':'Original quantum family identity on the shared local compact smooth/CAR domain, and the explicitly specified coefficient-left y0/y1/y2/y3 ordered formal extension. Every generated word through order3 is independently compared.',
        'not_inferred':'Equality to first reducing the classical symbol and then quantizing; convergence at epsilon1; selfadjoint realization; complete physical spectrum; proton invariant or lifetime.',
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'independent_source_quantum_ordered_temporal.json').write_text(json.dumps(output,separators=(',',':'))+'\n')
    print('PASS independent ordered temporal quantum audit',output['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
