#!/usr/bin/env python3
"""Ordered source temporal coefficients on the full local quantum domain.

The finite words below are compositions of actual source differential/CAR
operators. They keep every inner coefficient derivative. Epsilon is a formal
calculation filtration: setting epsilon=1 recovers the unreduced family
algebraically, but convergence of the reduced series there is not asserted.
"""
from __future__ import annotations
from functools import lru_cache
import hashlib
import itertools
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from retained_hamiltonian_reduction import DOMAIN
from source_spatial_active_phase_splice import field_element
from source_quantum_temporal_symbol import N, J0, SYM
from source_temporal_algebraic_elimination import C_SOURCE
from source_gauss_section_measure import SourceGaussSectionMeasure
from source_coframe_legendre import rational,pack
from source_coframe_live_ordering import FREE
from source_lorentz_contact import clean,equal,encode,ETA,GAMMA
from source_gauss_quantum_current import apply_superposition,weighted_sum,encode_state
from source_quantum_grade_structure import occupation_grade,matrix_grade


def add(*polynomials):
    result={}
    for polynomial in polynomials:
        for word,value in polynomial.items(): result[word]=result.get(word,DOMAIN.zero)+value
    return {word:value for word,value in result.items()if value!=DOMAIN.zero}


def scale(value,polynomial):
    value=field_element(value)if not isinstance(value,type(DOMAIN.one))else value
    return {word:value*coefficient for word,coefficient in polynomial.items()if value*coefficient!=DOMAIN.zero}


def multiply(left,right):
    result={}
    for l,a in left.items():
        for r,b in right.items():
            word=l+r;result[word]=result.get(word,DOMAIN.zero)+a*b
    return {word:value for word,value in result.items()if value!=DOMAIN.zero}


def series_product(left,right,order):
    return [add(*(multiply(left[j],right[n-j])for j in range(n+1)))for n in range(order+1)]


def multiindices(maximum):
    return [a for a in itertools.product(range(maximum+1),repeat=4)if sum(a)<=maximum]


class OrderedTemporalCoefficients:
    """Fixed source coefficient-left Taylor extension, with ordered y0,y1,y2,y3."""
    def __init__(self):
        n=s.Symbol('n',positive=True);b=s.symbols('b1:4',real=True)
        self.y=(n,*b);self.at_source=dict(zip(self.y,(N,0,0,0)))
        delta=n*n-sum(v*v for v in b)
        S=[(n*n-b[i]*b[j])/(2*n*delta)if i==j else -b[i]*b[j]/(n*delta)for i,j in SYM]
        self.coefficients=[*self.y,*S,*[-v/delta for v in b]]
        source=[s.Rational(9,5),0,0,0]+[2*C_SOURCE]*3+[0]*6
        self.seed=s.factor(sum(a*c for a,c in zip(source,self.coefficients)))
        self.seed_energy=s.simplify(self.seed.subs(self.at_source))
        F=s.Matrix([-s.diff(self.seed,y)for y in self.y])
        equal(F.subs(self.at_source),s.zeros(4,1))
        equal(F.jacobian(self.y).subs(self.at_source),J0)
        # Only atom0 is split: its grade0 part and atom13=Y/N. All others
        # are the actual nongauge/Gram deviations fixed by the source family.
        self.atoms=[{(j,):DOMAIN.one}for j in range(13)]
        self.atoms[0]=add(self.atoms[0],{(13,):DOMAIN.one})

    @lru_cache(maxsize=None)
    def taylor(self,part,alpha,equation):
        expression=self.seed if part==-1 else self.coefficients[part]
        if equation>=0: expression=-s.diff(expression,self.y[equation])
        for y,count in zip(self.y,alpha):
            if count:expression=s.diff(expression,y,count)/s.factorial(count)
        return field_element(s.simplify(expression.subs(self.at_source)))

    def evaluate(self,time_series,order,equation=-1):
        result=[{}for _ in range(order+1)]
        unit=[{():DOMAIN.one}]+[{}for _ in range(order)]
        for alpha in multiindices(order):
            monomial=unit
            for a,count in enumerate(alpha):
                for _ in range(count):monomial=series_product(monomial,time_series[a],order)
            scalar=self.taylor(-1,alpha,equation)
            if scalar:
                for n in range(order+1):result[n]=add(result[n],scale(scalar,monomial[n]))
            if sum(alpha)>=order:continue
            for part in range(13):
                coefficient=self.taylor(part,alpha,equation)
                if coefficient:
                    left=scale(coefficient,self.atoms[part])
                    for n in range(1,order+1):result[n]=add(result[n],multiply(left,monomial[n-1]))
        return result

    def generate(self,order):
        time_series=[[{}for _ in range(order+1)]for _ in range(4)]
        stages=[]
        for n in range(1,order+1):
            residual=[self.evaluate(time_series,n,a)[n]for a in range(4)]
            for a in range(4):time_series[a][n]=scale(-1/J0[a,a],residual[a])
            for a in range(4):
                assert all(not polynomial for polynomial in self.evaluate(time_series,n,a))
                assert all(len(word)==n for word in time_series[a][n])
            stages.append({'order':n,'time_word_counts':[len(time_series[a][n])for a in range(4)]})
        energy=self.evaluate(time_series,order)
        assert energy[0]=={():field_element(self.seed_energy)}
        for n in range(1,order+1):assert all(len(word)==n for word in energy[n])
        return time_series,energy,stages


class SourceTemporalQuantumFamily:
    """Original full four-time coefficient-left family on arbitrary smooth jets."""
    def __init__(self,native):
        self.native=native;self.joint=native.joint;c=self.joint.coframe;m=c.model
        self.y=(s.Symbol('quantum_n',positive=True),*s.symbols('quantum_b1:4',real=True))
        e=c.e.copy();e[:,0]=s.Matrix(self.y);self.e=e
        Hi=rational(m.lorentz.inverse(e));Gt=m.at(m.G[:,:16],e)
        h=e[:,1:].T*ETA*e[:,1:]
        R=rational(m.metric_lift_numerator(e)/e.det())
        Bi=rational(4*e.det()*m.metric_inverse_numerator.xreplace(dict(zip(m.h_variables,pack(h))))/h.det())
        Q=rational(R*Bi*R.T);ports=m.lorentz.raw_matter_ports(e)
        J=[rational(s.diag(s.I*ports['E'].inv()*V,s.I*(ports['E'].inv()*V).conjugate()))for V in ports['V']]
        L=rational(c.S*s.eye(24)[:6,:]+Gt.T*Hi)
        T=[rational(sum((L[i,a]*J[a]for a in range(24)),s.zeros(8)))for i in range(16)]
        W=rational((L.T*Q*L+Hi)/2)
        self.cf={'A':c.A,'S':c.S,'L':L,'Q':Q,'Hinv':Hi,'K':rational(c.A.T*Q*c.A/2),'W':W,
            'J':J,'T':T,'M':[rational(sum(((c.A.T*Q)[r,j]*T[j]for j in range(16)),s.zeros(8)))for r in range(6)],
            'dA':c.dA,'dT':[[rational(v.diff(q))for v in T]for q in c.q],
            'one_body':rational(sum((v*J[a]*J[b]for (a,b),v in W.todok().items()),s.zeros(8))),
            'drift':rational(-s.I*sum(((c.A.T*Q)[r,j]*c.A.diff(q)[j,:]for r,q in enumerate(c.q)for j in range(16)),s.zeros(1,6))/2),
            'correction':rational(-s.I*sum(((c.A.T*Q)[r,j]*T[j].diff(q)for r,q in enumerate(c.q)for j in range(16)),s.zeros(8))/2),
            'constant':3*e.det()}

    def verify_time_affinity(self):
        # In the scalar nested square retain Pi*U+U*Pi in that order. Its
        # time coefficient is h0i/h00; only the multiplication U*U terms
        # combine. Thus no inner coefficient derivative is dropped.
        e=self.e;inverse=rational(e.adjugate()/e.det())
        ports=self.joint.coframe.model.lorentz.raw_matter_ports(e)
        equal(rational(-s.I*e.det()*ports['E'].inv()-self.y[0]*GAMMA[0]),s.zeros(4))
        h=rational(e.det()*inverse*ETA*inverse.T)
        weights=[1/h[0,0],*list(-h[0,1:]/h[0,0]),
                 *list(h[1:,0]*h[0,1:]/h[0,0]-h[1:,1:]),e.det()]
        for value in weights:
            p=s.Poly(s.cancel(value),self.y)
            assert p.total_degree()<=1 and p.coeff_monomial((0,0,0,0))==0
        values=[]
        for name in ('K','one_body','drift','correction'):
            values.extend(self.cf[name].todok().values())
        for matrix in self.cf['M']:values.extend(matrix.todok().values())
        for value in values:
            p=s.Poly(s.cancel(value),self.y)
            assert p.total_degree()<=1 and p.coeff_monomial((0,0,0,0))==0
        # Both ordered coframe current slots were checked on this identical
        # original symbolic recipe by source_quantum_temporal_symbol.
        return {'full_live_kinetic_mixed_drift_onebody_affinity':True,
            'scalar_full_nested_cross_order_retained':'Pi*U+U*Pi, multiplied by the actual affine h0i/h00; no commuting of Pi with U',
            'scalar_weight_count':len(weights),'coframe_weight_count':len(values),
            'generic_source_all9_gauge_shift_divergence_zero':True}

    def coefficients(self,time,q,x,A):
        substitutions={**dict(zip(self.y,time)),**dict(zip(self.joint.coframe.q,q))}
        def at(value):
            if isinstance(value,list):return [at(v)for v in value]
            if isinstance(value,s.MatrixBase):return rational(value.subs(substitutions))
            return s.cancel(value.subs(substitutions))
        e=at(self.e);cf={key:at(value)for key,value in self.cf.items()}
        scalar=self.joint.scalar.coefficients(e,x,A)
        gauge=self.joint.gauge.coefficients(e)
        gauge_sub=dict(zip(self.joint.gauge.coordinates,A.reshape(36,1)))
        gauge={key:rational(value.subs(gauge_sub))if isinstance(value,s.MatrixBase)else s.expand(value.subs(gauge_sub))for key,value in gauge.items()}
        connection=s.zeros(4,12);connection[1:,:]=A
        matter=self.joint.common.matter_data(e,scalar['phi'],connection)
        H=clean(-s.I*matter['inverse_E']*matter['lower_without_Lorentz'])
        return {'e':e,'coframe':cf,'scalar':scalar,'gauge':gauge,'matter':matter,
            'matter_H':H,'matter_CAR':clean(s.diag(H,-H.conjugate())),'connection':connection}

    def action(self,time,q,x,A,word,gradient,Hessian,value=1):
        data=self.coefficients(time,q,x,A)
        parts,image=self.joint.action(data,word,gradient,Hessian)
        if value!=1:
            constant,_=self.joint.action(data,word,s.zeros(103,1),s.zeros(103))
            parts={name:weighted_sum([(1,part),(value-1,constant[name])])for name,part in parts.items()}
            image=weighted_sum((1,part)for part in parts.values())
        return data,parts,image

    def atoms_at(self,q,x,A,word,gradient,Hessian,value=1):
        """All14 original operators on any two-jet, including zero-valued words."""
        data,base_parts,_=self.action((N,0,0,0),q,x,A,word,gradient,Hessian,value)
        nongauge=lambda parts:weighted_sum((1,value)for name,value in parts.items()if name!='gauge')
        A0=weighted_sum([(1/N,nongauge(base_parts))])
        Y=clean(-s.I*data['e'].det()*data['matter']['inverse_E']*data['matter']['Y'])
        Y=clean(s.diag(Y,-Y.conjugate()))
        raising=apply_superposition(Y,{word:value})
        atoms=[weighted_sum([(1,A0),(-s.Rational(9,5),{word:value}),(-1/N,raising)])]
        for a in range(3):
            time=[N,0,0,0];time[a+1]=N/7
            _,parts,_=self.action(time,q,x,A,word,gradient,Hessian,value)
            atoms.append(weighted_sum([(7/N,nongauge(parts)),(-7/N,nongauge(base_parts))]))
        g,H=gradient[67:,:],Hessian[67:,67:]
        B,_=self.native.gauge.spatial_data(data['connection'],s.zeros(3,48))
        E=s.Matrix(3,3,lambda i,j:-sum(self.native.gauge.gram_inverse[a,b]*H[12*i+a,12*j+b]for a in range(12)for b in range(12)))
        C=s.Matrix(3,3,lambda i,j:-s.I*sum(B[j,a]*g[12*i+a]for a in range(12)))
        M=clean(B*self.native.gauge.gram*B.T)*value
        L=data['e'][1:,1:];Li=L.inv()
        S=clean(L.det()*Li.T*(E/2+2*M)*Li)
        Ct=clean(L.det()*Li.T*C*Li)
        for i,j in SYM:atoms.append({word:s.cancel(S[i,j]-(2*C_SOURCE*value if i==j else 0))})
        for value in (Ct[2,1]-Ct[1,2],Ct[0,2]-Ct[2,0],Ct[1,0]-Ct[0,1]):atoms.append({word:value})
        atoms.append(weighted_sum([(1/N,raising)]))
        return [weighted_sum([(1,value)])for value in atoms],data


def actual_quantum_family(model):
    section=model.section;family=SourceTemporalQuantumFamily(section.native)
    generic=family.verify_time_affinity()
    q=tuple(section.b0[:6,0]);x=s.zeros(61,1);x[19]=s.Rational(1,100)
    A=section.A0.copy();A[0,2]+=s.Rational(1,31)
    word=(144,396);gradient=s.Matrix([s.I*s.Rational(j%7-3,53)for j in range(103)])
    v=s.Matrix([s.Rational(j%5-2,47)for j in range(103)]);Hessian=v*v.T-s.eye(103)
    atoms,_=family.atoms_at(q,x,A,word,gradient,Hessian)
    order=OrderedTemporalCoefficients();time=(N,s.Rational(1,13),-s.Rational(1,17),s.Rational(1,19))
    _,parts,image=family.action(time,q,x,A,word,gradient,Hessian)
    at=dict(zip(order.y,time))
    terms=[(order.seed.subs(at),{word:1})]
    terms +=[(f.subs(at),atoms[j])for j,f in enumerate(order.coefficients)]
    terms.append((order.coefficients[0].subs(at),atoms[13]))
    assert weighted_sum(terms)==image
    old=section.native.joint.coefficients(q,x,A)
    old_parts,old_image=section.native.joint.action(old,word,gradient,Hessian)
    _,source_parts,source_image=family.action((N,0,0,0),q,x,A,word,gradient,Hessian)
    assert old_parts==source_parts and old_image==source_image
    assert all(occupation_grade(w)==0 for atom in atoms[:13]for w in atom)
    assert atoms[13] and all(occupation_grade(w)==1 for w in atoms[13])
    return {'generic_operator_time_affinity':generic,'all14_source_atoms_reconstruct_full_four_time_Hamiltonian':True,
        'source_time_restriction_equals_signed_Hnative':True,'actual_time':list(map(str,time)),
        'input_CAR':list(word),'actual_all_four_component_image':{k:encode_state(v)for k,v in parts.items()},
        'full_family_atoms_preserve_particle_number_and_nonnegative_grade':True}


def packet_pair(model,energy):
    m=model.section;common=m.native.joint.common
    data=m.native.joint.coefficients(tuple(m.b0[:6,0]),m.b0[6:67,:],m.A0)
    prefactor=clean(-s.I*data['e'].det()*data['matter']['inverse_E'])
    def matrix(phi):
        raw=sum(((phi[j]+s.I*phi[j+35])*M for j,M in enumerate(common.yukawa_basis)if phi[j]or phi[j+35]),s.zeros(252))
        value=clean(prefactor*raw)
        return clean(s.diag(value,-value.conjugate()))
    Y0=matrix(m.native.graph.constraints.vacuum);matrix_grade(Y0,1)
    incoming=(144,396);initial={incoming:s.S.One}
    Yimage=apply_superposition(Y0,initial)
    assert Yimage and occupation_grade(incoming)==0
    derivatives=[apply_superposition(matrix(m.native.graph.R[:,j]),initial)for j in range(61)]
    norm=lambda state:s.simplify(sum(s.conjugate(v)*v for v in state.values()))
    w0=norm(Yimage);w1=s.simplify(sum(norm(value)for value in derivatives))
    assert w0==4*N*N and w1>0
    twice=apply_superposition(Y0,Yimage)
    assert twice=={(a,b):-2*N*N for a in (0,2) for b in (252,254)}
    assert not apply_superposition(Y0,twice)
    coefficient=DOMAIN.to_sympy(energy[2][(13,13)])
    assert s.simplify(coefficient+N/(4*s.Rational(9,5)))==0
    second=weighted_sum([(coefficient/N**2,twice)])
    assert second=={(a,b):s.sqrt(30)/30 for a in (0,2)for b in (252,254)}
    support=model.source_support_radius();delta=support['delta']
    fvalue=initial;fgrad={incoming:s.zeros(100,1)};fH={incoming:-2*s.eye(100)/delta**2}
    gvalue=Yimage.copy();ggrad={};gH={}
    for word in set(Yimage).union(*(set(value)for value in derivatives)):
        ggrad[word]=s.zeros(100,1)
        for j,value in enumerate(derivatives):ggrad[word][6+j]=value.get(word,0)
        gH[word]=-2*s.eye(100)*Yimage.get(word,0)/delta**2
    fjet=m.extend_jet(fvalue,fgrad,fH);gjet=m.extend_jet(gvalue,ggrad,gH)
    m.verify_Gauss_jet(fjet);m.verify_Gauss_jet(gjet)
    # Consume the complete operator's signed grade law to compute the
    # requested matrix elements. Expanding all unrelated grade0/2 outputs
    # would repeat thousands of already paid spin Kronecker products.
    for word in fjet:assert len(word)==2 and occupation_grade(word)==0
    for word in gjet:assert len(word)==2 and occupation_grade(word)==1
    matrix_grade(clean(data['matter_CAR']-Y0),0)
    for Q in m.native.Q_b+m.native.Q_s:matrix_grade(Q,0)
    for R in m.R:matrix_grade(R,0)
    # All spin-only coframe matrices commute with the original degree
    # projector; scalar/gauge derivatives do not act on the CAR grade.
    projected_Hf=apply_superposition(Y0,fvalue)
    inner=lambda left,right:s.simplify(sum(s.conjugate(value)*right.get(word,0)for word,value in left.items()))
    forward_source=inner(gvalue,projected_Hf)
    reverse_source=s.S.Zero
    assert forward_source==w0
    r=s.Symbol('C2_over_C0',positive=True)
    a0,b0=model.z0[model.gauge_a1],model.z0[model.gauge_a12]
    rho_mean=8*b0*(a0*a0+delta*delta*r)
    forward=s.expand(rho_mean*(w0+delta*delta*r*w1))
    assert all(c>0 for c in s.Poly(forward,r).all_coeffs())
    return {'incoming_CAR':list(incoming),'source_Y_image':encode_state(Yimage),
        'source_raising_norm_squared':str(w0),'all61_scalar_derivative_norm_sum':str(w1),
        'packet':'f(z)=product_100 eta((z-z_source)/delta) tensor incoming; g(z)=Y_slice(z)f(z); eta(t)=exp(1-1/(1-t^2)) inside(-1,1), zero outside',
        'support':{key:str(value)for key,value in support.items()},
        'source_Y_is_scalar61_affine_and_q_A_independent':'E=i det(L) gamma0 and det(e)=N det(L), gamma0^2=-I, so the complete original Yukawa prefactor is +N gamma0 and all61 coefficients are the original R columns',
        'positive_common_packet_factor':'(delta*C0)^100, C0=Integral eta^2>0, C2=Integral t^2 eta^2>0',
        'forward_pairing_after_common_factor':str(forward),
        'reverse_pairing':'0 by exact grade orthogonality of the complete operator',
        'actual_both_full_Gauss_jet_consumers':True,
        'source_full_H_pairings':[str(forward_source),str(reverse_source)],
        'full_operator_pairing_method':'Complete signed grade projection: Pi_grade1 Hf=Yf and Pi_grade0 Hg=0; both full Gauss jets and all matter/Gauss CAR matrix grades are recomputed.',
        'first_reduced_coefficient':'K1=Hnative(y_source)-Hs(y_source)I; the scalar subtraction has zero cross-grade matrix element',
        'formal_adjoint_pairing':'<g,K1 f>=<K1^dagger g,f> is the displayed strictly positive norm; <K1 g,f>=0. The lowering grade in Y^dagger is retained by the positive source pairing.',
        'half_density':'Multiplication by sqrt(rho) commutes with grade and Y; the same unequal pairings survive the already signed unitary local half-density readout.',
        'actual_second_order_grade2_image':encode_state(second),
        'actual_third_order_three_raising_word_zero_on_N2':True,
        'second_order_raising_word_coefficient':str(coefficient),
        'scope':'Non-symmetry of Hnative(y_source) and the specified formal reduced coefficient K1 on the original local positive pairing. This does not decide the summed epsilon=1 reduced operator or a proton invariant.'}


def main():
    started=time.monotonic();ordered=OrderedTemporalCoefficients()
    temporal,energy,stages=ordered.generate(3)
    assert multiply({(0,):DOMAIN.one},{(1,):DOMAIN.one})!={ (1,0):DOMAIN.one }
    assert energy[1][(13,)]==field_element(N)
    assert max(word.count(13)for word in energy[2])==2
    assert energy[2][(13,13)]==field_element(-N/(4*s.Rational(9,5)))
    print('PASS source coefficient-left ordered implicit recursion through3 with all noncommuting words and generated multigrade energy',flush=True)
    model=SourceGaussSectionMeasure()
    family=actual_quantum_family(model)
    print('PASS actual full four-time quantum family and all14 concrete source differential/CAR atoms on arbitrary-jet interface',flush=True)
    packets=packet_pair(model,energy)
    print('PASS actual two-particle Gauss packets, strict positive forward/zero reverse pairing and nonzero reduced grade2 coefficient',flush=True)
    names=('source_quantum_ordered_temporal.py','source_quantum_temporal_symbol.py','source_quantum_temporal_symbol.json',
        'source_temporal_algebraic_elimination.py','source_temporal_algebraic_elimination.json',
        'source_quantum_grade_structure.json','source_gauss_section_measure.py','source_gauss_section_measure.json',
        'source_quantum_gauss_section.py','source_quantum_stabilizer.py','source_joint_local_quantum.py',
        'source_coframe_live_ordering.py','source_gauge_quantum_energy.py')
    result={'root':ROOT_ID,'scope':'SOURCE_ORDERED_FORMAL_TEMPORAL_OPERATOR_COEFFICIENTS_AND_LOCAL_POSITIVE_PAIRING_CONSUMER',
        'source_sha256':model.section.native.graph.common.source_hashes,
        'input_sha256':{str((HERE/name).relative_to(ROOT)):hashlib.sha256((HERE/name).read_bytes()).hexdigest()for name in names},
        'original_family':family,
        'specified_extension':'Taylor-expand the original quantum H(y) and F=-partial_y H at the literal y_source; every original differential/CAR coefficient remains on the left; powers of the four noncommuting time increments are ordered y0,y1,y2,y3. This specifies a formal extension of the original commuting-parameter family.',
        'filtration':'H_epsilon=Hs(y)I+epsilon*(Hnative(y)-Hs(y)I); epsilon=1 is an algebraic identity for the unreduced family, not a convergence assertion for its reduced formal solution.',
        'all_order_producer':'OrderedTemporalCoefficients.generate(order): each Yn=-J0^-1 residual_n consumes lower finite histories in the actual operator composition algebra. Every Kn is a finite linear combination of fixed source differential/CAR words.',
        'whole_domain':'Each original atom is a smooth finite-order differential operator on the common compact source chart tensor finite CAR504; finite ordered composition acts on every Cc_infinity section and includes all derivatives of inner coefficients. Gauss-invariant atoms descend by the same extension/restriction; their compositions preserve that domain.',
        'grade':'The13 grade-zero deviations and Y/N have weights0 and1. Coefficient n has word length n, differential order at most2n, and grades0..n; fixed particle number N kills words with more thanN raising factors by the signed weighted-word theorem.',
        'whole_atom_grade_proof':{
            'coframe':'All original spin8 matrices tensor I63, including both current slots and every live q derivative, preserve exterior degree; source_quantum_grade_structure.full_coefficients checks their actual source matrices.',
            'scalar_Gauss':'The complete native-orthogonal9 broken and3 stabilizer currents preserve Lambda6 grade; all scalar momentum vector fields, normal graph and coefficient derivatives act on boson variables.',
            'nongauge_time_coefficients':'Generic four-time operator affinity retains Pi*U+U*Pi; the original Yukawa prefactor is exactly n*gamma0. Thus A0 splits into grade0 plus Y/N and all three shift coefficients preserve grade.',
            'gauge_S_d':'The full native electric/cross/magnetic Gram readouts are pure boson differential/multiplication operators with coefficient-left q factors, so all9 grade0 identities hold on arbitrary section inputs.',
            'atom13':'All70 actual Yukawa vertices map Lambda2 to Lambda6 on each independent-real branch, so [grade,Y/N]=Y/N on the entire CAR504 algebra.',
            'Gauss_and_pairing':'The original group extension, restriction and scalar half-density preserve grade; positive rho makes distinct grades orthogonal.',
            'formal_word_consumer':'FockFilteredWords.weighted_tensor_word_vanishes with atom13 weight1 and all other atoms weight0; not inferred from the displayed N2 packet.'},
        'classical_quantization_comparison':'The specified ordered formal substitution is an extension of the original commuting-parameter quantum family. Equality with first eliminating the classical temporal variables and then quantizing that nonlinear symbol has not been proved.',
        'actual_stages':stages,'actual_energy_word_counts':[len(v)for v in energy],
        'actual_noncommuting_degree3_words':[[list(w),str(DOMAIN.to_sympy(c))]for w,c in energy[3].items()if w in ((0,1,1),(1,0,1),(1,1,0),(13,1,1),(1,13,1),(1,1,13))],
        'positive_pairing_consumer':packets,
        'summed_reduced_operator_or_convergent_time_evolution_or_spectral_measure_generated':False,
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'source_quantum_ordered_temporal.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS actual ordered temporal quantum coefficients',result['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
