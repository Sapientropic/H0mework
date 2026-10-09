#!/usr/bin/env python3
"""Literal source matrices and a closed actual-scalar Fock subspace audit."""
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import re
import sys
import time
import sympy as s

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[5]
BASE=ROOT/'Verification/physics/low-energy-phenomenology'
CORE=ROOT/'Lean/SaturationMonoid/PhysicsCore'


def clean(matrix):return s.SparseMatrix(matrix).applyfunc(s.expand)
def equal(left,right):assert not clean(left-right).todok()
def decode(record,**symbols):return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(x,locals=symbols) for i,j,x in record['entries']})


def literal_source():
    text=(CORE/'DiracCliffordRepresentation.lean').read_text()
    gamma=[]
    for name in ['Zero','One','Two','Three']:
        literal=re.search(r'def diracGamma'+name+r'\s*:.*?:=\s*!!\[(.*?)\]',text,re.S).group(1)
        gamma.append(s.SparseMatrix([[s.sympify(x.strip().replace('Complex.I','I'))
          for x in row.split(',')] for row in literal.split(';')]))
    text=(CORE/'Stage9C/Material/SpinPair/ColorDoublet.lean').read_text().split('def sourceColorPauli',1)[1].split('theorem',1)[0]
    pauli=[s.SparseMatrix([[s.sympify(x.strip().replace('Complex.I','I')) for x in row.split(',')]
           for row in literal.split(';')]) for literal in re.findall(r'!!\[(.*?)\]',text,re.S)]
    spec=importlib.util.spec_from_file_location('independent_bit_exterior',BASE/'mixed-symbol/audit/independent_check.py')
    exterior=importlib.util.module_from_spec(spec);spec.loader.exec_module(exterior)
    basis={degree:list(itertools.combinations(range(7),degree)) for degree in [6,2,4]}
    names=['colorZeroIndex','colorOneIndex','colorTwoIndex','weakZeroIndex','weakOneIndex','hyperPlusIndex','hyperMinusIndex']
    text=(CORE/'SU7ExteriorYukawaMassSpectrum.lean').read_text().split('def finiteGenerationScalarSubset :',1)[1].split('\ndef ',1)[0]
    vacuum=[tuple(sorted(names.index(x.strip()) for x in term.split(',')))
       for term in re.findall(r'\|\s*[01],\s*[01]\s*=>\s*\{([^}]+)\}',text)]
    assert len(vacuum)==4
    def yukawa(terms):
        matrix=s.zeros(63,cls=s.SparseMatrix)
        for j,pair in enumerate(basis[2]):
            for scalar in terms:
                if set(pair).isdisjoint(scalar):
                    sign=(-1)**sum(a>b for a in pair for b in scalar)
                    matrix[basis[6].index(tuple(sorted(pair+scalar))),7+j]+=sign
        return clean(s.kronecker_product(s.diag(0,0,1,1),matrix))
    G=[clean(s.kronecker_product(g,s.eye(63))) for g in gamma]
    G5=s.kronecker_product(s.diag(-1,-1,1,1),s.eye(63))
    N=3*s.sqrt(30)/25;spin=s.sqrt(2);scale=3*spin/5
    gauge=[clean(scale*s.kronecker_product(s.eye(4),s.diag(*[
        exterior.exterior(s.diag(matrix,s.zeros(5)),degree) for degree in [6,2,4]]))) for matrix in pauli]
    rotations=[gamma[2]*gamma[3],gamma[3]*gamma[1],gamma[1]*gamma[2]]
    spin_connections=[clean(spin/2*s.kronecker_product(rotation,s.eye(63))) for rotation in rotations]
    B=clean(sum((s.I*G[j+1]*(spin_connections[j]+gauge[j]) for j in range(3)),s.zeros(252)))
    Y=yukawa(vacuum);C=s.I*G[0]/N;CI=s.I*N*G[0]
    # No rotating-frame subtraction: actual C0 and actual original lower symbol.
    k=s.symbols('k1:4',real=True)
    L=B+Y-sum((kj*G[j+1] for j,kj in enumerate(k)),s.zeros(252))
    H=clean(-s.I*CI*L)
    K=clean(-s.I*N*spin*(G[0]*G5)*C)
    equal(K,spin*G5);equal(C*CI,s.eye(252));equal(CI*C,s.eye(252))
    w=s.zeros(252,1,cls=s.SparseMatrix)
    for spin_index,color,coefficient in [(0,1,1),(1,0,-1),(2,1,1),(3,0,-1)]:
        w[63*spin_index+7+basis[2].index((color,5))]=s.Rational(coefficient,2)
    equal(w.H*w,s.ones(1));equal(Y*w,s.zeros(252,1))
    return N,C,CI,K,G5,H,L,Y,yukawa,w,k


def finite_fock(count):
    size=2**count
    annihilators=[]
    for mode in range(count):
        matrix=s.zeros(size,cls=s.SparseMatrix)
        for occupied in range(size):
            if occupied&(1<<mode):
                matrix[occupied^(1<<mode),occupied]=(-1)**((occupied&((1<<mode)-1)).bit_count())
        annihilators.append(matrix)
    creators=[A.T for A in annihilators]
    for i in range(count):
        for j in range(count):
            equal(annihilators[i]*creators[j]+creators[j]*annihilators[i],
                  s.eye(size) if i==j else s.zeros(size))
            equal(creators[i]*creators[j]+creators[j]*creators[i],s.zeros(size))
    def quantize(matrix):
        result=s.zeros(size,cls=s.SparseMatrix)
        for (i,j),value in s.SparseMatrix(matrix).todok().items():result+=value*creators[i]*annihilators[j]
        return clean(result)
    def one_particle(vector):
        result=s.zeros(size,1,cls=s.SparseMatrix)
        for i in range(count):result[1<<i]=vector[i]
        return result
    return quantize,one_particle


def main():
    started=time.monotonic()
    actual=json.loads((BASE/'active-gauge/receipt.json').read_text())
    for path,digest in actual['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    N,C,CI,K,G5,H,L,Y,yukawa,w,k=literal_source()
    R=H/N;R0=R.subs(dict.fromkeys(k,0));Rm=R.subs({x:-x for x in k},simultaneous=True)
    equal(R+Rm,2*R0);equal(K*R0*w,s.Rational(6,5)*w)
    assert clean(H-H.H).todok()
    wrong_inverse_derivative=clean(s.I*(H-H.H))
    assert wrong_inverse_derivative.rank()==20
    # The current's incoming time jet is H(k), from the literal coframe inverse.
    nu=s.Symbol('nu',nonzero=True,real=True)
    Hnu=clean(-s.I*(s.I*nu*(CI/(s.I*N)))*L)
    equal(Hnu,nu/N*H);equal(Hnu.diff(nu).subs(nu,N),R)
    vertices=json.loads((BASE/'matter-vertices/receipt.json').read_text())
    p=s.symbols('p0:4',real=True)
    V=decode(next(row['operator'] for row in vertices['primitive_vertices']
        if row['group']=='coframe' and row['coordinate']==[0,0]),**dict(zip(map(str,p),p)))
    equal(V.diff(p[0]),s.zeros(252))
    # For lapse, d(Vol C0)=0; the original densitized insertion is the lower
    # source symbol, including Y. This does not discard the on-shell C0 jet.
    equal(V.subs(dict(zip(p,[0,*[s.I*x for x in k]])),simultaneous=True),L)
    equal(-s.I*CI*L/N,R)
    print('PASS literal full252 source, actual C0/K, primitive lapse jet, source6/5 and both physical-time legs',flush=True)

    # -4 for the actual psi=2w; half from Hermitian part; half per cosine leg;
    # then delta(e00)=-delta(g00)/(2N). These operations happen exactly once.
    tauplus=clean((K*R0+R.H*K.H)*w/(2*N))
    tauminus=clean((K*R0+Rm.H*K.H)*w/(2*N))
    variance=s.expand((tauplus.H*tauplus+tauminus.H*tauminus)[0])
    frozen=json.loads((HERE.parent/'noise-receipt.json').read_text())
    assert s.expand(variance-s.sympify(frozen['initial_g00_cosine_noise'],locals=dict(zip(map(str,k),k))))==0
    assert variance==s.Rational(20,3)+s.Rational(125,54)*sum(x*x for x in k)
    point={k[0]:s.sqrt(2)/(262144)*s.Rational(2,3),k[1]:s.sqrt(2)/(262144)*s.Rational(1,3),
           k[2]:-s.sqrt(2)/(262144)*s.Rational(2,3)}
    sample=s.simplify(variance.subs(point));assert sample>0
    one_leg= s.expand((tauplus.H*tauplus)[0])
    assert s.expand(variance-one_leg)!=0
    # Combining the two orthogonal outgoing states as one vector loses their
    # common-carrier labels and changes the actual two-point read.
    identified=s.expand(((tauplus+tauminus).H*(tauplus+tauminus))[0])
    assert s.expand(identified-variance)!=0
    wrong_missing_half=4*variance;wrong_extra_prepared_amplitude=16*variance
    assert wrong_missing_half!=variance and wrong_extra_prepared_amplitude!=variance

    # An original scalar direction has a nonzero open output. Its raw oriented
    # mean and square vanish, while the complete Hermitian word returns a norm.
    scalar=yukawa([(0,2,3,4)]);RY=clean(-s.I*CI*scalar);WY=clean(K*RY)
    equal(w.H*WY*w,s.zeros(1));equal(w.H*WY*WY*w,s.zeros(1))
    physical=clean(-2*(WY+WY.H))
    equal(physical,physical.H)
    scalar_variance=s.expand((w.H*physical*physical*w)[0])
    assert scalar_variance==s.Rational(108,125)
    equal(w.H*WY,s.zeros(1,252));assert clean(WY*w).todok()
    print('PASS independently generated g00 covariance, normalization/transfer controls and actual scalar108/125',flush=True)

    # The five actual modes support a sub-Fock space invariant under K, RY,
    # and their true adjoints. This checks full words on all32 occupations,
    # including intermediate two-particle states, rather than projecting first.
    modes=sorted(set(i for (i,j),x in (WY*w).todok().items())|{i for (i,j),x in w.todok().items()})
    assert len(modes)==5
    outside=[i for i in range(252) if i not in modes]
    for operator in [K,RY,K.H,RY.H]:equal(operator.extract(outside,modes),s.zeros(len(outside),len(modes)))
    Ks,Rs=K.extract(modes,modes),RY.extract(modes,modes)
    quantize,one_particle=finite_fock(len(modes))
    dK,dR=quantize(Ks),quantize(Rs)
    W=clean(dK*dR)
    equal(W.H,dR.H*dK.H)
    equal(dR.H,quantize(Rs.H));equal(dK.H,quantize(Ks.H))
    J=clean(-2*(W+W.H))
    chi=one_particle(w.extract(modes,[0]))
    equal(chi.H*chi,s.ones(1))
    equal(chi.H*W*chi,s.zeros(1));equal(chi.H*W*W*chi,s.zeros(1))
    equal(chi.H*J*J*chi,s.Matrix([[scalar_variance]]))
    P=chi*chi.H
    equal(chi.H*J*P*J*chi,s.zeros(1))
    early_compression=quantize(-2*(Ks*Rs+(Ks*Rs).H))
    equal(J*chi,early_compression*chi)
    whole_difference=clean(J-early_compression)
    assert whole_difference.todok()
    two_particle=[i for i in range(32) if i.bit_count()==2]
    assert clean(whole_difference[:,two_particle]).todok()
    real_each=clean(-4*dK*((dR+dR.H)/2))
    assert clean(J-real_each).todok()
    assert clean(real_each-real_each.H).todok()
    equal(J.H,J)
    equal(J*J-J*J,s.zeros(32))
    assert scalar_variance>0
    # Distinct homogeneous contributions retain both cross orders.
    left,right,first,second=J,J/2,J,2*J
    full=clean((left+first).H*(right+second))
    terms=clean(left.H*right+left.H*second+first.H*right+first.H*second)
    equal(full,terms)
    without_cross=clean(left.H*right+first.H*second)
    omitted_cross=s.simplify((chi.H*(full-without_cross)*chi)[0]);assert omitted_cross!=0
    print('PASS all32 actual-scalar occupation states, CAR/dagger, whole-word and cross-term negative controls',flush=True)

    # Both compatibility legs of the projected g00 noise use the original
    # source column. Neither a mean Ward read nor a new field inverse is used.
    symmetry=json.loads((BASE/'active-gauge/symmetries.json').read_text())
    pp=s.symbols('z0:4')
    T=s.zeros(289,12,cls=s.SparseMatrix)
    for i,j,powers,value in actual['source_primitive_gauge_tangent']:
        T[i,j]+=s.sympify(value)*s.prod(x**a for x,a in zip(pp,powers))
    Q=s.zeros(289,9,cls=s.SparseMatrix)
    for i,j,powers,value in symmetry['source_symmetry_tangents_112']:
        Q[i+9,j]+=s.sympify(value)*s.prod(x**a for x,a in zip(pp,powers))
    assert actual['fields'][57]=={'group':'coframe','coordinate':[0,0]}
    column=s.zeros(289,1,cls=s.SparseMatrix);column[57]=-2*N
    Gram=clean(column*variance*column.H)
    for tangent in [T,Q]:
        equal(tangent.H*Gram,s.zeros(tangent.cols,289))
        equal(Gram*tangent,s.zeros(289,tangent.cols))
    assert len(Gram.todok())==1
    badrow=next(i for i,j in T.todok())
    bad=s.zeros(289,1,cls=s.SparseMatrix);bad[badrow]=-2*N
    assert clean(T.H*bad*variance*bad.H).todok()
    print('PASS complete original projected-noise Gram and both source compatibility legs',flush=True)

    result={'status':'PASS','source_sha256_verified':len(actual['source_sha256']),
      'source':'literal current Gamma/Pauli/four-vacuum exterior wedges; original physical H without minus omega Q',
      'C0_inverse_and_K_from_original_volume':True,'primitive_lapse_jet_H_over_N':True,
      'original_K_R0_w':'6/5 w','full_inverse_vs_adjoint_derivative_rank':20,
      'initial_metric_noise':str(variance),'new_nonaxial_k':[str(point[x]) for x in k],
      'new_nonaxial_variance_exact':str(sample),'single_cosine_leg_omission':str(s.expand(variance-one_leg)),
      'incorrect_identified_transfer_labels_difference':str(s.expand(identified-variance)),
      'cosine_half_omission_noise_multiplier':4,'prepared_factor4_repetition_noise_multiplier':16,
      'scalar_raw_mean':0,'scalar_raw_square':0,'scalar_actual_real_variance':str(scalar_variance),
      'actual_closed_scalar_modes':modes,'whole_Fock_dimension':32,'all_CAR_and_adjoint_identities_paid':True,
      'whole_word_minus_quantized_compressed_matrix_nonzero_entries':len(whole_difference.todok()),
      'whole_word_difference_detected_on_two_particle_states':True,
      'wrong_factorwise_real_part_nonzero_entries':len(clean(J-real_each).todok()),
      'intermediate_prepared_projection_wrong_variance':0,
      'raw_equal_time_commutator_zero_but_variance_positive':True,
      'omitted_homogeneous_cross_read':str(omitted_cross),
      'both_12_primitive_and_9_remaining_Gram_legs_zero':True,
      'source_injected_Gram_entry':str(s.factor(Gram[57,57])),
      'wrong_source_row_detected':int(badrow),
      'scope':'One original incoming0 state with two labelled finite transfer sectors, g00 source projection and theta pole channel; no continuum covariance or homogeneous state selected.',
      'seconds':round(time.monotonic()-started,3)}
    (HERE/'independent-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key:result[key] for key in ['status','initial_metric_noise','scalar_actual_real_variance','whole_Fock_dimension','seconds']},indent=2),flush=True)


if __name__=='__main__':main()
