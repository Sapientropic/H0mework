import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationJointSourceAnnihilator
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationPreparedMomentumReturn
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Algebra.Polynomial.Div

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationAlgebraicResponse
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalFeedback
open PreparationVacuumPropagationPencil SourcePropagationResolvent SourcePropagationSpectralAxis
open SourcePropagationCommonMomentum PreparationVacuumRawJointFeedback
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFieldConstraintResponse
open PreparationVacuumActionFieldLift PreparationVacuumPhysicalHalfAxis
open Polynomial
open scoped BigOperators Matrix InnerProductSpace Topology
abbrev TransferOp:=SourcePropagationResolvent.TransferOp
local instance : IsScalarTower ℂ TransferOp TransferOp:=⟨by
  intro c A B
  apply ContinuousLinearMap.ext
  intro X
  rfl⟩
local instance : SMulCommClass ℂ TransferOp TransferOp:=⟨by
  intro c A B
  apply ContinuousLinearMap.ext
  intro X
  exact (map_smul A c (B X)).symm⟩
attribute [local irreducible] jointGenerator evolutionGenerator propagationPencil actualResolvent
  sourceRead sourceInverse rawInitial slopeInitial responseLeft responseRight

private def leftMultiplication : Op→ₐ[ℂ] TransferOp where
  toFun:=ContinuousLinearMap.mul ℂ Op
  map_zero':=by apply ContinuousLinearMap.ext;intro X;exact zero_mul X
  map_one':=by apply ContinuousLinearMap.ext;intro X;exact one_mul X
  map_add':=by intro A B;apply ContinuousLinearMap.ext;intro X;exact add_mul A B X
  map_mul':=by intro A B;apply ContinuousLinearMap.ext;intro X;exact mul_assoc A B X
  commutes':=by
    intro c
    apply ContinuousLinearMap.ext
    intro X
    simp only [Algebra.algebraMap_eq_smul_one,ContinuousLinearMap.mul_apply',smul_mul_assoc,
      one_mul,smul_apply,one_apply_eq_self]

private def rightMultiplication : Op→L[ℂ] TransferOp:=(ContinuousLinearMap.mul ℂ Op).flip

private theorem right_power {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]
    (A : R) (n : ℕ) :
    ((ContinuousLinearMap.mul ℂ R).flip A)^n=(ContinuousLinearMap.mul ℂ R).flip (A^n):=by
  induction n with
  | zero=>
    apply ContinuousLinearMap.ext
    intro X
    simp only [pow_zero,one_apply_eq_self,ContinuousLinearMap.flip_apply,ContinuousLinearMap.mul_apply',mul_one]
  | succ n ih=>
    conv_lhs=>rw [pow_succ']
    conv_rhs=>rw [pow_succ]
    rw [ih]
    apply ContinuousLinearMap.ext
    intro X
    simp only [mul_apply_eq_comp,ContinuousLinearMap.flip_apply,ContinuousLinearMap.mul_apply']
    exact mul_assoc _ _ _

private theorem rightMultiplication_pow (A : Op) (n : ℕ) :
    (rightMultiplication A)^n=rightMultiplication (A^n):=by
  unfold rightMultiplication
  exact right_power (R:=Op) A n

private theorem right_polynomial {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]
    (A : R) (P : ℂ[X]) :
    aeval ((ContinuousLinearMap.mul ℂ R).flip A) P=
      (ContinuousLinearMap.mul ℂ R).flip (aeval A P):=by
  rw [aeval_eq_sum_range,aeval_eq_sum_range,map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_smul,right_power]

private theorem rightMultiplication_polynomial (A : Op) (P : ℂ[X]) :
    aeval (rightMultiplication A) P=rightMultiplication (aeval A P):=by
  unfold rightMultiplication
  exact right_polynomial (R:=Op) A P

private theorem evolution_algebra {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (A B X : R) :
    -((-Complex.I) • A)*X+X*((-Complex.I) • B)=
      Complex.I • (A*X)+(-Complex.I) • (X*B):=by
  simp only [neg_smul,smul_mul_assoc,mul_smul_comm,mul_neg,neg_neg]

def sourceLeft (q : PhysicalResponsePoint) : TransferOp:=
  leftMultiplication (jointGenerator (q.p+q.k) q.F 0 0)
def sourceRight (q : PhysicalResponsePoint) : TransferOp:=
  rightMultiplication (jointGenerator q.p q.F 0 0)

theorem sourceLeftRight_commute (q : PhysicalResponsePoint) : Commute (sourceLeft q) (sourceRight q):=by
  apply ContinuousLinearMap.ext
  intro X
  change jointGenerator (q.p+q.k) q.F 0 0*(X*jointGenerator q.p q.F 0 0)=
    (jointGenerator (q.p+q.k) q.F 0 0*X)*jointGenerator q.p q.F 0 0
  exact (mul_assoc _ _ _).symm

theorem sourceEvolution_multiplications (q : PhysicalResponsePoint) :
    evolutionGenerator q=Complex.I • sourceLeft q+(-Complex.I) • sourceRight q:=by
  apply ContinuousLinearMap.ext
  intro X
  have actual:=evolutionGenerator_apply q X
  convert! (actual.trans (evolution_algebra (R:=Op)
    (jointGenerator (q.p+q.k) q.F 0 0) (jointGenerator q.p q.F 0 0) X)) using 1


private theorem sourceLeft_integral (q : PhysicalResponsePoint) : IsIntegral ℂ (sourceLeft q):=by
  have actual : IsIntegral ℂ (jointGenerator (q.p+q.k) q.F 0 0):=
    ⟨jointPolynomial (q.p+q.k) q.F,jointPolynomial_monic _ _,actualJoint_annihilated _ _⟩
  exact IsIntegral.map leftMultiplication actual

private theorem sourceRight_integral (q : PhysicalResponsePoint) : IsIntegral ℂ (sourceRight q):=by
  refine ⟨jointPolynomial q.p q.F,jointPolynomial_monic _ _,?_⟩
  change aeval (rightMultiplication (jointGenerator q.p q.F 0 0)) (jointPolynomial q.p q.F)=0
  have poly:=rightMultiplication_polynomial (jointGenerator q.p q.F 0 0) (jointPolynomial q.p q.F)
  have actual:=actualJoint_annihilated q.p q.F
  have zero:=congrArg rightMultiplication actual
  exact poly.trans (zero.trans (map_zero rightMultiplication))

set_option linter.style.haveILetI false in
private theorem commuting_integral_phase {A : Type*} [Ring A] [Algebra ℂ A]
    (x y : A) (commutes : Commute x y) (hx : IsIntegral ℂ x) (hy : IsIntegral ℂ y) :
    IsIntegral ℂ (Complex.I • x+(-Complex.I) • y):=by
  let S : Subalgebra ℂ A:=Algebra.adjoin ℂ {x,y}
  haveI : IsMulCommutative S:=by
    apply Algebra.isMulCommutative_adjoin
    intro a ha b hb
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
    · rfl
    · exact commutes.eq
    · exact commutes.eq.symm
    · rfl
  letI : CommRing S:={ Subalgebra.toRing S with mul_comm:=fun a b=>mul_comm' a b }
  let sx : S:=⟨x,Algebra.subset_adjoin (by simp)⟩
  let sy : S:=⟨y,Algebra.subset_adjoin (by simp)⟩
  have insideX : IsIntegral ℂ sx:=
    (isIntegral_algHom_iff S.val Subtype.val_injective).mp hx
  have insideY : IsIntegral ℂ sy:=
    (isIntegral_algHom_iff S.val Subtype.val_injective).mp hy
  have scalarX : IsIntegral ℂ (algebraMap ℂ S Complex.I):=isIntegral_algebraMap
  have scalarY : IsIntegral ℂ (algebraMap ℂ S (-Complex.I)):=isIntegral_algebraMap
  have inside:=(scalarX.mul insideX).add (scalarY.mul insideY)
  have actual:=IsIntegral.map S.val inside
  convert! actual using 1
  simp only [map_add,map_mul,AlgHom.commutes,Algebra.smul_def]
  rfl

theorem sourceEvolution_integral (q : PhysicalResponsePoint) : IsIntegral ℂ (evolutionGenerator q):=by
  have actual:=commuting_integral_phase (A:=TransferOp) (sourceLeft q) (sourceRight q)
    (sourceLeftRight_commute q) (sourceLeft_integral q) (sourceRight_integral q)
  rw [sourceEvolution_multiplications]
  exact actual

def propagationPolynomial (q : PhysicalResponsePoint) : ℂ[X]:=minpoly ℂ (evolutionGenerator q)

theorem propagationPolynomial_monic (q : PhysicalResponsePoint) : (propagationPolynomial q).Monic:=
  minpoly.monic (sourceEvolution_integral q)

theorem sourceEvolution_annihilated (q : PhysicalResponsePoint) :
    aeval (evolutionGenerator q) (propagationPolynomial q)=0:=by
  unfold propagationPolynomial
  exact minpoly.aeval ℂ (evolutionGenerator q)

def propagationNumerator (q : PhysicalResponsePoint) (lambda : ℂ) : TransferOp:=
  aeval (evolutionGenerator q) ((propagationPolynomial q)/ₘ(X-C lambda))

private theorem polynomial_pencil {A : Type*} [Ring A] [Algebra ℂ A]
    (T : A) (P : ℂ[X]) (annihilated : aeval T P=0) (lambda : ℂ) :
    (algebraMap ℂ A lambda-T)*aeval T (P/ₘ(X-C lambda))=algebraMap ℂ A (P.eval lambda):=by
  have divide:=congrArg (aeval T) (modByMonic_add_div P (X-C lambda))
  rw [modByMonic_X_sub_C_eq_C_eval,map_add,map_mul,map_sub,aeval_C,aeval_X,aeval_C,annihilated] at divide
  apply sub_eq_zero.mp
  calc
    _= -(algebraMap ℂ A (P.eval lambda)+(T-algebraMap ℂ A lambda)*aeval T (P/ₘ(X-C lambda))):=by noncomm_ring
    _=0:=by rw [divide,neg_zero]

theorem sourceNumerator_pencil (q : PhysicalResponsePoint) (lambda : ℂ) :
    propagationPencil q lambda*propagationNumerator q lambda=
      (propagationPolynomial q).eval lambda • (1:TransferOp):=by
  have actual:=polynomial_pencil (A:=TransferOp) (evolutionGenerator q) (propagationPolynomial q)
    (sourceEvolution_annihilated q) lambda
  unfold propagationNumerator
  convert! actual using 1
  · unfold propagationPencil
    simp only [Algebra.algebraMap_eq_smul_one,ContinuousLinearMap.one_def]

private theorem minpoly_nonzero_at_inverse {A : Type*} [Ring A] [Algebra ℂ A]
    (T U : A) (integral : IsIntegral ℂ T) (lambda : ℂ)
    (inverse : U*(algebraMap ℂ A lambda-T)=1) : (minpoly ℂ T).eval lambda≠0:=by
  intro root
  let P:=minpoly ℂ T
  let Q:=P/ₘ(X-C lambda)
  have nonzero : P≠0:=minpoly.ne_zero integral
  have numerator:=polynomial_pencil T P (minpoly.aeval ℂ T) lambda
  rw [root,map_zero] at numerator
  have zero : aeval T Q=0:=by
    calc
      _=(U*(algebraMap ℂ A lambda-T))*aeval T Q:=by rw [inverse,one_mul]
      _=U*((algebraMap ℂ A lambda-T)*aeval T Q):=mul_assoc _ _ _
      _=0:=by rw [numerator,mul_zero]
  have factor : (X-C lambda)*Q=P:=by
    have divide:=modByMonic_add_div P (X-C lambda)
    rw [modByMonic_X_sub_C_eq_C_eval,root,C_0,zero_add] at divide
    exact divide
  have quotient_nonzero : Q≠0:=by
    intro vanish
    rw [vanish,mul_zero] at factor
    exact nonzero factor.symm
  have lower:=minpoly.degree_le_of_ne_zero ℂ T quotient_nonzero zero
  have upper:=degree_divByMonic_lt P (X-C lambda) nonzero (by rw [degree_X_sub_C];decide)
  exact (not_lt_of_ge lower) upper

theorem propagationPolynomial_offAxis (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0) :
    (propagationPolynomial q).eval lambda≠0:=by
  apply minpoly_nonzero_at_inverse (evolutionGenerator q) (actualResolvent q lambda)
    (sourceEvolution_integral q) lambda
  have actual:=actualResolvent_right q lambda off
  unfold propagationPencil at actual
  simpa only [Algebra.algebraMap_eq_smul_one,ContinuousLinearMap.one_def] using actual

def polynomialResolvent (q : PhysicalResponsePoint) (lambda : ℂ) : TransferOp:=
  ((propagationPolynomial q).eval lambda)⁻¹ • propagationNumerator q lambda

private theorem scalar_normalized_inverse {A : Type*} [Ring A] [Algebra ℂ A]
    (P N : A) (d : ℂ) (relation : P*N=d • (1:A)) (nonzero : d≠0) :
    P*(d⁻¹ • N)=1:=by
  rw [mul_smul_comm,relation,smul_smul,inv_mul_cancel₀ nonzero,one_smul]

theorem polynomialResolvent_left (q : PhysicalResponsePoint) (lambda : ℂ)
    (regular : (propagationPolynomial q).eval lambda≠0) :
    propagationPencil q lambda*polynomialResolvent q lambda=1:=by
  unfold polynomialResolvent
  exact scalar_normalized_inverse (A:=TransferOp) (propagationPencil q lambda)
    (propagationNumerator q lambda) ((propagationPolynomial q).eval lambda)
    (sourceNumerator_pencil q lambda) regular

private theorem inverse_unique {A : Type*} [Ring A] (P U V : A)
    (right : U*P=1) (left : P*V=1) : U=V:=by
  calc
    U=U*(P*V):=by rw [left,mul_one]
    _=(U*P)*V:=(mul_assoc _ _ _).symm
    _=V:=by rw [right,one_mul]

theorem polynomialResolvent_actual (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0) :
    polynomialResolvent q lambda=actualResolvent q lambda:=
  (inverse_unique (propagationPencil q lambda) (actualResolvent q lambda) (polynomialResolvent q lambda)
    (actualResolvent_right q lambda off)
    (polynomialResolvent_left q lambda (propagationPolynomial_offAxis q lambda off))).symm

theorem polynomialResolvent_future (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re) :
    polynomialResolvent q lambda=sourceInverse q lambda:=by
  rw [polynomialResolvent_actual q lambda (ne_of_gt positive)]
  unfold actualResolvent
  simp only [positive,↓reduceIte]

def rationalPreparedOperator (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (i : Fin 289) : Op:=
  if response then polynomialResolvent q lambda (slopeInitial q (fieldUnit i) force-
    leftCurrent q force*polynomialResolvent q lambda (rawInitial q (fieldUnit i))+
    polynomialResolvent q lambda (rawInitial q (fieldUnit i))*rightCurrent q force)
  else polynomialResolvent q lambda (rawInitial q (fieldUnit i))

theorem rationalPreparedOperator_actual (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (positive : 0<lambda.re) (i : Fin 289) :
    rationalPreparedOperator q force response lambda i=inversePreparedOperator q force response lambda i:=by
  unfold rationalPreparedOperator inversePreparedOperator
  rw [polynomialResolvent_future q lambda positive]

def rationalSource (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (lambda : ℂ) : Fin 289→ℂ:=
  fun i=>-sourceRead q (rationalPreparedOperator q force response lambda i)

theorem rationalSource_actual (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (positive : 0<lambda.re) :
    rationalSource q force response lambda=halfForcing q force response lambda:=by
  rw [←inverseSource_actual q force response lambda positive]
  funext i
  unfold rationalSource inverseSource
  rw [rationalPreparedOperator_actual q force response lambda positive i]

def rationalField (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : physicalSpectralDomain q.k) : Fin 289→ℂ:=
  PreparationVacuumOriginalGreenFeedback.sourceField
    ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val,lambda.property⟩
      (rationalSource q force response lambda.val)

theorem rationalField_actual (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : physicalSpectralDomain q.k) (positive : 0<lambda.val.re) :
    rationalField q force response lambda=halfField q force response q.k lambda:=by
  unfold rationalField halfField
  rw [rationalSource_actual q force response lambda.val positive]

theorem rationalField_equation (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : physicalSpectralDomain q.k) (positive : 0<lambda.val.re) :
    originalJacobi (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)*ᵥrationalField q force response lambda=
      rationalSource q force response lambda.val-originalRowLift
        (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)*ᵥ
          sourceCompatibility (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)
            (rationalSource q force response lambda.val):=by
  rw [rationalField_actual q force response lambda positive,rationalSource_actual q force response lambda.val positive]
  exact halfField_equation q force response q.k lambda

theorem rationalField_curvature (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : physicalSpectralDomain q.k) (positive : 0<lambda.val.re) :
    originalReader36 (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)*ᵥrationalField q force response lambda=
      curvatureReturn q force response lambda:=by
  rw [rationalField_actual q force response lambda positive]
  unfold curvatureReturn
  rw [pencilField_actual q force response lambda positive]

def sourcePoleOrder (q : PhysicalResponsePoint) (a : ℂ) : ℕ:=
  (propagationPolynomial q).rootMultiplicity a

def sourcePoleDenominator (q : PhysicalResponsePoint) (a : ℂ) : ℂ[X]:=
  propagationPolynomial q/ₘ(X-C a)^sourcePoleOrder q a

theorem sourcePole_factor (q : PhysicalResponsePoint) (a lambda : ℂ) :
    (lambda-a)^sourcePoleOrder q a*(sourcePoleDenominator q a).eval lambda=
      (propagationPolynomial q).eval lambda:=by
  have actual:=congrArg (eval lambda)
    (pow_mul_divByMonic_rootMultiplicity_eq (propagationPolynomial q) a)
  simpa only [sourcePoleOrder,sourcePoleDenominator,eval_mul,eval_pow,eval_sub,eval_X,eval_C] using actual

theorem sourcePole_regular (q : PhysicalResponsePoint) (a : ℂ) :
    (sourcePoleDenominator q a).eval a≠0:=
  eval_divByMonic_pow_rootMultiplicity_ne_zero a (propagationPolynomial_monic q).ne_zero

def sourcePoleRegularOperator (q : PhysicalResponsePoint) (a lambda : ℂ) : TransferOp:=
  ((sourcePoleDenominator q a).eval lambda)⁻¹ • propagationNumerator q lambda

def sourceLeadingPole (q : PhysicalResponsePoint) (a : ℂ) : TransferOp:=
  sourcePoleRegularOperator q a a

private theorem scalar_power_removed {E : Type*} [AddCommGroup E] [Module ℂ E]
    (z h : ℂ) (m : ℕ) (v : E) (nonzero : z≠0) :
    z^m • ((z^m*h)⁻¹ • v)=h⁻¹ • v:=by
  rw [smul_smul,mul_inv]
  rw [←mul_assoc,mul_inv_cancel₀ (pow_ne_zero m nonzero),one_mul]

theorem sourcePole_removed (q : PhysicalResponsePoint) (a lambda : ℂ) (punctured : lambda≠a) :
    (lambda-a)^sourcePoleOrder q a • polynomialResolvent q lambda=
      sourcePoleRegularOperator q a lambda:=by
  unfold polynomialResolvent sourcePoleRegularOperator
  rw [←sourcePole_factor q a lambda]
  exact scalar_power_removed (E:=TransferOp) (lambda-a) ((sourcePoleDenominator q a).eval lambda)
    (sourcePoleOrder q a) (propagationNumerator q lambda) (sub_ne_zero.mpr punctured)

private theorem root_minpoly_numerator_nonzero {A : Type*} [Ring A] [Algebra ℂ A]
    (T : A) (integral : IsIntegral ℂ T) (a : ℂ) (root : (minpoly ℂ T).eval a=0) :
    aeval T ((minpoly ℂ T)/ₘ(X-C a))≠0:=by
  intro vanish
  let P:=minpoly ℂ T
  let Q:=P/ₘ(X-C a)
  have nonzero : P≠0:=minpoly.ne_zero integral
  have factor : (X-C a)*Q=P:=by
    have divide:=modByMonic_add_div P (X-C a)
    rw [modByMonic_X_sub_C_eq_C_eval,root,C_0,zero_add] at divide
    exact divide
  have quotient_nonzero : Q≠0:=by
    intro zero
    rw [zero,mul_zero] at factor
    exact nonzero factor.symm
  have lower:=minpoly.degree_le_of_ne_zero ℂ T quotient_nonzero vanish
  have upper:=degree_divByMonic_lt P (X-C a) nonzero (by rw [degree_X_sub_C];decide)
  exact (not_lt_of_ge lower) upper

theorem sourceLeadingPole_nonzero (q : PhysicalResponsePoint) (a : ℂ)
    (root : (propagationPolynomial q).eval a=0) : sourceLeadingPole q a≠0:=by
  unfold sourceLeadingPole sourcePoleRegularOperator
  have numerator : propagationNumerator q a≠0:=
    root_minpoly_numerator_nonzero (evolutionGenerator q) (sourceEvolution_integral q) a root
  have nonzero := smul_ne_zero (M:=TransferOp) (inv_ne_zero (sourcePole_regular q a)) numerator
  convert! nonzero using 1

def sourceVisibleLeading (q : PhysicalResponsePoint) (a : ℂ) (reader : Field289) : ℂ:=
  -sourceRead q (sourceLeadingPole q a (rawInitial q reader))

def sourceLeadingForcing (q : PhysicalResponsePoint) (a : ℂ) : Fin 289→ℂ:=
  fun i=>sourceVisibleLeading q a (fieldUnit i)

def sourceLeadingField (q : PhysicalResponsePoint) (a : physicalSpectralDomain q.k) : Fin 289→ℂ:=
  PreparationVacuumOriginalGreenFeedback.sourceField
    ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) a.val,a.property⟩
      (sourceLeadingForcing q a.val)

theorem sourceLeadingField_equation (q : PhysicalResponsePoint) (a : physicalSpectralDomain q.k) :
    originalJacobi (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) a.val)*ᵥsourceLeadingField q a=
      sourceLeadingForcing q a.val-originalRowLift
        (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) a.val)*ᵥ
          sourceCompatibility (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) a.val)
            (sourceLeadingForcing q a.val):=by
  unfold sourceLeadingField
  exact PreparationVacuumOriginalGreenFeedback.original_forced_field
    (p:=⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) a.val,a.property⟩)
    (sourceLeadingForcing q a.val)

private theorem numerator_sum {A : Type*} [Ring A] [Algebra ℂ A]
    (T : A) (P : ℂ[X]) (lambda : ℂ) :
    aeval T (P/ₘ(X-C lambda))=
      ∑n∈Finset.range (P.natDegree+1),
        (∑j∈Finset.Icc (n+1) P.natDegree,lambda^(j-(n+1))*P.coeff j) • T^n:=by
  have degree : (P/ₘ(X-C lambda)).natDegree<P.natDegree+1:=by
    rw [natDegree_divByMonic P (monic_X_sub_C lambda)]
    exact lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self _)
  rw [aeval_eq_sum_range' degree]
  apply Finset.sum_congr rfl
  intro n _
  rw [coeff_divByMonic_X_sub_C]

private theorem numerator_sum_continuous {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (T : A) (P : ℂ[X]) : Continuous (fun lambda : ℂ=>
      ∑n∈Finset.range (P.natDegree+1),
        (∑j∈Finset.Icc (n+1) P.natDegree,lambda^(j-(n+1))*P.coeff j) • T^n):=by
  fun_prop

theorem propagationNumerator_continuous (q : PhysicalResponsePoint) :
    Continuous (propagationNumerator q):=by
  have actual:=numerator_sum_continuous (A:=TransferOp) (evolutionGenerator q) (propagationPolynomial q)
  convert! actual using 1
  funext lambda
  exact numerator_sum (A:=TransferOp) (evolutionGenerator q) (propagationPolynomial q) lambda

theorem sourcePoleRegular_continuousAt (q : PhysicalResponsePoint) (a : ℂ) :
    ContinuousAt (sourcePoleRegularOperator q a) a:=by
  have scalar : ContinuousAt (fun lambda : ℂ=>((sourcePoleDenominator q a).eval lambda)⁻¹) a:=
    (sourcePoleDenominator q a).continuous.continuousAt.inv₀ (sourcePole_regular q a)
  exact scalar.smul (propagationNumerator_continuous q).continuousAt

theorem sourcePole_leading_limit (q : PhysicalResponsePoint) (a : ℂ) :
    Filter.Tendsto (fun lambda : ℂ=>(lambda-a)^sourcePoleOrder q a • polynomialResolvent q lambda)
      (nhdsWithin a {lambda | lambda≠a}) (nhds (sourceLeadingPole q a)):=by
  have actual : Filter.Tendsto (sourcePoleRegularOperator q a)
      (nhdsWithin a {lambda | lambda≠a}) (nhds (sourceLeadingPole q a)):=
    (sourcePoleRegular_continuousAt q a).tendsto.mono_left inf_le_left
  apply Filter.Tendsto.congr' _ actual
  filter_upwards [self_mem_nhdsWithin] with lambda h
  exact (sourcePole_removed q a lambda h).symm

theorem sourceVisible_leading_limit (q : PhysicalResponsePoint) (a : ℂ) (reader : Field289) :
    Filter.Tendsto (fun lambda : ℂ=>(lambda-a)^sourcePoleOrder q a*
      (-sourceRead q (polynomialResolvent q lambda (rawInitial q reader))))
      (nhdsWithin a {lambda | lambda≠a}) (nhds (sourceVisibleLeading q a reader)):=by
  have operator:=sourcePole_leading_limit q a
  have applied:=(ContinuousLinearMap.continuous (R₁:=ℂ) (R₂:=ℂ) (M₁:=TransferOp) (M₂:=Op)
    (ContinuousLinearMap.apply ℂ Op (rawInitial q reader))).continuousAt.tendsto.comp operator
  have read:=(sourceRead q).continuous.continuousAt.tendsto.comp applied
  have signed:=read.neg
  convert! signed using 1
  funext lambda
  simp only [Function.comp_apply,ContinuousLinearMap.apply_apply,smul_apply,map_smul,
    smul_eq_mul,mul_neg]

end LowEnergy.SourcePropagationAlgebraicResponse
