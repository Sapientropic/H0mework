import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationSourceSpectralInverse

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationConstrainedPoleReturn
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumPhysicalFeedback
open PreparationVacuumPropagationPencil SourcePropagationResolvent SourcePropagationSpectralAxis
open SourcePropagationAlgebraicResponse PreparationVacuumActionFieldLift PreparationVacuumJointFieldResponse PreparationVacuumMixedFieldReturn
open Filter
open scoped Topology BigOperators
attribute [local irreducible] polynomialResolvent sourcePoleRegularOperator sourceLeadingPole
  rationalPreparedOperator rawInitial slopeInitial leftCurrent rightCurrent sourceRead

private theorem twice_scaled_response {E : Type*} [NormedRing E] [NormedAlgebra ℂ E]
    (R : E→L[ℂ] E) (s : ℂ) (D L H X : E) :
    (s*s) • R (D-L*R X+R X*H)=
      (s • R) (s • D-L*(s • R) X+(s • R) X*H):=by
  simp only [smul_apply,map_add,map_sub,map_smul,smul_sub,smul_add,
    smul_mul_assoc,mul_smul_comm,smul_smul]

private theorem power_twice (z : ℂ) (n : ℕ) : z^(2*n)=z^n*z^n:=by
  rw [Nat.mul_comm,pow_mul,pow_two]

def normalizedRaw (q : PhysicalResponsePoint) (a lambda : ℂ) (reader : Field289) : Op:=
  sourcePoleRegularOperator q a lambda (rawInitial q reader)

def normalizedFive (q : PhysicalResponsePoint) (a lambda : ℂ) (reader force : Field289) : Op:=
  sourcePoleRegularOperator q a lambda
    ((lambda-a)^sourcePoleOrder q a • slopeInitial q reader force-
      leftCurrent q force*normalizedRaw q a lambda reader+
      normalizedRaw q a lambda reader*rightCurrent q force)

/-- The contact initial value survives with its own lower Laurent order. -/
theorem fullFive_scaled (q : PhysicalResponsePoint) (a lambda : ℂ)
    (reader force : Field289) (punctured : lambda≠a) :
    (lambda-a)^(2*sourcePoleOrder q a) •
      polynomialResolvent q lambda (slopeInitial q reader force-
        leftCurrent q force*polynomialResolvent q lambda (rawInitial q reader)+
        polynomialResolvent q lambda (rawInitial q reader)*rightCurrent q force)=
      normalizedFive q a lambda reader force:=by
  rw [power_twice]
  have actual:=twice_scaled_response (E:=Op) (polynomialResolvent q lambda)
    ((lambda-a)^sourcePoleOrder q a) (slopeInitial q reader force)
    (leftCurrent q force) (rightCurrent q force) (rawInitial q reader)
  rw [sourcePole_removed q a lambda punctured] at actual
  exact actual

def fullFiveLeading (q : PhysicalResponsePoint) (a : ℂ) (reader force : Field289) : Op:=
  sourceLeadingPole q a
    (-leftCurrent q force*sourceLeadingPole q a (rawInitial q reader)+
      sourceLeadingPole q a (rawInitial q reader)*rightCurrent q force)

private theorem regular_response_continuous {E : Type*} [NormedRing E] [NormedAlgebra ℂ E]
    (B : ℂ→(E→L[ℂ] E)) (s : ℂ→ℂ) (D L H X : E) (a : ℂ)
    (continuousB : ContinuousAt B a) (continuousS : ContinuousAt s a) :
    ContinuousAt (fun lambda=>B lambda (s lambda • D-L*(B lambda X)+B lambda X*H)) a:=by
  have applied : ContinuousAt (fun lambda=>B lambda X) a:=
    (ContinuousLinearMap.continuous (ContinuousLinearMap.apply ℂ E X)).continuousAt.comp continuousB
  exact continuousB.clm_apply ((continuousS.smul continuousAt_const).sub
    (continuousAt_const.mul applied) |>.add (applied.mul continuousAt_const))

theorem normalizedFive_continuousAt (q : PhysicalResponsePoint) (a : ℂ)
    (reader force : Field289) : ContinuousAt (fun lambda=>normalizedFive q a lambda reader force) a:=by
  have scalar : ContinuousAt (fun lambda : ℂ=>(lambda-a)^sourcePoleOrder q a) a:=by fun_prop
  exact regular_response_continuous (E:=Op) (sourcePoleRegularOperator q a)
    (fun lambda=>(lambda-a)^sourcePoleOrder q a) (slopeInitial q reader force)
    (leftCurrent q force) (rightCurrent q force) (rawInitial q reader) a
    (sourcePoleRegular_continuousAt q a) scalar

private theorem regular_at_zero {E : Type*} [NormedRing E] [NormedAlgebra ℂ E]
    (B : E→L[ℂ] E) (s : ℂ) (D L H X : E) (zero : s=0) :
    B (s • D-L*B X+B X*H)=B (-L*B X+B X*H):=by
  rw [zero,zero_smul,zero_sub,neg_mul]

theorem normalizedFive_at_pole (q : PhysicalResponsePoint) (a : ℂ)
    (reader force : Field289) (root : (propagationPolynomial q).eval a=0) :
    normalizedFive q a a reader force=fullFiveLeading q a reader force:=by
  have order : sourcePoleOrder q a≠0:=
    (Polynomial.rootMultiplicity_pos (propagationPolynomial_monic q).ne_zero).mpr root |>.ne'
  have scalarZero : (a-a)^sourcePoleOrder q a=(0:ℂ):=by rw [sub_self,zero_pow order]
  unfold normalizedFive normalizedRaw fullFiveLeading sourceLeadingPole
  exact regular_at_zero (E:=Op) (sourcePoleRegularOperator q a a)
    ((a-a)^sourcePoleOrder q a) (slopeInitial q reader force)
    (leftCurrent q force) (rightCurrent q force) (rawInitial q reader) scalarZero

theorem fullFive_leading_limit (q : PhysicalResponsePoint) (a : ℂ)
    (reader force : Field289) (root : (propagationPolynomial q).eval a=0) :
    Tendsto (fun lambda : ℂ=>(lambda-a)^(2*sourcePoleOrder q a) •
      polynomialResolvent q lambda (slopeInitial q reader force-
        leftCurrent q force*polynomialResolvent q lambda (rawInitial q reader)+
        polynomialResolvent q lambda (rawInitial q reader)*rightCurrent q force))
      (nhdsWithin a {lambda | lambda≠a}) (nhds (fullFiveLeading q a reader force)):=by
  have actual : Tendsto (fun lambda=>normalizedFive q a lambda reader force)
      (nhdsWithin a {lambda | lambda≠a}) (nhds (fullFiveLeading q a reader force)):=by
    rw [←normalizedFive_at_pole q a reader force root]
    exact (normalizedFive_continuousAt q a reader force).tendsto.mono_left inf_le_left
  apply Tendsto.congr' _ actual
  filter_upwards [self_mem_nhdsWithin] with lambda h
  exact (fullFive_scaled q a lambda reader force h).symm

def responsePoleOrder (q : PhysicalResponsePoint) (a : ℂ) (response : Bool) : ℕ:=
  if response then 2*sourcePoleOrder q a else sourcePoleOrder q a

def preparedLeadingOperator (q : PhysicalResponsePoint) (a : ℂ) (force : Field289)
    (response : Bool) (i : Fin 289) : Op:=
  if response then fullFiveLeading q a (fieldUnit i) force
  else sourceLeadingPole q a (rawInitial q (fieldUnit i))

theorem preparedOperator_leading_limit (q : PhysicalResponsePoint) (a : ℂ)
    (force : Field289) (response : Bool) (i : Fin 289)
    (root : (propagationPolynomial q).eval a=0) :
    Tendsto (fun lambda : ℂ=>(lambda-a)^responsePoleOrder q a response •
      rationalPreparedOperator q force response lambda i)
      (nhdsWithin a {lambda | lambda≠a}) (nhds (preparedLeadingOperator q a force response i)):=by
  cases response
  · have operator:=sourcePole_leading_limit q a
    have applied:=(ContinuousLinearMap.continuous (R₁:=ℂ) (R₂:=ℂ) (M₁:=TransferOp) (M₂:=Op)
      (ContinuousLinearMap.apply ℂ Op (rawInitial q (fieldUnit i)))).continuousAt.tendsto.comp operator
    convert! applied using 1
    funext lambda
    simp only [responsePoleOrder,preparedLeadingOperator,rationalPreparedOperator,↓reduceIte,
      Bool.false_eq_true,Function.comp_apply,ContinuousLinearMap.apply_apply,smul_apply]

  · simpa only [responsePoleOrder,preparedLeadingOperator,rationalPreparedOperator,↓reduceIte] using
      fullFive_leading_limit q a (fieldUnit i) force root

def preparedLeadingSource (q : PhysicalResponsePoint) (a : ℂ) (force : Field289)
    (response : Bool) : Fin 289→ℂ:=
  fun i=>-sourceRead q (preparedLeadingOperator q a force response i)

theorem preparedSource_leading_limit (q : PhysicalResponsePoint) (a : ℂ)
    (force : Field289) (response : Bool) (root : (propagationPolynomial q).eval a=0) :
    Tendsto (fun lambda : ℂ=>(lambda-a)^responsePoleOrder q a response • rationalSource q force response lambda)
      (nhdsWithin a {lambda | lambda≠a}) (nhds (preparedLeadingSource q a force response)):=by
  apply tendsto_pi_nhds.mpr
  intro i
  have operator:=preparedOperator_leading_limit q a force response i root
  have signed:=((sourceRead q).continuous.continuousAt.tendsto.comp operator).neg
  convert! signed using 1
  funext lambda
  simp only [rationalSource,Function.comp_apply,Pi.smul_apply,map_smul,smul_eq_mul,mul_neg]

def normalizedPreparedOperator (q : PhysicalResponsePoint) (a lambda : ℂ) (force : Field289)
    (response : Bool) (i : Fin 289) : Op:=
  if response then normalizedFive q a lambda (fieldUnit i) force
  else normalizedRaw q a lambda (fieldUnit i)

theorem preparedOperator_scaled (q : PhysicalResponsePoint) (a lambda : ℂ)
    (force : Field289) (response : Bool) (i : Fin 289) (punctured : lambda≠a) :
    (lambda-a)^responsePoleOrder q a response • rationalPreparedOperator q force response lambda i=
      normalizedPreparedOperator q a lambda force response i:=by
  cases response
  · have actual:=congrArg (fun B : TransferOp=>B (rawInitial q (fieldUnit i)))
      (sourcePole_removed q a lambda punctured)
    simpa only [responsePoleOrder,rationalPreparedOperator,normalizedPreparedOperator,normalizedRaw,
      Bool.false_eq_true,↓reduceIte,smul_apply] using actual
  · simpa only [responsePoleOrder,rationalPreparedOperator,normalizedPreparedOperator,↓reduceIte] using
      fullFive_scaled q a lambda (fieldUnit i) force punctured

theorem normalizedPreparedOperator_continuousAt (q : PhysicalResponsePoint) (a : ℂ)
    (force : Field289) (response : Bool) (i : Fin 289) :
    ContinuousAt (fun lambda=>normalizedPreparedOperator q a lambda force response i) a:=by
  cases response
  · exact (ContinuousLinearMap.continuous (ContinuousLinearMap.apply ℂ Op (rawInitial q (fieldUnit i)))).continuousAt.comp
      (sourcePoleRegular_continuousAt q a)
  · exact normalizedFive_continuousAt q a (fieldUnit i) force

theorem normalizedPreparedOperator_at_pole (q : PhysicalResponsePoint) (a : ℂ)
    (force : Field289) (response : Bool) (i : Fin 289) (root : (propagationPolynomial q).eval a=0) :
    normalizedPreparedOperator q a a force response i=preparedLeadingOperator q a force response i:=by
  cases response
  · simp only [normalizedPreparedOperator,normalizedRaw,preparedLeadingOperator,Bool.false_eq_true,↓reduceIte]
    rw [sourceLeadingPole]
  · exact normalizedFive_at_pole q a (fieldUnit i) force root

def normalizedPreparedSource (q : PhysicalResponsePoint) (a lambda : ℂ) (force : Field289)
    (response : Bool) : Fin 289→ℂ:=
  fun i=>-sourceRead q (normalizedPreparedOperator q a lambda force response i)

theorem preparedSource_scaled (q : PhysicalResponsePoint) (a lambda : ℂ)
    (force : Field289) (response : Bool) (punctured : lambda≠a) :
    (lambda-a)^responsePoleOrder q a response • rationalSource q force response lambda=
      normalizedPreparedSource q a lambda force response:=by
  funext i
  have actual:=congrArg (fun X : Op=>-sourceRead q X)
    (preparedOperator_scaled q a lambda force response i punctured)
  simpa only [rationalSource,normalizedPreparedSource,Pi.smul_apply,map_smul,smul_eq_mul,mul_neg] using actual

theorem normalizedPreparedSource_continuousAt (q : PhysicalResponsePoint) (a : ℂ)
    (force : Field289) (response : Bool) :
    ContinuousAt (fun lambda=>normalizedPreparedSource q a lambda force response) a:=by
  apply continuousAt_pi.mpr
  intro i
  exact ((sourceRead q).continuous.continuousAt.comp
    (normalizedPreparedOperator_continuousAt q a force response i)).neg

theorem normalizedPreparedSource_at_pole (q : PhysicalResponsePoint) (a : ℂ)
    (force : Field289) (response : Bool) (root : (propagationPolynomial q).eval a=0) :
    normalizedPreparedSource q a a force response=preparedLeadingSource q a force response:=by
  funext i
  unfold normalizedPreparedSource preparedLeadingSource
  rw [normalizedPreparedOperator_at_pole q a force response i root]

end LowEnergy.SourcePropagationConstrainedPoleReturn
