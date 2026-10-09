import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceMovingPoleGaussVertex
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceSignalOperatorPrice

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMovingPoleGaussReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumFockGauge GaussCoreHilbert GaussFockLift GaussQuantumMultiplier
open PreparationVacuumElectromagneticIdentity CanonicalGradedSpatialSource
open PreparationVacuumSourcePreparedState PreparationVacuumFieldConstraintResponse
open PreparationVacuumGaugeSourceInjection
open PreparationVacuumPhysicalFeedback PreparationVacuumIndependentMomentumReturn
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open PreparationVacuumMixedFieldReturn PreparationVacuumNoetherChart PreparationVacuumJointFieldResponse
open PreparationVacuumRawJointFeedback PreparationVacuumActionFieldLift
open SourcePropagationNoetherTime SourcePropagationNativeEulerHistory
open SourcePropagationMotherEulerKernel SourcePropagationTimeDependentFeedback
open Filter
open scoped BigOperators InnerProductSpace ContDiff Topology Matrix
abbrev PoleSourceOp:=H→L[ℂ] H
local instance : NormedAlgebra ℝ PoleSourceOp:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] actualMovingPolePreparation sourcePreparation
  sourceMovingIndependentKernel sourceMovingIndependentReader noetherReader
  sourceHistoryOperator noetherHistoryOperatorJet jointGenerator jointResolvent

def sourcePoleRead (epsilon : ℝ) (precision : 0<epsilon) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex) : PoleSourceOp→L[ℂ] ℂ:=
  (innerSL ℂ (sourcePolePrepared epsilon precision leftMomentum left)).comp
    (ContinuousLinearMap.apply ℂ H (sourcePolePrepared epsilon precision rightMomentum right))

theorem sourcePoleRead_actual (epsilon : ℝ) (precision : 0<epsilon) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex) (A : PoleSourceOp) :
    sourcePoleRead epsilon precision leftMomentum rightMomentum left right A=
      inner ℂ (sourcePolePrepared epsilon precision leftMomentum left)
        (A (sourcePolePrepared epsilon precision rightMomentum right)) :=rfl

theorem sourcePoleRead_price (epsilon : ℝ) (precision : 0<epsilon) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex) : ‖sourcePoleRead epsilon precision leftMomentum rightMomentum left right‖≤1 :=by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  rw [sourcePoleRead_actual,one_mul]
  have cost:=(norm_inner_le_norm (𝕜:=ℂ) (sourcePolePrepared epsilon precision leftMomentum left)
      (A (sourcePolePrepared epsilon precision rightMomentum right))).trans
    (mul_le_mul_of_nonneg_left (A.le_opNorm (sourcePolePrepared epsilon precision rightMomentum right))
      (norm_nonneg (sourcePolePrepared epsilon precision leftMomentum left)))
  simpa only [sourcePolePrepared_unit,one_mul,mul_one] using cost

def sourcePoleIndependentDual (epsilon : ℝ) (precision : 0<epsilon) (leftMomentum : PhysicalMomentum)
    (left : RestStateIndex) (q : PhysicalResponsePoint) (h : Field289) (age : ℝ) : H→L[ℂ] ℂ:=
  ((innerSL ℂ (sourcePolePrepared epsilon precision leftMomentum left)).comp
    (physicalTime (q.p+q.k) q.F (-age) h)).comp (jointResolvent (q.p+q.k) q.F q.z h)

def sourcePolePreparedPrimal (epsilon : ℝ) (precision : 0<epsilon) (rightMomentum : PhysicalMomentum)
    (right : RestStateIndex) (q : PhysicalResponsePoint) (h : Field289) (age : ℝ) : H:=
  jointResolvent q.p q.F q.w h (physicalTime q.p q.F age h
    (sourcePolePrepared epsilon precision rightMomentum right))

def sourcePolePreparedDensity (epsilon : ℝ) (precision : 0<epsilon) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex) (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) : ℂ:=
  sourcePoleIndependentDual epsilon precision leftMomentum left q h age
    (sourceMovingIndependentReader reader q.p q.F h
      (sourcePolePreparedPrimal epsilon precision rightMomentum right q h age))

theorem sourcePolePreparedDensity_kernel (epsilon : ℝ) (precision : 0<epsilon)
    (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) :
    sourcePolePreparedDensity epsilon precision leftMomentum rightMomentum left right q reader h age=
      sourcePoleRead epsilon precision leftMomentum rightMomentum left right
        (sourceMovingIndependentKernel q reader age h) :=by
  simp only [sourcePolePreparedDensity,sourcePoleIndependentDual,sourcePolePreparedPrimal,
    sourcePoleRead_actual,sourceMovingIndependentKernel,mul_apply_eq_comp,ContinuousLinearMap.comp_apply,innerSL_apply_apply]

theorem sourcePolePreparedDensity_source (epsilon : ℝ) (precision : 0<epsilon)
    (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (q : PhysicalResponsePoint) (reader : Field289) (age : ℝ) :
    sourcePolePreparedDensity epsilon precision leftMomentum rightMomentum left right q reader 0 age=
      sourcePoleRead epsilon precision leftMomentum rightMomentum left right
        (fiveKernel reader q.p q.k q.F q.z q.w age 0) :=by
  rw [sourcePolePreparedDensity_kernel,sourceMovingIndependentKernel,sourceMovingIndependentReader_source]
  rfl

theorem sourcePolePreparedDensity_C2 (epsilon : ℝ) (precision : 0<epsilon)
    (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (q : PhysicalResponsePoint) (reader : Field289) (age : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    ContDiffAt ℝ 2 (fun h=>sourcePolePreparedDensity epsilon precision leftMomentum rightMomentum left right q reader h age) 0 :=by
  have current:=((sourcePoleRead epsilon precision leftMomentum rightMomentum left right).restrictScalars ℝ).contDiff.contDiffAt.comp 0
    (sourceMovingIndependentKernel_C2 q reader age hz hw)
  convert! current using 1
  funext h
  exact sourcePolePreparedDensity_kernel epsilon precision leftMomentum rightMomentum left right q reader h age

theorem sourcePolePreparedDensity_frechet (epsilon : ℝ) (precision : 0<epsilon)
    (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (q : PhysicalResponsePoint) (reader : Field289) (age : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasFDerivAt (fun h=>sourcePolePreparedDensity epsilon precision leftMomentum rightMomentum left right q reader h age)
      (((sourcePoleRead epsilon precision leftMomentum rightMomentum left right).restrictScalars ℝ).comp
        (fderiv ℝ (sourceMovingIndependentKernel q reader age) 0)) 0 :=by
  have actual:=((sourcePoleRead epsilon precision leftMomentum rightMomentum left right).restrictScalars ℝ).hasFDerivAt.comp 0
    ((sourceMovingIndependentKernel_C2 q reader age hz hw).differentiableAt (by norm_num)).hasFDerivAt
  convert! actual using 1
  funext h
  exact sourcePolePreparedDensity_kernel epsilon precision leftMomentum rightMomentum left right q reader h age

attribute [local irreducible] sourcePoleRead sourcePolePrepared sourcePolePreparedDensity

private theorem fixedRead_mixed {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (read : V→L[ℝ] W) (A : E→V) (point f g : E) (regular : ContDiffAt ℝ 2 A point) :
    fderiv ℝ (fderiv ℝ (fun h=>read (A h))) point f g=read (fderiv ℝ (fderiv ℝ A) point f g) :=by
  have germ : fderiv ℝ (fun h=>read (A h))=ᶠ[𝓝 point] (fun h=>read.comp (fderiv ℝ A h)):=
    (regular.eventually (by norm_num)).mono (fun h hc=>
      (read.hasFDerivAt.comp h (hc.differentiableAt (by norm_num)).hasFDerivAt).fderiv)
  let compose : (E→L[ℝ] V)→L[ℝ] (E→L[ℝ] W):=(ContinuousLinearMap.compL ℝ E V W) read
  have derivative : DifferentiableAt ℝ (fderiv ℝ A) point:=
    (regular.fderiv_right (show (1:ℕ∞ω)+1≤2 by norm_num)).differentiableAt (by norm_num)
  have paid:=(compose.hasFDerivAt.comp point derivative.hasFDerivAt).fderiv
  change fderiv ℝ (fun h=>read.comp (fderiv ℝ A h)) point=
    compose.comp (fderiv ℝ (fderiv ℝ A) point) at paid
  rw [germ.fderiv_eq,paid]
  rfl

theorem sourcePolePreparedDensity_mixed (epsilon : ℝ) (precision : 0<epsilon)
    (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (q : PhysicalResponsePoint) (reader f g : Field289) (age : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    fderiv ℝ (fderiv ℝ (fun h=>sourcePolePreparedDensity epsilon precision leftMomentum rightMomentum left right q reader h age)) 0 f g=
      sourcePoleRead epsilon precision leftMomentum rightMomentum left right
        (fderiv ℝ (fderiv ℝ (sourceMovingIndependentKernel q reader age)) 0 f g) :=by
  have actual : (fun h=>sourcePolePreparedDensity epsilon precision leftMomentum rightMomentum left right q reader h age)=
      fun h=>((sourcePoleRead epsilon precision leftMomentum rightMomentum left right).restrictScalars ℝ)
        (sourceMovingIndependentKernel q reader age h) :=by
    funext h
    exact sourcePolePreparedDensity_kernel epsilon precision leftMomentum rightMomentum left right q reader h age
  have transported:=congrArg (fun value : Field289→ℂ=>fderiv ℝ (fderiv ℝ value) 0 f g) actual
  exact transported.trans (fixedRead_mixed _ _ 0 f g (sourceMovingIndependentKernel_C2 q reader age hz hw))

def sourcePoleHistoryJet (epsilon : ℝ) (precision : 0<epsilon) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex) (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (a : SignalAmplitude)
    (t : ℝ) (i : Fin 289) : SourceJet ℂ:=
  negativeJet (pairJet (sourcePolePrepared epsilon precision leftMomentum left)
    (sourcePolePrepared epsilon precision rightMomentum right)
      (noetherHistoryOperatorJet q (fieldUnit i) (nativeTimeSignal (sourceRealSignal p a)) t))

theorem sourcePoleHistoryJet_generated (epsilon : ℝ) (precision : 0<epsilon)
    (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (a : SignalAmplitude) (t : ℝ) (i : Fin 289) :
    HasSourceJets (fun s=>sourcePoleHistoryJet epsilon precision leftMomentum rightMomentum left right q p a s i) t :=
  negativeJets_generated _ _ (pairJets_generated _ _ _ _
    (noetherHistoryOperatorJet_generated q (fieldUnit i) (nativeTimeSignal (sourceRealSignal p a))
      (sourceTimeSignal_continuous p a).1 t (sourceTimeSignal_generated p a t)))

def sourcePoleCurrentOperator (epsilon : ℝ) (precision : 0<epsilon) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex) (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (t : ℝ) :
    SignalAmplitude→L[ℝ] SignalAmplitude:=
  ContinuousLinearMap.pi (fun i=>
    (-((sourcePoleRead epsilon precision leftMomentum rightMomentum left right).restrictScalars ℝ)).comp
      (sourceHistoryOperator q (fieldUnit i) p t))

theorem sourcePoleCurrentOperator_actual (epsilon : ℝ) (precision : 0<epsilon)
    (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (t : ℝ) (a : SignalAmplitude) :
    sourcePoleCurrentOperator epsilon precision leftMomentum rightMomentum left right q p t a=
      fun i=>(sourcePoleHistoryJet epsilon precision leftMomentum rightMomentum left right q p a t i).value :=by
  funext i
  simp only [sourcePoleCurrentOperator,ContinuousLinearMap.pi_apply,ContinuousLinearMap.comp_apply,neg_apply]
  rw [sourceHistoryOperator_actual]
  change -(sourcePoleRead epsilon precision leftMomentum rightMomentum left right
    (noetherHistoryOperatorJet q (fieldUnit i) (nativeTimeSignal (sourceRealSignal p a)) t).value)=_
  rw [sourcePoleRead_actual]
  rfl

theorem sourcePoleCurrentOperator_rowPrice (epsilon : ℝ) (precision : 0<epsilon)
    (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (eta t : ℝ) (positive : 0<eta) (future : 0≤t)
    (a : SignalAmplitude) (i : Fin 289) :
    ‖sourcePoleCurrentOperator epsilon precision leftMomentum rightMomentum left right q p t a i‖≤
      ((sourceHistoryLinearCoefficient q (fieldUnit i) eta*t+sourceHistoryConstantCoefficient q (fieldUnit i) eta)*
        Real.exp ((4*eta+sourceClockGrowth p)*t))*‖a‖ :=by
  simp only [sourcePoleCurrentOperator,ContinuousLinearMap.pi_apply,ContinuousLinearMap.comp_apply,neg_apply,norm_neg]
  have read:= (sourcePoleRead epsilon precision leftMomentum rightMomentum left right).le_opNorm
    (sourceHistoryOperator q (fieldUnit i) p t a)
  have unit:=mul_le_mul_of_nonneg_right (sourcePoleRead_price epsilon precision leftMomentum rightMomentum left right)
    (norm_nonneg (sourceHistoryOperator q (fieldUnit i) p t a))
  have history:=(sourceHistoryOperator q (fieldUnit i) p t).le_opNorm a
  have source:=sourceHistoryOperator_price q (fieldUnit i) p eta t positive future
  exact ((read.trans unit).trans (by simpa only [one_mul] using history)).trans
    (mul_le_mul_of_nonneg_right source (norm_nonneg a))

end LowEnergy.PreparationVacuumMovingPoleGaussReturn
