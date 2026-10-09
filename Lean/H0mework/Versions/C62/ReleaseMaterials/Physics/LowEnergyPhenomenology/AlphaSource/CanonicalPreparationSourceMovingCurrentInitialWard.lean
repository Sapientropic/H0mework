import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePhysicalCurrentResponse
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceMovingCurrentConservation

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumElectromagneticIdentity
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction
open SourcePropagationNativeActionHessian PreparationVacuumOriginalGreenFeedback PreparationVacuumLowerClassical
open PreparationVacuumMixedFieldReturn Stage9DEF Stage9DEF.Compatibility
open Stage10 Stage9C.Material.SpinPair
open ChargedPreparation.Dynamics ChargedPreparation.SpatialSpectrum
open DiracCliffordRepresentation SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeConnectionActionVariation PreparationVacuumCoefficientBudget
open StageNineEnrichedProofFreeSource StageNineGlobalIntegratedAction
open StageNineP286GaugeConnectionVariationDensity StageNineMatterVariation
open StageNineDiracKineticLocalSpinDensity StageNineMatterCovariantDerivativeAffine
open StageNineDiracDualFormNativeMatterVariation StageNineP286GaugeConnectionVariation
open StageNineP286GaugeAuxiliaryVariation StageNineP286GaugeConnectionActionVariation
open scoped Matrix BigOperators InnerProductSpace

private def initialReadbackCoefficient (p : Fin 4→ℂ) (constraint : Fin 9) (mu : Fin 4) (a : Fin 12) : ℂ :=
  if constraint=0 then
    (if a=1 then p mu/2 else 0)+
      if mu=2 then (if a=6 then -3*(spinScale:ℂ)/10 else if a=7 then 3*(spinScale:ℂ)/10 else 0)
      else if mu=3 ∧ a=0 then 3*(spinScale:ℂ)/10 else 0
  else if constraint=1 then
    (if a=0 then p mu/2 else 0)+
      if mu=1 then (if a=6 then 3*(spinScale:ℂ)/10 else if a=7 then -3*(spinScale:ℂ)/10 else 0)
      else if mu=3 ∧ a=1 then -3*(spinScale:ℂ)/10 else 0
  else if constraint=2 then
    (if a=6 then p mu/2 else if a=7 then -p mu/2 else 0)+
      if mu=1 ∧ a=0 then -3*(spinScale:ℂ)/10
      else if mu=2 ∧ a=1 then 3*(spinScale:ℂ)/10 else 0
  else 0

private theorem initialMatrix_reconstruct (p : Fin 4→ℂ) (constraint : Fin 9) :
    sourceMovingConstraintMatrix p constraint=
      ∑ mu : Fin 4,∑ a : Fin 12,initialReadbackCoefficient p constraint mu a • sourceMovingGaugeMatrix mu a := rfl

private def initialTemporal {V : Type} (M : Fin 4→Fin 12→V) [Sub V] [Zero V] (constraint : Fin 9) : V :=
  if constraint=0 then M 0 1 else if constraint=1 then M 0 0 else if constraint=2 then M 0 6-M 0 7 else 0

private theorem initialSum6_7 {V : Type} [AddCommMonoid V] (f g : Fin 12→V) :
    (∑ x : Fin 12,if x=6 then f x else if x=7 then g x else 0)=f 6+g 7 := by
  have split (x : Fin 12) : (if x=6 then f x else if x=7 then g x else 0)=
      (if x=6 then f x else 0)+(if x=7 then g x else 0) := by
    by_cases first : x=6
    · subst x
      simp [show (6:Fin 12)≠7 by decide]
    · simp [first]
  simp_rw [split]
  simp [Finset.sum_add_distrib]

private theorem initialMatrix_shift {V : Type} [AddCommGroup V] [Module ℂ V]
    (M : Fin 4→Fin 12→V) (p : Fin 4→ℂ) (readClock : ℂ) (constraint : Fin 9) :
    (∑ mu : Fin 4,∑ a : Fin 12,initialReadbackCoefficient (Function.update p 0 readClock) constraint mu a • M mu a)=
      (∑ mu : Fin 4,∑ a : Fin 12,initialReadbackCoefficient p constraint mu a • M mu a)+
        ((readClock-p 0)/2) • initialTemporal M constraint := by
  fin_cases constraint <;>
    simp [initialReadbackCoefficient,initialTemporal,Fin.sum_univ_four,Function.update,
      add_smul,ite_smul,Finset.sum_add_distrib]
  all_goals simp_rw [initialSum6_7]
  all_goals module

def sourceMovingTemporalGenerator (constraint : Fin 9) : Matrix Source.Index Source.Index ℂ :=
  initialTemporal sourceMovingGaugeMatrix constraint

theorem sourceMovingConstraintMatrix_readClock (p : Fin 4→ℂ) (readClock : ℂ) (constraint : Fin 9) :
    sourceMovingConstraintMatrix (Function.update p 0 readClock) constraint=
      sourceMovingConstraintMatrix p constraint+((readClock-p 0)/2) • sourceMovingTemporalGenerator constraint := by
  rw [initialMatrix_reconstruct,initialMatrix_reconstruct]
  exact initialMatrix_shift sourceMovingGaugeMatrix p readClock constraint

def sourceMovingInitialCurrent (leftMomentum rightMomentum : Fin 3→ℝ) (left right : RestStateIndex)
    (constraint : Fin 9) : ℂ :=
  (ActionNormalization.phaseMomentum:ℂ)/2*
    (star (sourceMovingPoleValues leftMomentum left) ⬝ᵥ
      (sourceMovingTemporalGenerator constraint *ᵥ sourceMovingPoleValues rightMomentum right))

theorem sourceMovingConstraintTensor_readClock (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (readClock : ℂ) (constraint : Fin 9) :
    sourceMovingConstraintTensor
      (Function.update (sourceMovingExchangeMomentum leftMomentum rightMomentum left right) 0 readClock)
      leftMomentum rightMomentum left right constraint=
      (readClock-sourceMovingExchangeMomentum leftMomentum rightMomentum left right 0)*
        sourceMovingInitialCurrent leftMomentum rightMomentum left right constraint := by
  rw [sourceMovingConstraintTensor_matrix,sourceMovingConstraintMatrix_readClock,
    Matrix.add_mulVec,Matrix.smul_mulVec,dotProduct_add,dotProduct_smul,mul_add]
  have zero:=sourceMovingConstraintTensor_onShell leftMomentum rightMomentum left right constraint
  rw [sourceMovingConstraintTensor_matrix] at zero
  rw [zero,zero_add]
  unfold sourceMovingInitialCurrent
  ring

private theorem initialCurrent_outside (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (constraint : Fin 9) (outside : 3 ≤ constraint.val) :
    sourceMovingInitialCurrent leftMomentum rightMomentum left right constraint=0 := by
  have a : constraint≠0:=by intro h; subst constraint; simp at outside
  have b : constraint≠1:=by intro h; subst constraint; simp at outside
  have c : constraint≠2:=by intro h; subst constraint; simp at outside
  simp [sourceMovingInitialCurrent,sourceMovingTemporalGenerator,initialTemporal,a,b,c]

def sourceMovingInitialCovector (leftMomentum rightMomentum : Fin 3→ℝ) (left right : RestStateIndex) : Fin 289→ℂ :=
  fun field=>if inside : 112 ≤ field.val ∧ field.val<121 then
    sourceMovingInitialCurrent leftMomentum rightMomentum left right ⟨field.val-112,by omega⟩ else 0

theorem sourceMovingInitialCovector_slot (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (constraint : Fin 9) :
    sourceMovingInitialCovector leftMomentum rightMomentum left right (sourceRestGaugeConstraintSlot constraint)=
      sourceMovingInitialCurrent leftMomentum rightMomentum left right constraint := by
  unfold sourceMovingInitialCovector
  have inside : 112 ≤ (sourceRestGaugeConstraintSlot constraint).val ∧
      (sourceRestGaugeConstraintSlot constraint).val<121 := by
    simp only [sourceRestGaugeConstraintSlot,Fin.val_mk]
    omega
  rw [dif_pos inside]
  congr 1
  apply Fin.ext
  simp [sourceRestGaugeConstraintSlot]

theorem actualMovingNativeForcing_readClock (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (readClock : ℂ) :
    sourceCompatibility
      (Function.update (sourceMovingExchangeMomentum leftMomentum rightMomentum left right) 0 readClock)
      (actualMovingNativeForcing 0 leftMomentum rightMomentum left right)=
      (readClock-sourceMovingExchangeMomentum leftMomentum rightMomentum left right 0) •
        sourceMovingInitialCovector leftMomentum rightMomentum left right := by
  funext field
  by_cases inside : 112 ≤ field.val ∧ field.val<121
  · let constraint : Fin 9:=⟨field.val-112,by omega⟩
    have same : sourceRestGaugeConstraintSlot constraint=field := by
      apply Fin.ext
      simp only [sourceRestGaugeConstraintSlot,Fin.val_mk]
      dsimp [constraint]
      omega
    rw [←same,actualMovingConstraintCurrent_generated,sourceMovingConstraintTensor_readClock]
    simp only [Pi.smul_apply,smul_eq_mul,sourceMovingInitialCovector_slot]
  · unfold sourceCompatibility nullProjection projectionMatrix sourceMovingInitialCovector
    rw [Matrix.mulVec_diagonal]
    have flag : nullFlag field=false := by
      simp only [nullFlag,decide_eq_false_iff_not]
      exact inside
    simp only [flag,Bool.false_eq_true,if_false,zero_mul,Pi.smul_apply,dif_neg inside,smul_eq_mul,mul_zero]

theorem actualMovingNativeHalfForcing_initial (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (readClock : ℂ)
    (distinct : readClock≠sourceMovingExchangeMomentum leftMomentum rightMomentum left right 0) :
    sourceCompatibility
      (Function.update (sourceMovingExchangeMomentum leftMomentum rightMomentum left right) 0 readClock)
      ((readClock-sourceMovingExchangeMomentum leftMomentum rightMomentum left right 0)⁻¹ •
        actualMovingNativeForcing 0 leftMomentum rightMomentum left right)=
      sourceMovingInitialCovector leftMomentum rightMomentum left right := by
  rw [sourceCompatibility,Matrix.mulVec_smul,Matrix.mulVec_smul]
  change (readClock-sourceMovingExchangeMomentum leftMomentum rightMomentum left right 0)⁻¹ •
    sourceCompatibility _ (actualMovingNativeForcing 0 leftMomentum rightMomentum left right)=_
  rw [actualMovingNativeForcing_readClock,smul_smul,inv_mul_cancel₀ (sub_ne_zero.mpr distinct),one_smul]

def sourceMovingReadMomentum (leftMomentum rightMomentum : Fin 3→ℝ) (readClock : ℂ) : Fin 4→ℂ :=
  PreparationVacuumPhysicalFeedback.fullMomentum
    (PreparationVacuumPhysicalFeedback.physicalSpatial
      (PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalTransfer leftMomentum rightMomentum)) readClock

private theorem initialReadMomentum_source (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (readClock : ℂ) :
    sourceMovingReadMomentum leftMomentum rightMomentum readClock=
      Function.update (sourceMovingExchangeMomentum leftMomentum rightMomentum left right) 0 readClock := by
  funext mu
  fin_cases mu <;> rfl

theorem sourceMovingPhysicalHalf_initial (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (readClock : ℂ) (off : 0<readClock.re) :
    sourceCompatibility (sourceMovingReadMomentum leftMomentum rightMomentum readClock)
      (PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalCurrentHalf
        leftMomentum rightMomentum left right readClock)=
      sourceMovingInitialCovector leftMomentum rightMomentum left right := by
  rw [initialReadMomentum_source,
    PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalCurrentHalf_generated _ _ _ _ readClock off]
  have distinct : readClock≠sourceMovingExchangeMomentum leftMomentum rightMomentum left right 0 := by
    intro same
    have real:=congrArg Complex.re same
    change readClock.re=(PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalClock
      leftMomentum rightMomentum left right).re at real
    rw [PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalClock_re] at real
    linarith
  exact actualMovingNativeHalfForcing_initial leftMomentum rightMomentum left right readClock distinct

theorem sourceMovingPhysicalHalf_native (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (readClock : ℂ) (off : 0<readClock.re)
    (regular : sourceMovingReadMomentum leftMomentum rightMomentum readClock∈regularSource) :
    nativeFourierHessian nativeHessian (sourceMovingReadMomentum leftMomentum rightMomentum readClock) *ᵥ
      PreparationVacuumOriginalGreenFeedback.sourceField
        ⟨sourceMovingReadMomentum leftMomentum rightMomentum readClock,regular⟩
        (PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalCurrentHalf
          leftMomentum rightMomentum left right readClock)=
      PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalCurrentHalf
        leftMomentum rightMomentum left right readClock-
      originalRowLift (sourceMovingReadMomentum leftMomentum rightMomentum readClock) *ᵥ
        sourceMovingInitialCovector leftMomentum rightMomentum left right := by
  have generated:=nativeAction_sourceField
    (⟨sourceMovingReadMomentum leftMomentum rightMomentum readClock,regular⟩:regularSource)
    (PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalCurrentHalf
      leftMomentum rightMomentum left right readClock)
  simpa only [sourceMovingPhysicalHalf_initial _ _ _ _ readClock off] using generated

def sourceMovingInitialDirection (constraint : Fin 9) : Field289 :=
  if constraint=0 then Pi.single (gaugeSlot 0 1) 1 else if constraint=1 then Pi.single (gaugeSlot 0 0) 1
  else if constraint=2 then Pi.single (gaugeSlot 0 6) 1-Pi.single (gaugeSlot 0 7) 1 else 0

private theorem initialSlot_source (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (a : Fin 12) :
    sourceMovingGaugeCurrentLinear 0 (actualMovingPairPoint 0 leftMomentum rightMomentum left right)
      (Pi.single (gaugeSlot 0 a) 1)=
      (ActionNormalization.phaseMomentum:ℂ)*
        (star (sourceMovingPoleValues leftMomentum left) ⬝ᵥ
          (sourceMovingGaugeMatrix 0 a *ᵥ sourceMovingPoleValues rightMomentum right)) := by
  change actualMovingNativeForcing 0 leftMomentum rightMomentum left right (gaugeSlot 0 a)=_
  exact actualMovingNativeForcing_slot 0 leftMomentum rightMomentum left right 0 a

theorem sourceMovingInitialCurrent_original (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (constraint : Fin 9) :
    sourceMovingInitialCurrent leftMomentum rightMomentum left right constraint=
      (1/2:ℂ)*sourceMovingGaugeCurrentLinear 0 (actualMovingPairPoint 0 leftMomentum rightMomentum left right)
        (sourceMovingInitialDirection constraint) := by
  fin_cases constraint <;> simp [sourceMovingInitialCurrent,sourceMovingInitialDirection,
    sourceMovingTemporalGenerator,initialTemporal,LinearMap.map_sub,initialSlot_source,
    Matrix.sub_mulVec,dotProduct_sub]
  all_goals ring

theorem sourceMovingInitialCurrent_kinetic (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (constraint : Fin 9) (parameter : ℝ) :
    HasDerivAt (actualMovingGaugeKineticCurve 0 leftMomentum rightMomentum left right
      (sourceMovingInitialDirection constraint))
      (2*(sourceMovingInitialCurrent leftMomentum rightMomentum left right constraint).re) parameter := by
  have generated:=actualMovingGaugeKineticCurve_hasDerivAt 0 leftMomentum rightMomentum left right
    (sourceMovingInitialDirection constraint) parameter
  rw [actualMovingNativeForcing_density,sourceNativeGaugeCurrentLinear_complex] at generated
  change HasDerivAt _ (sourceMovingGaugeCurrentLinear 0
    (actualMovingPairPoint 0 leftMomentum rightMomentum left right) (sourceMovingInitialDirection constraint)).re _ at generated
  have real:=congrArg Complex.re (sourceMovingInitialCurrent_original leftMomentum rightMomentum left right constraint)
  norm_num [Complex.mul_re] at real
  convert generated using 1; linarith

private def initialDirectionDensity (point : BasePoint) (field : StageNineContinuumPointField)
    (direction : Fin 4→DiracExteriorMatterCarrier) : ℝ :=
  matterCovariantDerivativeFirstVariationDensity positiveSmoothUnifiedSource 0 point field direction

private theorem initialKinetic_affine (point : BasePoint) (field : StageNineContinuumPointField)
    (direction : Fin 4→DiracExteriorMatterCarrier) (parameter : ℝ) :
    generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 point
      (withP286GaugeConnectionJets field (p286CurvatureCoordinate field) field.scalarCovariantDerivative
        (field.matterCovariantDerivative+parameter • direction))=
      generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 point field+
        parameter*(generatedVolumeDensity field*initialDirectionDensity point field direction) := by
  change generatedVolumeDensity field*
    (matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
      (matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point field
        (field.matterCovariantDerivative+parameter • direction))).re=
    generatedVolumeDensity field*
      (matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
        (matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point field field.matterCovariantDerivative)).re+_
  rw [matterCovariantDerivativeVariationVector_add,map_add,Complex.add_re]
  have scaled : (matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
      (matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point field (parameter • direction))).re=
      parameter*initialDirectionDensity point field direction := by
    rw [matterCovariantDerivativeVariationVector_real_smul]
    change (matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
      ((parameter:ℂ) • matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point field direction)).re=_
    rw [map_smul]
    simp only [smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rfl
  rw [scaled]
  ring


def sourceMovingInitialQuadratureConfiguration (part : Fin 2) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) : StageNineHolonomicConfiguration :=
  {actualMovingPairConfiguration leftMomentum rightMomentum left right with
    matter:=fun point=>sourceCurrentPhase part •
      (actualMovingPairConfiguration leftMomentum rightMomentum left right).matter point}

def sourceMovingInitialQuadraturePoint (part : Fin 2) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) : StageNineContinuumPointField :=
  toContinuumPointField (sourceMovingInitialQuadratureConfiguration part leftMomentum rightMomentum left right) 0

private theorem initialGaugeCurrent_expression (field : StageNineContinuumPointField) (force : Field289) :
    sourceNativeGaugeCurrentComplex 0 field force=
      (generatedVolumeDensity field:ℂ)*field.conjugateMatter
        (Complex.I • ∑ mu : Fin 4,diracMatrixMatterAction
          (inverseCoframeDiracGamma {coframe:=field.coframe,derivative:=0} mu)
          (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (fieldGauge force mu))) field.matter)) := by
  unfold sourceNativeGaugeCurrentComplex matterGaugeConnectionVariationVector matterGaugeKineticSum
  simp only [sourceGaugeMatterDirection,matterDualFrameRelative_zeroChart,matterDerivativeFrameRelative_zeroChart]

private theorem initialQuadrature_complex (part : Fin 2) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (force : Field289) :
    sourceNativeGaugeCurrentComplex 0 (sourceMovingInitialQuadraturePoint part leftMomentum rightMomentum left right) force=
      sourceCurrentPhase part*sourceNativeGaugeCurrentComplex 0 (actualMovingPairPoint 0 leftMomentum rightMomentum left right) force := by
  have volume : generatedVolumeDensity (sourceMovingInitialQuadraturePoint part leftMomentum rightMomentum left right)=
      generatedVolumeDensity (actualMovingPairPoint 0 leftMomentum rightMomentum left right) := rfl
  have frame : (sourceMovingInitialQuadraturePoint part leftMomentum rightMomentum left right).coframe=
      (actualMovingPairPoint 0 leftMomentum rightMomentum left right).coframe := rfl
  have matter : (sourceMovingInitialQuadraturePoint part leftMomentum rightMomentum left right).matter=
      sourceCurrentPhase part • (actualMovingPairPoint 0 leftMomentum rightMomentum left right).matter := rfl
  have dual : (sourceMovingInitialQuadraturePoint part leftMomentum rightMomentum left right).conjugateMatter=
      (actualMovingPairPoint 0 leftMomentum rightMomentum left right).conjugateMatter := rfl
  rw [initialGaugeCurrent_expression,initialGaugeCurrent_expression,volume,frame,matter,dual]
  simp only [map_smul]
  rw [←Finset.smul_sum,map_smul]
  simp only [smul_eq_mul]
  ring

def sourceMovingInitialQuadratureCurrent (part : Fin 2) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (constraint : Fin 9) : ℝ :=
  (1/2:ℝ)*sourceNativeGaugeCurrentLinear 0
    (sourceMovingInitialQuadraturePoint part leftMomentum rightMomentum left right)
    (sourceMovingInitialDirection constraint)

theorem sourceMovingInitialQuadratureCurrent_generated (part : Fin 2) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (constraint : Fin 9) :
    sourceMovingInitialQuadratureCurrent part leftMomentum rightMomentum left right constraint=
      if part=0 then (sourceMovingInitialCurrent leftMomentum rightMomentum left right constraint).re
      else (sourceMovingInitialCurrent leftMomentum rightMomentum left right constraint).im := by
  unfold sourceMovingInitialQuadratureCurrent
  rw [sourceNativeGaugeCurrentLinear_complex,initialQuadrature_complex,sourceMovingInitialCurrent_original]
  change (1/2:ℝ)*(sourceCurrentPhase part*sourceMovingGaugeCurrentLinear 0
    (actualMovingPairPoint 0 leftMomentum rightMomentum left right) (sourceMovingInitialDirection constraint)).re=_
  fin_cases part <;> norm_num [sourceCurrentPhase,Complex.mul_re,Complex.mul_im]

def sourceMovingInitialQuadratureCurve (part : Fin 2) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (constraint : Fin 9) (parameter : ℝ) : ℝ :=
  let field:=sourceMovingInitialQuadraturePoint part leftMomentum rightMomentum left right
  generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 0
    (withP286GaugeConnectionJets field (p286CurvatureCoordinate field) field.scalarCovariantDerivative
      (field.matterCovariantDerivative+parameter • sourceGaugeMatterDirection field (sourceMovingInitialDirection constraint)))

theorem sourceMovingInitialQuadratureCurve_generated (part : Fin 2) (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (constraint : Fin 9) (parameter : ℝ) :
    HasDerivAt (sourceMovingInitialQuadratureCurve part leftMomentum rightMomentum left right constraint)
      (2*sourceMovingInitialQuadratureCurrent part leftMomentum rightMomentum left right constraint) parameter := by
  have affine (r : ℝ) : sourceMovingInitialQuadratureCurve part leftMomentum rightMomentum left right constraint r=
      generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 0
        (sourceMovingInitialQuadraturePoint part leftMomentum rightMomentum left right)+
      r*sourceNativeGaugeCurrentLinear 0 (sourceMovingInitialQuadraturePoint part leftMomentum rightMomentum left right)
        (sourceMovingInitialDirection constraint) :=
    initialKinetic_affine 0 _ _ _
  have derivative:=((hasDerivAt_id parameter).mul_const
    (sourceNativeGaugeCurrentLinear 0 (sourceMovingInitialQuadraturePoint part leftMomentum rightMomentum left right)
      (sourceMovingInitialDirection constraint))).const_add
        (generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 0
          (sourceMovingInitialQuadraturePoint part leftMomentum rightMomentum left right))
  convert! derivative using 1
  · exact funext affine
  · unfold sourceMovingInitialQuadratureCurrent
    ring

theorem sourceMovingInitialCovector_supported (leftMomentum rightMomentum : Fin 3→ℝ)
    (left right : RestStateIndex) (field : Fin 289) (outside : field.val<112 ∨ 115 ≤ field.val) :
    sourceMovingInitialCovector leftMomentum rightMomentum left right field=0 := by
  unfold sourceMovingInitialCovector
  split_ifs with inside
  · apply initialCurrent_outside
    dsimp
    omega
  · rfl

theorem sourceMovingPhysicalDressed_initial (q : PreparationVacuumPhysicalFeedback.PhysicalResponsePoint)
    (leftMomentum rightMomentum : Fin 3→ℝ) (left right : RestStateIndex)
    (frequency : PreparationVacuumCurrentConstrainedInverse.sourceCurrentRegularDomain
      (PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalMediumPoint q leftMomentum rightMomentum)
      (PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalClock leftMomentum rightMomentum left right)) :
    let readClock:=frequency.val.val.val
    let p:=sourceMovingReadMomentum leftMomentum rightMomentum readClock
    let returned:=PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalDrivenField
      q leftMomentum rightMomentum left right frequency
    let feedback:=PreparationVacuumCurrentNativeLaplaceBridge.sourceLaplaceCurrent
      (PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalMediumPoint q leftMomentum rightMomentum)
      (PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalClock leftMomentum rightMomentum left right)
      readClock returned+
      PreparationVacuumCurrentNativeLaplaceBridge.sourceLaplaceInitial
      (PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalMediumPoint q leftMomentum rightMomentum)
      (PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalClock leftMomentum rightMomentum left right)
      readClock returned
    nativeFourierHessian nativeHessian p *ᵥ returned+
        originalRowLift p *ᵥ sourceMovingInitialCovector leftMomentum rightMomentum left right=
      PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalCurrentHalf
        leftMomentum rightMomentum left right readClock+feedback-
      originalRowLift p *ᵥ sourceCompatibility p feedback := by
  let p:=sourceMovingReadMomentum leftMomentum rightMomentum frequency.val.val.val
  let external:=PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalCurrentHalf
    leftMomentum rightMomentum left right frequency.val.val.val
  let returned:=PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalDrivenField
    q leftMomentum rightMomentum left right frequency
  let feedback:=PreparationVacuumCurrentNativeLaplaceBridge.sourceLaplaceCurrent
    (PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalMediumPoint q leftMomentum rightMomentum)
    (PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalClock leftMomentum rightMomentum left right)
    frequency.val.val.val returned+
    PreparationVacuumCurrentNativeLaplaceBridge.sourceLaplaceInitial
    (PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalMediumPoint q leftMomentum rightMomentum)
    (PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalClock leftMomentum rightMomentum left right)
    frequency.val.val.val returned
  change nativeFourierHessian nativeHessian p *ᵥ returned+originalRowLift p *ᵥ
    sourceMovingInitialCovector leftMomentum rightMomentum left right=
    external+feedback-originalRowLift p *ᵥ sourceCompatibility p feedback
  have native : nativeFourierHessian nativeHessian p *ᵥ returned=
      external+feedback-originalRowLift p *ᵥ sourceCompatibility p (external+feedback) := by
    have generated:=PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalDrivenField_native
      q leftMomentum rightMomentum left right frequency
    simpa only [p,external,returned,feedback,sourceMovingReadMomentum,
      PreparationVacuumCurrentConstrainedInverse.sourceDressedSource,
      PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalDrivenField,add_assoc]
      using generated
  have positive:=PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalFrequency_positive
    q leftMomentum rightMomentum left right frequency
  have compatibility : sourceCompatibility p (external+feedback)=sourceCompatibility p external+sourceCompatibility p feedback := by
    unfold sourceCompatibility
    rw [Matrix.mulVec_add,Matrix.mulVec_add]
  have initial : sourceCompatibility p external=sourceMovingInitialCovector leftMomentum rightMomentum left right :=
    sourceMovingPhysicalHalf_initial leftMomentum rightMomentum left right _ positive
  rw [compatibility,initial,Matrix.mulVec_add] at native
  rw [native]
  abel

end LowEnergy.PreparationVacuumElectromagneticIdentity
