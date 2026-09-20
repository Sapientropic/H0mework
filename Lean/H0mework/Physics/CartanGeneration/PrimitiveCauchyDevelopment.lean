import H0mework.Physics.CartanGeneration.LocalActualLift

/-!
# S9-C3h128: current Cartan actual germ assembled into a whole Cauchy development

C3h127 generates one current-state torsion-free Cartan actual germ at every
spatial contact.  This module restricts each matching actual germ to the
canonical physical-time line and assembles the results into a whole-slice
primitive development:

```text
source + initial primitive state
→ generated current primitive U(anchor)
→ at every space contact: current Cartan actual germ
→ canonical Cauchy restriction at relative time
→ whole-slice primitive U_Cartan(relative time)
→ later equation/residual acceptance.
```

All primitive fields come from the same local actual at each contact.  The
coframe is no longer frozen: its derivative replays the current-state Cartan
velocity.  The gravity auxiliary is derived pointwise as `B = II⁺(e)` at
every relative time.

This remains the torsion-free sector.  It is an explicit current-state local
development, not an exact nonlinear flow, semigroup, global solution, or
nonzero-spin Einstein--Cartan producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyDevelopment

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineEnrichedProofFreeSource
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedCurrentTorsionFreeCartanLocalActualLift
open StageNineSourceActionGeneratedJointPrimitiveCauchyPath
open StageNineSourceActionGeneratedJointPrimitiveCauchyUpdate
open StageNineSourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
open StageNineStateDependentCartanCoframeFirstJetLocalActualLift

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

abbrev sourceActionGeneratedCurrentPrimitiveCauchyState
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState) :
    StageNineCauchyState :=
  (sourceActionGeneratedPrimitiveCanonicalCurrent
    source anchor state).primitive

/-- Canonical Cauchy restriction of the current-state Cartan actual germ at
one matching spatial contact. -/
def sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyPath
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (relativeTime : ℝ) :
    StageNineCauchyState :=
  canonicalCauchyRestriction relativeTime
    (sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift
      source anchor state space)

/-- Pointwise assembly of all matching current-state Cartan actual paths. -/
def sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
    (source : SmoothUnifiedSource)
    (anchor relativeTime : ℝ)
    (state : StageNineCauchyState) :
    StageNineCauchyState where
  coframe := fun space =>
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyPath
      source anchor state space relativeTime).coframe 0
  gravityConnection := fun space =>
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyPath
      source anchor state space relativeTime).gravityConnection 0
  gravityAuxiliary := fun space =>
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyPath
      source anchor state space relativeTime).gravityAuxiliary 0
  gravitySimplicityMultiplier := fun space =>
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyPath
      source anchor state space relativeTime).gravitySimplicityMultiplier 0
  gaugeConnection := fun space =>
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyPath
      source anchor state space relativeTime).gaugeConnection 0
  gaugeAuxiliary := fun space =>
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyPath
      source anchor state space relativeTime).gaugeAuxiliary 0
  scalar := fun space =>
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyPath
      source anchor state space relativeTime).scalar 0
  scalarVelocity := fun space =>
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyPath
      source anchor state space relativeTime).scalarVelocity 0
  matter := fun space =>
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyPath
      source anchor state space relativeTime).matter 0
  conjugateMatter := fun space =>
    (sourceActionGeneratedJointPrimitiveCauchyPath source
      (sourceActionGeneratedCurrentPrimitiveCauchyState
        source anchor state)
      space relativeTime).conjugateMatter 0

private theorem canonicalCauchySlicePoint_zeroSpace_eq_timeLine
    (time : ℝ) :
    canonicalCauchySlicePoint time 0 =
      time • coordinateDirection canonicalLorentzianTimeDirection := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, coordinateDirection,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 0 = 0 := by
  rw [canonicalCauchySlicePoint_zeroSpace_eq_timeLine]
  simp

private theorem deriv_along_canonicalCauchyOrigin
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (field : BasePoint → V)
    (differentiable : DifferentiableAt ℝ field 0) :
    deriv
        (fun time : ℝ =>
          field (canonicalCauchySlicePoint time 0))
        0 =
      fieldDirectionalDerivative field 0
        canonicalLorentzianTimeDirection := by
  let line := fun time : ℝ =>
    time • coordinateDirection canonicalLorentzianTimeDirection
  have lineDerivative :
      HasDerivAt line
        (coordinateDirection canonicalLorentzianTimeDirection) 0 := by
    simpa [line] using
      (hasDerivAt_id (𝕜 := ℝ) 0).smul_const
        (coordinateDirection canonicalLorentzianTimeDirection)
  have outerDerivative :
      HasFDerivAt field (fderiv ℝ field 0) (line 0) := by
    simpa [line] using differentiable.hasFDerivAt
  have composed :=
    outerDerivative.comp_hasDerivAt 0 lineDerivative
  unfold fieldDirectionalDerivative
  rw [show
    (fun time : ℝ =>
      field (canonicalCauchySlicePoint time 0)) =
        field ∘ line by
    funext time
    simp only [Function.comp_apply, line,
      canonicalCauchySlicePoint_zeroSpace_eq_timeLine]]
  exact composed.deriv

/-! ## Current identity -/

theorem sourceActionGeneratedCurrentPrimitiveCauchyState_actionPrepared
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState) :
    sourceActionGeneratedJointPrimitiveActionInitialState
        (sourceActionGeneratedCurrentPrimitiveCauchyState
          source anchor state) =
      sourceActionGeneratedCurrentPrimitiveCauchyState
        source anchor state := by
  exact sourceActionGeneratedJointPrimitiveCauchyUpdate_actionPrepared
    source anchor state

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyPath_initialCoframe
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyPath
      source anchor state space 0).coframe 0 =
      (sourceActionGeneratedCurrentPrimitiveCauchyState
        source anchor state).coframe space := by
  change
    (sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift
      source anchor state space).coframe
        (canonicalCauchySlicePoint 0 0) = _
  rw [canonicalCauchySlicePoint_zero_zero]
  exact
    sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift_initialCoframe
      source anchor state space

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyPath_initialGravityAuxiliary
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyPath
      source anchor state space 0).gravityAuxiliary 0 =
      actionGeneratedGravityAuxiliary
        (sourceActionGeneratedCurrentPrimitiveCauchyState
          source anchor state)
        space := by
  change
    (sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift
      source anchor state space).gravityAuxiliary
        (canonicalCauchySlicePoint 0 0) = _
  rw [canonicalCauchySlicePoint_zero_zero]
  rw [
    sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift_gravityAuxiliary_generated]
  change
    physicalIIPlusBivector
        ((sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift
          source anchor state space).coframe 0) =
      _
  rw [
    sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift_initialCoframe]
  rfl

theorem sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_zero
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState) :
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
        source anchor 0 state =
      sourceActionGeneratedCurrentPrimitiveCauchyState
        source anchor state := by
  let current :=
    sourceActionGeneratedCurrentPrimitiveCauchyState source anchor state
  have sameZero :
      sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
          source anchor 0 state =
        sourceActionGeneratedJointPrimitiveCauchyUpdate
          source 0 current := by
    apply StageNineCauchyState.ext
    · funext space
      change
        (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyPath
          source anchor state space 0).coframe 0 =
          (sourceActionGeneratedJointPrimitiveCauchyPath
            source current space 0).coframe 0
      rw [
        sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyPath_initialCoframe,
        sourceActionGeneratedJointPrimitiveCauchyPath_initialCoframe]
    · rfl
    · funext space
      change
        (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyPath
          source anchor state space 0).gravityAuxiliary 0 =
          (sourceActionGeneratedJointPrimitiveCauchyPath
            source current space 0).gravityAuxiliary 0
      rw [
        sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyPath_initialGravityAuxiliary,
        sourceActionGeneratedJointPrimitiveCauchyPath_initialGravityAuxiliary]
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  calc
    _ = sourceActionGeneratedJointPrimitiveCauchyUpdate
          source 0 current := sameZero
    _ = sourceActionGeneratedJointPrimitiveActionInitialState current :=
      sourceActionGeneratedJointPrimitiveCauchyUpdate_zero source current
    _ = current :=
      sourceActionGeneratedCurrentPrimitiveCauchyState_actionPrepared
        source anchor state

/-! ## Generated coframe and derived auxiliary laws -/

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_coframeTangent
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (internal : LorentzianIndex) :
    deriv
        (fun relativeTime : ℝ =>
          (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
            source anchor relativeTime state).coframe
              space internal direction.succ)
        0 =
      cartanTorsionFreeSpatialCoframeVelocity
        (sourceActionGeneratedCurrentPrimitiveCauchyState
          source anchor state)
        space direction internal := by
  let actual :=
    sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift
      source anchor state space
  let field : BasePoint → ℝ :=
    fun point => actual.coframe point internal direction.succ
  have fieldDifferentiable : DifferentiableAt ℝ field 0 := by
    exact
      ((sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift_realizes
        source anchor state space).smooth.1 internal direction.succ
        |>.differentiable (by simp)).differentiableAt
  calc
    _ =
        deriv
          (fun relativeTime : ℝ =>
            field (canonicalCauchySlicePoint relativeTime 0))
          0 := rfl
    _ =
        fieldDirectionalDerivative field 0
          canonicalLorentzianTimeDirection :=
      deriv_along_canonicalCauchyOrigin field fieldDifferentiable
    _ =
        cartanTorsionFreeSpatialCoframeVelocity
          (sourceActionGeneratedCurrentPrimitiveCauchyState
            source anchor state)
          space direction internal := by
      exact
        sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift_replays_velocity
          source anchor state space direction internal

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_gravityAuxiliary_generated
    (source : SmoothUnifiedSource)
    (anchor relativeTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
      source anchor relativeTime state).gravityAuxiliary space =
      physicalIIPlusBivector
        ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
          source anchor relativeTime state).coframe space) := by
  rfl

/-- Bundled whole-slice producer law.  The residual layer is absent from the
mouth and may only inspect this generated development downstream. -/
structure StageNineCurrentTorsionFreeCartanPrimitiveCauchyDevelopmentLaw
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState)
    (development : ℝ → StageNineCauchyState) : Prop where
  generated :
    development =
      fun relativeTime =>
        sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
          source anchor relativeTime state
  currentInitial :
    development 0 =
      sourceActionGeneratedCurrentPrimitiveCauchyState
        source anchor state
  localActualGenerated :
    ∀ space,
      SourceActionCartanCoframeFirstJetLocalActualLaw
        source
        (sourceActionGeneratedCurrentPrimitiveCauchyState
          source anchor state)
        space
        (sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift
          source anchor state space)
  coframeTangent :
    ∀ space direction internal,
      deriv
          (fun relativeTime : ℝ =>
            (development relativeTime).coframe
              space internal direction.succ)
          0 =
        cartanTorsionFreeSpatialCoframeVelocity
          (sourceActionGeneratedCurrentPrimitiveCauchyState
            source anchor state)
          space direction internal
  gravityAuxiliaryGenerated :
    ∀ relativeTime space,
      (development relativeTime).gravityAuxiliary space =
        physicalIIPlusBivector
          ((development relativeTime).coframe space)

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyDevelopment_realizes
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState) :
    StageNineCurrentTorsionFreeCartanPrimitiveCauchyDevelopmentLaw
      source anchor state
      (fun relativeTime =>
        sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
          source anchor relativeTime state) := by
  exact
    { generated := rfl
      currentInitial :=
        sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_zero
          source anchor state
      localActualGenerated :=
        sourceActionGeneratedCurrentTorsionFreeCartanCoframeLocalActualLift_realizes
          source anchor state
      coframeTangent :=
        sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_coframeTangent
          source anchor state
      gravityAuxiliaryGenerated :=
        fun relativeTime space =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_gravityAuxiliary_generated
            source anchor relativeTime state space }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyDevelopment
