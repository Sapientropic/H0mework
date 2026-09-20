import H0mework.Physics.CurrentAction.LorentzActualFirstJetLift
import H0mework.Physics.Exterior.JointActionLocalActualLift

/-!
# Stage-9 post-Lorentz adjoint Cauchy update

The canonical Lorentz actual first-jet lift is generated before this module
does any adjoint repair.  Its physical `t = 0` restriction is then used as the
single final Cauchy state.  At every spatial point, the existing joint action
grammar generates a matching local actual from that state, and the adjoint
time path is read from the conjugate field of that actual:

```text
(source, current, contact)
-> canonical Lorentz actual first-jet lift
-> its exact final Cauchy state
-> matching action-generated local actual at every spatial point
-> unique adjoint action velocity
-> whole-slice conjugate-matter Cauchy update.
```

The update freezes the other nine primitive Cauchy fields.  It accepts no
residual, endpoint, coefficient, branch, event, scheduler, equation receipt,
or target jet.  The unit-time zero fiber is faithful to the generated adjoint
velocity.  This is a frozen-input local Cauchy response, not an independent
Euler--Lagrange closure, a nonlinear restart law, or global source-time
evolution.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCurrentCanonicalFullActionLorentzAdjointCauchyUpdate

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineCurrentCanonicalFullActionLorentzActualFirstJetLift
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineJointActionCanonicalPhasePathLaw
open StageNineJointActionLocalActualLift
open StageNineP286ActionCauchySplit

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

/-! ## Actual-first dependency graph -/

/-- The final Cauchy state is the physical zero-time restriction of the
already generated Lorentz actual. -/
def currentCanonicalFullActionLorentzFinalCauchyState
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) : StageNineCauchyState :=
  canonicalCauchyRestriction 0
    (currentCanonicalFullActionLorentzActualFirstJetLift source current space)

/-- The unique adjoint time velocity generated from the final state at every
spatial point. -/
def currentCanonicalFullActionLorentzAdjointVelocity
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineSpatialPoint → Module.Dual ℂ DiracExteriorMatterCarrier :=
  let finalState :=
    currentCanonicalFullActionLorentzFinalCauchyState source current space
  fun localSpace =>
    actionGeneratedConjugateMatterTimeDerivative finalState localSpace

/-- Regenerate one matching local action actual from the final Cauchy state.
The local spatial point is explicit contact data, not a branch selector. -/
def currentCanonicalFullActionLorentzAdjointLocalActual
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space localSpace : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedJointLocalActualLift source
    (currentCanonicalFullActionLorentzFinalCauchyState
      source current space)
    localSpace

/-- Physical-time restriction of the matching local action actual. -/
def currentCanonicalFullActionLorentzAdjointLocalPath
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space localSpace : StageNineSpatialPoint)
    (time : ℝ) : StageNineCauchyState :=
  canonicalCauchyRestriction time
    (currentCanonicalFullActionLorentzAdjointLocalActual
      source current space localSpace)

/-- Assemble the generated adjoint paths into one whole-slice update while
retaining every non-adjoint field of the final Lorentz state. -/
def currentCanonicalFullActionLorentzAdjointCauchyUpdate
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (time : ℝ) : StageNineCauchyState :=
  let finalState :=
    currentCanonicalFullActionLorentzFinalCauchyState source current space
  { finalState with
    conjugateMatter := fun localSpace =>
      (currentCanonicalFullActionLorentzAdjointLocalPath
        source current space localSpace time).conjugateMatter 0 }

private theorem canonicalCauchySlicePoint_zeroSpace_eq_timeLine
    (time : ℝ) :
    canonicalCauchySlicePoint time 0 =
      time • coordinateDirection canonicalLorentzianTimeDirection := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, coordinateDirection,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

/-! ## Generated affine response and regularity -/

theorem currentCanonicalFullActionLorentzAdjointCauchyUpdate_conjugateMatter_apply
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space localSpace : StageNineSpatialPoint)
    (time : ℝ)
    (matter : DiracExteriorMatterCarrier) :
    (currentCanonicalFullActionLorentzAdjointCauchyUpdate
        source current space time).conjugateMatter localSpace matter =
      (currentCanonicalFullActionLorentzFinalCauchyState
          source current space).conjugateMatter localSpace matter +
        time •
          currentCanonicalFullActionLorentzAdjointVelocity
            source current space localSpace matter := by
  simp only [currentCanonicalFullActionLorentzAdjointCauchyUpdate,
    currentCanonicalFullActionLorentzAdjointLocalPath,
    canonicalCauchyRestriction]
  change
    actionGeneratedConjugateMatterLocalField
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space)
        localSpace (canonicalCauchySlicePoint time 0) matter =
      _
  rw [actionGeneratedConjugateMatterLocalField_apply,
    canonicalCauchySlicePoint_zeroSpace_eq_timeLine, map_smul,
    actionGeneratedConjugateMatterLocalEvaluationIncrement_coordinateDirection]
  rfl

theorem currentCanonicalFullActionLorentzAdjointLocalActual_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space localSpace : StageNineSpatialPoint) :
    (currentCanonicalFullActionLorentzAdjointLocalActual
      source current space localSpace).Smooth := by
  exact sourceActionGeneratedJointLocalActualLift_smooth source
    (currentCanonicalFullActionLorentzFinalCauchyState
      source current space)
    localSpace

theorem currentCanonicalFullActionLorentzAdjointCauchyUpdate_zero
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    currentCanonicalFullActionLorentzAdjointCauchyUpdate
        source current space 0 =
      currentCanonicalFullActionLorentzFinalCauchyState
        source current space := by
  apply StageNineCauchyState.ext <;> try rfl
  funext localSpace
  apply LinearMap.ext
  intro matter
  rw [currentCanonicalFullActionLorentzAdjointCauchyUpdate_conjugateMatter_apply]
  simp

/-- The repair opens no new epoch for the other primitive fields. -/
theorem currentCanonicalFullActionLorentzAdjointCauchyUpdate_retainsFinalState
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (time : ℝ) :
    (currentCanonicalFullActionLorentzAdjointCauchyUpdate
          source current space time).coframe =
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space).coframe ∧
      (currentCanonicalFullActionLorentzAdjointCauchyUpdate
          source current space time).gravityConnection =
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space).gravityConnection ∧
      (currentCanonicalFullActionLorentzAdjointCauchyUpdate
          source current space time).gravityAuxiliary =
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space).gravityAuxiliary ∧
      (currentCanonicalFullActionLorentzAdjointCauchyUpdate
          source current space time).gravitySimplicityMultiplier =
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space).gravitySimplicityMultiplier ∧
      (currentCanonicalFullActionLorentzAdjointCauchyUpdate
          source current space time).gaugeConnection =
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space).gaugeConnection ∧
      (currentCanonicalFullActionLorentzAdjointCauchyUpdate
          source current space time).gaugeAuxiliary =
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space).gaugeAuxiliary ∧
      (currentCanonicalFullActionLorentzAdjointCauchyUpdate
          source current space time).scalar =
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space).scalar ∧
      (currentCanonicalFullActionLorentzAdjointCauchyUpdate
          source current space time).scalarVelocity =
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space).scalarVelocity ∧
      (currentCanonicalFullActionLorentzAdjointCauchyUpdate
          source current space time).matter =
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space).matter := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Branch-free action authority -/

theorem currentCanonicalFullActionLorentzAdjointVelocity_satisfies_actionLaw
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space localSpace : StageNineSpatialPoint) :
    IdentityCoframeConjugateMatterTimeActionLaw
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space)
        localSpace
        (currentCanonicalFullActionLorentzAdjointVelocity
          source current space localSpace) := by
  exact actionGeneratedConjugateMatterTimeDerivative_satisfies_actionLaw _ _

/-- The adjoint action law leaves no local or whole-slice branch choice. -/
theorem currentCanonicalFullActionLorentzAdjointVelocity_unique
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (candidate :
      StageNineSpatialPoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (candidateLaw : ∀ localSpace,
      IdentityCoframeConjugateMatterTimeActionLaw
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space)
        localSpace (candidate localSpace)) :
    candidate =
      currentCanonicalFullActionLorentzAdjointVelocity
        source current space := by
  funext localSpace
  exact identityCoframeConjugateMatterTimeActionLaw_unique
    (currentCanonicalFullActionLorentzFinalCauchyState
      source current space)
    localSpace _ _ (candidateLaw localSpace)
    (currentCanonicalFullActionLorentzAdjointVelocity_satisfies_actionLaw
      source current space localSpace)

theorem currentCanonicalFullActionLorentzAdjointCauchyUpdate_hasDerivAt
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space localSpace : StageNineSpatialPoint)
    (time : ℝ)
    (matter : DiracExteriorMatterCarrier) :
    HasDerivAt
      (fun candidate : ℝ =>
        (currentCanonicalFullActionLorentzAdjointCauchyUpdate
          source current space candidate).conjugateMatter localSpace matter)
      (currentCanonicalFullActionLorentzAdjointVelocity
        source current space localSpace matter)
      time := by
  rw [show
    (fun candidate : ℝ =>
      (currentCanonicalFullActionLorentzAdjointCauchyUpdate
        source current space candidate).conjugateMatter localSpace matter) =
      fun candidate : ℝ =>
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space).conjugateMatter localSpace matter +
          candidate •
            currentCanonicalFullActionLorentzAdjointVelocity
              source current space localSpace matter by
    funext candidate
    exact
      currentCanonicalFullActionLorentzAdjointCauchyUpdate_conjugateMatter_apply
        source current space localSpace candidate matter]
  exact hasDerivAt_const_add_time_smul _ _ time

/-- Equality of the unit and initial updates is equivalent to vanishing of
the complete generated adjoint velocity field. -/
theorem currentCanonicalFullActionLorentzAdjointCauchyUpdate_faithfulZeroFiber
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    currentCanonicalFullActionLorentzAdjointCauchyUpdate
          source current space 1 =
        currentCanonicalFullActionLorentzAdjointCauchyUpdate
          source current space 0 ↔
      currentCanonicalFullActionLorentzAdjointVelocity
          source current space =
        0 := by
  constructor
  · intro updateEqual
    funext localSpace
    apply LinearMap.ext
    intro matter
    have coordinateEqual := congrArg
      (fun state => state.conjugateMatter localSpace matter) updateEqual
    rw [
      currentCanonicalFullActionLorentzAdjointCauchyUpdate_conjugateMatter_apply,
      currentCanonicalFullActionLorentzAdjointCauchyUpdate_conjugateMatter_apply]
      at coordinateEqual
    simpa using coordinateEqual
  · intro velocityZero
    apply StageNineCauchyState.ext <;> try rfl
    funext localSpace
    apply LinearMap.ext
    intro matter
    rw [
      currentCanonicalFullActionLorentzAdjointCauchyUpdate_conjugateMatter_apply,
      currentCanonicalFullActionLorentzAdjointCauchyUpdate_conjugateMatter_apply,
      show
        currentCanonicalFullActionLorentzAdjointVelocity
            source current space localSpace = 0 by
          exact congrFun velocityZero localSpace]
    simp

/-! ## Bundled producer law -/

/-- The complete authority of the post-Lorentz adjoint update.  Its action
law fields are producer soundness, not independent equation closure. -/
structure StageNineCurrentCanonicalFullActionLorentzAdjointCauchyUpdateLaw
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (update : ℝ → StageNineCauchyState) : Prop where
  finalStateGenerated :
    currentCanonicalFullActionLorentzFinalCauchyState source current space =
      canonicalCauchyRestriction 0
        (currentCanonicalFullActionLorentzActualFirstJetLift
          source current space)
  localActualGenerated : ∀ localSpace,
    currentCanonicalFullActionLorentzAdjointLocalActual
        source current space localSpace =
      sourceActionGeneratedJointLocalActualLift source
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space)
        localSpace
  localActualSmooth : ∀ localSpace,
    (currentCanonicalFullActionLorentzAdjointLocalActual
      source current space localSpace).Smooth
  localPathGenerated : ∀ localSpace time,
    currentCanonicalFullActionLorentzAdjointLocalPath
        source current space localSpace time =
      canonicalCauchyRestriction time
        (currentCanonicalFullActionLorentzAdjointLocalActual
          source current space localSpace)
  updateGenerated :
    update =
      currentCanonicalFullActionLorentzAdjointCauchyUpdate
        source current space
  retainsFinalState : ∀ time,
    (update time).coframe =
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space).coframe ∧
      (update time).gravityConnection =
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space).gravityConnection ∧
      (update time).gravityAuxiliary =
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space).gravityAuxiliary ∧
      (update time).gravitySimplicityMultiplier =
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space).gravitySimplicityMultiplier ∧
      (update time).gaugeConnection =
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space).gaugeConnection ∧
      (update time).gaugeAuxiliary =
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space).gaugeAuxiliary ∧
      (update time).scalar =
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space).scalar ∧
      (update time).scalarVelocity =
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space).scalarVelocity ∧
      (update time).matter =
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space).matter
  actionLaw : ∀ localSpace,
    IdentityCoframeConjugateMatterTimeActionLaw
      (currentCanonicalFullActionLorentzFinalCauchyState
        source current space)
      localSpace
      (currentCanonicalFullActionLorentzAdjointVelocity
        source current space localSpace)
  actionVelocityUnique : ∀ candidate :
      StageNineSpatialPoint → Module.Dual ℂ DiracExteriorMatterCarrier,
    (∀ localSpace,
      IdentityCoframeConjugateMatterTimeActionLaw
        (currentCanonicalFullActionLorentzFinalCauchyState
          source current space)
        localSpace (candidate localSpace)) →
      candidate =
        currentCanonicalFullActionLorentzAdjointVelocity
          source current space
  initial :
    update 0 =
      currentCanonicalFullActionLorentzFinalCauchyState
        source current space
  conjugateMatterDerivative : ∀ time localSpace matter,
    HasDerivAt
      (fun candidate : ℝ =>
        (update candidate).conjugateMatter localSpace matter)
      (currentCanonicalFullActionLorentzAdjointVelocity
        source current space localSpace matter)
      time
  faithfulZeroFiber :
    update 1 = update 0 ↔
      currentCanonicalFullActionLorentzAdjointVelocity
          source current space =
        0

theorem currentCanonicalFullActionLorentzAdjointCauchyUpdate_realizes
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineCurrentCanonicalFullActionLorentzAdjointCauchyUpdateLaw
      source current space
      (currentCanonicalFullActionLorentzAdjointCauchyUpdate
        source current space) := by
  exact
    { finalStateGenerated := rfl
      localActualGenerated := fun _ => rfl
      localActualSmooth :=
        currentCanonicalFullActionLorentzAdjointLocalActual_smooth
          source current space
      localPathGenerated := fun _ _ => rfl
      updateGenerated := rfl
      retainsFinalState :=
        currentCanonicalFullActionLorentzAdjointCauchyUpdate_retainsFinalState
          source current space
      actionLaw :=
        currentCanonicalFullActionLorentzAdjointVelocity_satisfies_actionLaw
          source current space
      actionVelocityUnique :=
        currentCanonicalFullActionLorentzAdjointVelocity_unique
          source current space
      initial :=
        currentCanonicalFullActionLorentzAdjointCauchyUpdate_zero
          source current space
      conjugateMatterDerivative :=
        fun time localSpace matter =>
          currentCanonicalFullActionLorentzAdjointCauchyUpdate_hasDerivAt
            source current space localSpace time matter
      faithfulZeroFiber :=
        currentCanonicalFullActionLorentzAdjointCauchyUpdate_faithfulZeroFiber
          source current space }

end

end
  SaturationMonoid.PhysicsCore.StageNineCurrentCanonicalFullActionLorentzAdjointCauchyUpdate
