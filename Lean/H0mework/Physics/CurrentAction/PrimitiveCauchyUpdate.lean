import H0mework.Physics.Exterior.CanonicalLocalFullActionResponseOperator
import H0mework.Physics.Cauchy.CurrentFullSynchronizedCompleteP286PrimitiveCauchyUpdate

/-!
# Stage-9 current canonical full-action primitive Cauchy update

This module lifts the branch-free canonical local full-action operator to every
spatial contact of an arbitrary current Cauchy state:

```text
(proof-free source, current Cauchy state, spatial contact)
→ source/action-generated linear-Plebanski base actual
→ full synchronized gravity/matter response
→ complete P286 response
→ temporal primal-matter first-germ response
→ complete primal-matter first-germ response
→ canonical local path
→ one whole-slice primitive update.
```

The source and current actual generate the response before any residual is
read.  The two matter residuals are internal action readouts and retain their
stage-relative faithful zero fibers.  The P286 auxiliary time jet remains the
unique BF-Legendre response of the same full intermediate actual because both
matter legs preserve every non-matter field.

No residual, endpoint, response coefficient, event, branch, scheduler,
stationarity receipt, or equation certificate is accepted by a constructor.
In particular, this instantaneous contact-wise update does not infer an event
from current support and is not an autonomous or global source-time evolution.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate

open StageNineCanonicalCauchyState
open StageNineCanonicalLocalFullActionResponseOperator
open StageNineCurrentFullSynchronizedCompleteP286PrimitiveCauchyUpdate
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineMatterActionCompleteFirstGermResponse
open StageNineMatterActionTemporalFirstGermResponse
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance currentCanonicalFullActionP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance currentCanonicalFullActionP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance currentCanonicalFullActionP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Contact-local dependency graph -/

/-- The source/action-generated base actual at one spatial contact. -/
def currentCanonicalFullActionBaseActual
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  currentFullSynchronizedCompleteP286BaseActual source current space

/-- The full synchronized and complete-P286 response at the same contact. -/
def currentCanonicalFullActionP286Actual
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  canonicalLocalFullActionP286Actual source
    (currentCanonicalFullActionBaseActual source current space)

/-- The temporal primal-matter response generated after the P286 leg. -/
def currentCanonicalFullActionTemporalMatterActual
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  canonicalLocalFullActionTemporalMatterActual source
    (currentCanonicalFullActionBaseActual source current space)

/-- The complete branch-free canonical response at one generated contact. -/
def currentCanonicalFullActionActual
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  canonicalLocalFullActionResponseOperator source
    (currentCanonicalFullActionBaseActual source current space)

@[simp] theorem currentCanonicalFullActionP286Actual_eq_previous
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    currentCanonicalFullActionP286Actual source current space =
      currentFullSynchronizedCompleteP286Actual source current space :=
  rfl

theorem currentCanonicalFullActionTemporalMatterActual_faithfulZeroFiber
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    currentCanonicalFullActionTemporalMatterActual source current space =
          currentCanonicalFullActionP286Actual source current space ↔
      matterTemporalDiracYukawaFirstGermResidual source
          (currentCanonicalFullActionP286Actual source current space) =
        0 := by
  exact canonicalLocalFullActionTemporalMatterActual_eq_p286_iff source
    (currentCanonicalFullActionBaseActual source current space)

theorem currentCanonicalFullActionActual_faithfulCompleteZeroFiber
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    currentCanonicalFullActionActual source current space =
          currentCanonicalFullActionTemporalMatterActual source current space ↔
      matterCompleteDiracYukawaFirstGermResidual source
          (currentCanonicalFullActionTemporalMatterActual source current space) =
        0 := by
  exact canonicalLocalFullActionResponseOperator_eq_temporal_iff source
    (currentCanonicalFullActionBaseActual source current space)

/-! ## Canonical local path and whole-slice update -/

/-- Canonical physical-time restriction of the complete generated actual. -/
def currentCanonicalFullActionLocalPath
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (time : ℝ) :
    StageNineCauchyState :=
  canonicalCauchyRestriction time
    (currentCanonicalFullActionActual source current space)

/-- Assemble the origin of every generated contact-local path into one slice. -/
def currentCanonicalFullActionPrimitiveCauchyUpdate
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (time : ℝ) :
    StageNineCauchyState where
  coframe := fun space =>
    (currentCanonicalFullActionLocalPath source current space time).coframe 0
  gravityConnection := fun space =>
    (currentCanonicalFullActionLocalPath source current space time).gravityConnection 0
  gravityAuxiliary := fun space =>
    (currentCanonicalFullActionLocalPath source current space time).gravityAuxiliary 0
  gravitySimplicityMultiplier := fun space =>
    (currentCanonicalFullActionLocalPath source current space time).gravitySimplicityMultiplier 0
  gaugeConnection := fun space =>
    (currentCanonicalFullActionLocalPath source current space time).gaugeConnection 0
  gaugeAuxiliary := fun space =>
    (currentCanonicalFullActionLocalPath source current space time).gaugeAuxiliary 0
  scalar := fun space =>
    (currentCanonicalFullActionLocalPath source current space time).scalar 0
  scalarVelocity := fun space =>
    (currentCanonicalFullActionLocalPath source current space time).scalarVelocity 0
  matter := fun space =>
    (currentCanonicalFullActionLocalPath source current space time).matter 0
  conjugateMatter := fun space =>
    (currentCanonicalFullActionLocalPath source current space time).conjugateMatter 0

/-- The zero response is generated by the same contact-local action graph.  It
is not identified with the caller's input state. -/
def currentCanonicalFullActionGeneratedZeroResponseState
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    StageNineCauchyState :=
  currentCanonicalFullActionPrimitiveCauchyUpdate source current 0

/-- The generated zero response reads its gravity multiplier from the same
contact-local actual that produced the response.  This projection keeps
downstream proofs from unfolding the whole Cauchy-state record. -/
@[simp] theorem
    currentCanonicalFullActionGeneratedZeroResponseState_gravitySimplicityMultiplier
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalFullActionGeneratedZeroResponseState source current
        |>.gravitySimplicityMultiplier space) =
      (currentCanonicalFullActionActual source current space
        |>.gravitySimplicityMultiplier 0) := by
  unfold currentCanonicalFullActionGeneratedZeroResponseState
    currentCanonicalFullActionPrimitiveCauchyUpdate
    currentCanonicalFullActionLocalPath
    canonicalCauchyRestriction
  rfl

@[simp] theorem currentCanonicalFullActionPrimitiveCauchyUpdate_zero
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    currentCanonicalFullActionPrimitiveCauchyUpdate source current 0 =
      currentCanonicalFullActionGeneratedZeroResponseState source current :=
  rfl

/-! ## Preserved P286 action jet -/

/-- Both matter first-germ responses preserve the complete P286 auxiliary
field, so the new whole-slice update has the same P286 auxiliary component as
the earlier complete-P286 update. -/
theorem currentCanonicalFullActionPrimitiveCauchyUpdate_gaugeAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (time : ℝ) :
    (currentCanonicalFullActionPrimitiveCauchyUpdate source current time).gaugeAuxiliary =
      (currentFullSynchronizedCompleteP286PrimitiveCauchyUpdate source current
        time).gaugeAuxiliary := by
  funext space
  rfl

/-- The P286 auxiliary time jet is still generated by the unique spatial
BF-Legendre response of the same full synchronized intermediate actual. -/
theorem currentCanonicalFullActionPrimitiveCauchyUpdate_p286Auxiliary_hasDerivAt
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (globalSpace : StageNineSpatialPoint)
    (pair : Fin 6)
    (time : ℝ) :
    HasDerivAt
      (fun candidate : ℝ =>
        p286CoordinateEquiv
          ((currentCanonicalFullActionPrimitiveCauchyUpdate source current
            candidate).gaugeAuxiliary globalSpace pair))
      (p286SpatialAuxiliaryVelocityEmbedding
        (currentP286SpatialAuxiliaryVelocity source
          (currentFullSynchronizedResponseActual source current globalSpace))
        pair)
      time := by
  simpa only [currentCanonicalFullActionPrimitiveCauchyUpdate_gaugeAuxiliary]
    using
      (currentFullSynchronizedCompleteP286PrimitiveCauchyUpdate_p286Auxiliary_hasDerivAt
        source current globalSpace pair time)

/-! ## Generic action-first authority -/

structure StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdateLaw
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (update : ℝ → StageNineCauchyState) : Prop where
  updateGenerated :
    update = currentCanonicalFullActionPrimitiveCauchyUpdate source current
  baseActualGenerated : ∀ space,
    currentCanonicalFullActionBaseActual source current space =
      currentFullSynchronizedCompleteP286BaseActual source current space
  p286ActualGenerated : ∀ space,
    currentCanonicalFullActionP286Actual source current space =
      canonicalLocalFullActionP286Actual source
        (currentCanonicalFullActionBaseActual source current space)
  temporalMatterActualGenerated : ∀ space,
    currentCanonicalFullActionTemporalMatterActual source current space =
      canonicalLocalFullActionTemporalMatterActual source
        (currentCanonicalFullActionBaseActual source current space)
  completeActualGenerated : ∀ space,
    currentCanonicalFullActionActual source current space =
      canonicalLocalFullActionResponseOperator source
        (currentCanonicalFullActionBaseActual source current space)
  localPathGenerated : ∀ space time,
    currentCanonicalFullActionLocalPath source current space time =
      canonicalCauchyRestriction time
        (currentCanonicalFullActionActual source current space)
  temporalMatterFaithfulZeroFiber : ∀ space,
    currentCanonicalFullActionTemporalMatterActual source current space =
          currentCanonicalFullActionP286Actual source current space ↔
      matterTemporalDiracYukawaFirstGermResidual source
          (currentCanonicalFullActionP286Actual source current space) =
        0
  completeMatterFaithfulZeroFiber : ∀ space,
    currentCanonicalFullActionActual source current space =
          currentCanonicalFullActionTemporalMatterActual source current space ↔
      matterCompleteDiracYukawaFirstGermResidual source
          (currentCanonicalFullActionTemporalMatterActual source current space) =
        0
  zeroResponseGenerated :
    update 0 = currentCanonicalFullActionGeneratedZeroResponseState source current
  p286AuxiliaryTimeJet : ∀ globalSpace pair time,
    HasDerivAt
      (fun candidate : ℝ =>
        p286CoordinateEquiv
          ((update candidate).gaugeAuxiliary globalSpace pair))
      (p286SpatialAuxiliaryVelocityEmbedding
        (currentP286SpatialAuxiliaryVelocity source
          (currentFullSynchronizedResponseActual source current globalSpace))
        pair)
      time

theorem currentCanonicalFullActionPrimitiveCauchyUpdate_realizes
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdateLaw source current
      (currentCanonicalFullActionPrimitiveCauchyUpdate source current) := by
  exact
    { updateGenerated := rfl
      baseActualGenerated := fun _ => rfl
      p286ActualGenerated := fun _ => rfl
      temporalMatterActualGenerated := fun _ => rfl
      completeActualGenerated := fun _ => rfl
      localPathGenerated := fun _ _ => rfl
      temporalMatterFaithfulZeroFiber :=
        currentCanonicalFullActionTemporalMatterActual_faithfulZeroFiber source
          current
      completeMatterFaithfulZeroFiber :=
        currentCanonicalFullActionActual_faithfulCompleteZeroFiber source current
      zeroResponseGenerated :=
        currentCanonicalFullActionPrimitiveCauchyUpdate_zero source current
      p286AuxiliaryTimeJet :=
        currentCanonicalFullActionPrimitiveCauchyUpdate_p286Auxiliary_hasDerivAt
          source current }

end

end
  SaturationMonoid.PhysicsCore.StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
