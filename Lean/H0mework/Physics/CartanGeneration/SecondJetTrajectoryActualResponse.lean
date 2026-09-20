import H0mework.Physics.CartanGeneration.SecondJetPrimitiveCauchyDevelopment

/-!
# S9-C3h137: trajectory-indexed second-jet actual and response

C3h135 first generates a whole-slice quadratic trajectory `U₂(t)`.  This
module makes every already generated trajectory state the input of a new
C3h133 current-state actual/action construction:

```text
source + initial primitive state
→ C3h135 whole-slice U₂(trajectoryTime)
→ action-prepare that generated current state
→ C3h133 complete local second-jet actual at every spatial contact
→ C3h135 current-state whole-slice restart
→ complete ten-field synchronized response of the restart.
```

The constructor does not import C3h134/C3h136 acceptance and does not read a
residual, endpoint, inverse image, range witness, supplied actual, supplied
response, or branch receipt.  It generates `U` and its action response first.

This is still a fixed-current local quadratic restart.  It does not claim
that the outer C3h135 trajectory is an autonomous integral flow at nonzero
trajectory time.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryActualResponse

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineEnrichedProofFreeSource
open StageNineGravityGaugeActionLocalActualLift
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyDevelopment
open StageNineSourceActionGeneratedCurrentTorsionFreeCartanSecondJetLocalActualLift
open StageNineSourceActionGeneratedCurrentTorsionFreeCartanSecondJetPrimitiveCauchyDevelopment
open StageNineSourceActionGeneratedJointPrimitiveCauchyUpdate
open StageNineSourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
open StageNineSourceActionGeneratedPrimitiveCanonicalSplitDevelopment

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Generated current trajectory state -/

def sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
    (source : SmoothUnifiedSource)
    (anchor trajectoryTime : ℝ)
    (state : StageNineCauchyState) :
    StageNineCauchyState :=
  sourceActionGeneratedCurrentTorsionFreeCartanSecondJetPrimitiveCauchyUpdate
    source anchor trajectoryTime state

/-- Every generated C3h135 trajectory state is action-prepared because its
gravity auxiliary is derived from its own coframe. -/
theorem
    sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState_actionPrepared
    (source : SmoothUnifiedSource)
    (anchor trajectoryTime : ℝ)
    (state : StageNineCauchyState) :
    sourceActionGeneratedJointPrimitiveActionInitialState
        (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
          source anchor trajectoryTime state) =
      sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
        source anchor trajectoryTime state := by
  apply StageNineCauchyState.ext
  · rfl
  · rfl
  · funext space
    change
      actionGeneratedGravityAuxiliary
          (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetPrimitiveCauchyUpdate
            source anchor trajectoryTime state)
          space =
        (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetPrimitiveCauchyUpdate
          source anchor trajectoryTime state).gravityAuxiliary space
    rw [
      sourceActionGeneratedCurrentTorsionFreeCartanSecondJetPrimitiveCauchyUpdate_gravityAuxiliary_generated]
    rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- Re-entering the current-state constructor at anchor zero preserves the
already generated trajectory state. -/
theorem
    sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState_currentIdentity
    (source : SmoothUnifiedSource)
    (anchor trajectoryTime : ℝ)
    (state : StageNineCauchyState) :
    sourceActionGeneratedCurrentPrimitiveCauchyState source 0
        (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
          source anchor trajectoryTime state) =
      sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
        source anchor trajectoryTime state := by
  unfold sourceActionGeneratedCurrentPrimitiveCauchyState
    sourceActionGeneratedPrimitiveCanonicalCurrent
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate
  change
    sourceActionGeneratedJointPrimitiveCauchyUpdate source 0
        (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
          source anchor trajectoryTime state) =
      sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
        source anchor trajectoryTime state
  rw [sourceActionGeneratedJointPrimitiveCauchyUpdate_zero]
  exact
    sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState_actionPrepared
      source anchor trajectoryTime state

/-! ## Current-state actual and restart -/

def
    sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryLocalActualLift
    (source : SmoothUnifiedSource)
    (anchor trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :=
  sourceActionGeneratedCurrentTorsionFreeCartanSecondJetLocalActualLift
    source 0
    (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
      source anchor trajectoryTime state)
    space

def sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryRestart
    (source : SmoothUnifiedSource)
    (anchor trajectoryTime step : ℝ)
    (state : StageNineCauchyState) :
    StageNineCauchyState :=
  sourceActionGeneratedCurrentTorsionFreeCartanSecondJetPrimitiveCauchyUpdate
    source 0 step
    (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
      source anchor trajectoryTime state)

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryLocalActualLift_realizes
    (source : SmoothUnifiedSource)
    (anchor trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    SourceActionGeneratedCurrentCartanSecondJetLocalActualLaw
      source 0
      (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
        source anchor trajectoryTime state)
      space
      (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryLocalActualLift
        source anchor trajectoryTime state space) := by
  exact
    sourceActionGeneratedCurrentTorsionFreeCartanSecondJetLocalActualLift_realizes
      source 0
      (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
        source anchor trajectoryTime state)
      space

@[simp] theorem
    sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryRestart_zero
    (source : SmoothUnifiedSource)
    (anchor trajectoryTime : ℝ)
    (state : StageNineCauchyState) :
    sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryRestart
        source anchor trajectoryTime 0 state =
      sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
        source anchor trajectoryTime state := by
  unfold
    sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryRestart
  rw [
    sourceActionGeneratedCurrentTorsionFreeCartanSecondJetPrimitiveCauchyUpdate_zero]
  exact
    sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState_currentIdentity
      source anchor trajectoryTime state

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryRestart_hasSynchronizedActionResponse
    (source : SmoothUnifiedSource)
    (anchor trajectoryTime : ℝ)
    (state : StageNineCauchyState) :
    SourceActionGeneratedCurrentCartanSecondJetPrimitiveSynchronizedActionResponseLaw
      source 0
      (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
        source anchor trajectoryTime state)
      (fun step =>
        sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryRestart
          source anchor trajectoryTime step state) := by
  exact
    sourceActionGeneratedCurrentTorsionFreeCartanSecondJetPrimitiveCauchyDevelopment_hasSynchronizedActionResponse
      source 0
      (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
        source anchor trajectoryTime state)

/-! ## Complete trajectory-indexed actual/response producer law -/

structure
    SourceActionGeneratedCurrentCartanSecondJetTrajectoryActualResponseLaw
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState) : Prop where
  trajectoryGenerated :
    SourceActionGeneratedCurrentCartanSecondJetPrimitiveSynchronizedActionResponseLaw
      source anchor state
      (fun trajectoryTime =>
        sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
          source anchor trajectoryTime state)
  currentActionPrepared :
    ∀ trajectoryTime,
      sourceActionGeneratedJointPrimitiveActionInitialState
          (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
            source anchor trajectoryTime state) =
        sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
          source anchor trajectoryTime state
  currentIdentity :
    ∀ trajectoryTime,
      sourceActionGeneratedCurrentPrimitiveCauchyState source 0
          (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
            source anchor trajectoryTime state) =
        sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
          source anchor trajectoryTime state
  localActualGenerated :
    ∀ trajectoryTime space,
      SourceActionGeneratedCurrentCartanSecondJetLocalActualLaw
        source 0
        (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
          source anchor trajectoryTime state)
        space
        (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryLocalActualLift
          source anchor trajectoryTime state space)
  restartInitial :
    ∀ trajectoryTime,
      sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryRestart
          source anchor trajectoryTime 0 state =
        sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
          source anchor trajectoryTime state
  synchronizedCurrentResponse :
    ∀ trajectoryTime,
      SourceActionGeneratedCurrentCartanSecondJetPrimitiveSynchronizedActionResponseLaw
        source 0
        (sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState
          source anchor trajectoryTime state)
        (fun step =>
          sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryRestart
            source anchor trajectoryTime step state)

/-- Frontier theorem: the source-generated C3h135 trajectory first selects
each current state; actual dynamics then generate its complete local
second-jet actual and full ten-field current response. -/
theorem
    sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryActualResponse_realizes
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState) :
    SourceActionGeneratedCurrentCartanSecondJetTrajectoryActualResponseLaw
      source anchor state := by
  exact
    { trajectoryGenerated :=
        sourceActionGeneratedCurrentTorsionFreeCartanSecondJetPrimitiveCauchyDevelopment_hasSynchronizedActionResponse
          source anchor state
      currentActionPrepared := fun trajectoryTime =>
        sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState_actionPrepared
          source anchor trajectoryTime state
      currentIdentity := fun trajectoryTime =>
        sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryState_currentIdentity
          source anchor trajectoryTime state
      localActualGenerated := fun trajectoryTime space =>
        sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryLocalActualLift_realizes
          source anchor trajectoryTime state space
      restartInitial := fun trajectoryTime =>
        sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryRestart_zero
          source anchor trajectoryTime state
      synchronizedCurrentResponse := fun trajectoryTime =>
        sourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryRestart_hasSynchronizedActionResponse
          source anchor trajectoryTime state }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedCurrentTorsionFreeCartanSecondJetTrajectoryActualResponse
