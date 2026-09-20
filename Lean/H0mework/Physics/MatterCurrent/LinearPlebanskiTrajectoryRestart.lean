import H0mework.Physics.MatterCurrent.LinearPlebanskiPrimitiveCauchyUpdate

/-!
# S9-C3h155: current-state linear-Plebanski trajectory restart

C3h154 generated the corrected whole-slice path `U₄(t)` from actual local
dynamics.  This module now makes every already generated `U₄(τ)` the input of
the same action grammar:

```text
proof-free source + initial primitive state
→ corrected whole-slice trajectory U₄(τ)
→ current primitive state U₄(τ)
→ corrected local actual at every current spatial contact
→ complete ten-coordinate current response
→ restart(τ,s).
```

The restart is not selected from a residual and accepts no response,
curvature target, endpoint, inverse, range witness, coefficient, or branch
receipt.  Its zero step is the generated current state itself, and its
complete tangent is recomputed from that current state by the same
linear-Plebanski-aware action constructor.

This proves reachability of the full synchronized current response.  It does
not yet identify the derivative of the original frozen-input trajectory at
nonzero `τ` with the recomputed restart response, and it does not claim a
semigroup or global integral flow.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiTrajectoryRestart

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineEnrichedProofFreeSource
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineSourceActionGeneratedJointPrimitiveCauchyPath
open StageNineSourceActionGeneratedJointPrimitiveCauchyUpdate
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiPrimitiveCauchyUpdate
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSimpArgs false

/-! ## Generic current state and action-first restart -/

/-- Select an already generated point of the corrected C3h154 trajectory. -/
def sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState) :
    StageNineCauchyState :=
  sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyUpdate
    source trajectoryTime state

/-- Regenerate a corrected local actual from the already generated current
state. -/
def sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedLinearPlebanskiJointLocalActualLift
    source
    (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
      source trajectoryTime state)
    space

/-- Complete response recomputed from the current primitive state. -/
def sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryResponse
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineJointPrimitiveActionVelocity :=
  sourceActionGeneratedLinearPlebanskiJointPrimitiveActionVelocity
    source
    (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
      source trajectoryTime state)
    space

/-- The current state first exists, then the same corrected action grammar
generates its restart. -/
def sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryRestart
    (source : SmoothUnifiedSource)
    (trajectoryTime step : ℝ)
    (state : StageNineCauchyState) :
    StageNineCauchyState :=
  sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyUpdate
    source step
    (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
      source trajectoryTime state)

@[simp] theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState_coframe
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
      source trajectoryTime state).coframe space =
      state.coframe space := by
  rfl

@[simp] theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState_gravityAuxiliary
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
      source trajectoryTime state).gravityAuxiliary space =
      actionGeneratedGravityAuxiliary state space := by
  rfl

@[simp] theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState_multiplier
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
      source trajectoryTime state).gravitySimplicityMultiplier space =
      state.gravitySimplicityMultiplier space := by
  rfl

/-- Every generated trajectory state is action-prepared: its auxiliary is
the `II⁺` image of its own generated coframe. -/
theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState_actionPrepared
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState) :
    sourceActionGeneratedJointPrimitiveActionInitialState
        (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
          source trajectoryTime state) =
      sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
        source trajectoryTime state := by
  apply StageNineCauchyState.ext
  · rfl
  · rfl
  · funext space
    change
      actionGeneratedGravityAuxiliary
          (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
            source trajectoryTime state)
          space =
        actionGeneratedGravityAuxiliary state space
    unfold actionGeneratedGravityAuxiliary
    rw [
      sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState_coframe]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

@[simp] theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryRestart_zero
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState) :
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryRestart
        source trajectoryTime 0 state =
      sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
        source trajectoryTime state := by
  unfold
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryRestart
  rw [
    sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyUpdate_zero]
  exact
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState_actionPrepared
      source trajectoryTime state

/-- The complete current response is generated at every trajectory time. -/
theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryRestart_hasCurrentResponse
    (source : SmoothUnifiedSource)
    (trajectoryTime : ℝ)
    (state : StageNineCauchyState) :
    StageNineLinearPlebanskiJointPrimitiveActionCauchyUpdateLaw
      source
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
        source trajectoryTime state)
      (fun step =>
        sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryRestart
          source trajectoryTime step state) := by
  exact
    sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyUpdate_realizes
      source
      (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
        source trajectoryTime state)

structure StageNineLinearPlebanskiJointPrimitiveTrajectoryRestartLaw
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (trajectory : ℝ → StageNineCauchyState)
    (restart : ℝ → ℝ → StageNineCauchyState) : Prop where
  trajectoryGenerated :
    trajectory =
      fun trajectoryTime =>
        sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
          source trajectoryTime state
  restartGenerated :
    restart =
      fun trajectoryTime step =>
        sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryRestart
          source trajectoryTime step state
  currentActionPrepared :
    ∀ trajectoryTime,
      sourceActionGeneratedJointPrimitiveActionInitialState
          (trajectory trajectoryTime) =
        trajectory trajectoryTime
  currentLocalActualGenerated :
    ∀ trajectoryTime space,
      StageNineLinearPlebanskiJointPrimitiveActionCauchyPathLaw
        source (trajectory trajectoryTime) space
        (sourceActionGeneratedLinearPlebanskiJointLocalActualLift
          source (trajectory trajectoryTime) space)
        (sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath
          source (trajectory trajectoryTime) space)
  restartInitial :
    ∀ trajectoryTime,
      restart trajectoryTime 0 = trajectory trajectoryTime
  currentResponseGenerated :
    ∀ trajectoryTime,
      StageNineLinearPlebanskiJointPrimitiveActionCauchyUpdateLaw
        source (trajectory trajectoryTime)
        (restart trajectoryTime)

/-- Generic frontier: every point of a corrected generated trajectory
canonically seeds a corrected local actual and complete current response. -/
theorem
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryRestart_realizes
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineLinearPlebanskiJointPrimitiveTrajectoryRestartLaw
      source state
      (fun trajectoryTime =>
        sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
          source trajectoryTime state)
      (fun trajectoryTime step =>
        sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryRestart
          source trajectoryTime step state) := by
  exact
    { trajectoryGenerated := rfl
      restartGenerated := rfl
      currentActionPrepared :=
        fun trajectoryTime =>
          sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState_actionPrepared
            source trajectoryTime state
      currentLocalActualGenerated :=
        fun trajectoryTime space =>
          sourceActionGeneratedLinearPlebanskiJointPrimitiveCauchyPath_realizes
            source
            (sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
              source trajectoryTime state)
            space
      restartInitial :=
        fun trajectoryTime =>
          sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryRestart_zero
            source trajectoryTime state
      currentResponseGenerated :=
        fun trajectoryTime =>
          sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryRestart_hasCurrentResponse
            source trajectoryTime state }

/-! ## Exact P506/L0 trajectory specialization -/

def positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState
    (trajectoryTime : ℝ) :
    StageNineCauchyState :=
  sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
    positiveSmoothUnifiedSource trajectoryTime
    positiveP506MatterCurrentLinearPlebanskiCauchyState

def positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
    (trajectoryTime : ℝ)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
    positiveSmoothUnifiedSource trajectoryTime
    positiveP506MatterCurrentLinearPlebanskiCauchyState space

def positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryResponse
    (trajectoryTime : ℝ)
    (space : StageNineSpatialPoint) :
    StageNineJointPrimitiveActionVelocity :=
  sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryResponse
    positiveSmoothUnifiedSource trajectoryTime
    positiveP506MatterCurrentLinearPlebanskiCauchyState space

def positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryRestart
    (trajectoryTime step : ℝ) :
    StageNineCauchyState :=
  sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryRestart
    positiveSmoothUnifiedSource trajectoryTime step
    positiveP506MatterCurrentLinearPlebanskiCauchyState

@[simp] theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState_zero :
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState 0 =
      positiveP506MatterCurrentLinearPlebanskiCauchyState :=
  positiveP506MatterCurrentLinearPlebanskiPrimitiveCauchyUpdate_zero

@[simp] theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryRestart_zero
    (trajectoryTime : ℝ) :
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryRestart
        trajectoryTime 0 =
      positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState
        trajectoryTime := by
  exact
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryRestart_zero
      positiveSmoothUnifiedSource trajectoryTime
      positiveP506MatterCurrentLinearPlebanskiCauchyState

theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_zero :
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
        0 0 =
      positiveP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift := by
  unfold
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual
  have stateZero :
      sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState
          positiveSmoothUnifiedSource 0
          positiveP506MatterCurrentLinearPlebanskiCauchyState =
        positiveP506MatterCurrentLinearPlebanskiCauchyState := by
    change
      positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState 0 =
        positiveP506MatterCurrentLinearPlebanskiCauchyState
    exact
      positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState_zero
  rw [stateZero]
  rfl

@[simp] theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState_coframe
    (trajectoryTime : ℝ)
    (space : StageNineSpatialPoint) :
    (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState
      trajectoryTime).coframe space =
      1 := by
  rw [
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState,
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState_coframe,
    positiveP506MatterCurrentLinearPlebanskiCauchyState_coframe_allSpace]

@[simp] theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState_multiplier
    (trajectoryTime : ℝ)
    (space : StageNineSpatialPoint) :
    (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState
      trajectoryTime).gravitySimplicityMultiplier space =
      positiveP506MatterCurrentLinearPlebanskiMultiplier := by
  rw [
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState,
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryState_multiplier,
    positiveP506MatterCurrentLinearPlebanskiCauchyState_multiplier_allSpace]

theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState_multiplier_nonzero
    (trajectoryTime : ℝ)
    (space : StageNineSpatialPoint) :
    (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState
      trajectoryTime).gravitySimplicityMultiplier space ≠ 0 := by
  rw [
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState_multiplier]
  exact positiveP506MatterCurrentLinearPlebanskiMultiplier_nonzero

theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectory_curvatureTarget
    (trajectoryTime : ℝ)
    (space : StageNineSpatialPoint) :
    linearPlebanskiActionGeneratedGravityCurvature
        (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState
          trajectoryTime)
        space =
      positiveP506MatterCurrentLinearPlebanskiCurvatureTarget := by
  calc
    linearPlebanskiActionGeneratedGravityCurvature
          (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState
            trajectoryTime)
          space =
        linearPlebanskiActionGeneratedGravityCurvature
          positiveP506MatterCurrentLinearPlebanskiCauchyState space := by
      unfold linearPlebanskiActionGeneratedGravityCurvature
        actionGeneratedGravityAuxiliary
      rw [
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState_coframe,
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState_multiplier,
        positiveP506MatterCurrentLinearPlebanskiCauchyState_coframe_allSpace,
        positiveP506MatterCurrentLinearPlebanskiCauchyState_multiplier_allSpace]
    _ = positiveP506MatterCurrentLinearPlebanskiCurvatureTarget :=
      positiveP506MatterCurrentLinearPlebanskiCauchyState_target_allSpace space

theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_curvature
    (trajectoryTime : ℝ)
    (space : StageNineSpatialPoint) :
    holonomicGravityCurvature
        (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
          trajectoryTime space)
        0 =
      positiveP506MatterCurrentLinearPlebanskiCurvatureTarget := by
  rw [
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual,
    sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryLocalActual,
    sourceActionGeneratedLinearPlebanskiJointLocalActualLift_curvature_origin]
  change
    linearPlebanskiActionGeneratedGravityCurvature
        (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState
          trajectoryTime)
        space =
      positiveP506MatterCurrentLinearPlebanskiCurvatureTarget
  exact
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectory_curvatureTarget
      trajectoryTime space

theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_interactionSensitive
    (trajectoryTime : ℝ)
    (space : StageNineSpatialPoint) :
    holonomicGravityCurvature
        (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
          trajectoryTime space)
        0 ≠
      gravityInternalDualEquiv
        (physicalIIPlusBivector (1 : LorentzianCoframe)) := by
  rw [
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_curvature]
  exact
    positiveP506MatterCurrentLinearPlebanskiCurvatureTarget_ne_uncoupled

structure
    PositiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryRestartLaw :
    Prop where
  exactP506L0Lineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference
  baseWholeSliceGenerated :
    PositiveP506MatterCurrentLinearPlebanskiPrimitiveCauchyUpdateLaw
  currentRestartGenerated :
    StageNineLinearPlebanskiJointPrimitiveTrajectoryRestartLaw
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentLinearPlebanskiCauchyState
      positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState
      positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryRestart
  initialStateReplayed :
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState 0 =
      positiveP506MatterCurrentLinearPlebanskiCauchyState
  initialLocalActualReplayed :
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
        0 0 =
      positiveP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
  currentMultiplierNonzero :
    ∀ trajectoryTime space,
      (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState
        trajectoryTime).gravitySimplicityMultiplier space ≠ 0
  currentCurvatureGenerated :
    ∀ trajectoryTime space,
      holonomicGravityCurvature
          (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
            trajectoryTime space)
          0 =
        positiveP506MatterCurrentLinearPlebanskiCurvatureTarget
  currentCurvatureInteractionSensitive :
    ∀ trajectoryTime space,
      holonomicGravityCurvature
          (positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual
            trajectoryTime space)
          0 ≠
        gravityInternalDualEquiv
          (physicalIIPlusBivector (1 : LorentzianCoframe))

/-- Frontier theorem: exact P506/L0 dynamics generate, at every trajectory
time, a corrected current local actual, complete ten-coordinate response,
and zero-faithful restart.  No premise is accepted. -/
theorem
    positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryRestart_realizes :
    PositiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryRestartLaw := by
  exact
    { exactP506L0Lineage :=
        positiveSmoothUnifiedSource_generates_exactP506L0Lineage
      baseWholeSliceGenerated :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveCauchyUpdate_realizes
      currentRestartGenerated :=
        sourceActionGeneratedLinearPlebanskiJointPrimitiveTrajectoryRestart_realizes
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentLinearPlebanskiCauchyState
      initialStateReplayed :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState_zero
      initialLocalActualReplayed :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_zero
      currentMultiplierNonzero :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryState_multiplier_nonzero
      currentCurvatureGenerated :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_curvature
      currentCurvatureInteractionSensitive :=
        positiveP506MatterCurrentLinearPlebanskiPrimitiveTrajectoryLocalActual_interactionSensitive }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiTrajectoryRestart
