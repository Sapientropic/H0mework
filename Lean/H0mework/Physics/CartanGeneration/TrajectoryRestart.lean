import H0mework.Physics.CartanGeneration.PrimitiveCanonicalDevelopment

/-!
# S9-C3h131: source/action-generated trajectory restart

C3h130 produces a coordinated primitive/canonical development from one
anchor-current state.  This module makes every already generated point of
that trajectory the input of a new forward actual/action step:

```text
source + initial state
→ C3h130 trajectory U(trajectoryTime)
→ current := U(trajectoryTime)
├─ current.primitive → new Cartan actual path
└─ current canonical history → new canonical relative action update
→ restart(trajectoryTime, step).
```

The primitive restart is generated through the same C3h128/C3h129 actual
Cartan constructor.  The canonical restart advances from the existing
canonical state, so momentum history is not recomputed from primitive BF
fields.  At `step = 0` the restart is exactly the selected trajectory state,
and at every selected state it carries a complete current-state primitive
response plus P286/Lorentz/scalar canonical momentum derivatives.

This constructs `V(source, U(trajectoryTime))`; it does not yet prove that
the derivative of the original C3h130 trajectory equals that recomputed
response.  No residual, endpoint, inverse image, shell witness, or branch
certificate enters the constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedCurrentTorsionFreeCartanTrajectoryRestart

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineJointActionCanonicalPhasePathLaw
open StageNineLorentzActionCanonicalPairUpdate
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineScalarActionCanonicalMomentumUpdate
open StageNineSourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
open StageNineSourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyDevelopment
open StageNineSourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
open StageNineSourceActionGeneratedJointPrimitiveCauchyUpdate
open StageNineSourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
open StageNineSourceActionGeneratedPrimitiveCanonicalSplitDevelopment
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-! ## Generic current-split restart -/

/-- Restart one already generated split without rebuilding its canonical
base from primitive readouts. -/
def sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalRestartUpdate
    (source : SmoothUnifiedSource)
    (step : ℝ)
    (current : StageNinePrimitiveCanonicalSplitActionState) :
    StageNinePrimitiveCanonicalSplitActionState where
  primitive :=
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
      source 0 step current.primitive
  canonical :=
    sourceActionGeneratedJointCanonicalRelativeEulerUpdate
      source step current

/-- Every C3h128 Cartan-refined state is already action-prepared because its
gravity auxiliary is generated from its own coframe. -/
theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_actionPrepared
    (source : SmoothUnifiedSource)
    (anchor relativeTime : ℝ)
    (state : StageNineCauchyState) :
    sourceActionGeneratedJointPrimitiveActionInitialState
        (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
          source anchor relativeTime state) =
      sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
        source anchor relativeTime state := by
  apply StageNineCauchyState.ext
  · rfl
  · rfl
  · funext space
    change
      actionGeneratedGravityAuxiliary
          (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
            source anchor relativeTime state)
          space =
        _
    rw [
      sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_gravityAuxiliary_generated]
    rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalRestartUpdate_zero_of_actionPrepared
    (source : SmoothUnifiedSource)
    (current : StageNinePrimitiveCanonicalSplitActionState)
    (actionPrepared :
      sourceActionGeneratedJointPrimitiveActionInitialState
          current.primitive =
        current.primitive) :
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalRestartUpdate
        source 0 current =
      current := by
  apply StageNinePrimitiveCanonicalSplitActionState.ext
  · change
      sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
          source 0 0 current.primitive =
        current.primitive
    rw [
      sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_zero]
    change
      sourceActionGeneratedJointPrimitiveCauchyUpdate
          source 0 current.primitive =
        current.primitive
    rw [sourceActionGeneratedJointPrimitiveCauchyUpdate_zero]
    exact actionPrepared
  · exact
      sourceActionGeneratedJointCanonicalRelativeEulerUpdate_zero
        source current

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalRestartUpdate_hasPrimitiveResponse
    (source : SmoothUnifiedSource)
    (current : StageNinePrimitiveCanonicalSplitActionState) :
    StageNineCurrentTorsionFreeCartanPrimitiveSynchronizedActionResponseLaw
      source 0 current.primitive
      (fun step =>
        (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalRestartUpdate
          source step current).primitive) := by
  exact
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyDevelopment_hasSynchronizedActionResponse
      source 0 current.primitive

@[simp] theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalRestartUpdate_canonical
    (source : SmoothUnifiedSource)
    (step : ℝ)
    (current : StageNinePrimitiveCanonicalSplitActionState) :
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalRestartUpdate
      source step current).canonical =
      sourceActionGeneratedJointCanonicalRelativeEulerUpdate
        source step current :=
  rfl

/-! ## Generic current-state canonical momentum derivatives -/

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalRestartUpdate_p286MomentumHasDerivAt
    (source : SmoothUnifiedSource)
    (current : StageNinePrimitiveCanonicalSplitActionState)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (direction : P286SpatialGaugeDirection) :
    HasDerivAt
      (fun step : ℝ =>
        (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalRestartUpdate
          source step
          current).canonical.gravityGauge.p286.spatialBFMomentumEvaluation
            space direction)
      (sourceActionGeneratedP286SpatialBFMomentumVelocity
        source current.primitive space direction)
      time := by
  change HasDerivAt
    (fun step : ℝ =>
      current.canonical.gravityGauge.p286.spatialBFMomentumEvaluation
          space direction +
        step *
          sourceActionGeneratedP286SpatialBFMomentumVelocity
            source current.primitive space direction)
    _ time
  simpa only [smul_eq_mul] using
    hasDerivAt_const_add_time_smul
      (current.canonical.gravityGauge.p286.spatialBFMomentumEvaluation
        space direction)
      (sourceActionGeneratedP286SpatialBFMomentumVelocity
        source current.primitive space direction)
      time

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalRestartUpdate_lorentzMomentumHasDerivAt
    (source : SmoothUnifiedSource)
    (current : StageNinePrimitiveCanonicalSplitActionState)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (direction : LorentzSpatialBivectorDirection) :
    HasDerivAt
      (fun step : ℝ =>
        (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalRestartUpdate
          source step
          current).canonical.gravityGauge.lorentz.spatialBFMomentumEvaluation
            space direction)
      (sourceActionGeneratedLorentzSpatialBFMomentumVelocity
        source current.primitive space direction)
      time := by
  change HasDerivAt
    (fun step : ℝ =>
      current.canonical.gravityGauge.lorentz.spatialBFMomentumEvaluation
          space direction +
        step *
          sourceActionGeneratedLorentzSpatialBFMomentumVelocity
            source current.primitive space direction)
    _ time
  simpa only [smul_eq_mul] using
    hasDerivAt_const_add_time_smul
      (current.canonical.gravityGauge.lorentz.spatialBFMomentumEvaluation
        space direction)
      (sourceActionGeneratedLorentzSpatialBFMomentumVelocity
        source current.primitive space direction)
      time

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalRestartUpdate_scalarMomentumHasDerivAt
    (source : SmoothUnifiedSource)
    (current : StageNinePrimitiveCanonicalSplitActionState)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    HasDerivAt
      (fun step : ℝ =>
        (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalRestartUpdate
          source step current).canonical.scalar.temporalMomentumEvaluation
            space direction)
      (sourceActionGeneratedScalarTemporalMomentumVelocity
        source current.primitive space direction)
      time := by
  change HasDerivAt
    (fun step : ℝ =>
      current.canonical.scalar.temporalMomentumEvaluation space direction +
        step *
          sourceActionGeneratedScalarTemporalMomentumVelocity
            source current.primitive space direction)
    _ time
  simpa only [smul_eq_mul] using
    hasDerivAt_const_add_time_smul
      (current.canonical.scalar.temporalMomentumEvaluation
        space direction)
      (sourceActionGeneratedScalarTemporalMomentumVelocity
        source current.primitive space direction)
      time

/-! ## Trajectory-indexed specialization -/

def sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
    (source : SmoothUnifiedSource)
    (anchor trajectoryTime : ℝ)
    (state : StageNineCauchyState) :
    StageNinePrimitiveCanonicalSplitActionState :=
  sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
    source anchor trajectoryTime state

/-- The selected trajectory state is generated first and only then used as
the current state of the restart. -/
def sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryRestart
    (source : SmoothUnifiedSource)
    (anchor trajectoryTime step : ℝ)
    (state : StageNineCauchyState) :
    StageNinePrimitiveCanonicalSplitActionState :=
  sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalRestartUpdate
    source step
    (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
      source anchor trajectoryTime state)

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState_actionPrepared
    (source : SmoothUnifiedSource)
    (anchor trajectoryTime : ℝ)
    (state : StageNineCauchyState) :
    sourceActionGeneratedJointPrimitiveActionInitialState
        (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
          source anchor trajectoryTime state).primitive =
      (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
        source anchor trajectoryTime state).primitive := by
  exact
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_actionPrepared
      source anchor trajectoryTime state

@[simp] theorem
    sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryRestart_zero
    (source : SmoothUnifiedSource)
    (anchor trajectoryTime : ℝ)
    (state : StageNineCauchyState) :
    sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryRestart
        source anchor trajectoryTime 0 state =
      sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
        source anchor trajectoryTime state := by
  exact
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalRestartUpdate_zero_of_actionPrepared
      source
      (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
        source anchor trajectoryTime state)
      (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState_actionPrepared
        source anchor trajectoryTime state)

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryRestart_hasPrimitiveResponse
    (source : SmoothUnifiedSource)
    (anchor trajectoryTime : ℝ)
    (state : StageNineCauchyState) :
    StageNineCurrentTorsionFreeCartanPrimitiveSynchronizedActionResponseLaw
      source 0
      (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
        source anchor trajectoryTime state).primitive
      (fun step =>
        (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryRestart
          source anchor trajectoryTime step state).primitive) := by
  exact
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalRestartUpdate_hasPrimitiveResponse
      source
      (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
        source anchor trajectoryTime state)

/-! ## Bundled restart law -/

structure StageNineCurrentTorsionFreeCartanTrajectoryRestartLaw
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState)
    (restart :
      ℝ → ℝ → StageNinePrimitiveCanonicalSplitActionState) : Prop where
  generated :
    restart =
      fun trajectoryTime step =>
        sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryRestart
          source anchor trajectoryTime step state
  trajectoryDevelopment :
    StageNineCurrentTorsionFreeCartanPrimitiveCanonicalDevelopmentLaw
      source anchor state
      (fun trajectoryTime =>
        sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
          source anchor trajectoryTime state)
  currentActionPrepared :
    ∀ trajectoryTime,
      sourceActionGeneratedJointPrimitiveActionInitialState
          (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
            source anchor trajectoryTime state).primitive =
        (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
          source anchor trajectoryTime state).primitive
  zero :
    ∀ trajectoryTime,
      restart trajectoryTime 0 =
        sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
          source anchor trajectoryTime state
  primitiveResponse :
    ∀ trajectoryTime,
      StageNineCurrentTorsionFreeCartanPrimitiveSynchronizedActionResponseLaw
        source 0
        (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
          source anchor trajectoryTime state).primitive
        (fun step => (restart trajectoryTime step).primitive)
  canonicalGenerated :
    ∀ trajectoryTime step,
      (restart trajectoryTime step).canonical =
        sourceActionGeneratedJointCanonicalRelativeEulerUpdate
          source step
          (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
            source anchor trajectoryTime state)
  p286MomentumDerivative :
    ∀ trajectoryTime time space direction,
      HasDerivAt
        (fun step : ℝ =>
          (restart trajectoryTime
            step).canonical.gravityGauge.p286.spatialBFMomentumEvaluation
              space direction)
        (sourceActionGeneratedP286SpatialBFMomentumVelocity
          source
          (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
            source anchor trajectoryTime state).primitive
          space direction)
        time
  lorentzMomentumDerivative :
    ∀ trajectoryTime time space direction,
      HasDerivAt
        (fun step : ℝ =>
          (restart trajectoryTime
            step).canonical.gravityGauge.lorentz.spatialBFMomentumEvaluation
              space direction)
        (sourceActionGeneratedLorentzSpatialBFMomentumVelocity
          source
          (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
            source anchor trajectoryTime state).primitive
          space direction)
        time
  scalarMomentumDerivative :
    ∀ trajectoryTime time space direction,
      HasDerivAt
        (fun step : ℝ =>
          (restart trajectoryTime
            step).canonical.scalar.temporalMomentumEvaluation
              space direction)
        (sourceActionGeneratedScalarTemporalMomentumVelocity
          source
          (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
            source anchor trajectoryTime state).primitive
          space direction)
        time

/-- Frontier theorem: every point of the generated C3h130 trajectory
canonically seeds a new actual/action restart with exact zero-step identity
and complete current-state responses. -/
theorem
    sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryRestart_realizes
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState) :
    StageNineCurrentTorsionFreeCartanTrajectoryRestartLaw
      source anchor state
      (fun trajectoryTime step =>
        sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryRestart
          source anchor trajectoryTime step state) := by
  exact
    { generated := rfl
      trajectoryDevelopment :=
        sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_realizes
          source anchor state
      currentActionPrepared :=
        fun trajectoryTime =>
          sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState_actionPrepared
            source anchor trajectoryTime state
      zero :=
        fun trajectoryTime =>
          sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryRestart_zero
            source anchor trajectoryTime state
      primitiveResponse :=
        fun trajectoryTime =>
          sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryRestart_hasPrimitiveResponse
            source anchor trajectoryTime state
      canonicalGenerated := fun _ _ => rfl
      p286MomentumDerivative :=
        fun trajectoryTime time space direction =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalRestartUpdate_p286MomentumHasDerivAt
            source
            (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
              source anchor trajectoryTime state)
            time space direction
      lorentzMomentumDerivative :=
        fun trajectoryTime time space direction =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalRestartUpdate_lorentzMomentumHasDerivAt
            source
            (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
              source anchor trajectoryTime state)
            time space direction
      scalarMomentumDerivative :=
        fun trajectoryTime time space direction =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalRestartUpdate_scalarMomentumHasDerivAt
            source
            (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
              source anchor trajectoryTime state)
            time space direction }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedCurrentTorsionFreeCartanTrajectoryRestart
