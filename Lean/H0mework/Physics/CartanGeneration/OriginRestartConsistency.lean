import H0mework.Physics.CartanGeneration.TrajectoryRestart

/-!
# S9-C3h132: origin consistency of trajectory and restart responses

C3h131 generates a new current-state restart from every point of the C3h130
trajectory.  Before asking for arbitrary-time autonomous consistency, the
two forward constructions must agree where they share the same generated
current state.  This module proves that complete typed equality at
`trajectoryTime = 0`:

```text
original C3h130 response at its relative origin
= C3h131 response recomputed from U(0).
```

It then rewrites all ten primitive derivatives and all three canonical
momentum derivatives against the response generated from `U(0)`.  Thus the
origin satisfies the exact current-state law
`dU/dt|₀ = V(source,U(0))` on the full typed response carrier.

No residual, endpoint, zero-fiber witness, inverse image, or supplied
response enters the proof.  This theorem does not assert the corresponding
equality at nonzero trajectory time.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedCurrentTorsionFreeCartanOriginRestartConsistency

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineLorentzActionCanonicalPairUpdate
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineScalarActionCanonicalMomentumUpdate
open StageNineSourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
open StageNineSourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyDevelopment
open StageNineSourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
open StageNineSourceActionGeneratedCurrentTorsionFreeCartanTrajectoryRestart
open StageNineSourceActionGeneratedJointPrimitiveCauchyPath
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

/-! ## Response recomputed from a generated trajectory state -/

def sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryRestartPrimitiveResponse
    (source : SmoothUnifiedSource)
    (anchor trajectoryTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineJointPrimitiveActionVelocity :=
  sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
    source 0 0
    (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
      source anchor trajectoryTime state).primitive
    space

/-- Full typed equality of the original and recomputed responses at the
shared generated current state. -/
theorem
    sourceActionGeneratedCurrentTorsionFreeCartan_originResponse_eq_restartResponse
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
        source anchor 0 state space =
      sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryRestartPrimitiveResponse
        source anchor 0 state space := by
  have trajectoryZero :
      sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
          source anchor 0 state =
        sourceActionGeneratedPrimitiveCanonicalCurrent
          source anchor state :=
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_zero
      source anchor state
  unfold
    sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryRestartPrimitiveResponse
  rw [trajectoryZero]
  let current :=
    (sourceActionGeneratedPrimitiveCanonicalCurrent
      source anchor state).primitive
  have currentPrepared :
      sourceActionGeneratedJointPrimitiveActionInitialState current =
        current := by
    exact
      sourceActionGeneratedCurrentPrimitiveCauchyState_actionPrepared
        source anchor state
  have restartCurrent :
      sourceActionGeneratedCurrentPrimitiveCauchyState
          source 0 current =
        current := by
    change
      sourceActionGeneratedJointPrimitiveCauchyUpdate
          source 0 current =
        current
    rw [sourceActionGeneratedJointPrimitiveCauchyUpdate_zero]
    exact currentPrepared
  have originalZero :
      sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
          source anchor 0 state =
        current := by
    exact
      sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_zero
        source anchor state
  have restartZero :
      sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
          source 0 0 current =
        current := by
    rw [
      sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_zero]
    exact restartCurrent
  unfold
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
    sourceActionGeneratedCurrentTorsionFreeCartanCoframeResponse
  rw [restartCurrent, originalZero, restartZero]

/-! ## A reusable complete primitive response-at-time law -/

structure StageNinePrimitiveCauchyResponseAtLaw
    (development : ℝ → StageNineCauchyState)
    (time : ℝ)
    (response : StageNineSpatialPoint →
      StageNineJointPrimitiveActionVelocity) : Prop where
  coframeDerivative :
    ∀ space internal coordinate,
      HasDerivAt
        (fun candidate : ℝ =>
          (development candidate).coframe space internal coordinate)
        ((response space).coframe internal coordinate)
        time
  gravityConnectionDerivative :
    ∀ space formDirection internalPair,
      HasDerivAt
        (fun candidate : ℝ =>
          loweredLorentzConnectionCoefficient
            ((development candidate).gravityConnection space)
            formDirection internalPair)
        ((response space).gravityConnection formDirection internalPair)
        time
  gravityAuxiliaryDerivative :
    ∀ space internalPair spacetimePair,
      HasDerivAt
        (fun candidate : ℝ =>
          (development candidate).gravityAuxiliary
            space internalPair spacetimePair)
        ((response space).gravityAuxiliary internalPair spacetimePair)
        time
  multiplierDerivative :
    ∀ space internalPair spacetimePair,
      HasDerivAt
        (fun candidate : ℝ =>
          (development candidate).gravitySimplicityMultiplier
            space internalPair spacetimePair)
        ((response space).gravitySimplicityMultiplier
          internalPair spacetimePair)
        time
  p286ConnectionDerivative :
    ∀ space formDirection,
      HasDerivAt
        (fun candidate : ℝ =>
          p286CoordinateEquiv
            ((development candidate).gaugeConnection
              space formDirection))
        ((response space).p286Connection formDirection)
        time
  p286AuxiliaryDerivative :
    ∀ space pair,
      HasDerivAt
        (fun candidate : ℝ =>
          p286CoordinateEquiv
            ((development candidate).gaugeAuxiliary space pair))
        ((response space).p286Auxiliary pair)
        time
  scalarDerivative :
    ∀ space,
      HasDerivAt
        (fun candidate : ℝ =>
          (development candidate).scalar space)
        ((response space).scalar)
        time
  scalarVelocityDerivative :
    ∀ space,
      HasDerivAt
        (fun candidate : ℝ =>
          (development candidate).scalarVelocity space)
        ((response space).scalarVelocity)
        time
  matterDerivative :
    ∀ space,
      HasDerivAt
        (fun candidate : ℝ =>
          matterCoordinateEquiv
            ((development candidate).matter space))
        ((response space).matter)
        time
  conjugateMatterDerivative :
    ∀ space matter,
      HasDerivAt
        (fun candidate : ℝ =>
          (development candidate).conjugateMatter space matter)
        ((response space).conjugateMatter matter)
        time

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanTrajectory_hasOriginRestartPrimitiveResponse
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState) :
    StageNinePrimitiveCauchyResponseAtLaw
      (fun trajectoryTime =>
        (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
          source anchor trajectoryTime state).primitive)
      0
      (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryRestartPrimitiveResponse
        source anchor 0 state) := by
  let original :=
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyDevelopment_hasSynchronizedActionResponse
      source anchor state
  exact
    { coframeDerivative := fun space internal coordinate => by
        have generated :=
          original.coframeDerivative 0 space internal coordinate
        rw [
          sourceActionGeneratedCurrentTorsionFreeCartan_originResponse_eq_restartResponse
            source anchor state space] at generated
        exact generated
      gravityConnectionDerivative :=
        fun space formDirection internalPair => by
          have generated :=
            original.gravityConnectionDerivative
              0 space formDirection internalPair
          rw [
            sourceActionGeneratedCurrentTorsionFreeCartan_originResponse_eq_restartResponse
              source anchor state space] at generated
          exact generated
      gravityAuxiliaryDerivative :=
        fun space internalPair spacetimePair => by
          have generated :=
            original.gravityAuxiliaryDerivative
              0 space internalPair spacetimePair
          rw [
            sourceActionGeneratedCurrentTorsionFreeCartan_originResponse_eq_restartResponse
              source anchor state space] at generated
          exact generated
      multiplierDerivative :=
        fun space internalPair spacetimePair => by
          have generated :=
            original.multiplierDerivative
              0 space internalPair spacetimePair
          rw [
            sourceActionGeneratedCurrentTorsionFreeCartan_originResponse_eq_restartResponse
              source anchor state space] at generated
          exact generated
      p286ConnectionDerivative := fun space formDirection => by
        have generated :=
          original.p286ConnectionDerivative 0 space formDirection
        rw [
          sourceActionGeneratedCurrentTorsionFreeCartan_originResponse_eq_restartResponse
            source anchor state space] at generated
        exact generated
      p286AuxiliaryDerivative := fun space pair => by
        have generated :=
          original.p286AuxiliaryDerivative 0 space pair
        rw [
          sourceActionGeneratedCurrentTorsionFreeCartan_originResponse_eq_restartResponse
            source anchor state space] at generated
        exact generated
      scalarDerivative := fun space => by
        have generated := original.scalarDerivative 0 space
        rw [
          sourceActionGeneratedCurrentTorsionFreeCartan_originResponse_eq_restartResponse
            source anchor state space] at generated
        exact generated
      scalarVelocityDerivative := fun space => by
        have generated := original.scalarVelocityDerivative 0 space
        rw [
          sourceActionGeneratedCurrentTorsionFreeCartan_originResponse_eq_restartResponse
            source anchor state space] at generated
        exact generated
      matterDerivative := fun space => by
        have generated := original.matterDerivative 0 space
        rw [
          sourceActionGeneratedCurrentTorsionFreeCartan_originResponse_eq_restartResponse
            source anchor state space] at generated
        exact generated
      conjugateMatterDerivative := fun space matter => by
        have generated :=
          original.conjugateMatterDerivative 0 space matter
        rw [
          sourceActionGeneratedCurrentTorsionFreeCartan_originResponse_eq_restartResponse
            source anchor state space] at generated
        exact generated }

/-! ## Full primitive/canonical origin consistency -/

structure StageNineCurrentTorsionFreeCartanOriginRestartConsistencyLaw
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState) : Prop where
  responseEquality :
    ∀ space,
      sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
          source anchor 0 state space =
        sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryRestartPrimitiveResponse
          source anchor 0 state space
  primitiveResponse :
    StageNinePrimitiveCauchyResponseAtLaw
      (fun trajectoryTime =>
        (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
          source anchor trajectoryTime state).primitive)
      0
      (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryRestartPrimitiveResponse
        source anchor 0 state)
  p286MomentumDerivative :
    ∀ space direction,
      HasDerivAt
        (fun trajectoryTime : ℝ =>
          (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
            source anchor trajectoryTime
            state).canonical.gravityGauge.p286.spatialBFMomentumEvaluation
              space direction)
        (sourceActionGeneratedP286SpatialBFMomentumVelocity
          source
          (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
            source anchor 0 state).primitive
          space direction)
        0
  lorentzMomentumDerivative :
    ∀ space direction,
      HasDerivAt
        (fun trajectoryTime : ℝ =>
          (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
            source anchor trajectoryTime
            state).canonical.gravityGauge.lorentz.spatialBFMomentumEvaluation
              space direction)
        (sourceActionGeneratedLorentzSpatialBFMomentumVelocity
          source
          (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
            source anchor 0 state).primitive
          space direction)
        0
  scalarMomentumDerivative :
    ∀ space direction,
      HasDerivAt
        (fun trajectoryTime : ℝ =>
          (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
            source anchor trajectoryTime
            state).canonical.scalar.temporalMomentumEvaluation
              space direction)
        (sourceActionGeneratedScalarTemporalMomentumVelocity
          source
          (sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
            source anchor 0 state).primitive
          space direction)
        0

/-- Frontier theorem: the full original trajectory response is exactly the
response recomputed from its generated origin state. -/
theorem
    sourceActionGeneratedCurrentTorsionFreeCartanOriginRestartConsistency_realizes
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState) :
    StageNineCurrentTorsionFreeCartanOriginRestartConsistencyLaw
      source anchor state := by
  have trajectoryZero :
      sourceActionGeneratedCurrentTorsionFreeCartanTrajectoryState
          source anchor 0 state =
        sourceActionGeneratedPrimitiveCanonicalCurrent source anchor state :=
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_zero
      source anchor state
  exact
    { responseEquality :=
        sourceActionGeneratedCurrentTorsionFreeCartan_originResponse_eq_restartResponse
          source anchor state
      primitiveResponse :=
        sourceActionGeneratedCurrentTorsionFreeCartanTrajectory_hasOriginRestartPrimitiveResponse
          source anchor state
      p286MomentumDerivative := fun space direction => by
        rw [trajectoryZero]
        exact
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_p286MomentumHasDerivAt
            source anchor 0 state space direction
      lorentzMomentumDerivative := fun space direction => by
        rw [trajectoryZero]
        exact
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_lorentzMomentumHasDerivAt
            source anchor 0 state space direction
      scalarMomentumDerivative := fun space direction => by
        rw [trajectoryZero]
        exact
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_scalarMomentumHasDerivAt
            source anchor 0 state space direction }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedCurrentTorsionFreeCartanOriginRestartConsistency
