import H0mework.Physics.ActionGeneration.PrimitiveCanonicalSplitDevelopment

/-!
# S9-C3h126: source/action-generated primitive--canonical relative Euler development

C3h125 computes a primitive actual path and a native canonical action path
from the same source, primitive state, and physical time.  A genuine restart
cannot simply call that constructor again on the current primitive
projection: doing so would recompute the canonical momentum base point from
the primitive BF fields and discard the canonical momentum already generated
along the preceding path.

This module therefore defines the history-preserving relative action step:

```text
current primitive/canonical split
→ recompute every action tangent from current.primitive
→ primitive⁺ := current-state actual Euler step
→ canonical⁺ := current.canonical + step * current-state action tangent
→ shared-coordinate synchronization
→ later equation/residual acceptance.
```

The primitive and canonical outputs are generated before any acceptance
law.  In particular, no residual, endpoint, inverse image, quotient
representative, shell witness, stationarity receipt, or branch selector
enters the update.  This is an explicit current-state Euler development, not
an exact nonlinear flow: no semigroup, cocycle with the earlier affine path,
well-posedness, or on-shell claim is made here.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineJointActionCanonicalPhasePathLaw
open StageNineJointActionCanonicalPhaseUpdate
open StageNineJointActionLocalActualLift
open StageNineLorentzActionCanonicalPairUpdate
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineScalarActionCanonicalMomentumUpdate
open StageNineSourceActionGeneratedJointPrimitiveCauchyDevelopment
open StageNineSourceActionGeneratedJointPrimitiveCauchyUpdate
open StageNineSourceActionGeneratedPrimitiveCanonicalSplitDevelopment
open StageNineSourceGeneratedMatterSpinActionUpdate
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

/-! ## History-preserving canonical sector steps -/

def sourceActionGeneratedP286CanonicalRelativeEulerUpdate
    (source : SmoothUnifiedSource)
    (step : ℝ)
    (primitive : StageNineCauchyState)
    (current : StageNineP286CanonicalPhaseState) :
    StageNineP286CanonicalPhaseState where
  spatialConnection := fun space direction =>
    current.spatialConnection space direction +
      step •
        (sourceActionGeneratedP286CanonicalPhaseVelocity
          source primitive).spatialConnection space direction
  spatialBFMomentumEvaluation := fun space direction =>
    current.spatialBFMomentumEvaluation space direction +
      step *
        (sourceActionGeneratedP286CanonicalPhaseVelocity
          source primitive).spatialBFMomentumEvaluation space direction

def sourceActionGeneratedLorentzCanonicalRelativeEulerUpdate
    (source : SmoothUnifiedSource)
    (step : ℝ)
    (primitive : StageNineCauchyState)
    (current : StageNineLorentzCanonicalPhaseState) :
    StageNineLorentzCanonicalPhaseState where
  spatialConnection := fun space direction internalPair =>
    current.spatialConnection space direction internalPair +
      step *
        (sourceActionGeneratedLorentzCanonicalPhaseVelocity
          source primitive).spatialConnection
            space direction internalPair
  spatialBFMomentumEvaluation := fun space direction =>
    current.spatialBFMomentumEvaluation space direction +
      step *
        (sourceActionGeneratedLorentzCanonicalPhaseVelocity
          source primitive).spatialBFMomentumEvaluation space direction

def sourceActionGeneratedScalarCanonicalRelativeEulerUpdate
    (source : SmoothUnifiedSource)
    (step : ℝ)
    (primitive : StageNineCauchyState)
    (current : StageNineScalarCanonicalPhaseState) :
    StageNineScalarCanonicalPhaseState where
  scalarCoordinate := fun space =>
    current.scalarCoordinate space +
      step •
        (sourceActionGeneratedScalarCanonicalPhaseVelocity
          source primitive).scalarCoordinate space
  temporalMomentumEvaluation := fun space direction =>
    current.temporalMomentumEvaluation space direction +
      step *
        (sourceActionGeneratedScalarCanonicalPhaseVelocity
          source primitive).temporalMomentumEvaluation space direction

/-- Advance every native canonical action coordinate from its already
generated current value.  The tangent is recomputed from the current
primitive state; no canonical momentum is reset from a primitive readout. -/
def sourceActionGeneratedJointCanonicalRelativeEulerUpdate
    (source : SmoothUnifiedSource)
    (step : ℝ)
    (current : StageNinePrimitiveCanonicalSplitActionState) :
    StageNineJointCanonicalPhaseState where
  frozenCoframeSnapshot := current.canonical.frozenCoframeSnapshot
  gravitySimplicityMultiplier :=
    current.canonical.gravitySimplicityMultiplier
  temporalGravityConnection :=
    current.canonical.temporalGravityConnection
  temporalGaugeConnection :=
    current.canonical.temporalGaugeConnection
  gravityGauge :=
    { p286 :=
        sourceActionGeneratedP286CanonicalRelativeEulerUpdate
          source step current.primitive current.canonical.gravityGauge.p286
      lorentz :=
        sourceActionGeneratedLorentzCanonicalRelativeEulerUpdate
          source step current.primitive
          current.canonical.gravityGauge.lorentz }
  scalar :=
    sourceActionGeneratedScalarCanonicalRelativeEulerUpdate
      source step current.primitive current.canonical.scalar
  matter := fun space =>
    current.canonical.matter space +
      step • actionGeneratedMatterRawTimeVelocity
        current.primitive space
  conjugateMatter := fun space =>
    current.canonical.conjugateMatter space +
      step • actionGeneratedConjugateMatterTimeDerivative
        current.primitive space

/-- One explicit current-state primitive/canonical Euler step. -/
def sourceActionGeneratedPrimitiveCanonicalRelativeEulerUpdate
    (source : SmoothUnifiedSource)
    (step : ℝ)
    (current : StageNinePrimitiveCanonicalSplitActionState) :
    StageNinePrimitiveCanonicalSplitActionState where
  primitive :=
    sourceActionGeneratedJointPrimitiveCauchyUpdate
      source step current.primitive
  canonical :=
    sourceActionGeneratedJointCanonicalRelativeEulerUpdate
      source step current

/-! ## Source-generated current split -/

def sourceActionGeneratedPrimitiveCanonicalCurrent
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState) :
    StageNinePrimitiveCanonicalSplitActionState :=
  sourceActionGeneratedPrimitiveCanonicalSplitUpdate
    source anchor state

def sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
    (source : SmoothUnifiedSource)
    (anchor step : ℝ)
    (state : StageNineCauchyState) :
    StageNinePrimitiveCanonicalSplitActionState :=
  sourceActionGeneratedPrimitiveCanonicalRelativeEulerUpdate
    source step
    (sourceActionGeneratedPrimitiveCanonicalCurrent source anchor state)

@[simp] theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_primitive
    (source : SmoothUnifiedSource)
    (anchor step : ℝ)
    (state : StageNineCauchyState) :
    (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
      source anchor step state).primitive =
      sourceActionGeneratedJointPrimitiveCauchyUpdate
        source step
        (sourceActionGeneratedPrimitiveCanonicalCurrent
          source anchor state).primitive :=
  rfl

@[simp] theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_conjugateMatter
    (source : SmoothUnifiedSource)
    (anchor step : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
      source anchor step state).canonical.conjugateMatter space =
      (sourceActionGeneratedPrimitiveCanonicalCurrent
          source anchor state).canonical.conjugateMatter space +
        step • actionGeneratedConjugateMatterTimeDerivative
          (sourceActionGeneratedPrimitiveCanonicalCurrent
            source anchor state).primitive space :=
  rfl

/-! ## Zero-step and action-preparation laws -/

@[simp] theorem sourceActionGeneratedJointCanonicalRelativeEulerUpdate_zero
    (source : SmoothUnifiedSource)
    (current : StageNinePrimitiveCanonicalSplitActionState) :
    sourceActionGeneratedJointCanonicalRelativeEulerUpdate
        source 0 current =
      current.canonical := by
  apply StageNineJointCanonicalPhaseState.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · apply StageNineGravityGaugeCanonicalPhaseState.ext
    · apply StageNineP286CanonicalPhaseState.ext <;>
        funext space direction <;>
        simp [sourceActionGeneratedJointCanonicalRelativeEulerUpdate,
          sourceActionGeneratedP286CanonicalRelativeEulerUpdate]
    · apply StageNineLorentzCanonicalPhaseState.ext
      · funext space direction internalPair
        simp [sourceActionGeneratedJointCanonicalRelativeEulerUpdate,
          sourceActionGeneratedLorentzCanonicalRelativeEulerUpdate]
      · funext space direction
        simp [sourceActionGeneratedJointCanonicalRelativeEulerUpdate,
          sourceActionGeneratedLorentzCanonicalRelativeEulerUpdate]
  · apply StageNineScalarCanonicalPhaseState.ext
    · funext space
      simp [sourceActionGeneratedJointCanonicalRelativeEulerUpdate,
        sourceActionGeneratedScalarCanonicalRelativeEulerUpdate]
    · funext space direction
      simp [sourceActionGeneratedJointCanonicalRelativeEulerUpdate,
        sourceActionGeneratedScalarCanonicalRelativeEulerUpdate]
  · funext space
    change
      current.canonical.matter space +
          (0 : ℝ) • actionGeneratedMatterRawTimeVelocity
            current.primitive space =
        current.canonical.matter space
    module
  · funext space
    simp [sourceActionGeneratedJointCanonicalRelativeEulerUpdate]

theorem
    sourceActionGeneratedJointPrimitiveCauchyUpdate_actionPrepared
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState) :
    sourceActionGeneratedJointPrimitiveActionInitialState
        (sourceActionGeneratedJointPrimitiveCauchyUpdate
          source anchor state) =
      sourceActionGeneratedJointPrimitiveCauchyUpdate
        source anchor state := by
  apply StageNineCauchyState.ext
  · funext space
    rfl
  · funext space
    rfl
  · funext space
    rfl
  · funext space
    rfl
  · funext space
    rfl
  · funext space
    rfl
  · funext space
    rfl
  · funext space
    rfl
  · funext space
    rfl
  · funext space
    rfl

@[simp] theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_zero
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState) :
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
        source anchor 0 state =
      sourceActionGeneratedPrimitiveCanonicalCurrent
        source anchor state := by
  apply StageNinePrimitiveCanonicalSplitActionState.ext
  · simp only [
      sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment,
      sourceActionGeneratedPrimitiveCanonicalRelativeEulerUpdate,
      sourceActionGeneratedPrimitiveCanonicalCurrent]
    rw [sourceActionGeneratedJointPrimitiveCauchyUpdate_zero]
    exact sourceActionGeneratedJointPrimitiveCauchyUpdate_actionPrepared
      source anchor state
  · exact
      sourceActionGeneratedJointCanonicalRelativeEulerUpdate_zero
        source
        (sourceActionGeneratedPrimitiveCanonicalCurrent
          source anchor state)

/-! ## Shared-coordinate synchronization after the relative step -/

theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_coframe_sync
    (source : SmoothUnifiedSource)
    (anchor step : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
      source anchor step state).primitive.coframe space =
      (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
        source anchor step state).canonical.frozenCoframeSnapshot space := by
  let current :=
    sourceActionGeneratedPrimitiveCanonicalCurrent source anchor state
  have currentSync :=
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_coframe_sync
      source anchor state space
  change
    current.primitive.coframe space =
      current.canonical.frozenCoframeSnapshot space at currentSync
  have nextSync :=
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_coframe_sync
      source step current.primitive space
  change
    (sourceActionGeneratedJointPrimitiveCauchyUpdate
      source step current.primitive).coframe space =
      current.canonical.frozenCoframeSnapshot space
  calc
    _ =
        (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
          source step
          current.primitive).canonical.frozenCoframeSnapshot space :=
      nextSync
    _ = current.primitive.coframe space := rfl
    _ = current.canonical.frozenCoframeSnapshot space := currentSync

theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_multiplier_sync
    (source : SmoothUnifiedSource)
    (anchor step : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
      source anchor step
      state).primitive.gravitySimplicityMultiplier space =
      (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
        source anchor step
        state).canonical.gravitySimplicityMultiplier space := by
  let current :=
    sourceActionGeneratedPrimitiveCanonicalCurrent source anchor state
  have currentSync :=
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_multiplier_sync
      source anchor state space
  change
    current.primitive.gravitySimplicityMultiplier space =
      current.canonical.gravitySimplicityMultiplier space at currentSync
  have nextSync :=
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_multiplier_sync
      source step current.primitive space
  change
    (sourceActionGeneratedJointPrimitiveCauchyUpdate
      source step
      current.primitive).gravitySimplicityMultiplier space =
      current.canonical.gravitySimplicityMultiplier space
  calc
    _ =
        (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
          source step
          current.primitive).canonical.gravitySimplicityMultiplier space :=
      nextSync
    _ = current.primitive.gravitySimplicityMultiplier space := rfl
    _ = current.canonical.gravitySimplicityMultiplier space := currentSync

theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_temporalLorentz_sync
    (source : SmoothUnifiedSource)
    (anchor step : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (internalPair : Fin 6) :
    loweredLorentzConnectionCoefficient
        ((sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
          source anchor step state).primitive.gravityConnection space)
        canonicalLorentzianTimeDirection internalPair =
      (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
        source anchor step state).canonical.temporalGravityConnection
          space internalPair := by
  let current :=
    sourceActionGeneratedPrimitiveCanonicalCurrent source anchor state
  have currentSync :=
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_temporalLorentz_sync
      source anchor state space internalPair
  change
    loweredLorentzConnectionCoefficient
        (current.primitive.gravityConnection space)
        canonicalLorentzianTimeDirection internalPair =
      current.canonical.temporalGravityConnection
        space internalPair at currentSync
  have nextSync :=
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_temporalLorentz_sync
      source step current.primitive space internalPair
  change
    loweredLorentzConnectionCoefficient
        ((sourceActionGeneratedJointPrimitiveCauchyUpdate
          source step current.primitive).gravityConnection space)
        canonicalLorentzianTimeDirection internalPair =
      current.canonical.temporalGravityConnection space internalPair
  calc
    _ =
        (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
          source step current.primitive).canonical.temporalGravityConnection
            space internalPair := nextSync
    _ =
        loweredLorentzConnectionCoefficient
            (current.primitive.gravityConnection space)
            canonicalLorentzianTimeDirection internalPair := rfl
    _ = current.canonical.temporalGravityConnection space internalPair :=
      currentSync

theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_spatialLorentz_sync
    (source : SmoothUnifiedSource)
    (anchor step : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (internalPair : Fin 6) :
    loweredLorentzConnectionCoefficient
        ((sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
          source anchor step state).primitive.gravityConnection space)
        direction.succ internalPair =
      (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
        source anchor step
        state).canonical.gravityGauge.lorentz.spatialConnection
          space direction internalPair := by
  let current :=
    sourceActionGeneratedPrimitiveCanonicalCurrent source anchor state
  have currentSync :=
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_spatialLorentz_sync
      source anchor state space direction internalPair
  change
    loweredLorentzConnectionCoefficient
        (current.primitive.gravityConnection space)
        direction.succ internalPair =
      current.canonical.gravityGauge.lorentz.spatialConnection
        space direction internalPair at currentSync
  have nextSync :=
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_spatialLorentz_sync
      source step current.primitive space direction internalPair
  change
    loweredLorentzConnectionCoefficient
        ((sourceActionGeneratedJointPrimitiveCauchyUpdate
          source step current.primitive).gravityConnection space)
        direction.succ internalPair =
      current.canonical.gravityGauge.lorentz.spatialConnection
            space direction internalPair +
        step *
          (sourceActionGeneratedLorentzCanonicalPhaseVelocity
            source current.primitive).spatialConnection
              space direction internalPair
  calc
    _ =
        (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
          source step
          current.primitive).canonical.gravityGauge.lorentz.spatialConnection
            space direction internalPair := nextSync
    _ =
        loweredLorentzConnectionCoefficient
            (current.primitive.gravityConnection space)
            direction.succ internalPair +
          step *
            (sourceActionGeneratedLorentzCanonicalPhaseVelocity
              source current.primitive).spatialConnection
                space direction internalPair := rfl
    _ =
        current.canonical.gravityGauge.lorentz.spatialConnection
              space direction internalPair +
          step *
            (sourceActionGeneratedLorentzCanonicalPhaseVelocity
              source current.primitive).spatialConnection
                space direction internalPair := by rw [currentSync]

theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_temporalP286_sync
    (source : SmoothUnifiedSource)
    (anchor step : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
      source anchor step state).primitive.gaugeConnection
        space canonicalLorentzianTimeDirection =
      (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
        source anchor step state).canonical.temporalGaugeConnection space := by
  let current :=
    sourceActionGeneratedPrimitiveCanonicalCurrent source anchor state
  have currentSync :=
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_temporalP286_sync
      source anchor state space
  change
    current.primitive.gaugeConnection
        space canonicalLorentzianTimeDirection =
      current.canonical.temporalGaugeConnection space at currentSync
  have nextSync :=
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_temporalP286_sync
      source step current.primitive space
  change
    (sourceActionGeneratedJointPrimitiveCauchyUpdate
      source step current.primitive).gaugeConnection
        space canonicalLorentzianTimeDirection =
      current.canonical.temporalGaugeConnection space
  calc
    _ =
        (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
          source step current.primitive).canonical.temporalGaugeConnection
            space := nextSync
    _ =
        current.primitive.gaugeConnection
          space canonicalLorentzianTimeDirection := rfl
    _ = current.canonical.temporalGaugeConnection space := currentSync

theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_spatialP286_sync
    (source : SmoothUnifiedSource)
    (anchor step : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    p286CoordinateEquiv
        ((sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
          source anchor step state).primitive.gaugeConnection
            space direction.succ) =
      (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
        source anchor step
        state).canonical.gravityGauge.p286.spatialConnection
          space direction := by
  let current :=
    sourceActionGeneratedPrimitiveCanonicalCurrent source anchor state
  have currentSync :
      p286CoordinateEquiv
          (current.primitive.gaugeConnection space direction.succ) =
        current.canonical.gravityGauge.p286.spatialConnection
          space direction := by
    exact
      sourceActionGeneratedPrimitiveCanonicalSplitUpdate_spatialP286_sync
        source anchor state space direction
  have nextSync :
      p286CoordinateEquiv
          ((sourceActionGeneratedPrimitiveCanonicalSplitUpdate
            source step current.primitive).primitive.gaugeConnection
              space direction.succ) =
        (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
          source step
          current.primitive).canonical.gravityGauge.p286.spatialConnection
            space direction :=
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_spatialP286_sync
      source step current.primitive space direction
  change
    p286CoordinateEquiv
        ((sourceActionGeneratedJointPrimitiveCauchyUpdate
          source step current.primitive).gaugeConnection
            space direction.succ) =
      current.canonical.gravityGauge.p286.spatialConnection
          space direction +
        step •
          (sourceActionGeneratedP286CanonicalPhaseVelocity
            source current.primitive).spatialConnection space direction
  calc
    _ =
        (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
          source step
          current.primitive).canonical.gravityGauge.p286.spatialConnection
            space direction := nextSync
    _ =
        p286CoordinateEquiv
            (current.primitive.gaugeConnection space direction.succ) +
          step •
            (sourceActionGeneratedP286CanonicalPhaseVelocity
              source current.primitive).spatialConnection
                space direction := rfl
    _ =
        current.canonical.gravityGauge.p286.spatialConnection
            space direction +
          step •
            (sourceActionGeneratedP286CanonicalPhaseVelocity
              source current.primitive).spatialConnection
                space direction := by rw [currentSync]

theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_scalar_sync
    (source : SmoothUnifiedSource)
    (anchor step : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
      source anchor step state).primitive.scalar space =
      (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
        source anchor step state).canonical.scalar.scalarCoordinate space := by
  let current :=
    sourceActionGeneratedPrimitiveCanonicalCurrent source anchor state
  have currentSync :=
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_scalar_sync
      source anchor state space
  change
    current.primitive.scalar space =
      current.canonical.scalar.scalarCoordinate space at currentSync
  have nextSync :=
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_scalar_sync
      source step current.primitive space
  change
    (sourceActionGeneratedJointPrimitiveCauchyUpdate
      source step current.primitive).scalar space =
      current.canonical.scalar.scalarCoordinate space +
        step •
          (sourceActionGeneratedScalarCanonicalPhaseVelocity
            source current.primitive).scalarCoordinate space
  calc
    _ =
        (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
          source step current.primitive).canonical.scalar.scalarCoordinate
            space := nextSync
    _ =
        current.primitive.scalar space +
          step •
            (sourceActionGeneratedScalarCanonicalPhaseVelocity
              source current.primitive).scalarCoordinate space := rfl
    _ =
        current.canonical.scalar.scalarCoordinate space +
          step •
            (sourceActionGeneratedScalarCanonicalPhaseVelocity
              source current.primitive).scalarCoordinate space := by
      rw [currentSync]

theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_matter_sync
    (source : SmoothUnifiedSource)
    (anchor step : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
      source anchor step state).primitive.matter space =
      (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
        source anchor step state).canonical.matter space := by
  let current :=
    sourceActionGeneratedPrimitiveCanonicalCurrent source anchor state
  have currentSync :=
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_matter_sync
      source anchor state space
  change
    current.primitive.matter space =
      current.canonical.matter space at currentSync
  have nextSync :=
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_matter_sync
      source step current.primitive space
  change
    (sourceActionGeneratedJointPrimitiveCauchyUpdate
      source step current.primitive).matter space =
      current.canonical.matter space +
        step • actionGeneratedMatterRawTimeVelocity
          current.primitive space
  calc
    _ =
        (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
          source step current.primitive).canonical.matter space :=
      nextSync
    _ =
        current.primitive.matter space +
          step • actionGeneratedMatterRawTimeVelocity
            current.primitive space := rfl
    _ =
        current.canonical.matter space +
          step • actionGeneratedMatterRawTimeVelocity
            current.primitive space := by rw [currentSync]

private theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerUpdate_conjugateMatter_sync_of
    (source : SmoothUnifiedSource)
    (step : ℝ)
    (current : StageNinePrimitiveCanonicalSplitActionState)
    (space : StageNineSpatialPoint)
    (matter : DiracExteriorMatterCarrier)
    (currentSync :
      current.primitive.conjugateMatter space =
        current.canonical.conjugateMatter space) :
    (sourceActionGeneratedPrimitiveCanonicalRelativeEulerUpdate
      source step current).primitive.conjugateMatter space matter =
      (sourceActionGeneratedPrimitiveCanonicalRelativeEulerUpdate
        source step current).canonical.conjugateMatter space matter := by
  have nextSyncMap :=
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_conjugateMatter_sync
      source step current.primitive space
  have nextSync :
      (sourceActionGeneratedJointPrimitiveCauchyUpdate
          source step current.primitive).conjugateMatter space matter =
        (sourceActionGeneratedPrimitiveCanonicalSplitUpdate
          source step
          current.primitive).canonical.conjugateMatter space matter :=
    congrArg (fun dual => dual matter) nextSyncMap
  change
    (sourceActionGeneratedJointPrimitiveCauchyUpdate
      source step current.primitive).conjugateMatter space matter =
      (current.canonical.conjugateMatter space +
        step • actionGeneratedConjugateMatterTimeDerivative
          current.primitive space) matter
  rw [nextSync]
  change
    (current.primitive.conjugateMatter space +
        step • actionGeneratedConjugateMatterTimeDerivative
          current.primitive space) matter =
      (current.canonical.conjugateMatter space +
        step • actionGeneratedConjugateMatterTimeDerivative
          current.primitive space) matter
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [congrArg (fun dual => dual matter) currentSync]

theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_conjugateMatter_sync
    (source : SmoothUnifiedSource)
    (anchor step : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (matter : DiracExteriorMatterCarrier) :
    (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
      source anchor step state).primitive.conjugateMatter space matter =
      (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
        source anchor step state).canonical.conjugateMatter space matter := by
  apply
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerUpdate_conjugateMatter_sync_of
  exact
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_conjugateMatter_sync
      source anchor state space

theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_p286Momentum_increment
    (source : SmoothUnifiedSource)
    (anchor step : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : P286SpatialGaugeDirection) :
    (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
          source anchor step
          state).canonical.gravityGauge.p286.spatialBFMomentumEvaluation
          space direction -
        (sourceActionGeneratedPrimitiveCanonicalCurrent
          source anchor
          state).canonical.gravityGauge.p286.spatialBFMomentumEvaluation
          space direction =
      step *
        sourceActionGeneratedP286SpatialBFMomentumVelocity
          source
          (sourceActionGeneratedPrimitiveCanonicalCurrent
            source anchor state).primitive
          space direction := by
  simp [sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment,
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerUpdate,
    sourceActionGeneratedJointCanonicalRelativeEulerUpdate,
    sourceActionGeneratedP286CanonicalRelativeEulerUpdate,
    sourceActionGeneratedP286CanonicalPhaseVelocity]

theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_p286Momentum_hasDerivAt
    (source : SmoothUnifiedSource)
    (anchor time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : P286SpatialGaugeDirection) :
    HasDerivAt
        (fun step : ℝ =>
          (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
            source anchor step
            state).canonical.gravityGauge.p286.spatialBFMomentumEvaluation
              space direction)
        (sourceActionGeneratedP286SpatialBFMomentumVelocity
          source
          (sourceActionGeneratedPrimitiveCanonicalCurrent
            source anchor state).primitive
          space direction)
        time := by
  change HasDerivAt
    (fun step : ℝ =>
      (sourceActionGeneratedPrimitiveCanonicalCurrent
            source anchor
            state).canonical.gravityGauge.p286.spatialBFMomentumEvaluation
          space direction +
        step *
          sourceActionGeneratedP286SpatialBFMomentumVelocity
            source
            (sourceActionGeneratedPrimitiveCanonicalCurrent
              source anchor state).primitive
            space direction)
    _ time
  simpa only [smul_eq_mul] using
    hasDerivAt_const_add_time_smul
      ((sourceActionGeneratedPrimitiveCanonicalCurrent
            source anchor
            state).canonical.gravityGauge.p286.spatialBFMomentumEvaluation
          space direction)
      (sourceActionGeneratedP286SpatialBFMomentumVelocity
        source
        (sourceActionGeneratedPrimitiveCanonicalCurrent
          source anchor state).primitive
        space direction)
      time

theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_lorentzMomentum_increment
    (source : SmoothUnifiedSource)
    (anchor step : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzSpatialBivectorDirection) :
    (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
          source anchor step
          state).canonical.gravityGauge.lorentz.spatialBFMomentumEvaluation
          space direction -
        (sourceActionGeneratedPrimitiveCanonicalCurrent
          source anchor
          state).canonical.gravityGauge.lorentz.spatialBFMomentumEvaluation
          space direction =
      step *
        sourceActionGeneratedLorentzSpatialBFMomentumVelocity
          source
          (sourceActionGeneratedPrimitiveCanonicalCurrent
            source anchor state).primitive
          space direction := by
  simp [sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment,
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerUpdate,
    sourceActionGeneratedJointCanonicalRelativeEulerUpdate,
    sourceActionGeneratedLorentzCanonicalRelativeEulerUpdate,
    sourceActionGeneratedLorentzCanonicalPhaseVelocity]

theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_lorentzMomentum_hasDerivAt
    (source : SmoothUnifiedSource)
    (anchor time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzSpatialBivectorDirection) :
    HasDerivAt
        (fun step : ℝ =>
          (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
            source anchor step
            state).canonical.gravityGauge.lorentz.spatialBFMomentumEvaluation
              space direction)
        (sourceActionGeneratedLorentzSpatialBFMomentumVelocity
          source
          (sourceActionGeneratedPrimitiveCanonicalCurrent
            source anchor state).primitive
          space direction)
        time := by
  change HasDerivAt
    (fun step : ℝ =>
      (sourceActionGeneratedPrimitiveCanonicalCurrent
            source anchor
            state).canonical.gravityGauge.lorentz.spatialBFMomentumEvaluation
          space direction +
        step *
          sourceActionGeneratedLorentzSpatialBFMomentumVelocity
            source
            (sourceActionGeneratedPrimitiveCanonicalCurrent
              source anchor state).primitive
            space direction)
    _ time
  simpa only [smul_eq_mul] using
    hasDerivAt_const_add_time_smul
      ((sourceActionGeneratedPrimitiveCanonicalCurrent
            source anchor
            state).canonical.gravityGauge.lorentz.spatialBFMomentumEvaluation
          space direction)
      (sourceActionGeneratedLorentzSpatialBFMomentumVelocity
        source
        (sourceActionGeneratedPrimitiveCanonicalCurrent
          source anchor state).primitive
        space direction)
      time

theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_scalarMomentum_increment
    (source : SmoothUnifiedSource)
    (anchor step : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
          source anchor step
          state).canonical.scalar.temporalMomentumEvaluation
          space direction -
        (sourceActionGeneratedPrimitiveCanonicalCurrent
          source anchor state).canonical.scalar.temporalMomentumEvaluation
          space direction =
      step *
        sourceActionGeneratedScalarTemporalMomentumVelocity
          source
          (sourceActionGeneratedPrimitiveCanonicalCurrent
            source anchor state).primitive
          space direction := by
  simp [sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment,
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerUpdate,
    sourceActionGeneratedJointCanonicalRelativeEulerUpdate,
    sourceActionGeneratedScalarCanonicalRelativeEulerUpdate,
    sourceActionGeneratedScalarCanonicalPhaseVelocity]

theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_scalarMomentum_hasDerivAt
    (source : SmoothUnifiedSource)
    (anchor time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    HasDerivAt
        (fun step : ℝ =>
          (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
            source anchor step
            state).canonical.scalar.temporalMomentumEvaluation
              space direction)
        (sourceActionGeneratedScalarTemporalMomentumVelocity
          source
          (sourceActionGeneratedPrimitiveCanonicalCurrent
            source anchor state).primitive
          space direction)
        time := by
  change HasDerivAt
    (fun step : ℝ =>
      (sourceActionGeneratedPrimitiveCanonicalCurrent
            source anchor
            state).canonical.scalar.temporalMomentumEvaluation
          space direction +
        step *
          sourceActionGeneratedScalarTemporalMomentumVelocity
            source
            (sourceActionGeneratedPrimitiveCanonicalCurrent
              source anchor state).primitive
            space direction)
    _ time
  simpa only [smul_eq_mul] using
    hasDerivAt_const_add_time_smul
      ((sourceActionGeneratedPrimitiveCanonicalCurrent
            source anchor
            state).canonical.scalar.temporalMomentumEvaluation
          space direction)
      (sourceActionGeneratedScalarTemporalMomentumVelocity
        source
        (sourceActionGeneratedPrimitiveCanonicalCurrent
          source anchor state).primitive
        space direction)
      time

/-! ## Bundled current-state relative development -/

theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_hasPrimitiveDevelopment
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState) :
    StageNineJointPrimitiveFrozenInputActionCauchyDevelopmentLaw
      source
      (sourceActionGeneratedPrimitiveCanonicalCurrent
        source anchor state).primitive
      (fun step =>
        (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
          source anchor step state).primitive) := by
  simpa [sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment,
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerUpdate] using
    sourceActionGeneratedJointPrimitiveCauchyUpdate_hasFrozenInputDevelopment
      source
      (sourceActionGeneratedPrimitiveCanonicalCurrent
        source anchor state).primitive

/-- The current split is generated first.  The relative step then preserves
that canonical base point, recomputes all action tangents from the current
primitive state, and keeps every shared coordinate synchronized. -/
structure StageNinePrimitiveCanonicalRelativeEulerDevelopmentLaw
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState)
    (update : ℝ → StageNinePrimitiveCanonicalSplitActionState) : Prop where
  updateGenerated :
    update =
      fun step =>
        sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
          source anchor step state
  zero :
    update 0 =
      sourceActionGeneratedPrimitiveCanonicalCurrent source anchor state
  primitiveDevelopment :
    StageNineJointPrimitiveFrozenInputActionCauchyDevelopmentLaw
      source
      (sourceActionGeneratedPrimitiveCanonicalCurrent
        source anchor state).primitive
      (fun step => (update step).primitive)
  coframeSync :
    ∀ step space,
      (update step).primitive.coframe space =
        (update step).canonical.frozenCoframeSnapshot space
  multiplierSync :
    ∀ step space,
      (update step).primitive.gravitySimplicityMultiplier space =
        (update step).canonical.gravitySimplicityMultiplier space
  temporalLorentzSync :
    ∀ step space internalPair,
      loweredLorentzConnectionCoefficient
          ((update step).primitive.gravityConnection space)
          canonicalLorentzianTimeDirection internalPair =
        (update step).canonical.temporalGravityConnection
          space internalPair
  spatialLorentzSync :
    ∀ step space direction internalPair,
      loweredLorentzConnectionCoefficient
          ((update step).primitive.gravityConnection space)
          direction.succ internalPair =
        (update step).canonical.gravityGauge.lorentz.spatialConnection
          space direction internalPair
  temporalP286Sync :
    ∀ step space,
      (update step).primitive.gaugeConnection
          space canonicalLorentzianTimeDirection =
        (update step).canonical.temporalGaugeConnection space
  spatialP286Sync :
    ∀ step space direction,
      p286CoordinateEquiv
          ((update step).primitive.gaugeConnection
            space direction.succ) =
        (update step).canonical.gravityGauge.p286.spatialConnection
          space direction
  scalarSync :
    ∀ step space,
      (update step).primitive.scalar space =
        (update step).canonical.scalar.scalarCoordinate space
  matterSync :
    ∀ step space,
      (update step).primitive.matter space =
        (update step).canonical.matter space
  conjugateMatterSync :
    ∀ step space matter,
      (update step).primitive.conjugateMatter space matter =
        (update step).canonical.conjugateMatter space matter
  p286MomentumDerivative :
    ∀ time space direction,
      HasDerivAt
        (fun step : ℝ =>
          (update step).canonical.gravityGauge.p286.spatialBFMomentumEvaluation
            space direction)
        (sourceActionGeneratedP286SpatialBFMomentumVelocity
          source
          (sourceActionGeneratedPrimitiveCanonicalCurrent
            source anchor state).primitive
          space direction)
        time
  lorentzMomentumDerivative :
    ∀ time space direction,
      HasDerivAt
        (fun step : ℝ =>
          (update step).canonical.gravityGauge.lorentz.spatialBFMomentumEvaluation
            space direction)
        (sourceActionGeneratedLorentzSpatialBFMomentumVelocity
          source
          (sourceActionGeneratedPrimitiveCanonicalCurrent
            source anchor state).primitive
          space direction)
        time
  scalarMomentumDerivative :
    ∀ time space direction,
      HasDerivAt
        (fun step : ℝ =>
          (update step).canonical.scalar.temporalMomentumEvaluation
            space direction)
        (sourceActionGeneratedScalarTemporalMomentumVelocity
          source
          (sourceActionGeneratedPrimitiveCanonicalCurrent
            source anchor state).primitive
          space direction)
        time

/-- Frontier theorem: source and actual dynamics generate a current-state
relative step on the full primitive/canonical carrier before residual
acceptance. -/
theorem
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_realizes
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState) :
    StageNinePrimitiveCanonicalRelativeEulerDevelopmentLaw
      source anchor state
      (fun step =>
        sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
          source anchor step state) := by
  exact
    { updateGenerated := rfl
      zero :=
        sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_zero
          source anchor state
      primitiveDevelopment :=
        sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_hasPrimitiveDevelopment
          source anchor state
      coframeSync :=
        fun step space =>
          sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_coframe_sync
            source anchor step state space
      multiplierSync :=
        fun step space =>
          sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_multiplier_sync
            source anchor step state space
      temporalLorentzSync :=
        fun step space internalPair =>
          sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_temporalLorentz_sync
            source anchor step state space internalPair
      spatialLorentzSync :=
        fun step space direction internalPair =>
          sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_spatialLorentz_sync
            source anchor step state space direction internalPair
      temporalP286Sync :=
        fun step space =>
          sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_temporalP286_sync
            source anchor step state space
      spatialP286Sync :=
        fun step space direction =>
          sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_spatialP286_sync
            source anchor step state space direction
      scalarSync :=
        fun step space =>
          sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_scalar_sync
            source anchor step state space
      matterSync :=
        fun step space =>
          sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_matter_sync
            source anchor step state space
      conjugateMatterSync :=
        fun step space matter =>
          sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_conjugateMatter_sync
            source anchor step state space matter
      p286MomentumDerivative :=
        fun time space direction =>
          sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_p286Momentum_hasDerivAt
            source anchor time state space direction
      lorentzMomentumDerivative :=
        fun time space direction =>
          sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_lorentzMomentum_hasDerivAt
            source anchor time state space direction
      scalarMomentumDerivative :=
        fun time space direction =>
          sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_scalarMomentum_hasDerivAt
            source anchor time state space direction }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
