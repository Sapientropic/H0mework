import H0mework.Physics.CartanGeneration.PrimitiveSynchronizedResponse

/-!
# S9-C3h130: current Cartan primitive and canonical-momentum development

C3h129 generates and differentiates the complete Cartan-refined primitive
path.  C3h126 independently generates a history-preserving canonical Euler
response from the same current primitive/canonical split.  This module joins
those forward outputs:

```text
generated current split
├─ actual Cartan germs → primitive U_Cartan(relativeTime)
└─ current action tangent → canonical momentum relative update
→ coordinated primitive/canonical development
→ later equation/residual acceptance.
```

The dynamic coframe belongs to the primitive actual path.  The canonical
field named `frozenCoframeSnapshot` remains the anchor snapshot and records
provenance; it is not overwritten with an evolving coframe.  All other
shared canonical coordinates synchronize with the retained action fields of
the Cartan actual, while P286/Lorentz/scalar momenta retain their already
generated base values and current-state action derivatives.

No momentum is inverted into a primitive auxiliary, and no residual,
endpoint, preimage, shell witness, or branch certificate enters the
constructor.  The matter/dual coordinate synchronization retains the
existing identity-coframe formal-candidate boundary.  This is not an exact
flow, a Legendre-equivalence theorem, an on-shell law, or a nonzero-spin
Einstein--Cartan producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment

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
open StageNineSourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyDevelopment
open StageNineSourceActionGeneratedCurrentTorsionFreeCartanPrimitiveSynchronizedResponse
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

/-! ## Forward coordinated development -/

/-- One common relative-time development.  Both projections are computed
from the same generated current split; neither is caller supplied. -/
def sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
    (source : SmoothUnifiedSource)
    (anchor relativeTime : ℝ)
    (state : StageNineCauchyState) :
    StageNinePrimitiveCanonicalSplitActionState where
  primitive :=
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
      source anchor relativeTime state
  canonical :=
    sourceActionGeneratedJointCanonicalRelativeEulerUpdate
      source relativeTime
      (sourceActionGeneratedPrimitiveCanonicalCurrent
        source anchor state)

@[simp] theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_primitive
    (source : SmoothUnifiedSource)
    (anchor relativeTime : ℝ)
    (state : StageNineCauchyState) :
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
      source anchor relativeTime state).primitive =
      sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
        source anchor relativeTime state :=
  rfl

@[simp] theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_canonical
    (source : SmoothUnifiedSource)
    (anchor relativeTime : ℝ)
    (state : StageNineCauchyState) :
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
      source anchor relativeTime state).canonical =
      sourceActionGeneratedJointCanonicalRelativeEulerUpdate
        source relativeTime
        (sourceActionGeneratedPrimitiveCanonicalCurrent
          source anchor state) :=
  rfl

@[simp] theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_zero
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState) :
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
        source anchor 0 state =
      sourceActionGeneratedPrimitiveCanonicalCurrent
        source anchor state := by
  apply StageNinePrimitiveCanonicalSplitActionState.ext
  · exact
      sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate_zero
        source anchor state
  · exact
      sourceActionGeneratedJointCanonicalRelativeEulerUpdate_zero
        source
        (sourceActionGeneratedPrimitiveCanonicalCurrent
          source anchor state)

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_hasPrimitiveResponse
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState) :
    StageNineCurrentTorsionFreeCartanPrimitiveSynchronizedActionResponseLaw
      source anchor state
      (fun relativeTime =>
        (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
          source anchor relativeTime state).primitive) := by
  exact
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyDevelopment_hasSynchronizedActionResponse
      source anchor state

/-! ## Snapshot provenance and shared coordinates -/

/-- The canonical coframe field is deliberately the generated anchor
snapshot.  The evolving coframe remains owned by the primitive actual path. -/
theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_frozenCoframeProvenance
    (source : SmoothUnifiedSource)
    (anchor relativeTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
      source anchor relativeTime state).canonical.frozenCoframeSnapshot
        space =
      (sourceActionGeneratedPrimitiveCanonicalCurrent
        source anchor state).primitive.coframe space := by
  exact
    (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_coframe_sync
      source anchor relativeTime state space).symm

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_coframeInitialSync
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
      source anchor 0 state).primitive.coframe space =
      (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
        source anchor 0 state).canonical.frozenCoframeSnapshot space := by
  rw [
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_zero]
  exact
    sourceActionGeneratedPrimitiveCanonicalSplitUpdate_coframe_sync
      source anchor state space

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_multiplierSync
    (source : SmoothUnifiedSource)
    (anchor relativeTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
      source anchor relativeTime state).primitive.gravitySimplicityMultiplier
        space =
      (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
        source anchor relativeTime state).canonical.gravitySimplicityMultiplier
          space := by
  exact
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_multiplier_sync
      source anchor relativeTime state space

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_temporalLorentzSync
    (source : SmoothUnifiedSource)
    (anchor relativeTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (internalPair : Fin 6) :
    loweredLorentzConnectionCoefficient
        ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
          source anchor relativeTime state).primitive.gravityConnection space)
        canonicalLorentzianTimeDirection internalPair =
      (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
        source anchor relativeTime state).canonical.temporalGravityConnection
          space internalPair := by
  exact
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_temporalLorentz_sync
      source anchor relativeTime state space internalPair

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_spatialLorentzSync
    (source : SmoothUnifiedSource)
    (anchor relativeTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (internalPair : Fin 6) :
    loweredLorentzConnectionCoefficient
        ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
          source anchor relativeTime state).primitive.gravityConnection space)
        direction.succ internalPair =
      (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
        source anchor relativeTime
        state).canonical.gravityGauge.lorentz.spatialConnection
          space direction internalPair := by
  exact
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_spatialLorentz_sync
      source anchor relativeTime state space direction internalPair

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_temporalP286Sync
    (source : SmoothUnifiedSource)
    (anchor relativeTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
      source anchor relativeTime state).primitive.gaugeConnection
        space canonicalLorentzianTimeDirection =
      (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
        source anchor relativeTime state).canonical.temporalGaugeConnection
          space := by
  exact
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_temporalP286_sync
      source anchor relativeTime state space

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_spatialP286Sync
    (source : SmoothUnifiedSource)
    (anchor relativeTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    p286CoordinateEquiv
        ((sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
          source anchor relativeTime state).primitive.gaugeConnection
            space direction.succ) =
      (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
        source anchor relativeTime
        state).canonical.gravityGauge.p286.spatialConnection
          space direction := by
  exact
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_spatialP286_sync
      source anchor relativeTime state space direction

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_scalarSync
    (source : SmoothUnifiedSource)
    (anchor relativeTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
      source anchor relativeTime state).primitive.scalar space =
      (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
        source anchor relativeTime state).canonical.scalar.scalarCoordinate
          space := by
  exact
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_scalar_sync
      source anchor relativeTime state space

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_matterSync
    (source : SmoothUnifiedSource)
    (anchor relativeTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
      source anchor relativeTime state).primitive.matter space =
      (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
        source anchor relativeTime state).canonical.matter space := by
  exact
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_matter_sync
      source anchor relativeTime state space

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_conjugateMatterSync
    (source : SmoothUnifiedSource)
    (anchor relativeTime : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
      source anchor relativeTime state).primitive.conjugateMatter space =
      (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
        source anchor relativeTime state).canonical.conjugateMatter space := by
  apply LinearMap.ext
  intro matter
  change
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
      source anchor relativeTime state).conjugateMatter space matter =
      _
  rw [show
    (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCauchyUpdate
      source anchor relativeTime state).conjugateMatter space =
        (sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment
          source anchor relativeTime state).primitive.conjugateMatter space by
    rfl]
  exact
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_conjugateMatter_sync
      source anchor relativeTime state space matter

/-! ## History-preserving canonical momentum responses -/

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_p286MomentumHasDerivAt
    (source : SmoothUnifiedSource)
    (anchor time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : P286SpatialGaugeDirection) :
    HasDerivAt
      (fun relativeTime : ℝ =>
        (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
          source anchor relativeTime
          state).canonical.gravityGauge.p286.spatialBFMomentumEvaluation
            space direction)
      (sourceActionGeneratedP286SpatialBFMomentumVelocity
        source
        (sourceActionGeneratedPrimitiveCanonicalCurrent
          source anchor state).primitive
        space direction)
      time := by
  exact
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_p286Momentum_hasDerivAt
      source anchor time state space direction

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_lorentzMomentumHasDerivAt
    (source : SmoothUnifiedSource)
    (anchor time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzSpatialBivectorDirection) :
    HasDerivAt
      (fun relativeTime : ℝ =>
        (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
          source anchor relativeTime
          state).canonical.gravityGauge.lorentz.spatialBFMomentumEvaluation
            space direction)
      (sourceActionGeneratedLorentzSpatialBFMomentumVelocity
        source
        (sourceActionGeneratedPrimitiveCanonicalCurrent
          source anchor state).primitive
        space direction)
      time := by
  exact
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_lorentzMomentum_hasDerivAt
      source anchor time state space direction

theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_scalarMomentumHasDerivAt
    (source : SmoothUnifiedSource)
    (anchor time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    HasDerivAt
      (fun relativeTime : ℝ =>
        (sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
          source anchor relativeTime
          state).canonical.scalar.temporalMomentumEvaluation
            space direction)
      (sourceActionGeneratedScalarTemporalMomentumVelocity
        source
        (sourceActionGeneratedPrimitiveCanonicalCurrent
          source anchor state).primitive
        space direction)
      time := by
  exact
    sourceActionGeneratedPrimitiveCanonicalRelativeEulerDevelopment_scalarMomentum_hasDerivAt
      source anchor time state space direction

/-! ## Bundled producer law -/

/-- Complete forward coordination law.  The primitive actual response and
canonical momentum response are both generated before any equation or
residual inspection. -/
structure
    StageNineCurrentTorsionFreeCartanPrimitiveCanonicalDevelopmentLaw
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState)
    (development : ℝ → StageNinePrimitiveCanonicalSplitActionState) : Prop where
  generated :
    development =
      fun relativeTime =>
        sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
          source anchor relativeTime state
  currentInitial :
    development 0 =
      sourceActionGeneratedPrimitiveCanonicalCurrent
        source anchor state
  primitiveResponse :
    StageNineCurrentTorsionFreeCartanPrimitiveSynchronizedActionResponseLaw
      source anchor state
      (fun relativeTime => (development relativeTime).primitive)
  canonicalGenerated :
    ∀ relativeTime,
      (development relativeTime).canonical =
        sourceActionGeneratedJointCanonicalRelativeEulerUpdate
          source relativeTime
          (sourceActionGeneratedPrimitiveCanonicalCurrent
            source anchor state)
  frozenCoframeProvenance :
    ∀ relativeTime space,
      (development relativeTime).canonical.frozenCoframeSnapshot space =
        (sourceActionGeneratedPrimitiveCanonicalCurrent
          source anchor state).primitive.coframe space
  coframeInitialSync :
    ∀ space,
      (development 0).primitive.coframe space =
        (development 0).canonical.frozenCoframeSnapshot space
  multiplierSync :
    ∀ relativeTime space,
      (development relativeTime).primitive.gravitySimplicityMultiplier
          space =
        (development relativeTime).canonical.gravitySimplicityMultiplier
          space
  temporalLorentzSync :
    ∀ relativeTime space internalPair,
      loweredLorentzConnectionCoefficient
          ((development relativeTime).primitive.gravityConnection space)
          canonicalLorentzianTimeDirection internalPair =
        (development relativeTime).canonical.temporalGravityConnection
          space internalPair
  spatialLorentzSync :
    ∀ relativeTime space direction internalPair,
      loweredLorentzConnectionCoefficient
          ((development relativeTime).primitive.gravityConnection space)
          direction.succ internalPair =
        (development relativeTime
          ).canonical.gravityGauge.lorentz.spatialConnection
            space direction internalPair
  temporalP286Sync :
    ∀ relativeTime space,
      (development relativeTime).primitive.gaugeConnection
          space canonicalLorentzianTimeDirection =
        (development relativeTime).canonical.temporalGaugeConnection space
  spatialP286Sync :
    ∀ relativeTime space direction,
      p286CoordinateEquiv
          ((development relativeTime).primitive.gaugeConnection
            space direction.succ) =
        (development relativeTime
          ).canonical.gravityGauge.p286.spatialConnection
            space direction
  scalarSync :
    ∀ relativeTime space,
      (development relativeTime).primitive.scalar space =
        (development relativeTime).canonical.scalar.scalarCoordinate space
  matterSync :
    ∀ relativeTime space,
      (development relativeTime).primitive.matter space =
        (development relativeTime).canonical.matter space
  conjugateMatterSync :
    ∀ relativeTime space,
      (development relativeTime).primitive.conjugateMatter space =
        (development relativeTime).canonical.conjugateMatter space
  p286MomentumDerivative :
    ∀ time space direction,
      HasDerivAt
        (fun relativeTime : ℝ =>
          (development relativeTime
            ).canonical.gravityGauge.p286.spatialBFMomentumEvaluation
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
        (fun relativeTime : ℝ =>
          (development relativeTime
            ).canonical.gravityGauge.lorentz.spatialBFMomentumEvaluation
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
        (fun relativeTime : ℝ =>
          (development relativeTime
            ).canonical.scalar.temporalMomentumEvaluation
              space direction)
        (sourceActionGeneratedScalarTemporalMomentumVelocity
          source
          (sourceActionGeneratedPrimitiveCanonicalCurrent
            source anchor state).primitive
          space direction)
        time

/-- Frontier theorem: the same source-generated current state produces the
complete Cartan primitive response and the history-preserving canonical
momentum development, with their distinct coframe responsibilities kept
explicit. -/
theorem
    sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_realizes
    (source : SmoothUnifiedSource)
    (anchor : ℝ)
    (state : StageNineCauchyState) :
    StageNineCurrentTorsionFreeCartanPrimitiveCanonicalDevelopmentLaw
      source anchor state
      (fun relativeTime =>
        sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
          source anchor relativeTime state) := by
  exact
    { generated := rfl
      currentInitial :=
        sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_zero
          source anchor state
      primitiveResponse :=
        sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_hasPrimitiveResponse
          source anchor state
      canonicalGenerated := fun _ => rfl
      frozenCoframeProvenance :=
        fun relativeTime space =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_frozenCoframeProvenance
            source anchor relativeTime state space
      coframeInitialSync :=
        sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_coframeInitialSync
          source anchor state
      multiplierSync :=
        fun relativeTime space =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_multiplierSync
            source anchor relativeTime state space
      temporalLorentzSync :=
        fun relativeTime space internalPair =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_temporalLorentzSync
            source anchor relativeTime state space internalPair
      spatialLorentzSync :=
        fun relativeTime space direction internalPair =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_spatialLorentzSync
            source anchor relativeTime state space direction internalPair
      temporalP286Sync :=
        fun relativeTime space =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_temporalP286Sync
            source anchor relativeTime state space
      spatialP286Sync :=
        fun relativeTime space direction =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_spatialP286Sync
            source anchor relativeTime state space direction
      scalarSync :=
        fun relativeTime space =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_scalarSync
            source anchor relativeTime state space
      matterSync :=
        fun relativeTime space =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_matterSync
            source anchor relativeTime state space
      conjugateMatterSync :=
        fun relativeTime space =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_conjugateMatterSync
            source anchor relativeTime state space
      p286MomentumDerivative :=
        fun time space direction =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_p286MomentumHasDerivAt
            source anchor time state space direction
      lorentzMomentumDerivative :=
        fun time space direction =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_lorentzMomentumHasDerivAt
            source anchor time state space direction
      scalarMomentumDerivative :=
        fun time space direction =>
          sourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment_scalarMomentumHasDerivAt
            source anchor time state space direction }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedCurrentTorsionFreeCartanPrimitiveCanonicalDevelopment
