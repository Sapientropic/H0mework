import H0mework.Physics.MatterCurrent.CanonicalLorentzAdjointDiagonalActual

/-!
# C3h197: fresh response provenance core

This dependency-light layer names the C3h187 contact, stress, coframe response,
and multiplier later consumed by the C3h196 actual.  It also exposes the exact
non-gravity consumed-field projection.  The analytic temporal-germ derivative
chain lives in the structural successor module, so provenance comparisons do
not need to load that large proof.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineP506CanonicalLorentzAdjointTemporalFirstGermStructural

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCanonicalLocalFullActionResponseOperator
open StageNineCoframeSectorStress
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineEnrichedProofFreeSource
open StageNineFullSynchronizedActionResponseOperator
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLinearPlebanskiGravityCoupledCoframeActionResponse
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalGravityPreservingLorentzDualResponse
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointCauchyUpdate
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzActualFirstJetLift
open StageNineSourceActionGeneratedP506MatterCurrentCompleteFirstGermCanonicalPrimitiveCauchyUpdate

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

abbrev c3h196Actual : StageNineHolonomicConfiguration :=
  positiveP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

abbrev c3h196PriorActual : StageNineHolonomicConfiguration :=
  positiveP506MatterCurrentCanonicalLorentzActualFirstJetLift 0

abbrev c3h196FinalState : StageNineCauchyState :=
  positiveP506MatterCurrentCanonicalLorentzFinalCauchyState

abbrev c3h196SeedState : StageNineCauchyState :=
  positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState

/-! ## Fresh C3h187 multiplier provenance -/

/-- The exact contact base consumed while C3h187 generated its zero response. -/
def c3h196SeedContactBaseActual
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
    positiveP506MatterCurrentCompleteFirstGermCanonicalCauchyState space

/-- Non-gravity stress freshly read from the C3h187 contact base. -/
def c3h196SeedNonGravityCoframeStress
    (space : StageNineSpatialPoint) : LorentzianCoframe →L[ℝ] ℝ :=
  fullSynchronizedActionNonGravityCoframeStress positiveSmoothUnifiedSource
    (c3h196SeedContactBaseActual space)

/-- The exact resynchronized point field consumed by the fresh stress. -/
def c3h196SeedMatterOriginField
    (space : StageNineSpatialPoint) : StageNineContinuumPointField :=
  fullSynchronizedActionMatterOriginField positiveSmoothUnifiedSource
    (c3h196SeedContactBaseActual space)

/-- Forget exactly the three gravity slots ignored by all non-gravity
coframe-stress sectors. -/
def c3h196NonGravityContactProjection
    (field : StageNineContinuumPointField) : StageNineContinuumPointField :=
  { field with
    gravityCurvature := 0
    gravityAuxiliary := 0
    gravitySimplicityMultiplier := 0 }

@[simp] theorem c3h196NonGravityContactProjection_gaugeStress
    (source : SmoothUnifiedSource) (field : StageNineContinuumPointField) :
    coframeGaugeSectorStressCovector source
        (c3h196NonGravityContactProjection field) =
      coframeGaugeSectorStressCovector source field :=
  rfl

@[simp] theorem c3h196NonGravityContactProjection_scalarStress
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField) :
    coframeScalarSectorStressCovector source point
        (c3h196NonGravityContactProjection field) =
      coframeScalarSectorStressCovector source point field :=
  rfl

@[simp] theorem c3h196NonGravityContactProjection_matterStress
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField) :
    coframeMatterSectorStressCovector source point
        (c3h196NonGravityContactProjection field) =
      coframeMatterSectorStressCovector source point field :=
  rfl

/-- A non-gravity coframe stress depends only on the public consumed-field
projection.  This is a readout congruence, not a supplied matching receipt. -/
theorem fullSynchronizedActionNonGravityCoframeStress_eq_of_consumedProjection
    (source : SmoothUnifiedSource)
    (first second : StageNineHolonomicConfiguration)
    (consumed :
      c3h196NonGravityContactProjection
          (fullSynchronizedActionMatterOriginField source first) =
        c3h196NonGravityContactProjection
          (fullSynchronizedActionMatterOriginField source second)) :
    fullSynchronizedActionNonGravityCoframeStress source first =
      fullSynchronizedActionNonGravityCoframeStress source second := by
  unfold fullSynchronizedActionNonGravityCoframeStress
  calc
    _ =
        coframeGaugeSectorStressCovector source
            (c3h196NonGravityContactProjection
              (fullSynchronizedActionMatterOriginField source first)) +
          coframeScalarSectorStressCovector source 0
            (c3h196NonGravityContactProjection
              (fullSynchronizedActionMatterOriginField source first)) +
          coframeMatterSectorStressCovector source 0
            (c3h196NonGravityContactProjection
              (fullSynchronizedActionMatterOriginField source first)) := by
      simp
    _ =
        coframeGaugeSectorStressCovector source
            (c3h196NonGravityContactProjection
              (fullSynchronizedActionMatterOriginField source second)) +
          coframeScalarSectorStressCovector source 0
            (c3h196NonGravityContactProjection
              (fullSynchronizedActionMatterOriginField source second)) +
          coframeMatterSectorStressCovector source 0
            (c3h196NonGravityContactProjection
              (fullSynchronizedActionMatterOriginField source second)) := by
      rw [consumed]
    _ = _ := by simp

/-- Coframe response generated from the fresh C3h187 stress. -/
def c3h196SeedCoframeResponse
    (space : StageNineSpatialPoint) : LorentzianCoframe :=
  gravityCoupledLinearPlebanskiCoframeResponseOfStress
    (c3h196SeedNonGravityCoframeStress space)

/-- Gravity multiplier generated from the fresh C3h187 coframe response. -/
def c3h196SeedGravityMultiplier
    (space : StageNineSpatialPoint) : PhysicalBivector :=
  gravityCoupledLinearPlebanskiMultiplier
    (c3h196SeedCoframeResponse space)

/-- Exact producer provenance of the multiplier later consumed by C3h196.
No equality of whole point fields or whole actuals is used. -/
theorem c3h196SeedState_gravitySimplicityMultiplier_eq_freshActionResponse
    (space : StageNineSpatialPoint) :
    c3h196SeedState.gravitySimplicityMultiplier space =
      c3h196SeedGravityMultiplier space := by
  unfold c3h196SeedState
    positiveP506MatterCurrentCanonicalGravityPreservingLorentzDualCurrentState
    positiveP506MatterCurrentCompleteFirstGermCanonicalGeneratedZeroResponseState
  rw [currentCanonicalFullActionGeneratedZeroResponseState_gravitySimplicityMultiplier]
  change
    (canonicalLocalFullActionResponseOperator positiveSmoothUnifiedSource
        (c3h196SeedContactBaseActual space)).gravitySimplicityMultiplier 0 =
      c3h196SeedGravityMultiplier space
  rw [canonicalLocalFullActionResponseOperator_gravitySimplicityMultiplier]
  rfl

/-- Coordinate-ready form of the same provenance theorem. -/
theorem c3h196SeedState_gravitySimplicityMultiplier_eq_freshStress
    (space : StageNineSpatialPoint) :
    c3h196SeedState.gravitySimplicityMultiplier space =
      gravityCoupledLinearPlebanskiMultiplier
        (gravityCoupledLinearPlebanskiCoframeResponseOfStress
          (c3h196SeedNonGravityCoframeStress space)) := by
  rw [c3h196SeedState_gravitySimplicityMultiplier_eq_freshActionResponse]
  rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineP506CanonicalLorentzAdjointTemporalFirstGermStructural
