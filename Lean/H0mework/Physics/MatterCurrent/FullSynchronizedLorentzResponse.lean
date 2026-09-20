import H0mework.Physics.SynchronizedJoint.Response
import H0mework.Physics.MatterPreparation.ContorsionSpatialProfileFullLorentzCurrentResponseRestart

/-!
# C3h203: exact P506/L0 full-synchronized Lorentz response

This module specializes the generic full-action Lorentz producer to the latest
C3h200n current exposed by the C3h200p restart:

```text
exact P506/L0 source + endpoint 11
→ C3h200n pre-contorsion full-Lorentz current
→ complete synchronized Lorentz action dual
→ contact-local faithful auxiliary first-jet actual.
```

The whole-slice action dual is branch-free and unique from the same source,
current, and action.  Its actual derivative realization is intentionally
restricted to contact `0`, where the latest current has the identity coframe
needed by the BF momentum principal.

This is a new full-synchronized producer epoch.  It is not identified with the
older gravity-preserving fresh/coherent actual.  The corrected coframe-density
zero derivative is producer soundness of the same action graph, not an
independent Ward constraint.  No residual value, response coefficient, branch,
event, stationarity receipt, endpoint shell, or equation certificate is
supplied.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzResponse

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageEightProofFreeSource
open StageNineCanonicalCauchyState
open StageNineCurrentCanonicalFullActionLorentzDualResponse
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentFullSynchronizedLorentzResponse
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLinearPlebanskiGravityCoupledCoframeActionResponse
open StageNineLorentzActionCanonicalPairUpdate
open StageNineLorentzActionCauchySplit
open StageNineLorentzConnectionMomentumRegularity
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedJointPrimitiveCauchyUpdate
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzCurrentResponseRestart
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzTriangularActualLift

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

private abbrev CurrentState : StageNineCauchyState :=
  PreContorsionFullLorentzTriangularCurrent

/-! ## Exact source/action-generated objects -/

/-- The coframe response generated at the canonical contact of the latest
C3h200n current. -/
def positiveP506MatterCurrentFullSynchronizedLorentzCoframeResponse :
    LorentzianCoframe :=
  currentFullSynchronizedCoframeResponse positiveSmoothUnifiedSource
    CurrentState 0

/-- The full spatial family of Lorentz action responses.  No support
coordinate is selected by this definition. -/
def positiveP506MatterCurrentFullSynchronizedLorentzVelocity :
    StageNineSpatialPoint → LorentzSpatialBivectorDirection → Real :=
  currentFullSynchronizedLorentzVelocity positiveSmoothUnifiedSource
    CurrentState

/-- The auxiliary first-jet actual generated at the canonical contact. -/
def positiveP506MatterCurrentFullSynchronizedLorentzActual :
    StageNineHolonomicConfiguration :=
  currentFullSynchronizedLorentzActualFirstJetLift positiveSmoothUnifiedSource
    CurrentState 0

/-- The corrected producer-density path at the canonical contact. -/
def positiveP506MatterCurrentFullSynchronizedLorentzCoframeDensityPath
    (variation : LorentzianCoframe) : Real → Real :=
  currentFullSynchronizedProducerCoframeDensityPath
    positiveSmoothUnifiedSource CurrentState 0 variation

/-! ## Exact-lineage and latest-current provenance -/

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzResponse_exactP506L0Lineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference :=
  positiveP506MatterPreContorsionFullLorentzCurrentResponseRestart_realizes_C3h200p
    |>.exactP506L0Lineage

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzResponse_endpointEleven :
    positiveSmoothUnifiedSource.stageEight.generatedSelectedEndpoint
        canonicalSource_generatedLineage_height_pos =
      11 :=
  positiveP506MatterPreContorsionFullLorentzCurrentResponseRestart_realizes_C3h200p
    |>.endpointEleven

/-- The response is based on the C3h200n final actual, not an earlier current. -/
theorem
    positiveP506MatterCurrentFullSynchronizedLorentzResponse_latestCurrentGenerated :
    PreContorsionFullLorentzTriangularCurrent =
      canonicalCauchyRestriction 0
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual :=
  positiveP506MatterPreContorsionFullLorentzCurrentResponseRestart_realizes_C3h200p
    |>.finalCurrentGenerated

/-- The latest current still visibly carries the preceding action-generated
connection correction at the common contact. -/
theorem
    positiveP506MatterCurrentFullSynchronizedLorentzResponse_correctedConnectionPresent :
    PreContorsionFullLorentzTriangularCurrent.gravityConnection 0 =
      lorentzSkewConnectionOfBivectorOneForm
        preContorsionFullLorentzConnectionCorrection :=
  positiveP506MatterPreContorsionFullLorentzCurrentResponseRestart_realizes_C3h200p
    |>.correctedConnectionPresent

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzResponse_actionPrepared :
    sourceActionGeneratedJointPrimitiveActionInitialState
        PreContorsionFullLorentzTriangularCurrent =
      PreContorsionFullLorentzTriangularCurrent :=
  positiveP506MatterPreContorsionFullLorentzCurrentResponseRestart_realizes_C3h200p
    |>.actionPrepared

/-! ## Same-action producer soundness and response provenance -/

/-- The corrected producer density has the generated zero derivative in every
coframe direction at the canonical contact.  This is same-action producer
soundness. -/
theorem
    positiveP506MatterCurrentFullSynchronizedLorentzCoframeDensityPath_hasDerivAt_zero
    (variation : LorentzianCoframe) :
    HasDerivAt
      (positiveP506MatterCurrentFullSynchronizedLorentzCoframeDensityPath
        variation)
      0
      0 := by
  exact
    currentFullSynchronizedProducerCoframeDensityPath_hasDerivAt_zero
      positiveSmoothUnifiedSource CurrentState 0
      preContorsionFullLorentzTriangularCurrent_coframe_origin variation

/-- The final exact actual carries the multiplier generated from the same
full-synchronized coframe response. -/
theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActual_multiplier_eq_response :
    positiveP506MatterCurrentFullSynchronizedLorentzActual.gravitySimplicityMultiplier =
      fun _ =>
        gravityCoupledLinearPlebanskiMultiplier
          positiveP506MatterCurrentFullSynchronizedLorentzCoframeResponse := by
  exact
    currentFullSynchronizedLorentzActualFirstJetLift_multiplier_eq_response
      positiveSmoothUnifiedSource CurrentState 0

/-- The same exact actual retains the curvature generated from that response. -/
theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActual_curvature_eq_response :
    holonomicGravityCurvature
        positiveP506MatterCurrentFullSynchronizedLorentzActual 0 =
      gravityCoupledLinearPlebanskiCurvature
        positiveP506MatterCurrentFullSynchronizedLorentzCoframeResponse := by
  exact
    currentFullSynchronizedLorentzActualFirstJetLift_curvature_eq_response
      positiveSmoothUnifiedSource CurrentState 0

theorem positiveP506MatterCurrentFullSynchronizedLorentzVelocity_actionLaw :
    CurrentFullSynchronizedLorentzVelocityLaw positiveSmoothUnifiedSource
      CurrentState
      positiveP506MatterCurrentFullSynchronizedLorentzVelocity := by
  exact currentFullSynchronizedLorentzVelocity_satisfies_actionLaw
    positiveSmoothUnifiedSource CurrentState

/-- The action law uniquely fixes the whole-slice response; it carries no
observable free coefficient. -/
theorem positiveP506MatterCurrentFullSynchronizedLorentzVelocity_unique
    (candidate :
      StageNineSpatialPoint → LorentzSpatialBivectorDirection → Real)
    (candidateLaw :
      CurrentFullSynchronizedLorentzVelocityLaw positiveSmoothUnifiedSource
        CurrentState candidate) :
    candidate =
      positiveP506MatterCurrentFullSynchronizedLorentzVelocity := by
  exact currentFullSynchronizedLorentzVelocityLaw_unique
    positiveSmoothUnifiedSource CurrentState candidate
    positiveP506MatterCurrentFullSynchronizedLorentzVelocity candidateLaw
    positiveP506MatterCurrentFullSynchronizedLorentzVelocity_actionLaw

/-! ## Faithful actual first-jet realization -/

theorem positiveP506MatterCurrentFullSynchronizedLorentzVelocity_eq_zero_iff :
    positiveP506MatterCurrentFullSynchronizedLorentzVelocity = 0 ↔
      ∀ space spatialDirection internalPair,
        currentFullSynchronizedLorentzRawActionReadout
            positiveSmoothUnifiedSource CurrentState space
            (canonicalLorentzSpatialBivectorCoordinateDirection
              spatialDirection internalPair) =
          0 := by
  exact currentFullSynchronizedLorentzVelocity_eq_zero_iff
    positiveSmoothUnifiedSource CurrentState

/-- One exposed nonzero action coordinate forces a nonzero whole-slice
Lorentz response.  It is a readout criterion, not a coordinate selected by
the producer. -/
theorem
    positiveP506MatterCurrentFullSynchronizedLorentzVelocity_ne_zero_of_raw_coordinate_ne_zero
    (space : StageNineSpatialPoint)
    (spatialDirection : Fin 3)
    (internalPair : Fin 6)
    (coordinateNonzero :
      currentFullSynchronizedLorentzRawActionReadout
          positiveSmoothUnifiedSource CurrentState space
          (canonicalLorentzSpatialBivectorCoordinateDirection
            spatialDirection internalPair) ≠
        0) :
    positiveP506MatterCurrentFullSynchronizedLorentzVelocity ≠ 0 := by
  intro velocityZero
  have coordinatesZero :=
    positiveP506MatterCurrentFullSynchronizedLorentzVelocity_eq_zero_iff.mp
      velocityZero
  exact coordinateNonzero
    (coordinatesZero space spatialDirection internalPair)

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActual_eq_base_iff :
    positiveP506MatterCurrentFullSynchronizedLorentzActual =
          currentCanonicalFullActionActual positiveSmoothUnifiedSource
            CurrentState 0 ↔
      positiveP506MatterCurrentFullSynchronizedLorentzVelocity 0 = 0 := by
  exact currentFullSynchronizedLorentzActualFirstJetLift_eq_base_iff
    positiveSmoothUnifiedSource CurrentState 0

/-- The contact actual realizes the generated Lorentz response as a genuine
time-axis derivative of BF momentum for every test direction. -/
theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActual_BFMomentum_hasDerivAt
    (time : Real)
    (direction : LorentzSpatialBivectorDirection) :
    HasDerivAt
      (fun candidate : Real =>
        lorentzConnectionBFDifferentialMomentum
          positiveP506MatterCurrentFullSynchronizedLorentzActual
          (lorentzConnectionExteriorDerivativeDirection
            canonicalLorentzianTimeDirection
            (canonicalLorentzSpatialBivectorOneForm direction))
          (canonicalCauchySlicePoint candidate 0))
      (positiveP506MatterCurrentFullSynchronizedLorentzVelocity 0 direction)
      time := by
  exact
    currentFullSynchronizedLorentzActualFirstJetLift_BFMomentum_hasDerivAt
      positiveSmoothUnifiedSource CurrentState 0
      preContorsionFullLorentzTriangularCurrent_coframe_origin time direction

theorem positiveP506MatterCurrentFullSynchronizedLorentzActual_smooth :
    positiveP506MatterCurrentFullSynchronizedLorentzActual.Smooth := by
  exact currentFullSynchronizedLorentzActualFirstJetLift_smooth
    positiveSmoothUnifiedSource CurrentState 0

theorem positiveP506MatterCurrentFullSynchronizedLorentzActual_nondegenerate :
    positiveP506MatterCurrentFullSynchronizedLorentzActual.Nondegenerate := by
  exact currentFullSynchronizedLorentzActualFirstJetLift_nondegenerate
    positiveSmoothUnifiedSource CurrentState 0
    preContorsionFullLorentzTriangularCurrent_coframe_origin

/-! ## No-premise checkpoint law -/

/-- Role-separated C3h203 checkpoint.  The lineage, endpoint, prepared-current,
and corrected-connection fields are inherited provenance.  New producer
content is the unique full-synchronized action response and its faithful
contact actual.  The density derivative remains producer consistency. -/
structure PositiveP506MatterCurrentFullSynchronizedLorentzResponseLaw :
    Prop where
  exactP506L0Lineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference
  endpointEleven :
    positiveSmoothUnifiedSource.stageEight.generatedSelectedEndpoint
        canonicalSource_generatedLineage_height_pos =
      11
  latestCurrentGenerated :
    PreContorsionFullLorentzTriangularCurrent =
      canonicalCauchyRestriction 0
        positiveP506MatterPreContorsionSpatialProfileFullLorentzTriangularActual
  correctedConnectionPresent :
    PreContorsionFullLorentzTriangularCurrent.gravityConnection 0 =
      lorentzSkewConnectionOfBivectorOneForm
        preContorsionFullLorentzConnectionCorrection
  actionPrepared :
    sourceActionGeneratedJointPrimitiveActionInitialState
        PreContorsionFullLorentzTriangularCurrent =
      PreContorsionFullLorentzTriangularCurrent
  correctedCoframeProducerSoundness : ∀ variation,
    HasDerivAt
      (positiveP506MatterCurrentFullSynchronizedLorentzCoframeDensityPath
        variation)
      0
      0
  multiplierFromSameResponse :
    positiveP506MatterCurrentFullSynchronizedLorentzActual.gravitySimplicityMultiplier =
      fun _ =>
        gravityCoupledLinearPlebanskiMultiplier
          positiveP506MatterCurrentFullSynchronizedLorentzCoframeResponse
  curvatureFromSameResponse :
    holonomicGravityCurvature
        positiveP506MatterCurrentFullSynchronizedLorentzActual 0 =
      gravityCoupledLinearPlebanskiCurvature
        positiveP506MatterCurrentFullSynchronizedLorentzCoframeResponse
  lorentzVelocityActionLaw :
    CurrentFullSynchronizedLorentzVelocityLaw positiveSmoothUnifiedSource
      CurrentState
      positiveP506MatterCurrentFullSynchronizedLorentzVelocity
  lorentzVelocityUnique : ∀ candidate,
    CurrentFullSynchronizedLorentzVelocityLaw positiveSmoothUnifiedSource
        CurrentState candidate →
      candidate =
        positiveP506MatterCurrentFullSynchronizedLorentzVelocity
  velocityFaithfulZeroFiber :
    positiveP506MatterCurrentFullSynchronizedLorentzVelocity = 0 ↔
      ∀ space spatialDirection internalPair,
        currentFullSynchronizedLorentzRawActionReadout
            positiveSmoothUnifiedSource CurrentState space
            (canonicalLorentzSpatialBivectorCoordinateDirection
              spatialDirection internalPair) =
          0
  actualFaithfulZeroFiber :
    positiveP506MatterCurrentFullSynchronizedLorentzActual =
          currentCanonicalFullActionActual positiveSmoothUnifiedSource
            CurrentState 0 ↔
      positiveP506MatterCurrentFullSynchronizedLorentzVelocity 0 = 0
  bfMomentumFirstJet : ∀ time direction,
    HasDerivAt
      (fun candidate : Real =>
        lorentzConnectionBFDifferentialMomentum
          positiveP506MatterCurrentFullSynchronizedLorentzActual
          (lorentzConnectionExteriorDerivativeDirection
            canonicalLorentzianTimeDirection
            (canonicalLorentzSpatialBivectorOneForm direction))
          (canonicalCauchySlicePoint candidate 0))
      (positiveP506MatterCurrentFullSynchronizedLorentzVelocity 0 direction)
      time
  smooth :
    positiveP506MatterCurrentFullSynchronizedLorentzActual.Smooth
  nondegenerate :
    positiveP506MatterCurrentFullSynchronizedLorentzActual.Nondegenerate

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzResponse_realizes_C3h203 :
    PositiveP506MatterCurrentFullSynchronizedLorentzResponseLaw := by
  exact
    { exactP506L0Lineage :=
        positiveP506MatterCurrentFullSynchronizedLorentzResponse_exactP506L0Lineage
      endpointEleven :=
        positiveP506MatterCurrentFullSynchronizedLorentzResponse_endpointEleven
      latestCurrentGenerated :=
        positiveP506MatterCurrentFullSynchronizedLorentzResponse_latestCurrentGenerated
      correctedConnectionPresent :=
        positiveP506MatterCurrentFullSynchronizedLorentzResponse_correctedConnectionPresent
      actionPrepared :=
        positiveP506MatterCurrentFullSynchronizedLorentzResponse_actionPrepared
      correctedCoframeProducerSoundness :=
        positiveP506MatterCurrentFullSynchronizedLorentzCoframeDensityPath_hasDerivAt_zero
      multiplierFromSameResponse :=
        positiveP506MatterCurrentFullSynchronizedLorentzActual_multiplier_eq_response
      curvatureFromSameResponse :=
        positiveP506MatterCurrentFullSynchronizedLorentzActual_curvature_eq_response
      lorentzVelocityActionLaw :=
        positiveP506MatterCurrentFullSynchronizedLorentzVelocity_actionLaw
      lorentzVelocityUnique :=
        positiveP506MatterCurrentFullSynchronizedLorentzVelocity_unique
      velocityFaithfulZeroFiber :=
        positiveP506MatterCurrentFullSynchronizedLorentzVelocity_eq_zero_iff
      actualFaithfulZeroFiber :=
        positiveP506MatterCurrentFullSynchronizedLorentzActual_eq_base_iff
      bfMomentumFirstJet :=
        positiveP506MatterCurrentFullSynchronizedLorentzActual_BFMomentum_hasDerivAt
      smooth :=
        positiveP506MatterCurrentFullSynchronizedLorentzActual_smooth
      nondegenerate :=
        positiveP506MatterCurrentFullSynchronizedLorentzActual_nondegenerate }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzResponse
