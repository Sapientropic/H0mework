import H0mework.Physics.Exterior.CanonicalLocalFullActionResponseOperator
import H0mework.Physics.Coframe.CoframeNonGravityContactProjection
import H0mework.Physics.SynchronizedJoint.Response

/-!
# Stage-9 canonical local full-action origin fidelity

This module proves the exact contact-origin bridges needed to compare a
canonical full-action actual with the earlier producer state that generated
its coframe response.

The temporal and complete matter response legs add quadratic coordinate
corrections, so they preserve both matter value and first covariant jet at
the origin.  The complete P286 leg already preserves the whole origin point
field.  The full-synchronized response may replace gravity curvature and
multiplier, but its non-gravity contact projection agrees with the matter
origin that generated the coframe stress.

These are provenance/fidelity theorems.  The projection is not a physical
quotient, and no equation, residual, response target, or stationarity
certificate is accepted.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCanonicalLocalFullActionOriginFidelity

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCanonicalLocalFullActionResponseOperator
open StageNineCoframeNonGravityContactProjection
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentFullSynchronizedLorentzResponse
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineFullSynchronizedActionResponseOperator
open StageNineFullSynchronizedCompleteP286ActionResponseOperator
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterActionCompleteFirstGermResponse
open StageNineMatterActionTemporalFirstGermResponse
open StageNineMatterVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

/-! ## Matter-response origin fidelity -/

theorem actionGeneratedMatterTemporalFirstGermActual_pointField_origin
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    toContinuumPointField
        (actionGeneratedMatterTemporalFirstGermActual source configuration) 0 =
      toContinuumPointField configuration 0 := by
  unfold actionGeneratedMatterTemporalFirstGermActual
  rw [toContinuumPointField_installMatterTemporalFirstGermResponse
    configuration smooth _ 0]
  have covariantVariationZero :
      holonomicMatterVariationCovariantDerivative configuration
          (matterQuadraticTimeCoordinateCorrection
            (actionGeneratedMatterTemporalFirstGermAcceleration source
              configuration))
          0 =
        0 := by
    exact holonomicMatterVariationCovariantDerivative_eq_zero_of_jet_zero
      configuration
      (matterQuadraticTimeCoordinateCorrection
        (actionGeneratedMatterTemporalFirstGermAcceleration source
          configuration))
      0
      (matterQuadraticTimeCoordinateCorrection_origin _)
      (matterQuadraticTimeCoordinateCorrection_directionalDerivative_origin _)
  rw [matterQuadraticTimeCoordinateCorrection_origin, map_zero,
    covariantVariationZero]
  simp [toContinuumPointField, withMatterJets]

theorem actionGeneratedMatterCompleteFirstGermActual_pointField_origin
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    toContinuumPointField
        (actionGeneratedMatterCompleteFirstGermActual source configuration) 0 =
      toContinuumPointField configuration 0 := by
  unfold actionGeneratedMatterCompleteFirstGermActual
  rw [toContinuumPointField_installMatterCompleteFirstGermResponse
    configuration smooth _ 0]
  have covariantVariationZero :
      holonomicMatterVariationCovariantDerivative configuration
          (matterCompleteQuadraticCoordinateCorrection
            (actionGeneratedMatterCompleteFirstGermHessian source
              configuration))
          0 =
        0 := by
    exact holonomicMatterVariationCovariantDerivative_eq_zero_of_jet_zero
      configuration
      (matterCompleteQuadraticCoordinateCorrection
        (actionGeneratedMatterCompleteFirstGermHessian source configuration))
      0
      (matterCompleteQuadraticCoordinateCorrection_origin _)
      (matterCompleteQuadraticCoordinateCorrection_directionalDerivative_origin _)
  rw [matterCompleteQuadraticCoordinateCorrection_origin, map_zero,
    covariantVariationZero]
  simp [toContinuumPointField, withMatterJets]

/-! ## Full-synchronized producer bridge -/

theorem
    fullSynchronizedActionResponseOperator_nonGravityOrigin_eq_matterOrigin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    coframeNonGravityContactProjection
        (toContinuumPointField
          (fullSynchronizedActionResponseOperator source current) 0) =
      coframeNonGravityContactProjection
        (fullSynchronizedActionMatterOriginField source current) := by
  unfold fullSynchronizedActionMatterOriginField
  apply StageNineContinuumPointField.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext direction
    change
      holonomicMatterCovariantDerivative
          (fullSynchronizedActionResponseOperator source current) 0 direction =
        holonomicMatterCovariantDerivative
          (fullSynchronizedActionMatterActual source current) 0 direction
    have matterConnectionOrigin :
        (fullSynchronizedActionMatterActual source current).gravityConnection
            0 =
          fullSynchronizedActionLorentzOrigin source current := by
      exact normalizedAffineLorentzConnectionField_zero _ _
    have matterFieldEq :
        (fullSynchronizedActionResponseOperator source current).matter =
          (fullSynchronizedActionMatterActual source current).matter :=
      rfl
    have gaugeConnectionEq :
        (fullSynchronizedActionResponseOperator source current).gaugeConnection =
          (fullSynchronizedActionMatterActual source current).gaugeConnection :=
      rfl
    unfold holonomicMatterCovariantDerivative
    rw [matterFieldEq, gaugeConnectionEq,
      fullSynchronizedActionResponseOperator_connection_origin,
      matterConnectionOrigin]
  · rfl

/-- The complete canonical response has the same non-gravity origin contact
as the forward matter state that generated its coframe response. -/
theorem
    canonicalLocalFullActionResponseOperator_nonGravityOrigin_eq_producer
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) :
    coframeNonGravityContactProjection
        (toContinuumPointField
          (canonicalLocalFullActionResponseOperator source current) 0) =
      coframeNonGravityContactProjection
        (fullSynchronizedActionMatterOriginField source current) := by
  have fullSynchronizedSmooth :
      (fullSynchronizedActionResponseOperator source current).Smooth :=
    fullSynchronizedActionResponseOperator_smooth source current smooth
  have p286Smooth :
      (canonicalLocalFullActionP286Actual source current).Smooth := by
    exact currentP286CompleteActionResponseOperator_smooth source
      (fullSynchronizedActionResponseOperator source current)
      fullSynchronizedSmooth
  have temporalSmooth :
      (canonicalLocalFullActionTemporalMatterActual source current).Smooth :=
    actionGeneratedMatterTemporalFirstGermActual_smooth source
      (canonicalLocalFullActionP286Actual source current) p286Smooth
  calc
    coframeNonGravityContactProjection
        (toContinuumPointField
          (canonicalLocalFullActionResponseOperator source current) 0) =
      coframeNonGravityContactProjection
        (toContinuumPointField
          (canonicalLocalFullActionTemporalMatterActual source current) 0) := by
        simpa only [canonicalLocalFullActionResponseOperator] using
          congrArg coframeNonGravityContactProjection
            (actionGeneratedMatterCompleteFirstGermActual_pointField_origin
              source
              (canonicalLocalFullActionTemporalMatterActual source current)
              temporalSmooth)
    _ =
      coframeNonGravityContactProjection
        (toContinuumPointField
          (canonicalLocalFullActionP286Actual source current) 0) := by
        simpa only [canonicalLocalFullActionTemporalMatterActual] using
          congrArg coframeNonGravityContactProjection
            (actionGeneratedMatterTemporalFirstGermActual_pointField_origin
              source (canonicalLocalFullActionP286Actual source current)
              p286Smooth)
    _ =
      coframeNonGravityContactProjection
        (toContinuumPointField
          (fullSynchronizedActionResponseOperator source current) 0) := by
        simpa only [canonicalLocalFullActionP286Actual] using
          congrArg coframeNonGravityContactProjection
            (fullSynchronizedCompleteP286ActionResponseOperator_pointField_origin
              source current)
    _ =
      coframeNonGravityContactProjection
        (fullSynchronizedActionMatterOriginField source current) :=
      fullSynchronizedActionResponseOperator_nonGravityOrigin_eq_matterOrigin
        source current

/-! ## Latest Lorentz first-jet origin fidelity -/

/-- Installing the action-generated Lorentz auxiliary first jet changes no
contact-origin field coordinate.  The only definitionally changed slot is
the gravity auxiliary field, whose time-linear correction vanishes at the
origin. -/
theorem
    currentFullSynchronizedLorentzActualFirstJetLift_pointField_origin
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    toContinuumPointField
        (currentFullSynchronizedLorentzActualFirstJetLift source current
          space)
        0 =
      toContinuumPointField
        (currentCanonicalFullActionActual source current space)
        0 := by
  apply StageNineContinuumPointField.ext
  · rfl
  · rfl
  · exact currentFullSynchronizedLorentzActualFirstJetLift_origin
      source current space
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The latest Lorentz first-jet lift therefore retains exactly the
non-gravity contact that generated the synchronized coframe response. -/
theorem
    currentFullSynchronizedLorentzActualFirstJetLift_nonGravityOriginProjection_eq_producer
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (smooth :
      (currentCanonicalFullActionBaseActual source current space).Smooth) :
    coframeNonGravityContactProjection
        (toContinuumPointField
          (currentFullSynchronizedLorentzActualFirstJetLift source current
            space)
          0) =
      coframeNonGravityContactProjection
        (currentFullSynchronizedProducerOriginField source current space) := by
  rw [
    currentFullSynchronizedLorentzActualFirstJetLift_pointField_origin]
  simpa only [currentCanonicalFullActionActual,
    currentFullSynchronizedProducerOriginField] using
    (canonicalLocalFullActionResponseOperator_nonGravityOrigin_eq_producer
      source (currentCanonicalFullActionBaseActual source current space)
      smooth)

end

end
  SaturationMonoid.PhysicsCore.StageNineCanonicalLocalFullActionOriginFidelity
