import H0mework.Physics.Exterior.CanonicalLocalFullActionOriginFidelity
import H0mework.Physics.MatterCurrent.FullSynchronizedLorentzMixedBFReadout

/-!
# C3h206: latest-current actual-origin coframe action

C3h204 kept the producer coframe/stress channel separate because its density
had not yet been identified with a density read from the judged C3h203
actual.  This module supplies that missing contact-origin bridge.

The final actual is compared with the forward producer state only through
the non-gravity contact projection; gravity auxiliary, curvature, and
multiplier are reinserted through their independent action-generated
equalities.  The resulting corrected coframe density is therefore a genuine
function of the judged actual's origin point field, and its derivative is
transported from the already generated producer covector.

This remains producer consistency.  The coframe path parameter is not the
physical-time parameter of the temporal-Gauss trace, and no multiplier
Lorentz transformation law or four-sector Ward totalization is claimed.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzActualOriginCoframeAction

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCanonicalLocalFullActionOriginFidelity
open StageNineCanonicalLocalFullActionResponseOperator
open StageNineCoframeNonGravityContactProjection
open StageNineCoframeSectorStress
open StageNineCoframeVariation
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentFullSynchronizedCompleteP286PrimitiveCauchyUpdate
open StageNineCurrentFullSynchronizedLorentzResponse
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityAuxiliaryVariation
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineLinearPlebanskiGravityCoupledCoframeActionResponse
open StageNineLorentzConnectionMomentumRegularity
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzFirstVariationObstruction
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzMixedBFReadout
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzResponse
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileFullLorentzCurrentResponseRestart
open scoped Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

private abbrev CurrentState : StageNineCauchyState :=
  PreContorsionFullLorentzTriangularCurrent

private abbrev BaseActual : StageNineHolonomicConfiguration :=
  currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
    CurrentState 0

private abbrev JudgedActual : StageNineHolonomicConfiguration :=
  positiveP506MatterCurrentFullSynchronizedLorentzActual

private theorem baseActual_smooth : BaseActual.Smooth := by
  change
    (currentFullSynchronizedCompleteP286BaseActual positiveSmoothUnifiedSource
      CurrentState 0).Smooth
  exact sourceActionGeneratedLinearPlebanskiJointLocalActualLift_smooth
    positiveSmoothUnifiedSource CurrentState 0

/-! ## Actual-origin provenance -/

def positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField :
    StageNineContinuumPointField :=
  toContinuumPointField JudgedActual 0

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_eq_canonical :
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField =
      toContinuumPointField
        (currentCanonicalFullActionActual positiveSmoothUnifiedSource
          CurrentState 0)
        0 := by
  exact
    currentFullSynchronizedLorentzActualFirstJetLift_pointField_origin
      positiveSmoothUnifiedSource CurrentState 0

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_nonGravity_eq_producer :
    coframeNonGravityContactProjection
        positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField =
      coframeNonGravityContactProjection
        (currentFullSynchronizedProducerOriginField positiveSmoothUnifiedSource
          CurrentState 0) := by
  exact
    currentFullSynchronizedLorentzActualFirstJetLift_nonGravityOriginProjection_eq_producer
      positiveSmoothUnifiedSource CurrentState 0 baseActual_smooth

@[simp] theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_coframe :
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField.coframe =
      (1 : LorentzianCoframe) := by
  change JudgedActual.coframe 0 = 1
  exact currentFullSynchronizedLorentzActualFirstJetLift_coframe_one
    positiveSmoothUnifiedSource CurrentState 0
    preContorsionFullLorentzTriangularCurrent_coframe_origin 0

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_gravityAuxiliary :
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField.gravityAuxiliary =
      physicalIIPlusBivector (1 : LorentzianCoframe) := by
  change JudgedActual.gravityAuxiliary 0 = physicalIIPlusBivector 1
  change
    (currentFullSynchronizedLorentzActualFirstJetLift
      positiveSmoothUnifiedSource CurrentState 0).gravityAuxiliary 0 =
      physicalIIPlusBivector 1
  rw [currentFullSynchronizedLorentzActualFirstJetLift_origin]
  change
    actionGeneratedGravityAuxiliary CurrentState 0 =
      physicalIIPlusBivector 1
  unfold actionGeneratedGravityAuxiliary
  rw [preContorsionFullLorentzTriangularCurrent_coframe_origin]

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_simplicity :
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField.gravityAuxiliary =
      physicalIIPlusBivector
        positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField.coframe := by
  rw [
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_coframe,
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_gravityAuxiliary]

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_multiplier :
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField.gravitySimplicityMultiplier =
      gravityCoupledLinearPlebanskiMultiplier
        positiveP506MatterCurrentFullSynchronizedLorentzCoframeResponse := by
  change
    JudgedActual.gravitySimplicityMultiplier 0 =
      gravityCoupledLinearPlebanskiMultiplier
        positiveP506MatterCurrentFullSynchronizedLorentzCoframeResponse
  rw [
    positiveP506MatterCurrentFullSynchronizedLorentzActual_multiplier_eq_response]

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_gravityCurvature :
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField.gravityCurvature =
      gravityCoupledLinearPlebanskiCurvature
        positiveP506MatterCurrentFullSynchronizedLorentzCoframeResponse := by
  change
    holonomicGravityCurvature JudgedActual 0 =
      gravityCoupledLinearPlebanskiCurvature
        positiveP506MatterCurrentFullSynchronizedLorentzCoframeResponse
  exact
    positiveP506MatterCurrentFullSynchronizedLorentzActual_curvature_eq_response

/-! ## Actual-origin corrected density -/

def positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensity
    (candidate : LorentzianCoframe) : ℝ :=
  generatedVolumeDensity
        (withCoframe
          positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField
          candidate) *
      generatedGravityBFDensity
        (withCoframe
          positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField
          candidate) +
    linearPlebanskiSimplicityDensity
      positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField.gravityAuxiliary
      positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField.gravitySimplicityMultiplier
      candidate +
    coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField
      candidate +
    coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
      positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField
      candidate +
    coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
      positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField
      candidate

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_gaugeDensity_eq_producer
    (candidate : LorentzianCoframe) :
    coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField
        candidate =
      coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        (currentFullSynchronizedProducerOriginField positiveSmoothUnifiedSource
          CurrentState 0)
        candidate := by
  calc
    _ = coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
          (coframeNonGravityContactProjection
            positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField)
          candidate := by rw [coframeGaugeSectorLocalDensity_projection]
    _ = coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
          (coframeNonGravityContactProjection
            (currentFullSynchronizedProducerOriginField
              positiveSmoothUnifiedSource CurrentState 0))
          candidate := by
      rw [
        positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_nonGravity_eq_producer]
    _ = _ := coframeGaugeSectorLocalDensity_projection _ _ _

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_scalarDensity_eq_producer
    (candidate : LorentzianCoframe) :
    coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField
        candidate =
      coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
        (currentFullSynchronizedProducerOriginField positiveSmoothUnifiedSource
          CurrentState 0)
        candidate := by
  calc
    _ = coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
          (coframeNonGravityContactProjection
            positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField)
          candidate := by rw [coframeScalarSectorLocalDensity_projection]
    _ = coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
          (coframeNonGravityContactProjection
            (currentFullSynchronizedProducerOriginField
              positiveSmoothUnifiedSource CurrentState 0))
          candidate := by
      rw [
        positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_nonGravity_eq_producer]
    _ = _ := coframeScalarSectorLocalDensity_projection _ _ _ _

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_matterDensity_eq_producer
    (candidate : LorentzianCoframe) :
    coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField
        candidate =
      coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        (currentFullSynchronizedProducerOriginField positiveSmoothUnifiedSource
          CurrentState 0)
        candidate := by
  calc
    _ = coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
          (coframeNonGravityContactProjection
            positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField)
          candidate := by rw [coframeMatterSectorLocalDensity_projection]
    _ = coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
          (coframeNonGravityContactProjection
            (currentFullSynchronizedProducerOriginField
              positiveSmoothUnifiedSource CurrentState 0))
          candidate := by
      rw [
        positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_nonGravity_eq_producer]
    _ = _ := coframeMatterSectorLocalDensity_projection _ _ _ _

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_gravityBFDensity_eq_producer
    (candidate : LorentzianCoframe)
    (nondegenerate : Matrix.det candidate ≠ 0) :
    generatedVolumeDensity
          (withCoframe
            positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField
            candidate) *
        generatedGravityBFDensity
          (withCoframe
            positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField
            candidate) =
      gravityCoupledLinearPlebanskiBFCoframeDensity
        positiveP506MatterCurrentFullSynchronizedLorentzCoframeResponse
        candidate := by
  unfold generatedVolumeDensity generatedGravityBFDensity
    gravityCoupledLinearPlebanskiBFCoframeDensity
    gravityCoupledLinearPlebanskiBFPolynomial
  simp only [withCoframe]
  rw [
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_gravityAuxiliary,
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_gravityCurvature]
  rw [gravityAuxiliaryHodgePairingPolynomial_eq candidate nondegenerate,
    gravityAuxiliaryHodgePairingPolynomial_eq candidate nondegenerate]

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensity_eq_producer
    (candidate : LorentzianCoframe)
    (nondegenerate : Matrix.det candidate ≠ 0) :
    positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensity
        candidate =
      currentFullSynchronizedProducerCoframeDensity positiveSmoothUnifiedSource
        CurrentState 0 candidate := by
  unfold
    positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensity
    currentFullSynchronizedProducerCoframeDensity
  rw [
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_gravityBFDensity_eq_producer
      candidate nondegenerate,
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_gravityAuxiliary,
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_multiplier,
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_gaugeDensity_eq_producer,
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_scalarDensity_eq_producer,
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_matterDensity_eq_producer]
  dsimp only [gravityCoupledLinearPlebanskiMultiplier]
  unfold
    positiveP506MatterCurrentFullSynchronizedLorentzCoframeResponse
  abel

/-! ## Genuine actual-origin density derivative -/

def positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensityPath
    (variation : LorentzianCoframe)
    (parameter : ℝ) : ℝ :=
  positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensity
    (positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField.coframe +
      parameter • variation)

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensityPath_hasDerivAt
    (variation : LorentzianCoframe) :
    HasDerivAt
      (positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensityPath
        variation)
      (currentFullSynchronizedProducerCoframeActionCovector
        positiveSmoothUnifiedSource CurrentState 0 variation)
      0 := by
  have determinantContinuous :
      Continuous fun parameter : ℝ =>
        Matrix.det
          ((1 : LorentzianCoframe) + parameter • variation) :=
    StageNineCoframeVariation.coframe_det_contDiff.continuous.comp
      (by fun_prop)
  have eventuallyNondegenerate :
      ∀ᶠ parameter in nhds (0 : ℝ),
        Matrix.det
            ((1 : LorentzianCoframe) + parameter • variation) ≠
          0 :=
    determinantContinuous.continuousAt.eventually_ne (by simp)
  have densityEventually : Filter.EventuallyEq (nhds (0 : ℝ))
      (fun parameter : ℝ =>
        positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensity
          ((1 : LorentzianCoframe) + parameter • variation))
      (currentFullSynchronizedProducerCoframeDensityPath
        positiveSmoothUnifiedSource CurrentState 0 variation) := by
    filter_upwards [eventuallyNondegenerate] with parameter nondegenerate
    exact
      positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensity_eq_producer
        _ nondegenerate
  have producerDerivative :=
    currentFullSynchronizedProducerCoframeDensityPath_hasDerivAt
      positiveSmoothUnifiedSource CurrentState 0
      preContorsionFullLorentzTriangularCurrent_coframe_origin variation
  have actualAtIdentity :=
    producerDerivative.congr_of_eventuallyEq densityEventually
  rw [show
    positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensityPath
        variation =
      fun parameter : ℝ =>
        positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensity
          ((1 : LorentzianCoframe) + parameter • variation) by
    funext parameter
    unfold
      positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensityPath
    rw [
      positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_coframe]]
  exact actualAtIdentity

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensityPath_hasDerivAt_zero
    (variation : LorentzianCoframe) :
    HasDerivAt
      (positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensityPath
        variation)
      0
      0 := by
  have actual :=
    positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensityPath_hasDerivAt
      variation
  rw [currentFullSynchronizedProducerCoframeActionCovector_eq_zero] at actual
  simpa using actual

/-! ## No-premise exact-source checkpoint -/

structure
    PositiveP506MatterCurrentFullSynchronizedLorentzActualOriginCoframeActionLaw :
    Prop where
  positiveC3h205 :
    PositiveP506MatterCurrentFullSynchronizedLorentzMixedBFReadoutLaw
  nonGravityOriginFidelity :
    coframeNonGravityContactProjection
        positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField =
      coframeNonGravityContactProjection
        (currentFullSynchronizedProducerOriginField positiveSmoothUnifiedSource
          CurrentState 0)
  actualOriginSimplicity :
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField.gravityAuxiliary =
      physicalIIPlusBivector
        positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField.coframe
  densityBridge : ∀ candidate,
    Matrix.det candidate ≠ 0 →
      positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensity
          candidate =
        currentFullSynchronizedProducerCoframeDensity
          positiveSmoothUnifiedSource CurrentState 0 candidate
  actualDensityDerivative : ∀ variation,
    HasDerivAt
      (positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensityPath
        variation)
      (currentFullSynchronizedProducerCoframeActionCovector
        positiveSmoothUnifiedSource CurrentState 0 variation)
      0
  producerConsistency : ∀ variation,
    HasDerivAt
      (positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensityPath
        variation)
      0
      0

theorem
    positiveP506MatterCurrentFullSynchronizedLorentzActualOriginCoframeAction_realizes_C3h206 :
    PositiveP506MatterCurrentFullSynchronizedLorentzActualOriginCoframeActionLaw := by
  exact
    { positiveC3h205 :=
        positiveP506MatterCurrentFullSynchronizedLorentzMixedBFReadout_realizes_C3h205
      nonGravityOriginFidelity :=
        positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_nonGravity_eq_producer
      actualOriginSimplicity :=
        positiveP506MatterCurrentFullSynchronizedLorentzActualOriginField_simplicity
      densityBridge :=
        positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensity_eq_producer
      actualDensityDerivative :=
        positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensityPath_hasDerivAt
      producerConsistency :=
        positiveP506MatterCurrentFullSynchronizedLorentzActualCoframeDensityPath_hasDerivAt_zero }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedLorentzActualOriginCoframeAction
