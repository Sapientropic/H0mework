import H0mework.Physics.ConnectionJets.CurrentP286CompleteActionResponseFirstJet
import H0mework.Physics.MatterCurrent.FullSynchronizedResponseLocalActualLift

/-!
# S9-C3h168: current-action P286 response replay on the synchronized actual

The dependency-light current P286 operator takes the exact P506/L0 source and
the already generated synchronized actual `U*`.  It recomputes the complete
P286 action dual, uniquely generates its BF-Legendre velocity and
Lie-pairing charge, and installs the canonical temporal-plus-radial auxiliary
germ.  This module proves that the resulting actual is exactly the same
`U*`.

The fixed-point equality is a specialization readout, not the producer by
itself.  The producer authority is the generic `(source, current) → actual`
operator together with its forward BF-momentum first-jet laws.  Substitution
in the defining P286 equation remains producer consistency, while the scalar
equation retained from C3h166 remains the independent constraint.

No residual inverse, endpoint, response witness, velocity, charge,
coefficient, source value, ansatz, branch receipt, or equation certificate
enters this construction.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedP286ResponseReplay

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineBlockwiseConstitutive
open StageNineCoframeTwoFormPairing
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

/-! ## Exact current-action specialization -/

theorem positiveP506MatterCurrentUStarP286FullActionTarget_eq_U7 :
    currentP286FullActionTarget positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift =
      positiveP506MatterCurrentP286NonzeroCurvatureFullActionTarget := by
  apply LinearMap.ext
  intro direction
  change
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      positiveP506MatterCurrentP286NonzeroCurvatureFullActionTarget direction
  calc
    _ =
        p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentCompleteBaseActual direction 0 :=
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_p286ActionCurrent_eq_completeBase
        direction
    _ =
        positiveP506MatterCurrentP286NonzeroCurvatureFullActionTarget
          direction :=
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift_actionCurrent_origin
        direction

theorem positiveP506MatterCurrentUStarP286SpatialActionTarget_eq_U7 :
    currentP286SpatialActionTarget positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift =
      positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget := by
  apply LinearMap.ext
  intro direction
  rw [currentP286SpatialActionTarget_apply,
    positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget_apply,
    positiveP506MatterCurrentUStarP286FullActionTarget_eq_U7]

theorem positiveP506MatterCurrentUStarP286TemporalActionTarget_eq_U7 :
    currentP286TemporalActionTarget positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift =
      positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget := by
  apply LinearMap.ext
  intro component
  rw [currentP286TemporalActionTarget_apply,
    positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget_apply,
    positiveP506MatterCurrentUStarP286FullActionTarget_eq_U7]

theorem positiveP506MatterCurrentUStarP286SpatialAuxiliaryVelocity_eq_U7 :
    currentP286SpatialAuxiliaryVelocity positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift =
      positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity := by
  unfold currentP286SpatialAuxiliaryVelocity
    positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity
  rw [positiveP506MatterCurrentUStarP286SpatialActionTarget_eq_U7]

theorem positiveP506MatterCurrentUStarP286GaussCharge_eq_U7 :
    currentP286GaussCharge positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift =
      positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge := by
  unfold currentP286GaussCharge
    positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
  rw [positiveP506MatterCurrentUStarP286TemporalActionTarget_eq_U7]

theorem positiveP506MatterCurrentUStar_gaugeAuxiliary_origin_eq_U7 :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gaugeAuxiliary
        0 =
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeAuxiliary
        0 := by
  change
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift.gaugeAuxiliary
        0 =
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeAuxiliary
        0
  exact
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift_gaugeAuxiliary_origin

theorem positiveP506MatterCurrentUStarP286OriginAuxiliaryCoordinate_eq_U7 :
    currentP286OriginAuxiliaryCoordinate
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift =
      positiveP506MatterCurrentP286NonzeroCurvatureOriginAuxiliaryCoordinate := by
  funext pair
  exact congrArg p286CoordinateEquiv
    (congrFun positiveP506MatterCurrentUStar_gaugeAuxiliary_origin_eq_U7 pair)

theorem
    positiveP506MatterCurrentUStarP286CompleteResponseAuxiliaryCoordinate_eq_U8 :
    currentP286CompleteResponseAuxiliaryCoordinate
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift =
      positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate := by
  funext point
  unfold currentP286CompleteResponseAuxiliaryCoordinate
    positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate
  rw [positiveP506MatterCurrentUStarP286OriginAuxiliaryCoordinate_eq_U7,
    positiveP506MatterCurrentUStarP286SpatialAuxiliaryVelocity_eq_U7,
    positiveP506MatterCurrentUStarP286GaussCharge_eq_U7,
    currentP286CanonicalGaussRadialAuxiliaryProfile_eq_existing]

theorem
    positiveP506MatterCurrentUStarP286CompleteResponseAuxiliaryField_eq_U8 :
    currentP286CompleteResponseAuxiliaryField
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift =
      positiveP506MatterCurrentP286CompleteResponseAuxiliaryField := by
  funext point pair
  unfold currentP286CompleteResponseAuxiliaryField
    positiveP506MatterCurrentP286CompleteResponseAuxiliaryField
  rw [
    positiveP506MatterCurrentUStarP286CompleteResponseAuxiliaryCoordinate_eq_U8]

theorem
    positiveP506MatterCurrentUStarP286CompleteResponseAuxiliaryField_eq_UStar :
    currentP286CompleteResponseAuxiliaryField
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift =
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gaugeAuxiliary := by
  calc
    _ = positiveP506MatterCurrentP286CompleteResponseAuxiliaryField :=
      positiveP506MatterCurrentUStarP286CompleteResponseAuxiliaryField_eq_U8
    _ =
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gaugeAuxiliary :=
      rfl

/-- Specialization replay: recomputing and installing the complete P286
response from `U*` yields the same whole actual. -/
theorem
    positiveP506MatterCurrentUStarP286CompleteActionResponseOperator_replays :
    currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift =
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift := by
  apply StageNineHolonomicConfiguration.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact
      positiveP506MatterCurrentUStarP286CompleteResponseAuxiliaryField_eq_UStar
  · rfl
  · rfl
  · rfl

/-! ## Same-actual forward first-jet laws -/

theorem positiveP506MatterCurrentUStarP286BFMomentumDerivative
    (direction : P286GaugeTwoForm)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
          direction)
        0 derivativeDirection =
      (if canonicalLorentzianTimeDirection = derivativeDirection then
        p286GaugeAuxiliaryHodgePairingPolynomial 1
          (p286SpatialAuxiliaryVelocityEmbedding
            (currentP286SpatialAuxiliaryVelocity positiveSmoothUnifiedSource
              positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift))
          direction
      else 0) +
        ∑ axis : Fin 3,
          if axis.succ = derivativeDirection then
            canonicalP286EqualAxisCoefficient *
              p286GaugeAuxiliaryHodgePairingPolynomial 1
                (p286GaussAuxiliaryAxisEmbedding
                  (currentP286GaussCharge positiveSmoothUnifiedSource
                    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift)
                  axis)
                direction
          else 0 := by
  simpa only [
    positiveP506MatterCurrentUStarP286CompleteActionResponseOperator_replays]
    using
      currentP286CompleteActionResponseOperator_bfMomentum_derivative
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframe_one
        direction derivativeDirection

theorem positiveP506MatterCurrentUStarP286TemporalBFMomentumResponse
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionTemporalBFMomentumDerivative
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      currentP286SpatialActionTarget positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        (fun index => direction index.succ) := by
  simpa only [
    positiveP506MatterCurrentUStarP286CompleteActionResponseOperator_replays]
    using
      currentP286CompleteActionResponseOperator_temporalBFMomentumResponse
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframe_one
        direction

theorem positiveP506MatterCurrentUStarP286SpatialBFMomentumResponse
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionSpatialBFMomentumDivergence
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      currentP286TemporalActionTarget positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        (direction canonicalLorentzianTimeDirection) := by
  simpa only [
    positiveP506MatterCurrentUStarP286CompleteActionResponseOperator_replays]
    using
      currentP286CompleteActionResponseOperator_spatialBFMomentumResponse
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframe_one
        direction

/-- Re-substitution in the same defining action equation is producer
consistency, not an independent constraint. -/
theorem positiveP506MatterCurrentUStarP286ConnectionProducerConsistency
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      0 := by
  simpa only [
    positiveP506MatterCurrentUStarP286CompleteActionResponseOperator_replays]
    using
      currentP286CompleteActionResponseOperator_connectionEquation_origin
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframe_one
        direction

/-! ## No-premise C3h168 law -/

structure PositiveP506MatterCurrentFullSynchronizedP286ResponseReplayLaw :
    Prop where
  sourceGeneratedUStar :
    PositiveP506MatterCurrentFullSynchronizedResponseLocalActualLaw
  exactP506L0Lineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference
  fullActionReadFromUStar : ∀ direction : P286GaugeOneForm,
    currentP286FullActionTarget positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0
  spatialResponse :
    p286SpatialBFLegendreDualOperator
        (currentP286SpatialAuxiliaryVelocity positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift) =
      currentP286SpatialActionTarget positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
  spatialResponseUnique : ∀ candidate : P286SpatialGaugeDirection,
    p286SpatialBFLegendreDualOperator candidate =
        currentP286SpatialActionTarget positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift →
      candidate =
        currentP286SpatialAuxiliaryVelocity positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
  temporalResponse : ∀ component : P286CoordinateCarrier,
    p286CoordinateLiePairing
        (currentP286GaussCharge positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift)
        component =
      currentP286TemporalActionTarget positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        component
  temporalResponseUnique : ∀ candidate : P286CoordinateCarrier,
    (∀ component,
      p286CoordinateLiePairing candidate component =
        currentP286TemporalActionTarget positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
          component) →
      candidate =
        currentP286GaussCharge positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
  symmetricNormalizationUnique : ∀ candidate : ℝ,
    (∑ _axis : Fin 3, candidate) = 1 →
      candidate = canonicalP286EqualAxisCoefficient
  generatedSameActual :
    currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift =
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
  actualTemporalMomentumResponse : ∀ direction : P286GaugeOneForm,
    p286GaugeConnectionTemporalBFMomentumDerivative
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      currentP286SpatialActionTarget positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        (fun index => direction index.succ)
  actualSpatialMomentumResponse : ∀ direction : P286GaugeOneForm,
    p286GaugeConnectionSpatialBFMomentumDivergence
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      currentP286TemporalActionTarget positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        (direction canonicalLorentzianTimeDirection)
  producerP286ConnectionConsistency : ∀ direction : P286GaugeOneForm,
    p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      0
  independentScalarConstraint : ∀ direction : ScalarCoordinateCarrier,
    scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      0
  retainedGaugeCurvatureNonzero :
    holonomicGaugeCurvature
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0 ≠
      0

theorem
    positiveP506MatterCurrentFullSynchronizedP286ResponseReplay_realizes_C3h168 :
    PositiveP506MatterCurrentFullSynchronizedP286ResponseReplayLaw := by
  exact
    { sourceGeneratedUStar :=
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_realizes_C3h166
      exactP506L0Lineage :=
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_realizes_C3h166.producerSoundness.exactP506L0Lineage
      fullActionReadFromUStar := fun _ => rfl
      spatialResponse :=
        currentP286SpatialAuxiliaryVelocity_response _ _
      spatialResponseUnique := fun candidate response =>
        currentP286SpatialAuxiliaryVelocity_unique _ _ candidate response
      temporalResponse :=
        currentP286GaussCharge_response _ _
      temporalResponseUnique := fun candidate response =>
        currentP286GaussCharge_unique _ _ candidate response
      symmetricNormalizationUnique := fun candidate normalized =>
        canonicalP286EqualAxisCoefficient_unique candidate normalized
      generatedSameActual :=
        positiveP506MatterCurrentUStarP286CompleteActionResponseOperator_replays
      actualTemporalMomentumResponse :=
        positiveP506MatterCurrentUStarP286TemporalBFMomentumResponse
      actualSpatialMomentumResponse :=
        positiveP506MatterCurrentUStarP286SpatialBFMomentumResponse
      producerP286ConnectionConsistency :=
        positiveP506MatterCurrentUStarP286ConnectionProducerConsistency
      independentScalarConstraint :=
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_realizes_C3h166.independentScalarConstraint
      retainedGaugeCurvatureNonzero :=
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_gaugeCurvature_ne_zero }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedP286ResponseReplay
