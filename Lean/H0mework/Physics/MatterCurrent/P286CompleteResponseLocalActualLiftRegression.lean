import H0mework.Physics.MatterCurrent.P286CompleteResponseLocalActualLift
import H0mework.Physics.Gauge.ConnectionSectorSourceBalance
import H0mework.Physics.MatterCurrent.CoframeStress
import H0mework.Physics.MatterCurrent.P286NonzeroCurvatureScalarLocalStationarity

/-!
# S9-C3h165 direct regression: complete U7-action response on U8

These regressions consume the C3h165 producer-soundness law.  They verify
exact P506/L0 lineage, uniqueness of both action responses, retained nonzero
curvature, origin fidelity, and the direct full-direction momentum response.

The connection equation check is recorded only as producer consistency: its
unique velocity and charge were obtained by inverting that same action
equation.  The scalar and P286-auxiliary checks below are dependency audits,
not new independent closures: changing the auxiliary germ preserves the
fields they read at the tested contact.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLiftRegression

open ProofFreeRicherAnholonomicSource
open DiracExteriorMatterAction
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineCanonicalCauchyState
open StageNineBiradialCoframeResponse
open StageNineConnectionSectorSourceBalance
open StageNineJointActionLocalActualLift
open StageNineMatterActionTimeVelocity
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariationDensity
open StageNineScalarPointwiseEquation
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCartanActual
open StageNineSourceActionGeneratedP506MatterCurrentCoframeStress
open StageNineSourceActionGeneratedP506MatterCurrentEinsteinCartanLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentEinsteinCartanPrimitiveCauchyUpdate
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledLinearPlebanskiLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledP286GaussLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureScalarLocalStationarity
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open StageNineSourceGeneratedMatterSpinActionUpdate

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

theorem c3h165_positive_regression :
    PositiveP506MatterCurrentP286CompleteResponseProducerSoundnessLaw :=
  positiveP506MatterCurrentP286CompleteResponseLocalActualLift_realizes_C3h165

theorem c3h165_exact_lineage_regression :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference :=
  c3h165_positive_regression.sourceGeneratedU7.exactP506L0Lineage

theorem c3h165_unique_complete_response_regression :
    (∀ candidate : P286SpatialGaugeDirection,
        p286SpatialBFLegendreDualOperator candidate =
            positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget →
          candidate =
            positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity) ∧
      (∀ candidate : P286CoordinateCarrier,
        (∀ component,
          p286CoordinateLiePairing candidate component =
            positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget
              component) →
          candidate = positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge) :=
  ⟨c3h165_positive_regression.spatialResponseUnique,
    c3h165_positive_regression.temporalResponseUnique⟩

theorem c3h165_nonzero_curvature_and_consistency_regression :
    holonomicGaugeCurvature
          positiveP506MatterCurrentP286CompleteResponseLocalActualLift 0 ≠ 0 ∧
      ∀ direction : P286GaugeOneForm,
        p286GaugeConnectionEulerLagrangeCoefficient
            positiveSmoothUnifiedSource
            positiveP506MatterCurrentP286CompleteResponseLocalActualLift
            direction 0 = 0 :=
  ⟨c3h165_positive_regression.retainedCurvatureNonzero,
    c3h165_positive_regression.producerConsistency⟩

theorem c3h165_p286_auxiliary_origin_dependency_regression :
    holonomicGaugeCurvature
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift 0 =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear
            (positiveP506MatterCurrentP286CompleteResponseLocalActualLift.coframe
              0))
        (positiveP506MatterCurrentP286CompleteResponseLocalActualLift.gaugeAuxiliary
          0) := by
  rw [positiveP506MatterCurrentP286CompleteResponseLocalActualLift_gaugeCurvature_origin,
    c3h165_positive_regression.retainsU7Fields.1,
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift_gaugeAuxiliary_origin]
  exact
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_p286AuxiliaryEquation_origin

/-- Installing a different P286 auxiliary germ does not enter the scalar
Euler coefficient.  This theorem prevents a field update from being mistaken
for evidence that an unrelated old equation became false. -/
theorem installGeneratedGaugeAuxiliaryGerm_scalarEuler_eq
    (source : SmoothUnifiedSource)
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData)
    (direction : ScalarCoordinateCarrier) (point : BasePoint) :
    scalarEulerLagrangeDirectionalCoefficient source
        (installGeneratedGaugeAuxiliaryGerm base auxiliary) direction point =
      scalarEulerLagrangeDirectionalCoefficient source base direction point := by
  rfl

theorem c3h165_scalar_origin_dependency_regression
    (direction : ScalarCoordinateCarrier) :
    scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift
        direction 0 = 0 := by
  rw [positiveP506MatterCurrentP286CompleteResponseLocalActualLift,
    installGeneratedGaugeAuxiliaryGerm_scalarEuler_eq]
  exact
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarEuler_origin
      direction

/-! ## Attached nontrivial-current control -/

private theorem actionGeneratedMatterLocalField_zeroSlice_of_constant
    (state : StageNineCauchyState) (anchor : StageNineSpatialPoint)
    (target : DiracExteriorMatterCarrier)
    (stateMatter : state.matter = fun _ => target)
    (space : StageNineSpatialPoint) :
    actionGeneratedMatterLocalField state anchor
        (canonicalCauchySlicePoint 0 space) = target := by
  have spatialDerivativeZero (direction : Fin 3) :
      cauchyMatterSpatialDerivativeCoordinate state anchor direction = 0 := by
    unfold cauchyMatterSpatialDerivativeCoordinate
    rw [stateMatter]
    simp
  apply matterCoordinateEquiv.injective
  simp [actionGeneratedMatterLocalField,
    actionGeneratedMatterLocalCoordinate,
    actionGeneratedMatterLocalIncrement,
    actionGeneratedMatterLocalJetCoordinate,
    stateMatter, spatialDerivativeZero,
    canonicalCauchySlicePoint, Fin.sum_univ_four]

private theorem
    currentEinsteinCartanLocalActualLift_matter_zeroSlice
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentEinsteinCartanLocalActualLift.matter
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe := by
  change
    actionGeneratedMatterLocalField
        positiveP506MatterCurrentEinsteinCartanCauchyState 0
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe
  exact actionGeneratedMatterLocalField_zeroSlice_of_constant
    positiveP506MatterCurrentEinsteinCartanCauchyState 0
    diracSpinTwoMatterProbe
    positiveP506MatterCurrentEinsteinCartanCauchyState_matter_constant
    space

private theorem currentLinearPlebanskiLocalActualLift_matter_zeroSlice
    (space : StageNineSpatialPoint) :
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.matter
        (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe := by
  have retained :
      positiveP506MatterCurrentLinearPlebanskiLocalActualLift.matter =
        positiveP506MatterCurrentLinearPlebanskiBaseActual.matter :=
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_realizes
      |>.retainsBasePrimitiveFields |>.2 |>.2 |>.2 |>.2 |>.2 |>.1
  have baseEq :
      positiveP506MatterCurrentLinearPlebanskiBaseActual.matter =
        positiveP506MatterCurrentEinsteinCartanLocalActualLift.matter :=
    congrArg StageNineHolonomicConfiguration.matter
      positiveP506MatterCurrentLinearPlebanskiBaseActual_eq_feedbackActual
  calc
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.matter
          (canonicalCauchySlicePoint 0 space) =
        positiveP506MatterCurrentLinearPlebanskiBaseActual.matter
          (canonicalCauchySlicePoint 0 space) :=
      congrFun retained _
    _ = positiveP506MatterCurrentEinsteinCartanLocalActualLift.matter
          (canonicalCauchySlicePoint 0 space) :=
      congrFun baseEq _
    _ = _ := currentEinsteinCartanLocalActualLift_matter_zeroSlice space

private theorem currentLinearPlebanskiCauchyState_matter_allSpace :
    positiveP506MatterCurrentLinearPlebanskiCauchyState.matter =
      fun _ => diracSpinTwoMatterProbe := by
  funext space
  unfold positiveP506MatterCurrentLinearPlebanskiCauchyState
    canonicalCauchyRestriction
  exact currentLinearPlebanskiLocalActualLift_matter_zeroSlice space

theorem c3h165_U7_matter_origin_regression :
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.matter 0 =
      diracSpinTwoMatterProbe := by
  change
    (sourceActionGeneratedJointLocalActualLift positiveSmoothUnifiedSource
      positiveP506MatterCurrentP286GaussCauchyState
      positiveP506MatterCurrentP286AxisContact).matter 0 =
      _
  rw [sourceActionGeneratedJointLocalActualLift_initialMatter]
  unfold positiveP506MatterCurrentP286GaussCauchyState
    canonicalCauchyRestriction
  change
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.matter
        (canonicalCauchySlicePoint 0
          positiveP506MatterCurrentP286AxisContact) =
      _
  rw [
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_matter,
    positiveP506MatterCurrentGravityCoupledLocalActualLift_matter,
    positiveP506MatterCurrentGravityCoupledBaseActual_eq_synchronized]
  change
    actionGeneratedMatterLocalField
        positiveP506MatterCurrentLinearPlebanskiCauchyState 0
        (canonicalCauchySlicePoint 0
          positiveP506MatterCurrentP286AxisContact) =
      _
  exact actionGeneratedMatterLocalField_zeroSlice_of_constant
    positiveP506MatterCurrentLinearPlebanskiCauchyState 0
    diracSpinTwoMatterProbe currentLinearPlebanskiCauchyState_matter_allSpace
    positiveP506MatterCurrentP286AxisContact

/-! ## Normalization-invariant nontriviality of the generated charge -/

private theorem p286GaugeBFAlgebraicCoefficient_origin_zero_of_connection_zero
    (configuration : StageNineHolonomicConfiguration)
    (connectionZero : configuration.gaugeConnection 0 = 0)
    (direction : P286GaugeOneForm) :
    p286GaugeBFAlgebraicCoefficient configuration direction 0 = 0 := by
  have algebraicZero :
      p286GaugeConnectionAlgebraicCurvatureDirection configuration direction
          0 =
        0 := by
    funext pair
    unfold p286GaugeConnectionAlgebraicCurvatureDirection
      p286GaugeConnectionAlgebraicCurvatureVariation
      holonomicP286GaugeConnectionCoordinate
    simp only [connectionZero, Pi.zero_apply, map_zero,
      p286CoordinateLieBracket_zero_left,
      p286CoordinateLieBracket_zero_right, zero_add]
  unfold p286GaugeBFAlgebraicCoefficient
  rw [algebraicZero]
  simp

private theorem p286ScalarCurrentCoefficient_origin_zero_of_covariantDerivative_zero
    (configuration : StageNineHolonomicConfiguration)
    (derivativeZero :
      ∀ formDirection,
        holonomicScalarCovariantDerivative configuration 0 formDirection = 0)
    (direction : P286GaugeOneForm) :
    p286ScalarCurrentCoefficient positiveSmoothUnifiedSource configuration
        direction 0 =
      0 := by
  unfold p286ScalarCurrentCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
  have pointDerivativeZero :
      (toContinuumPointField configuration 0).scalarCovariantDerivative = 0 := by
    funext formDirection
    exact derivativeZero formDirection
  rw [pointDerivativeZero]
  simp [scalarFrameRelativeCovariantDerivative,
    scalarCoordinatePairingRe]

private theorem p286MatterCurrentCoefficient_origin_eq_of_contact
    (first second : StageNineHolonomicConfiguration)
    (coframeEq : first.coframe 0 = second.coframe 0)
    (matterEq : first.matter 0 = second.matter 0)
    (conjugateEq : first.conjugateMatter 0 = second.conjugateMatter 0)
    (direction : P286GaugeOneForm) :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource first direction 0 =
      p286MatterCurrentCoefficient positiveSmoothUnifiedSource second direction
        0 := by
  unfold p286MatterCurrentCoefficient generatedVolumeDensity
    matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
    holonomicMatterGaugeConnectionVariation
  simp only [toContinuumPointField]
  rw [coframeEq, matterEq, conjugateEq]

private theorem c3h165_U7_gaugeConnection_origin_zero :
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeConnection
        0 =
      0 := by
  funext direction
  apply p286CoordinateEquiv.injective
  simpa [currentP506MatterP286ConnectionCoordinate] using
    currentP506MatterP286ConnectionCoordinate_origin_zero direction

private theorem c3h165_U7_coframe_origin_one :
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.coframe 0 =
      1 := by
  rw [positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_coframe_biradial]
  exact biradialCoframe_one_one

private theorem c3h165_U7_actionCurrent_origin_eq_currentU5
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift direction
        0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledLocalActualLift direction 0 := by
  rw [p286GaugeConnectionAlgebraicCurrentCoefficient_eq_sectors,
    p286GaugeConnectionAlgebraicCurrentCoefficient_eq_sectors]
  rw [p286GaugeBFAlgebraicCoefficient_origin_zero_of_connection_zero
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
      c3h165_U7_gaugeConnection_origin_zero,
    p286GaugeBFAlgebraicCoefficient_origin_zero_of_connection_zero
      positiveP506MatterCurrentGravityCoupledLocalActualLift (by
        rw [positiveP506MatterCurrentGravityCoupledLocalActualLift_gaugeConnection_zero]
        rfl),
    p286ScalarCurrentCoefficient_origin_zero_of_covariantDerivative_zero
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarCovariantDerivative_origin_zero,
    p286ScalarCurrentCoefficient_origin_zero_of_covariantDerivative_zero
      positiveP506MatterCurrentGravityCoupledLocalActualLift
      (positiveP506MatterCurrentGravityCoupledLocalActualLift_scalarCovariantDerivative_zero
        0)]
  simp only [zero_add]
  apply p286MatterCurrentCoefficient_origin_eq_of_contact
  · rw [c3h165_U7_coframe_origin_one,
      positiveP506MatterCurrentGravityCoupledLocalActualLift_coframe_one]
  · rw [c3h165_U7_matter_origin_regression,
      positiveP506MatterCurrentGravityCoupledLocalActualLift_matter_origin]
  · rw [
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_conjugate_origin,
      positiveP506MatterCurrentGravityCoupledLocalActualLift_conjugate_origin]

private theorem c3h165_currentMomentum_actionCurrent_origin_eq_currentU5
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift
        direction 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledLocalActualLift direction 0 := by
  rw [p286GaugeConnectionAlgebraicCurrentCoefficient_eq_sectors,
    p286GaugeConnectionAlgebraicCurrentCoefficient_eq_sectors]
  rw [p286GaugeBFAlgebraicCoefficient_origin_zero_of_connection_zero
      positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift (by
        change
          positiveP506MatterCurrentGravityCoupledLocalActualLift.gaugeConnection
              0 =
            0
        rw [positiveP506MatterCurrentGravityCoupledLocalActualLift_gaugeConnection_zero]
        rfl),
    p286GaugeBFAlgebraicCoefficient_origin_zero_of_connection_zero
      positiveP506MatterCurrentGravityCoupledLocalActualLift (by
        rw [positiveP506MatterCurrentGravityCoupledLocalActualLift_gaugeConnection_zero]
        rfl),
    p286ScalarCurrentCoefficient_origin_zero_of_covariantDerivative_zero
      positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift (by
        intro formDirection
        change
          holonomicScalarCovariantDerivative
              positiveP506MatterCurrentGravityCoupledLocalActualLift 0
              formDirection =
            0
        exact
          positiveP506MatterCurrentGravityCoupledLocalActualLift_scalarCovariantDerivative_zero
            0 formDirection),
    p286ScalarCurrentCoefficient_origin_zero_of_covariantDerivative_zero
      positiveP506MatterCurrentGravityCoupledLocalActualLift
      (positiveP506MatterCurrentGravityCoupledLocalActualLift_scalarCovariantDerivative_zero
        0)]
  simp only [zero_add]
  apply p286MatterCurrentCoefficient_origin_eq_of_contact <;> rfl

/-- Convention-locked readout only.  Physical progress below consumes only
its normalization-invariant consequence that the generated target is
nonzero. -/
private theorem c3h165_temporalActionTarget_hypercharge_conventionReadout :
    positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget
        hyperchargeCoordinate =
      -1 := by
  calc
    _ = p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
          (p286TemporalGaugeOneForm hyperchargeCoordinate) 0 := rfl
    _ = p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentGravityCoupledLocalActualLift
          (p286TemporalGaugeOneForm hyperchargeCoordinate) 0 :=
      c3h165_U7_actionCurrent_origin_eq_currentU5 _
    _ = p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift
          (p286TemporalGaugeOneForm hyperchargeCoordinate) 0 :=
      (c3h165_currentMomentum_actionCurrent_origin_eq_currentU5 _).symm
    _ = positiveP506MatterCurrentGravityCoupledP286TemporalGaussActionTarget
          hyperchargeCoordinate := rfl
    _ = -1 := temporalGaussActionTarget_hypercharge

theorem c3h165_generatedGaussCharge_ne_zero_regression :
    positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge ≠ 0 := by
  intro chargeZero
  have response :=
    positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge_response
      hyperchargeCoordinate
  rw [chargeZero,
    c3h165_temporalActionTarget_hypercharge_conventionReadout] at response
  norm_num at response

/-! ## Negative control attached to the positive producer

Freezing the old auxiliary value preserves the origin contact but removes the
generated first jet.  The nonzero temporal action response therefore rejects
that frozen germ.  This is a necessity regression for the C3h165 update, not
a standalone no-go for other source-generated developments.
-/

def c3h165FrozenAuxiliaryLocalActualLift :
    StageNineHolonomicConfiguration :=
  installGeneratedGaugeAuxiliaryGerm
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
    (fun _ =>
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeAuxiliary
        0)

private theorem c3h165FrozenAuxiliaryLocalActualLift_bfMomentum_constant
    (direction : P286GaugeTwoForm) :
    p286GaugeConnectionBFDifferentialMomentum
        c3h165FrozenAuxiliaryLocalActualLift direction =
      fun _ =>
        p286GaugeConnectionBFDifferentialMomentum
          c3h165FrozenAuxiliaryLocalActualLift direction 0 := by
  funext point
  unfold p286GaugeConnectionBFDifferentialMomentum generatedVolumeDensity
    holonomicP286GaugeAuxiliaryCoordinate
    c3h165FrozenAuxiliaryLocalActualLift
  simp only [toContinuumPointField, installGeneratedGaugeAuxiliaryGerm]
  rw [
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_coframe_biradial]

private theorem c3h165FrozenAuxiliaryLocalActualLift_bfDivergence_zero
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionBFDifferentialMomentumDivergence
        c3h165FrozenAuxiliaryLocalActualLift direction 0 =
      0 := by
  unfold p286GaugeConnectionBFDifferentialMomentumDivergence
  apply Finset.sum_eq_zero
  intro derivativeDirection _
  rw [
    c3h165FrozenAuxiliaryLocalActualLift_bfMomentum_constant]
  simp [fieldDirectionalDerivative]

private theorem c3h165FrozenAuxiliaryLocalActualLift_actionCurrent_origin
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource c3h165FrozenAuxiliaryLocalActualLift
        direction 0 =
      positiveP506MatterCurrentP286NonzeroCurvatureFullActionTarget
        direction := by
  rw [c3h165FrozenAuxiliaryLocalActualLift]
  exact installGeneratedGaugeAuxiliaryGerm_actionCurrent_eq_of_contact
    positiveSmoothUnifiedSource _ _ 0 rfl direction

theorem c3h165_frozen_auxiliary_germ_rejected_regression :
    p286GaugeConnectionEulerLagrangeCoefficient
        positiveSmoothUnifiedSource c3h165FrozenAuxiliaryLocalActualLift
        (p286TemporalGaugeOneForm hyperchargeCoordinate) 0 ≠
      0 := by
  rw [p286GaugeConnectionEulerLagrangeCoefficient,
    c3h165FrozenAuxiliaryLocalActualLift_actionCurrent_origin,
    c3h165FrozenAuxiliaryLocalActualLift_bfDivergence_zero]
  change
    positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget
        hyperchargeCoordinate -
        0 ≠
      0
  rw [c3h165_temporalActionTarget_hypercharge_conventionReadout]
  norm_num

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLiftRegression
