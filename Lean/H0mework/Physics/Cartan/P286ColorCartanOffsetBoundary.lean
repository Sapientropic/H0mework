import H0mework.Physics.ConnectionJets.P286SourceAffineCurvatureJetNormalForm

/-!
# S9-C3h77c readout: actual P286 color-Cartan offset boundary

This module fixes the color-Cartan generator in spacetime direction 0 and
uses the actual source-affine curvature-jet normal form to expose the four
C3h70 connection-response sectors.  At the canonical origin the BF algebraic,
BF divergence, scalar-current, and matter-current readouts are respectively
0, -1, 0, and 0; hence the actual affine offset evaluates to +1 on this
direction.

The result supplies a readout for the downstream carrier-class obstruction on
the frozen connection-only slice; it does not itself classify the response
range or zero fiber.  It accepts no range premise, zero-fiber witness,
connection displacement, endpoint, branch, source receipt, or stationarity
certificate, and it does not claim that the full joint shell is empty.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineP286ColorCartanOffsetBoundary

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineCompactSupportIntegrationByParts
open StageNineConnectionSectorSourceBalance
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGravityAlgebraicKeepResponseCoframeDefect
open StageNineGravityAlgebraicKeepResponseP286Defect
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ColorMixingOriginResidualTransport
open StageNineP286FixedBackgroundAffineResponseFiber
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286SameLineageAffineResponseSpecialization
open StageNinePositiveSourceGravityMouthResidualTransportIteration
open StageNinePositiveSourceNativeAlgebraicEliminationUpdate
open StageNinePositiveSourceNativeGravityCurvatureBridge
open StageNineResidualLimitCoframeBalanceDecision
open StageNineResidualLimitLorentzClassObstruction
open StageNineResidualLimitP286BFBalanceDecision
open StageNineResidualLimitP286ScalarSourceNormalForm
open StageNineResidualLimitScalarBalanceClosure
open StageNineSourceGeneratedP286AffineConnectionGerm
open StageNineSourceGeneratedPartialPrimitiveCarrier
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

open StageNineP286SourceAffineCurvatureJetNormalForm

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Fixed representation-derived diagnostic direction -/

/-- Color-Cartan in the `mu = 0` one-form component and zero elsewhere. -/
def colorCartanMuZeroDirection : P286GaugeOneForm
  | 0 => p286CoordinateEquiv colorCartanP286ConnectionDirection
  | _ => 0

theorem colorCartanMuZeroDirection_eq_existingProbe :
    colorCartanMuZeroDirection = colorCartanP286Probe := by
  funext direction
  fin_cases direction <;>
    rfl

/-! ## Three sectors not involving the actual auxiliary jet -/

theorem colorCartanMuZero_linearResponse_eq_zero :
    colorMixingOriginLinearResponse colorCartanMuZeroDirection = 0 := by
  unfold colorMixingOriginLinearResponse colorCartanMuZeroDirection
  change -(1 / 2 : ℝ) *
      p286CoordinateLiePairing
        (p286CoordinateEquiv canonicalP286Generator)
        (p286CoordinateLieBracket
          (p286CoordinateEquiv colorCartanP286ConnectionDirection)
          (p286CoordinateEquiv colorMixingP286ConnectionDirection)) = 0
  rw [canonicalP286Pairing_colorCartanBracket_zero]
  norm_num

theorem residualLimit_colorCartanMuZero_p286BFAlgebraic_eq_zero :
    p286GaugeBFAlgebraicCoefficient residualLimitLorentzCarrierReader
        colorCartanMuZeroDirection 0 = 0 := by
  have balance := colorMixingOriginP286BFBalance_linear (1 / 2 : ℝ)
    colorCartanMuZeroDirection
  have divergence := colorMixingOriginP286Divergence_eq_zero (1 / 2 : ℝ)
    colorCartanMuZeroDirection
  rw [colorMixingOriginConfiguration_source] at balance divergence
  rw [colorCartanMuZero_linearResponse_eq_zero] at balance
  unfold p286GaugeBFBalanceCoefficient at balance
  rw [divergence] at balance
  norm_num at balance ⊢
  exact balance

theorem canonicalInput_p286AuxiliaryCoordinate_origin_eq_residualLimit :
    holonomicP286GaugeAuxiliaryCoordinate canonicalSourceNativeP286Input 0 =
      positiveResidualLimitP286AuxiliaryCoordinate 0 := by
  have curvatureEq :=
    positiveSourceP286AffineConnection_actualCurvature
      (installPositiveSourceNativeGravityKinematics
        residualLimitLorentzCarrierReader)
  change
    (fun pair => p286CoordinateEquiv
      (generatedP286GaugeConstitutiveAuxiliary positiveSmoothUnifiedSource
        (positiveSmoothUnifiedSource.legacy.coframeAt 0)
        (holonomicGaugeCurvature
          (positiveSourceNativeKinematicSeed
            residualLimitLorentzCarrierReader) 0) pair)) = _
  change
    holonomicGaugeCurvature
        (positiveSourceNativeKinematicSeed residualLimitLorentzCarrierReader)
        0 = sourceP286TargetCurvature positiveSmoothUnifiedSource.legacy
      at curvatureEq
  rw [curvatureEq]
  rfl

theorem canonicalInput_colorCartanMuZero_p286BFAlgebraic_eq_zero :
    p286GaugeBFAlgebraicCoefficient canonicalSourceNativeP286Input
        colorCartanMuZeroDirection 0 = 0 := by
  unfold p286GaugeBFAlgebraicCoefficient
  rw [canonicalInput_p286AuxiliaryCoordinate_origin_eq_residualLimit]
  change positiveResidualLimitP286BFAlgebraicResponse
      colorCartanMuZeroDirection = 0
  have residual :=
    residualLimit_colorCartanMuZero_p286BFAlgebraic_eq_zero
  unfold p286GaugeBFAlgebraicCoefficient at residual
  exact residual

theorem canonicalInput_scalar_eq_constantVacuum :
    canonicalSourceNativeP286Input.scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  change positiveResidualLimitSixFieldCarrier.scalar = _
  exact positiveResidualLimitSixFieldCarrier_scalar_eq_constantVacuum

theorem canonicalInput_scalarCovariantDerivative_origin_eq_source
    (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative canonicalSourceNativeP286Input 0 direction =
      positiveSourceOriginScalarGaugeDerivative direction := by
  unfold holonomicScalarCovariantDerivative
    positiveSourceOriginScalarGaugeDerivative
  rw [canonicalInput_scalar_eq_constantVacuum,
    positiveSourceNativeAlgebraicEliminationUpdate_gaugeConnection]
  simp [sourceP286AffineConnectionField_origin,
    fieldDirectionalDerivative]

theorem canonicalInput_colorCartanMuZero_p286ScalarCurrent_eq_zero :
    p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
      canonicalSourceNativeP286Input colorCartanMuZeroDirection 0 = 0 := by
  have coframeOrigin :
      (toContinuumPointField canonicalSourceNativeP286Input 0).coframe = 1 := by
    change canonicalSourceNativeP286Input.coframe 0 = 1
    rw [positiveSourceNativeAlgebraicEliminationUpdate_coframe]
    exact positiveSmoothUnifiedSource.legacy.coframeAt_zero
  have scalarOrigin :
      canonicalSourceNativeP286Input.scalar 0 =
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
    rw [canonicalInput_scalar_eq_constantVacuum]
  have covariantDerivativeOrigin :
      (toContinuumPointField canonicalSourceNativeP286Input
        0).scalarCovariantDerivative = positiveSourceOriginScalarGaugeDerivative := by
    funext direction
    exact canonicalInput_scalarCovariantDerivative_origin_eq_source direction
  have currentEq :
      p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
          canonicalSourceNativeP286Input colorCartanMuZeroDirection 0 =
        positiveSourceOriginP286ScalarCurrent colorCartanMuZeroDirection := by
    unfold p286ScalarCurrentCoefficient
      scalarGaugeConnectionKineticFirstVariationDensity
      positiveSourceOriginP286ScalarCurrent
      holonomicScalarGaugeConnectionVariation
    rw [coframeOrigin, scalarOrigin, covariantDerivativeOrigin]
    simp [generatedVolumeDensity, scalarFrameRelativeCovariantDerivative,
      p286GaugeConnectionMotherVariation]
    rw [coframeOrigin, Matrix.det_one, abs_one, one_mul]
  rw [currentEq]
  exact positiveSourceOriginP286ScalarCurrent_eq_zero
    colorCartanMuZeroDirection

theorem canonicalInput_colorCartanMuZero_p286MatterCurrent_eq_zero :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource
      canonicalSourceNativeP286Input colorCartanMuZeroDirection 0 = 0 := by
  unfold p286MatterCurrentCoefficient
    matterGaugeConnectionFirstVariationDensity
  have matterZero : canonicalSourceNativeP286Input.matter = 0 := by
    rfl
  have conjugateMatterZero : canonicalSourceNativeP286Input.conjugateMatter = 0 := by
    rfl
  rw [show
      (toContinuumPointField canonicalSourceNativeP286Input 0).conjugateMatter =
        0 by
    change canonicalSourceNativeP286Input.conjugateMatter 0 = 0
    rw [conjugateMatterZero]
    rfl]
  simp

/-! ## Four divergence summands for the color-Cartan direction -/

theorem colorCartanMomentum_direction_zero
    (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
        (p286GaugeExteriorDerivativeDirection 0 colorCartanMuZeroDirection)
        point = 0 := by
  rw [canonicalInput_p286DifferentialMomentum_normalForm_local,
    Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_positiveSourceFrame_apply_local]
  simp [p286GaugeExteriorDerivativeDirection, colorCartanMuZeroDirection,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond]

theorem colorCartanMomentum_direction_one
    (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
        (p286GaugeExteriorDerivativeDirection 1 colorCartanMuZeroDirection)
        point =
      2 * p286CoordinateLiePairing
        (actualNativeCurvatureCoordinate point 0)
        (p286CoordinateEquiv colorCartanP286ConnectionDirection) := by
  rw [canonicalInput_p286DifferentialMomentum_normalForm_local,
    Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_positiveSourceFrame_apply_local]
  simp [p286GaugeExteriorDerivativeDirection, colorCartanMuZeroDirection,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond,
    p286CoordinateLiePairing_neg_right_local]

theorem colorCartanMomentum_direction_two
    (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
        (p286GaugeExteriorDerivativeDirection 2 colorCartanMuZeroDirection)
        point =
      2 * p286CoordinateLiePairing
        (actualNativeCurvatureCoordinate point 1 +
          point 2 • actualNativeCurvatureCoordinate point 5)
        (p286CoordinateEquiv colorCartanP286ConnectionDirection) := by
  rw [canonicalInput_p286DifferentialMomentum_normalForm_local,
    Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_positiveSourceFrame_apply_local]
  simp [p286GaugeExteriorDerivativeDirection, colorCartanMuZeroDirection,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond,
    p286CoordinateLiePairing_neg_right_local]

theorem colorCartanMomentum_direction_three
    (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
        (p286GaugeExteriorDerivativeDirection 3 colorCartanMuZeroDirection)
        point =
      2 * p286CoordinateLiePairing
        (actualNativeCurvatureCoordinate point 2 -
          point 2 • actualNativeCurvatureCoordinate point 4)
        (p286CoordinateEquiv colorCartanP286ConnectionDirection) := by
  rw [canonicalInput_p286DifferentialMomentum_normalForm_local,
    Fin.sum_univ_six]
  simp_rw [liftGaugeTwoFormOperator_positiveSourceFrame_apply_local]
  simp [p286GaugeExteriorDerivativeDirection, colorCartanMuZeroDirection,
    lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond,
    p286CoordinateLiePairing_neg_right_local]

theorem colorCartanMomentum_direction_zero_derivative_eq_zero :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 0 colorCartanMuZeroDirection))
        0 0 = 0 := by
  have momentumFunction :
      p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 0 colorCartanMuZeroDirection) =
        fun _ => 0 := by
    funext point
    exact colorCartanMomentum_direction_zero point
  rw [momentumFunction]
  simp [fieldDirectionalDerivative]

theorem colorCartanMomentum_direction_one_derivative_eq_neg_one :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 1 colorCartanMuZeroDirection))
        0 1 = -1 := by
  let pairingFunction : BasePoint → ℝ := fun point =>
    p286CoordinateLiePairing (actualNativeCurvatureCoordinate point 0)
      (p286CoordinateEquiv colorCartanP286ConnectionDirection)
  have momentumFunction :
      p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 1 colorCartanMuZeroDirection) =
        fun point => 2 * pairingFunction point := by
    funext point
    exact colorCartanMomentum_direction_one point
  have pairingHasDerivative :=
    p286CoordinateLiePairingBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear
        (actualNativeCurvatureCoordinate_hasFDerivAt_origin 0)
        (hasFDerivAt_const
          (p286CoordinateEquiv colorCartanP286ConnectionDirection) 0)
  have pairingDifferentiable : DifferentiableAt ℝ pairingFunction 0 := by
    exact pairingHasDerivative.differentiableAt
  rw [momentumFunction]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul pairingDifferentiable 2]
  simp only [smul_apply, smul_eq_mul]
  change 2 * fieldDirectionalDerivative pairingFunction 0 1 = -1
  rw [fieldDirectionalDerivative_pairing_const_local
    (fun point => actualNativeCurvatureCoordinate point 0)
    (actualNativeCurvatureFDeriv 0) 0 1
    (p286CoordinateEquiv colorCartanP286ConnectionDirection)
    (actualNativeCurvatureCoordinate_hasFDerivAt_origin 0)]
  rw [actualNativeCurvature_zero_direction_one_pairing_colorCartan_eq_neg_half]
  norm_num

theorem actualFramedCurvatureOne_direction_two_eq_zero :
    fieldDirectionalDerivative
        (fun point : BasePoint =>
          actualNativeCurvatureCoordinate point 1 +
            point 2 • actualNativeCurvatureCoordinate point 5)
        0 2 = 0 := by
  let productDerivative : BasePoint →L[ℝ] P286CoordinateCarrier :=
    (p286BaseCoordinate 2 0) • actualNativeCurvatureFDeriv 5 +
      (p286BaseCoordinate 2).smulRight
        (actualNativeCurvatureCoordinate 0 5)
  have productHasDerivative :
      HasFDerivAt
          (fun point : BasePoint =>
            point 2 • actualNativeCurvatureCoordinate point 5)
          productDerivative 0 := by
    have rawDerivative :=
      (p286BaseCoordinate 2).hasFDerivAt.smul
        (actualNativeCurvatureCoordinate_hasFDerivAt_origin 5)
    change HasFDerivAt
      (fun point : BasePoint =>
        p286BaseCoordinate 2 point • actualNativeCurvatureCoordinate point 5)
      productDerivative 0 at rawDerivative
    simpa only [p286BaseCoordinate_apply] using rawDerivative
  have framedHasDerivative :
      HasFDerivAt
          (fun point : BasePoint =>
            actualNativeCurvatureCoordinate point 1 +
              point 2 • actualNativeCurvatureCoordinate point 5)
          (actualNativeCurvatureFDeriv 1 + productDerivative) 0 := by
    have rawDerivative :=
      (actualNativeCurvatureCoordinate_hasFDerivAt_origin 1).add
        productHasDerivative
    change HasFDerivAt
      (fun point : BasePoint =>
        actualNativeCurvatureCoordinate point 1 +
          point 2 • actualNativeCurvatureCoordinate point 5)
      (actualNativeCurvatureFDeriv 1 + productDerivative) 0 at rawDerivative
    exact rawDerivative
  have curvatureOneLinearZero :
      actualNativeCurvatureFDeriv 1 (coordinateDirection 2) = 0 := by
    have directionalZero := actualNativeCurvature_one_direction_two_eq_zero
    unfold fieldDirectionalDerivative at directionalZero
    rw [(actualNativeCurvatureCoordinate_hasFDerivAt_origin 1).fderiv]
      at directionalZero
    exact directionalZero
  change
    (fderiv ℝ
      (fun point : BasePoint =>
        actualNativeCurvatureCoordinate point 1 +
          point 2 • actualNativeCurvatureCoordinate point 5) 0)
        (coordinateDirection 2) = 0
  rw [framedHasDerivative.fderiv]
  simp only [add_apply]
  rw [curvatureOneLinearZero]
  simp [productDerivative,
    actualNativeCurvatureCoordinate_origin_five_eq_zero,
    p286BaseCoordinate_apply, coordinateDirection]

theorem actualFramedCurvatureTwo_direction_three_eq_zero :
    fieldDirectionalDerivative
        (fun point : BasePoint =>
          actualNativeCurvatureCoordinate point 2 -
            point 2 • actualNativeCurvatureCoordinate point 4)
        0 3 = 0 := by
  let productDerivative : BasePoint →L[ℝ] P286CoordinateCarrier :=
    (p286BaseCoordinate 2 0) • actualNativeCurvatureFDeriv 4 +
      (p286BaseCoordinate 2).smulRight
        (actualNativeCurvatureCoordinate 0 4)
  have productHasDerivative :
      HasFDerivAt
          (fun point : BasePoint =>
            point 2 • actualNativeCurvatureCoordinate point 4)
          productDerivative 0 := by
    have rawDerivative :=
      (p286BaseCoordinate 2).hasFDerivAt.smul
        (actualNativeCurvatureCoordinate_hasFDerivAt_origin 4)
    change HasFDerivAt
      (fun point : BasePoint =>
        p286BaseCoordinate 2 point • actualNativeCurvatureCoordinate point 4)
      productDerivative 0 at rawDerivative
    simpa only [p286BaseCoordinate_apply] using rawDerivative
  have framedHasDerivative :
      HasFDerivAt
          (fun point : BasePoint =>
            actualNativeCurvatureCoordinate point 2 -
              point 2 • actualNativeCurvatureCoordinate point 4)
          (actualNativeCurvatureFDeriv 2 - productDerivative) 0 := by
    have rawDerivative :=
      (actualNativeCurvatureCoordinate_hasFDerivAt_origin 2).sub
        productHasDerivative
    change HasFDerivAt
      (fun point : BasePoint =>
        actualNativeCurvatureCoordinate point 2 -
          point 2 • actualNativeCurvatureCoordinate point 4)
      (actualNativeCurvatureFDeriv 2 - productDerivative) 0 at rawDerivative
    exact rawDerivative
  have curvatureTwoLinearZero :
      actualNativeCurvatureFDeriv 2 (coordinateDirection 3) = 0 := by
    have directionalZero := actualNativeCurvature_two_direction_three_eq_zero
    unfold fieldDirectionalDerivative at directionalZero
    rw [(actualNativeCurvatureCoordinate_hasFDerivAt_origin 2).fderiv]
      at directionalZero
    exact directionalZero
  change
    (fderiv ℝ
      (fun point : BasePoint =>
        actualNativeCurvatureCoordinate point 2 -
          point 2 • actualNativeCurvatureCoordinate point 4) 0)
        (coordinateDirection 3) = 0
  rw [framedHasDerivative.fderiv]
  simp only [sub_apply]
  rw [curvatureTwoLinearZero]
  simp [productDerivative, p286BaseCoordinate_apply, coordinateDirection]

theorem colorCartanMomentum_direction_two_derivative_eq_zero :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 2 colorCartanMuZeroDirection))
        0 2 = 0 := by
  let framedField : BasePoint → P286CoordinateCarrier := fun point =>
    actualNativeCurvatureCoordinate point 1 +
      point 2 • actualNativeCurvatureCoordinate point 5
  let pairingFunction : BasePoint → ℝ := fun point =>
    p286CoordinateLiePairing (framedField point)
      (p286CoordinateEquiv colorCartanP286ConnectionDirection)
  have productDifferentiable :
      DifferentiableAt ℝ
        (fun point : BasePoint =>
          point 2 • actualNativeCurvatureCoordinate point 5) 0 := by
    have rawDerivative :=
      ((p286BaseCoordinate 2).hasFDerivAt.smul
        (actualNativeCurvatureCoordinate_hasFDerivAt_origin 5)).differentiableAt
    change DifferentiableAt ℝ
      (fun point : BasePoint =>
        p286BaseCoordinate 2 point • actualNativeCurvatureCoordinate point 5)
      0 at rawDerivative
    simpa only [p286BaseCoordinate_apply] using rawDerivative
  have framedDifferentiable : DifferentiableAt ℝ framedField 0 := by
    have rawDerivative :=
      (actualNativeCurvatureCoordinate_hasFDerivAt_origin 1).differentiableAt.add
        productDifferentiable
    change DifferentiableAt ℝ
      (fun point : BasePoint =>
        actualNativeCurvatureCoordinate point 1 +
          point 2 • actualNativeCurvatureCoordinate point 5) 0 at rawDerivative
    exact rawDerivative
  have pairingHasDerivative :=
    p286CoordinateLiePairingBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear framedDifferentiable.hasFDerivAt
        (hasFDerivAt_const
          (p286CoordinateEquiv colorCartanP286ConnectionDirection) 0)
  have pairingDifferentiable : DifferentiableAt ℝ pairingFunction 0 := by
    exact pairingHasDerivative.differentiableAt
  have momentumFunction :
      p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 2 colorCartanMuZeroDirection) =
        fun point => 2 * pairingFunction point := by
    funext point
    exact colorCartanMomentum_direction_two point
  rw [momentumFunction]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul pairingDifferentiable 2]
  simp only [smul_apply, smul_eq_mul]
  change 2 * fieldDirectionalDerivative pairingFunction 0 2 = 0
  rw [fieldDirectionalDerivative_pairing_const_local framedField
    (fderiv ℝ framedField 0) 0 2
    (p286CoordinateEquiv colorCartanP286ConnectionDirection)
    framedDifferentiable.hasFDerivAt]
  rw [actualFramedCurvatureOne_direction_two_eq_zero]
  simp

theorem colorCartanMomentum_direction_three_derivative_eq_zero :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 3 colorCartanMuZeroDirection))
        0 3 = 0 := by
  let framedField : BasePoint → P286CoordinateCarrier := fun point =>
    actualNativeCurvatureCoordinate point 2 -
      point 2 • actualNativeCurvatureCoordinate point 4
  let pairingFunction : BasePoint → ℝ := fun point =>
    p286CoordinateLiePairing (framedField point)
      (p286CoordinateEquiv colorCartanP286ConnectionDirection)
  have productDifferentiable :
      DifferentiableAt ℝ
        (fun point : BasePoint =>
          point 2 • actualNativeCurvatureCoordinate point 4) 0 := by
    have rawDerivative :=
      ((p286BaseCoordinate 2).hasFDerivAt.smul
        (actualNativeCurvatureCoordinate_hasFDerivAt_origin 4)).differentiableAt
    change DifferentiableAt ℝ
      (fun point : BasePoint =>
        p286BaseCoordinate 2 point • actualNativeCurvatureCoordinate point 4)
      0 at rawDerivative
    simpa only [p286BaseCoordinate_apply] using rawDerivative
  have framedDifferentiable : DifferentiableAt ℝ framedField 0 := by
    have rawDerivative :=
      (actualNativeCurvatureCoordinate_hasFDerivAt_origin 2).differentiableAt.sub
        productDifferentiable
    change DifferentiableAt ℝ
      (fun point : BasePoint =>
        actualNativeCurvatureCoordinate point 2 -
          point 2 • actualNativeCurvatureCoordinate point 4) 0 at rawDerivative
    exact rawDerivative
  have pairingHasDerivative :=
    p286CoordinateLiePairingBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear framedDifferentiable.hasFDerivAt
        (hasFDerivAt_const
          (p286CoordinateEquiv colorCartanP286ConnectionDirection) 0)
  have pairingDifferentiable : DifferentiableAt ℝ pairingFunction 0 := by
    exact pairingHasDerivative.differentiableAt
  have momentumFunction :
      p286GaugeConnectionBFDifferentialMomentum canonicalSourceNativeP286Input
          (p286GaugeExteriorDerivativeDirection 3 colorCartanMuZeroDirection) =
        fun point => 2 * pairingFunction point := by
    funext point
    exact colorCartanMomentum_direction_three point
  rw [momentumFunction]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul pairingDifferentiable 2]
  simp only [smul_apply, smul_eq_mul]
  change 2 * fieldDirectionalDerivative pairingFunction 0 3 = 0
  rw [fieldDirectionalDerivative_pairing_const_local framedField
    (fderiv ℝ framedField 0) 0 3
    (p286CoordinateEquiv colorCartanP286ConnectionDirection)
    framedDifferentiable.hasFDerivAt]
  rw [actualFramedCurvatureTwo_direction_three_eq_zero]
  simp

theorem canonicalInput_colorCartanMuZero_p286Divergence_eq_neg_one :
    p286GaugeConnectionBFDifferentialMomentumDivergence
        canonicalSourceNativeP286Input colorCartanMuZeroDirection 0 = -1 := by
  unfold p286GaugeConnectionBFDifferentialMomentumDivergence
  rw [Fin.sum_univ_four,
    colorCartanMomentum_direction_zero_derivative_eq_zero,
    colorCartanMomentum_direction_one_derivative_eq_neg_one,
    colorCartanMomentum_direction_two_derivative_eq_zero,
    colorCartanMomentum_direction_three_derivative_eq_zero]
  norm_num

/-! ## Canonical-response sector decomposition and fixed offset -/

theorem canonicalResponse_colorCartanMuZero_p286BFAlgebraic_eq_zero :
    p286GaugeBFAlgebraicCoefficient canonicalResponse
        colorCartanMuZeroDirection 0 = 0 := by
  change p286GaugeBFAlgebraicCoefficient canonicalSourceNativeP286Input
      colorCartanMuZeroDirection 0 = 0
  exact canonicalInput_colorCartanMuZero_p286BFAlgebraic_eq_zero

theorem canonicalResponse_colorCartanMuZero_p286Divergence_eq_neg_one :
    p286GaugeConnectionBFDifferentialMomentumDivergence canonicalResponse
        colorCartanMuZeroDirection 0 = -1 := by
  change p286GaugeConnectionBFDifferentialMomentumDivergence
      canonicalSourceNativeP286Input colorCartanMuZeroDirection 0 = -1
  exact canonicalInput_colorCartanMuZero_p286Divergence_eq_neg_one

theorem canonicalResponse_colorCartanMuZero_p286ScalarCurrent_eq_zero :
    p286ScalarCurrentCoefficient positiveSmoothUnifiedSource canonicalResponse
        colorCartanMuZeroDirection 0 = 0 := by
  change p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
      canonicalSourceNativeP286Input colorCartanMuZeroDirection 0 = 0
  exact canonicalInput_colorCartanMuZero_p286ScalarCurrent_eq_zero

theorem canonicalResponse_colorCartanMuZero_p286MatterCurrent_eq_zero :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource canonicalResponse
        colorCartanMuZeroDirection 0 = 0 := by
  change p286MatterCurrentCoefficient positiveSmoothUnifiedSource
      canonicalSourceNativeP286Input colorCartanMuZeroDirection 0 = 0
  exact canonicalInput_colorCartanMuZero_p286MatterCurrent_eq_zero

/-- Direct evaluation of the actual C3h70 offset in the color-Cartan test
direction.  This is a single functional readout; it does not classify the
response range or select a point in its zero fiber. -/
theorem positiveC3h70P286Response_offset_colorCartanMuZero_eq_one :
    positiveC3h70P286Response 0 colorCartanMuZeroDirection = 1 := by
  unfold positiveC3h70P286Response fixedBackgroundP286Response
  rw [installConstantP286ConnectionShift_zero]
  rw [p286GaugeConnectionEulerLagrangeCoefficient_eq_sectorBalance]
  unfold p286GaugeBFBalanceCoefficient
  rw [canonicalResponse_colorCartanMuZero_p286BFAlgebraic_eq_zero,
    canonicalResponse_colorCartanMuZero_p286Divergence_eq_neg_one,
    canonicalResponse_colorCartanMuZero_p286ScalarCurrent_eq_zero,
    canonicalResponse_colorCartanMuZero_p286MatterCurrent_eq_zero]
  norm_num

theorem positiveC3h70P286Response_offset_colorCartanMuZero_ne_zero :
    positiveC3h70P286Response 0 colorCartanMuZeroDirection ≠ 0 := by
  rw [positiveC3h70P286Response_offset_colorCartanMuZero_eq_one]
  norm_num

end

end SaturationMonoid.PhysicsCore.StageNineP286ColorCartanOffsetBoundary
