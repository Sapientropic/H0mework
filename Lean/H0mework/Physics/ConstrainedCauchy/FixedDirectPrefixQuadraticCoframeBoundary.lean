import H0mework.Physics.ConstrainedCauchy.FixedJointDirectPrimitivePath
import H0mework.Physics.ConstrainedCauchy.FixedOriginJointResidual
import H0mework.Physics.QuarticDynamics.FixedHessianLiveDiagonalLoad
import H0mework.Physics.QuarticDynamics.FixedHessianOffDiagonalRows

/-!
# Fixed P506/L0 direct-prefix quadratic coframe boundary

The source/action Hessian is genuinely installed, but its identity-contact
quadratic realization is not a global `GL(4)`-valued coframe.  At the exact
time-axis point `sqrt 6 * e₀`, two generated spatial rows collapse and the
determinant vanishes.  This freezes only that polynomial realization; it does
not reject the generated Hessian or manufacture a successor from the failure.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyDirectPrefixQuadraticCoframeBoundary

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeFirstJet
open StageNineCoframeHolonomicSecondJetCarrier
open StageNineDiracDualFormNativeCartanConnectionActualizationRegression
open StageNineDiracDualFormNativeCartanGravityAuxiliaryObstructionRegression
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyCompleteJointDirectPrimitivePath
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailCoframeLoadTemporalSpatial01
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticHessianLiveDiagonalLoad
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticHessianOffDiagonalRows
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumCarry
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumIdentityECLoadTransport
open StageNineDiracDualFormNativeIdentityECCartanRestartOriginFirstGerm
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianSection
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianUpdate
open StageNineDiracDualFormNativeIdentityECNonlinearLeviCivitaFirstGerm
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineLorentzConnectionVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineP286ActionCauchySplit
open StageNineTopologicalFourFormPairing

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchyGlobalActual

private abbrev CartanBase : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECCauchyTemporalBase

private abbrev HessianIncrement : CoframeHolonomicSecondJet :=
  sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
    Source CartanBase

private abbrev Prefix : StageNineHolonomicConfiguration :=
  directPrimitivePathPrefix Source Current

private abbrev U6Current : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticScalarMomentumCarryActual

private abbrev HessianRows : IdentityECEtaCompatibleRows :=
  sourceActionGeneratedIdentityECCoframeAccelerationRows Source CartanBase

private abbrev LowerOrderRows : LorentzianCoframe :=
  sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates Source CartanBase

private theorem cartanBase_load_eq_u6 :
    diracDualFormNativeIdentityECLoad Source CartanBase =
      diracDualFormNativeIdentityECLoad Source U6Current := by
  rw [base_load_eq_input]
  exact
    fixedP506L0ActionSelectedGravityTail_contactLoad_eq_u6RadialQuarticIdentityLoad

private theorem canonicalSlice_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem cartanBase_connection_origin_eq_fixedAction :
    CartanBase.gravityConnection 0 = fixedActionCartanConnection := by
  have generated := base_connection_zeroSlice_eq_fixedAction
    (0 : StageNineSpatialPoint)
  rw [canonicalSlice_zero] at generated
  exact generated

private theorem cartanBase_connectionDerivative_origin_zero
    (direction formDirection internalOut internalIn : LorentzianIndex) :
    gravityConnectionDerivative CartanBase 0 direction
        formDirection internalOut internalIn = 0 := by
  fin_cases direction
  · exact base_connection_temporalDerivative_origin_zero
      formDirection internalOut internalIn
  · simpa using base_connection_spatialDerivative_origin_zero
      (0 : Fin 3) formDirection internalOut internalIn
  · simpa using base_connection_spatialDerivative_origin_zero
      (1 : Fin 3) formDirection internalOut internalIn
  · simpa using base_connection_spatialDerivative_origin_zero
      (2 : Fin 3) formDirection internalOut internalIn

private theorem cartanBase_curvature_origin_eq_bracket :
    holonomicGravityCurvature CartanBase 0 =
      originLorentzBracketCurvature fixedActionCartanConnection := by
  ext internalPair spacetimePair
  unfold holonomicGravityCurvature
  dsimp only
  simp only [cartanBase_connectionDerivative_origin_zero]
  rw [cartanBase_connection_origin_eq_fixedAction]
  unfold originLorentzBracketCurvature
  ring

private theorem cartanBase_curvatureObservation_temporalDiagonal00 :
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature CartanBase 0)
        (coframeCoordinateDirection 0 0) = (1 / 8 : ℝ) := by
  rw [cartanBase_curvature_origin_eq_bracket,
    fixedActionCartanConnection_eq_positiveNormalForm]
  simp +decide [identityDiracDualECCurvatureObservation,
    coframeCoordinateDirection, physicalIIPlusCoframeTangent,
    coframeWedgeTangent, internalBivectorDual, lorentzianCoframeHodge,
    gravityInternalPairVarianceNormalization,
    gravityTopologicalWedgeCoefficient,
    orientedTwoFormWedgeCoefficient_explicit, lorentzianTwoFormSign,
    originLorentzBracketCurvature,
    lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    positiveDiracDualCartanContorsionNormalForm,
    minkowskiInternalSign, pairFirst, pairSecond, Matrix.one_apply,
    Fin.sum_univ_four, Fin.sum_univ_six]
  norm_num

private theorem cartanBase_curvatureObservation_spatialDiagonal11 :
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature CartanBase 0)
        (coframeCoordinateDirection 1 1) = 0 := by
  rw [cartanBase_curvature_origin_eq_bracket,
    fixedActionCartanConnection_eq_positiveNormalForm]
  simp +decide [identityDiracDualECCurvatureObservation,
    coframeCoordinateDirection, physicalIIPlusCoframeTangent,
    coframeWedgeTangent, internalBivectorDual, lorentzianCoframeHodge,
    gravityInternalPairVarianceNormalization,
    gravityTopologicalWedgeCoefficient,
    orientedTwoFormWedgeCoefficient_explicit, lorentzianTwoFormSign,
    originLorentzBracketCurvature,
    lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    positiveDiracDualCartanContorsionNormalForm,
    minkowskiInternalSign, pairFirst, pairSecond, Matrix.one_apply,
    Fin.sum_univ_four, Fin.sum_univ_six]

private theorem cartanBase_curvatureObservation_spatialDiagonal22 :
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature CartanBase 0)
        (coframeCoordinateDirection 2 2) = 0 := by
  rw [cartanBase_curvature_origin_eq_bracket,
    fixedActionCartanConnection_eq_positiveNormalForm]
  simp +decide [identityDiracDualECCurvatureObservation,
    coframeCoordinateDirection, physicalIIPlusCoframeTangent,
    coframeWedgeTangent, internalBivectorDual, lorentzianCoframeHodge,
    gravityInternalPairVarianceNormalization,
    gravityTopologicalWedgeCoefficient,
    orientedTwoFormWedgeCoefficient_explicit, lorentzianTwoFormSign,
    originLorentzBracketCurvature,
    lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    positiveDiracDualCartanContorsionNormalForm,
    minkowskiInternalSign, pairFirst, pairSecond, Matrix.one_apply,
    Fin.sum_univ_four, Fin.sum_univ_six]

private theorem cartanBase_curvatureObservation_spatialDiagonal33 :
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature CartanBase 0)
        (coframeCoordinateDirection 3 3) = -(1 / 8 : ℝ) := by
  rw [cartanBase_curvature_origin_eq_bracket,
    fixedActionCartanConnection_eq_positiveNormalForm]
  simp +decide [identityDiracDualECCurvatureObservation,
    coframeCoordinateDirection, physicalIIPlusCoframeTangent,
    coframeWedgeTangent, internalBivectorDual, lorentzianCoframeHodge,
    gravityInternalPairVarianceNormalization,
    gravityTopologicalWedgeCoefficient,
    orientedTwoFormWedgeCoefficient_explicit, lorentzianTwoFormSign,
    originLorentzBracketCurvature,
    lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    positiveDiracDualCartanContorsionNormalForm,
    minkowskiInternalSign, pairFirst, pairSecond, Matrix.one_apply,
    Fin.sum_univ_four, Fin.sum_univ_six]
  norm_num

private theorem cartanBase_load_temporalDiagonal00 :
    diracDualFormNativeIdentityECLoad Source CartanBase
        (coframeCoordinateDirection 0 0) = -(665 / 216 : ℝ) := by
  rw [cartanBase_load_eq_u6]
  exact current_identityECLoad_temporalDiagonal00

private theorem cartanBase_load_spatialDiagonal11 :
    diracDualFormNativeIdentityECLoad Source CartanBase
        (coframeCoordinateDirection 1 1) = -(319 / 108 : ℝ) := by
  rw [cartanBase_load_eq_u6]
  exact current_identityECLoad_spatialDiagonal11

private theorem cartanBase_load_spatialDiagonal22 :
    diracDualFormNativeIdentityECLoad Source CartanBase
        (coframeCoordinateDirection 2 2) = -(329 / 108 : ℝ) := by
  rw [cartanBase_load_eq_u6]
  exact current_identityECLoad_spatialDiagonal22

private theorem cartanBase_load_spatialDiagonal33 :
    diracDualFormNativeIdentityECLoad Source CartanBase
        (coframeCoordinateDirection 3 3) = -(631 / 216 : ℝ) := by
  rw [cartanBase_load_eq_u6]
  exact current_identityECLoad_spatialDiagonal33

private theorem hessianRows_diagonal_eq_neg_lowerOrder
    (row : LorentzianIndex) :
    HessianRows.1 row row = -LowerOrderRows row row := by
  change
    (1 / 2 : ℝ) *
        (-LowerOrderRows row row +
          minkowskiInternalSign row * minkowskiInternalSign row *
            (-LowerOrderRows row row)) = _
  have signSq :
      minkowskiInternalSign row * minkowskiInternalSign row = 1 := by
    fin_cases row <;> simp [minkowskiInternalSign]
  rw [signSq]
  ring

private theorem hessianRows_temporalDiagonal00 :
    HessianRows.1 0 0 = (319 / 108 : ℝ) := by
  rw [hessianRows_diagonal_eq_neg_lowerOrder]
  unfold LowerOrderRows
    sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
    coframeCovectorCoordinates
  simp only [Matrix.of_apply, add_apply]
  rw [cartanBase_curvatureObservation_temporalDiagonal00,
    cartanBase_load_temporalDiagonal00]
  norm_num

private theorem hessianRows_spatialDiagonal11 :
    HessianRows.1 1 1 = (319 / 108 : ℝ) := by
  rw [hessianRows_diagonal_eq_neg_lowerOrder]
  unfold LowerOrderRows
    sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
    coframeCovectorCoordinates
  simp only [Matrix.of_apply, add_apply]
  rw [cartanBase_curvatureObservation_spatialDiagonal11,
    cartanBase_load_spatialDiagonal11]
  norm_num

private theorem hessianRows_spatialDiagonal22 :
    HessianRows.1 2 2 = (329 / 108 : ℝ) := by
  rw [hessianRows_diagonal_eq_neg_lowerOrder]
  unfold LowerOrderRows
    sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
    coframeCovectorCoordinates
  simp only [Matrix.of_apply, add_apply]
  rw [cartanBase_curvatureObservation_spatialDiagonal22,
    cartanBase_load_spatialDiagonal22]
  norm_num

private theorem hessianRows_spatialDiagonal33 :
    HessianRows.1 3 3 = (329 / 108 : ℝ) := by
  rw [hessianRows_diagonal_eq_neg_lowerOrder]
  unfold LowerOrderRows
    sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
    coframeCovectorCoordinates
  simp only [Matrix.of_apply, add_apply]
  rw [cartanBase_curvatureObservation_spatialDiagonal33,
    cartanBase_load_spatialDiagonal33]
  norm_num

private theorem cartanBase_load_spatial23_symmetric :
    diracDualFormNativeIdentityECLoad Source CartanBase
        (coframeCoordinateDirection 2 3 + coframeCoordinateDirection 3 2) = 0 := by
  rw [cartanBase_load_eq_u6]
  have generated := current_identityECLoad_spatial23_zero
  change
    diracDualFormNativeIdentityECLoad Source U6Current
        (coframeCoordinateDirection 2 3 + coframeCoordinateDirection 3 2) = 0
    at generated
  exact generated

private theorem cartanBase_curvatureObservation_spatial23_symmetric :
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature CartanBase 0)
        (coframeCoordinateDirection 2 3 + coframeCoordinateDirection 3 2) = 0 := by
  rw [cartanBase_curvature_origin_eq_bracket,
    fixedActionCartanConnection_eq_positiveNormalForm]
  simp +decide [identityDiracDualECCurvatureObservation,
    coframeCoordinateDirection, physicalIIPlusCoframeTangent,
    coframeWedgeTangent, internalBivectorDual, lorentzianCoframeHodge,
    gravityInternalPairVarianceNormalization,
    gravityTopologicalWedgeCoefficient,
    orientedTwoFormWedgeCoefficient_explicit, lorentzianTwoFormSign,
    originLorentzBracketCurvature,
    lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    positiveDiracDualCartanContorsionNormalForm,
    minkowskiInternalSign, pairFirst, pairSecond, Matrix.one_apply,
    Fin.sum_univ_four, Fin.sum_univ_six]

private theorem hessianRows_spatial23_zero :
    HessianRows.1 2 3 = 0 := by
  change
    (1 / 2 : ℝ) *
      (-LowerOrderRows 2 3 +
        minkowskiInternalSign 2 * minkowskiInternalSign 3 *
          (-LowerOrderRows 3 2)) = 0
  have lowerSymmetric : LowerOrderRows 2 3 + LowerOrderRows 3 2 = 0 := by
    unfold LowerOrderRows
      sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
      coframeCovectorCoordinates
    simp only [Matrix.of_apply]
    rw [← map_add]
    simp only [add_apply]
    rw [cartanBase_curvatureObservation_spatial23_symmetric,
      cartanBase_load_spatial23_symmetric]
    norm_num
  simp [minkowskiInternalSign]
  linarith

private theorem hessianRows_spatial32_zero :
    HessianRows.1 3 2 = 0 := by
  have compatible := HessianRows.2 3 2
  simp [minkowskiInternalSign] at compatible
  rw [compatible, hessianRows_spatial23_zero]

private theorem lowerOrderRows_temporalSpatial02_zero :
    LowerOrderRows 0 2 = 0 := by
  exact
    fixedP506L0CartanECCauchyTemporalBase_balance_temporalSpatial
      (1 : Fin 3)

private theorem lowerOrderRows_spatialTemporal20_zero :
    LowerOrderRows 2 0 = 0 := by
  exact
    fixedP506L0CartanECCauchyTemporalBase_balance_spatialTemporal
      (1 : Fin 3)

private theorem lowerOrderRows_temporalSpatial03_zero :
    LowerOrderRows 0 3 = 0 := by
  exact
    fixedP506L0CartanECCauchyTemporalBase_balance_temporalSpatial
      (2 : Fin 3)

private theorem lowerOrderRows_spatialTemporal30_zero :
    LowerOrderRows 3 0 = 0 := by
  exact
    fixedP506L0CartanECCauchyTemporalBase_balance_spatialTemporal
      (2 : Fin 3)

private theorem hessianRows_zero_two_zero :
    HessianRows.1 0 2 = 0 := by
  change
    (1 / 2 : ℝ) *
      (-LowerOrderRows 0 2 +
        minkowskiInternalSign 0 * minkowskiInternalSign 2 *
          (-LowerOrderRows 2 0)) = 0
  rw [lowerOrderRows_temporalSpatial02_zero,
    lowerOrderRows_spatialTemporal20_zero]
  norm_num

private theorem hessianRows_zero_three_zero :
    HessianRows.1 0 3 = 0 := by
  change
    (1 / 2 : ℝ) *
      (-LowerOrderRows 0 3 +
        minkowskiInternalSign 0 * minkowskiInternalSign 3 *
          (-LowerOrderRows 3 0)) = 0
  rw [lowerOrderRows_temporalSpatial03_zero,
    lowerOrderRows_spatialTemporal30_zero]
  norm_num

private theorem hessianRows_two_zero_zero :
    HessianRows.1 2 0 = 0 := by
  have compatible := HessianRows.2 (2 : LorentzianIndex) 0
  simp [minkowskiInternalSign, hessianRows_zero_two_zero] at compatible
  exact compatible

private theorem hessianRows_three_zero_zero :
    HessianRows.1 3 0 = 0 := by
  have compatible := HessianRows.2 (3 : LorentzianIndex) 0
  simp [minkowskiInternalSign, hessianRows_zero_three_zero] at compatible
  exact compatible

/-- Exact source/action row receipt consumed by the Cauchy-safe `e₁` flux
diagnostic.  It exposes only the ten finite coordinates needed by that
consumer, not the private curvature/load calculation chain. -/
theorem fixedP506L0CartanECCauchyTemporalBase_accelerationRows_e1_exact :
    let rows := sourceActionGeneratedIdentityECCoframeAccelerationRows
      positiveSmoothUnifiedSource fixedP506L0CartanECCauchyTemporalBase
    rows.1 0 0 = (319 / 108 : ℝ) ∧
      rows.1 1 1 = (319 / 108 : ℝ) ∧
      rows.1 2 2 = (329 / 108 : ℝ) ∧
      rows.1 3 3 = (329 / 108 : ℝ) ∧
      rows.1 0 2 = 0 ∧ rows.1 2 0 = 0 ∧
      rows.1 0 3 = 0 ∧ rows.1 3 0 = 0 ∧
      rows.1 2 3 = 0 ∧ rows.1 3 2 = 0 := by
  exact ⟨hessianRows_temporalDiagonal00,
    hessianRows_spatialDiagonal11,
    hessianRows_spatialDiagonal22,
    hessianRows_spatialDiagonal33,
    hessianRows_zero_two_zero,
    hessianRows_two_zero_zero,
    hessianRows_zero_three_zero,
    hessianRows_three_zero_zero,
    hessianRows_spatial23_zero,
    hessianRows_spatial32_zero⟩

private theorem hessianIncrement_timeTime_row2_column0 :
    HessianIncrement.1 (coordinateDirection 0) (coordinateDirection 0) 2 0 = 0 := by
  unfold HessianIncrement
    sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
    identityECTypedHolonomicCoframeHessianSection
  rw [identityECHolonomicCoframeHessianSection_coordinate]
  simp [identityECNormalCoframeHessianCoordinate,
    identityECNormalMetricHessianCoordinate,
    identityECWeylZeroRiemannCoordinate,
    identityECRicciTensorCoordinate,
    identityECScalarCurvature,
    identityECEinsteinTensorCoordinate,
    identityECEinsteinTrace,
    identityECMinkowskiMetricCoordinate,
    identityECEtaSymmetricPart_typed,
    minkowskiInternalSign, Fin.sum_univ_four]

private theorem hessianIncrement_timeTime_row2_column2 :
    HessianIncrement.1 (coordinateDirection 0) (coordinateDirection 0) 2 2 =
      -(1 / 3 : ℝ) := by
  unfold HessianIncrement
    sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
    identityECTypedHolonomicCoframeHessianSection
  rw [identityECHolonomicCoframeHessianSection_coordinate]
  simp [identityECNormalCoframeHessianCoordinate,
    identityECNormalMetricHessianCoordinate,
    identityECWeylZeroRiemannCoordinate,
    identityECRicciTensorCoordinate,
    identityECScalarCurvature,
    identityECEinsteinTensorCoordinate,
    identityECEinsteinTrace,
    identityECMinkowskiMetricCoordinate,
    identityECEtaSymmetricPart_typed,
    minkowskiInternalSign, Fin.sum_univ_four,
    hessianRows_temporalDiagonal00, hessianRows_spatialDiagonal11,
    hessianRows_spatialDiagonal22, hessianRows_spatialDiagonal33]
  norm_num

private theorem hessianIncrement_timeTime_row2_column3 :
    HessianIncrement.1 (coordinateDirection 0) (coordinateDirection 0) 2 3 = 0 := by
  unfold HessianIncrement
    sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
    identityECTypedHolonomicCoframeHessianSection
  rw [identityECHolonomicCoframeHessianSection_coordinate]
  simp [identityECNormalCoframeHessianCoordinate,
    identityECNormalMetricHessianCoordinate,
    identityECWeylZeroRiemannCoordinate,
    identityECRicciTensorCoordinate,
    identityECScalarCurvature,
    identityECEinsteinTensorCoordinate,
    identityECEinsteinTrace,
    identityECMinkowskiMetricCoordinate,
    identityECEtaSymmetricPart_typed,
    minkowskiInternalSign, Fin.sum_univ_four,
    hessianRows_spatial23_zero, hessianRows_spatial32_zero]

private theorem hessianIncrement_timeTime_row3_column2 :
    HessianIncrement.1 (coordinateDirection 0) (coordinateDirection 0) 3 2 = 0 := by
  unfold HessianIncrement
    sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
    identityECTypedHolonomicCoframeHessianSection
  rw [identityECHolonomicCoframeHessianSection_coordinate]
  simp [identityECNormalCoframeHessianCoordinate,
    identityECNormalMetricHessianCoordinate,
    identityECWeylZeroRiemannCoordinate,
    identityECRicciTensorCoordinate,
    identityECScalarCurvature,
    identityECEinsteinTensorCoordinate,
    identityECEinsteinTrace,
    identityECMinkowskiMetricCoordinate,
    identityECEtaSymmetricPart_typed,
    minkowskiInternalSign, Fin.sum_univ_four,
    hessianRows_spatial23_zero, hessianRows_spatial32_zero]

private theorem hessianIncrement_timeTime_row3_column3 :
    HessianIncrement.1 (coordinateDirection 0) (coordinateDirection 0) 3 3 =
      -(1 / 3 : ℝ) := by
  unfold HessianIncrement
    sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
    identityECTypedHolonomicCoframeHessianSection
  rw [identityECHolonomicCoframeHessianSection_coordinate]
  simp [identityECNormalCoframeHessianCoordinate,
    identityECNormalMetricHessianCoordinate,
    identityECWeylZeroRiemannCoordinate,
    identityECRicciTensorCoordinate,
    identityECScalarCurvature,
    identityECEinsteinTensorCoordinate,
    identityECEinsteinTrace,
    identityECMinkowskiMetricCoordinate,
    identityECEtaSymmetricPart_typed,
    minkowskiInternalSign, Fin.sum_univ_four,
    hessianRows_temporalDiagonal00, hessianRows_spatialDiagonal11,
    hessianRows_spatialDiagonal22, hessianRows_spatialDiagonal33]
  norm_num

private theorem hessianIncrement_timeTime_timeRow
    (column : LorentzianIndex) :
    HessianIncrement.1 (coordinateDirection 0) (coordinateDirection 0) 0 column = 0 := by
  unfold HessianIncrement
    sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
    identityECTypedHolonomicCoframeHessianSection
  rw [identityECHolonomicCoframeHessianSection_coordinate]
  fin_cases column <;>
    simp [identityECNormalCoframeHessianCoordinate,
      identityECNormalMetricHessianCoordinate,
      identityECWeylZeroRiemannCoordinate,
      identityECRicciTensorCoordinate,
      identityECScalarCurvature,
      identityECEinsteinTensorCoordinate,
      identityECEinsteinTrace,
      identityECMinkowskiMetricCoordinate,
      identityECEtaSymmetricPart_typed,
      minkowskiInternalSign, Fin.sum_univ_four]

/-- Identifies the direct-prefix coframe with the source-generated quadratic
prepared actual. -/
theorem directPrefix_coframe_eq_quadraticPrepared :
    (directPrimitivePathPrefix positiveSmoothUnifiedSource
      fixedP506L0CartanECConstraintCauchyGlobalActual).coframe =
      fixedP506L0CartanECConstraintPreparedActual.coframe := by
  unfold directPrimitivePathPrefix
  rw [sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_coframe]
  rfl

theorem directPrefix_coframe_eq_quadratic :
    Prefix.coframe = identityECQuadraticCoframeField HessianIncrement := by
  unfold Prefix directPrimitivePathPrefix
  rw [sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_coframe]
  change
    fixedP506L0CartanECConstraintPreparedActual.coframe =
      identityECQuadraticCoframeField HessianIncrement
  unfold fixedP506L0CartanECConstraintPreparedActual
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
  exact
    identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_eq_quadratic
      CartanBase HessianIncrement
      fixedP506L0CartanECCauchyTemporalBase_coframe_eq_one

private theorem directPrefix_coframe_timeAxis_normalForm
    (time : ℝ) (internal column : LorentzianIndex) :
    Prefix.coframe (time • coordinateDirection 0) internal column =
      (1 : LorentzianCoframe) internal column +
        time ^ 2 / 2 *
          HessianIncrement.1 (coordinateDirection 0) (coordinateDirection 0)
            internal column := by
  rw [directPrefix_coframe_eq_quadratic]
  unfold identityECQuadraticCoframeField
    coframeFieldOfFirstAndSecondJet
  simp only [Matrix.add_apply,
    coframeHolonomicSecondJetQuadraticRealization_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [map_smul, map_smul]
  simp [affineCoframeFieldOfJet, identityECZeroCoframeFirstJet,
    coframeJetAffineComponentLinear,
    smul_apply, Matrix.smul_apply]
  ring

private def singularTime : ℝ := Real.sqrt 6

def fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint :
    BasePoint :=
  singularTime • coordinateDirection 0

private theorem singularTime_sq : singularTime ^ 2 = 6 := by
  unfold singularTime
  exact Real.sq_sqrt (by norm_num)

private theorem directPrefix_singular_timeRow
    (column : LorentzianIndex) :
    Prefix.coframe
        fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint
        0 column =
      (1 : LorentzianCoframe) 0 column := by
  rw [fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint,
    directPrefix_coframe_timeAxis_normalForm,
    hessianIncrement_timeTime_timeRow]
  ring

private theorem directPrefix_singular_spatial22 :
    Prefix.coframe
        fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint
        2 2 = 0 := by
  rw [fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint,
    directPrefix_coframe_timeAxis_normalForm,
    hessianIncrement_timeTime_row2_column2, singularTime_sq]
  norm_num

private theorem directPrefix_singular_spatial23 :
    Prefix.coframe
        fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint
        2 3 = 0 := by
  rw [fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint,
    directPrefix_coframe_timeAxis_normalForm,
    hessianIncrement_timeTime_row2_column3]
  simp

private theorem directPrefix_singular_spatial32 :
    Prefix.coframe
        fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint
        3 2 = 0 := by
  rw [fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint,
    directPrefix_coframe_timeAxis_normalForm,
    hessianIncrement_timeTime_row3_column2]
  simp

private theorem directPrefix_singular_spatial33 :
    Prefix.coframe
        fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint
        3 3 = 0 := by
  rw [fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint,
    directPrefix_coframe_timeAxis_normalForm,
    hessianIncrement_timeTime_row3_column3, singularTime_sq]
  norm_num

theorem
    fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframe_determinant_zero :
    Matrix.det
        ((directPrimitivePathPrefix positiveSmoothUnifiedSource
            fixedP506L0CartanECConstraintCauchyGlobalActual).coframe
          fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint) =
      0 := by
  rw [Matrix.det_succ_row_zero]
  simp +decide [Matrix.det_fin_three, Fin.sum_univ_four, Fin.succAbove,
    directPrefix_singular_timeRow,
    directPrefix_singular_spatial22, directPrefix_singular_spatial23,
    directPrefix_singular_spatial32, directPrefix_singular_spatial33]

theorem
    fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframe_not_nondegenerate :
    ¬ (directPrimitivePathPrefix positiveSmoothUnifiedSource
        fixedP506L0CartanECConstraintCauchyGlobalActual).Nondegenerate := by
  intro nondegenerate
  exact
    (nondegenerate
      fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint)
      fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframe_determinant_zero

/-- Reads the exact global nondegeneracy failure on the quadratic prepared
actual. -/
theorem fixedP506L0CartanECConstraintPreparedActual_determinant_zero :
    Matrix.det
        (fixedP506L0CartanECConstraintPreparedActual.coframe
          fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint) =
      0 := by
  rw [← directPrefix_coframe_eq_quadraticPrepared]
  exact
    fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframe_determinant_zero

theorem fixedP506L0CartanECConstraintPreparedActual_not_nondegenerate :
    ¬ fixedP506L0CartanECConstraintPreparedActual.Nondegenerate := by
  intro nondegenerate
  exact
    (nondegenerate
      fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint)
      fixedP506L0CartanECConstraintPreparedActual_determinant_zero

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyDirectPrefixQuadraticCoframeBoundary
