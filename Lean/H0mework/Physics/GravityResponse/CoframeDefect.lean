import H0mework.Physics.GravityResponse.FullDefect
import H0mework.Physics.Coframe.ResidualLimitCoframeBalanceDecision

/-!
# S9-C3h73c: actual identity-coframe defect of the C3h70 response

This module computes the first exact coframe coordinate of the canonical
C3h70 full lift defect from the action-owned Fréchet derivative.  The input
gravity BF scalar is `0`; the response gravity BF scalar is `-7/16`; the
shared P286 sector is `-5/16`; and scalar and matter sectors vanish.  Hence
the identity-direction coframe Euler readouts are `-5/2` and `-6`, the actual
delta is `-7/2`, and the complete lift defect is `-19/4`.

The response curvature coordinate `(0,0) = -3/8` is deliberately kept
separate from the local contracted gravity BF action-density scalar `-7/16`.
This prevents the curvature coordinate from being reused as an action
density.

Every value is derived from the primitive source connection, its actual
`dω + ω∧ω` curvature, the generated auxiliaries, and the declared action.
No residual value, zero/stationarity premise, target field, branch receipt,
or new source parameter is accepted.  This is a readout/diagnostic theorem:
it proves the fixed-coframe response has nonzero coframe defect, but does not
turn a coframe covector into a coframe state repair.
-/

namespace SaturationMonoid.PhysicsCore.StageNineGravityAlgebraicKeepResponseCoframeDefect

open AffineRelaxation
open EmpiricalReferenceScaleCouplingBoundary
open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineCoframeLocalDifferentiability
open StageNineCoframeSectorStress
open StageNineCoframeTwoFormPairing
open StageNineCoframeVariation
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityAlgebraicKeepEndpoint
open StageNineGravityAlgebraicKeepResponseFullDefect
open StageNineGravityAlgebraicKeepResponseGerm
open StageNineGlobalConnection
open StageNineHolonomicField
open StageNineJointShellResidualCarrier
open StageNineJointShellResidualTransportRoot
open StageNineJointStateLiftDefect
open StageNinePositiveSourceGravityMouthResidualTransportIteration
open StageNinePositiveSourceGravityMouthResidualOrbitConnectionLift
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNinePositiveSourceNativeAlgebraicEliminationUpdate
open StageNinePositiveSourceNativeAlgebraicEliminationLiftDefect
open StageNinePositiveSourceNativeGravityCurvatureBridge
open StageNineResidualLimitCoframeBalanceDecision
open StageNineResidualLimitLorentzClassObstruction
open StageNineResidualLimitP286ScalarSourceNormalForm
open StageNineP286GaugeAuxiliaryEquation
open StageNineSourceGeneratedP286AffineConnectionGerm
open SU7MotherGaugeTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000

abbrev canonicalInput : StageNineHolonomicConfiguration :=
  algebraicKeepResponseInput residualLimitLorentzCarrierReader

abbrev canonicalResponse : StageNineHolonomicConfiguration :=
  algebraicKeepResponseImage residualLimitLorentzCarrierReader

abbrev canonicalInputField : StageNineContinuumPointField :=
  toContinuumPointField canonicalInput 0

abbrev canonicalResponseField : StageNineContinuumPointField :=
  toContinuumPointField canonicalResponse 0

def sourceGravityConnectionNormalForm
    (point : BasePoint) : PointwiseLorentzSpinConnection :=
  ![
    ![![0, 0, 0, 0], ![0, 0, -(1 / 2 : ℝ), 0],
      ![0, (1 / 2 : ℝ), 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, (1 / 2 : ℝ), 0],
      ![0, 0, -(point 2 / 2), 0],
      ![(1 / 2 : ℝ), point 2 / 2, 0, 0], ![0, 0, 0, 0]],
    ![![0, -(1 / 2 : ℝ), 0, 0],
      ![-(1 / 2 : ℝ), 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]

theorem generatedLorentzConnection_eq_normalForm
    (point : BasePoint) :
    generatedLorentzConnectionAt positiveSmoothUnifiedSource point =
      sourceGravityConnectionNormalForm point := by
  funext direction internalOut internalIn
  change
    (canonicalPhysicalSource.jetAt point).lorentzSpinConnection direction
        internalOut internalIn = _
  unfold PointwiseLorentzianCoframeJet.lorentzSpinConnection
    PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix
    PointwiseLorentzianCoframeJet.coordinateConnectionMatrix
    affineConnectionMatrix
    PointwiseLorentzianCoframeJet.coframeDerivativeMatrix
    PointwiseLorentzianCoframeJet.leviCivitaConnection
    PointwiseLorentzianCoframeJet.leviCivitaConnectionVector
  rw [show
      (canonicalPhysicalSource.jetAt point).coframe⁻¹ =
        Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
          (-(point 2)) by
      exact canonicalSourceCoframe_inv point,
    canonicalSourceMetric_inv point,
    show
      (canonicalPhysicalSource.jetAt point).coframe =
        Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
          (point 2) by
      exact canonicalPhysicalSource_coframeAt_eq_transvection point]
  unfold PointwiseLorentzianCoframeJet.loweredLeviCivitaVector
    PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection
    PointwiseLorentzianCoframeJet.metricDerivative
  rw [show
      (canonicalPhysicalSource.jetAt point).coframe =
        Matrix.transvection (0 : LorentzianIndex) (1 : LorentzianIndex)
          (point 2) by
      exact canonicalPhysicalSource_coframeAt_eq_transvection point]
  fin_cases direction <;> fin_cases internalOut <;> fin_cases internalIn <;>
    simp [sourceGravityConnectionNormalForm,
      canonicalSourceMetricInverseCandidate,
      ProofFreeRicherAnholonomicSource.Source.jetAt,
      StageEightProofFreeSource.Source.toPhysicalSource,
      StageEightProofFreeSource.canonicalSource,
      ProofFreeRicherAnholonomicSource.shearCoefficient,
      minkowskiInternalMetric, minkowskiInternalSign,
      Matrix.mulVec, Matrix.mul_apply, Matrix.transvection, Matrix.single,
      dotProduct, Fin.sum_univ_succ,
      Matrix.diagonal_apply, Matrix.one_apply] <;>
    ring

theorem canonicalInput_gravityConnection_eq_normalForm :
    canonicalInput.gravityConnection = sourceGravityConnectionNormalForm := by
  funext point
  change generatedLorentzConnectionAt positiveSmoothUnifiedSource point = _
  exact generatedLorentzConnection_eq_normalForm point

def sourceGravityCurvatureNormalForm : PhysicalBivector :=
  ![![(1 / 4 : ℝ), 0, 0, 0, 0, 0],
    ![0, (1 / 4 : ℝ), 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, (3 / 4 : ℝ)]]

theorem canonicalInput_gravityCurvature_eq_normalForm :
    canonicalInputField.gravityCurvature = sourceGravityCurvatureNormalForm := by
  change holonomicGravityCurvature canonicalInput 0 = _
  unfold holonomicGravityCurvature
  funext internalPair spacetimePair
  unfold gravityConnectionDerivative
  rw [canonicalInput_gravityConnection_eq_normalForm]
  have coordinateDerivative :
      HasFDerivAt (fun point : BasePoint => point 2)
        (baseCoordinate 2) 0 :=
    (baseCoordinate 2).hasFDerivAt
  have coordinateHalfFDeriv :=
    (coordinateDerivative.mul_const' (1 / 2 : ℝ)).fderiv
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [sourceGravityConnectionNormalForm,
      sourceGravityCurvatureNormalForm,
      pairFirst, pairSecond, minkowskiInternalSign,
      div_eq_mul_inv,
      coordinateDirection, Fin.sum_univ_four] <;>
    norm_num
  all_goals
    rw [coordinateHalfFDeriv]
    simp [baseCoordinate]
  all_goals norm_num

def sourceGravityAuxiliaryNormalForm : PhysicalBivector :=
  ![![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, -(3 / 4 : ℝ)],
    ![(1 / 4 : ℝ), 0, 0, 0, 0, 0],
    ![0, (1 / 4 : ℝ), 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0]]

theorem canonicalInput_gravityAuxiliary_eq_normalForm :
    canonicalInputField.gravityAuxiliary =
      sourceGravityAuxiliaryNormalForm := by
  apply gravityInternalDualEquiv.injective
  have auxiliaryEquation :=
    positiveSourceNativeAlgebraicEliminationUpdate_gravityAuxiliaryEquation
      residualLimitLorentzCarrierReader 0
  change
    canonicalInputField.gravityCurvature =
      gravityInternalDualEquiv canonicalInputField.gravityAuxiliary
      at auxiliaryEquation
  rw [← auxiliaryEquation, canonicalInput_gravityCurvature_eq_normalForm]
  funext internalPair spacetimePair
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [sourceGravityCurvatureNormalForm,
      sourceGravityAuxiliaryNormalForm,
      gravityInternalDualEquiv, gravityInternalDualLinear,
      internalBivectorDual, lorentzianCoframeHodge]

theorem canonicalInput_coframe_eq_one :
    canonicalInputField.coframe = (1 : LorentzianCoframe) := by
  change positiveSmoothUnifiedSource.legacy.coframeAt 0 = 1
  exact positiveSmoothUnifiedSource.legacy.coframeAt_zero

theorem canonicalInput_gravityBFDensity_eq_zero :
    generatedGravityBFDensity canonicalInputField = 0 := by
  unfold generatedGravityBFDensity gravitySpacetimeHodge
    gravityCoframePairing coframeTwoFormMetricPairing
  rw [canonicalInput_coframe_eq_one,
    canonicalInput_gravityCurvature_eq_normalForm,
    canonicalInput_gravityAuxiliary_eq_normalForm,
    coframeGaugeSpacetimeHodgeLinear_one]
  simp only [coframeTwoFormLinear_one, LinearMap.id_apply]
  simp [sourceGravityCurvatureNormalForm,
    sourceGravityAuxiliaryNormalForm,
    gravityInternalDualEquiv, gravityInternalDualLinear,
    internalBivectorDual,
    lorentzianCoframeHodgeEquiv, lorentzianCoframeHodge,
    lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond,
    Fin.sum_univ_six]

def sourceResponseGravityAuxiliaryNormalForm : PhysicalBivector :=
  ![![0, 0, 0, (1 / 2 : ℝ), 0, 0],
    ![0, 0, 0, 0, (1 / 2 : ℝ), 0],
    ![0, 0, 0, 0, 0, (1 / 8 : ℝ)],
    ![-(3 / 8 : ℝ), 0, 0, 0, 0, 0],
    ![0, -(3 / 8 : ℝ), 0, 0, 0, 0],
    ![0, 0, -(1 / 2 : ℝ), 0, 0, 0]]

theorem canonicalResponse_gravityAuxiliary_eq_normalForm :
    canonicalResponseField.gravityAuxiliary =
      sourceResponseGravityAuxiliaryNormalForm := by
  change
    gravityAlgebraicKeepResponseAuxiliaryField positiveSmoothUnifiedSource
        canonicalInput 0 = _
  unfold gravityAlgebraicKeepResponseAuxiliaryField
    forcedGravityAuxiliaryKeepEndpoint
  have inputAuxiliary :
      canonicalInput.gravityAuxiliary 0 =
        sourceGravityAuxiliaryNormalForm := by
    exact canonicalInput_gravityAuxiliary_eq_normalForm
  have inputCoframe :
      canonicalInput.coframe 0 = (1 : LorentzianCoframe) := by
    exact canonicalInput_coframe_eq_one
  rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half,
    inputAuxiliary, inputCoframe,
    physicalIIPlusBivector_one_eq_identityCoordinates]
  funext internalPair spacetimePair
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [sourceGravityAuxiliaryNormalForm,
      sourceResponseGravityAuxiliaryNormalForm,
      identityPhysicalIIPlusBivector] <;>
    norm_num

def sourceResponseGravityCurvatureNormalForm : PhysicalBivector :=
  ![![-(3 / 8 : ℝ), 0, 0, 0, 0, 0],
    ![0, -(3 / 8 : ℝ), 0, 0, 0, 0],
    ![0, 0, -(1 / 2 : ℝ), 0, 0, 0],
    ![0, 0, 0, -(1 / 2 : ℝ), 0, 0],
    ![0, 0, 0, 0, -(1 / 2 : ℝ), 0],
    ![0, 0, 0, 0, 0, -(1 / 8 : ℝ)]]

theorem canonicalResponse_gravityCurvature_eq_normalForm :
    canonicalResponseField.gravityCurvature =
      sourceResponseGravityCurvatureNormalForm := by
  have transported :=
    positiveSourceNativeGravityAlgebraicKeepResponse_auxiliaryResidual_origin
      residualLimitLorentzCarrierReader
  have inputZero :=
    (positiveSourceNativeAlgebraicEliminationUpdate_solvedAlgebraicResiduals
      residualLimitLorentzCarrierReader 0).1
  change
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
      canonicalResponse 0).gravityAuxiliary =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) •
        (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
          canonicalInput 0).gravityAuxiliary at transported
  change
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
      canonicalInput 0).gravityAuxiliary = 0 at inputZero
  rw [inputZero, smul_zero] at transported
  change
    canonicalResponseField.gravityCurvature -
      gravityInternalDualEquiv canonicalResponseField.gravityAuxiliary = 0
      at transported
  rw [sub_eq_zero, canonicalResponse_gravityAuxiliary_eq_normalForm]
    at transported
  rw [transported]
  funext internalPair spacetimePair
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [sourceResponseGravityAuxiliaryNormalForm,
      sourceResponseGravityCurvatureNormalForm,
      gravityInternalDualEquiv, gravityInternalDualLinear,
      internalBivectorDual, lorentzianCoframeHodge]

theorem canonicalResponse_coframe_eq_one :
    canonicalResponseField.coframe = (1 : LorentzianCoframe) := by
  change positiveSmoothUnifiedSource.legacy.coframeAt 0 = 1
  exact positiveSmoothUnifiedSource.legacy.coframeAt_zero

theorem canonicalResponse_gravityBFDensity_eq_neg_seven_sixteenths :
    generatedGravityBFDensity canonicalResponseField = -(7 / 16 : ℝ) := by
  unfold generatedGravityBFDensity gravitySpacetimeHodge
    gravityCoframePairing coframeTwoFormMetricPairing
  rw [canonicalResponse_coframe_eq_one,
    canonicalResponse_gravityCurvature_eq_normalForm,
    canonicalResponse_gravityAuxiliary_eq_normalForm,
    coframeGaugeSpacetimeHodgeLinear_one]
  simp only [coframeTwoFormLinear_one, LinearMap.id_apply]
  simp [sourceResponseGravityCurvatureNormalForm,
    sourceResponseGravityAuxiliaryNormalForm,
    gravityInternalDualEquiv, gravityInternalDualLinear,
    internalBivectorDual,
    lorentzianCoframeHodgeEquiv, lorentzianCoframeHodge,
    lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond, Fin.sum_univ_six]
  norm_num

/-- The `-3/8` value is the `(0, 0)` curvature coordinate, not the integrated
gravity BF scalar. -/
theorem canonicalResponse_curvature_zero_zero_eq_neg_three_eighths :
    canonicalResponseField.gravityCurvature 0 0 = -(3 / 8 : ℝ) := by
  rw [canonicalResponse_gravityCurvature_eq_normalForm]
  norm_num [sourceResponseGravityCurvatureNormalForm]

/-- Negative regression preventing the response curvature coordinate from being
silently substituted for the gravity BF scalar. -/
theorem canonicalResponse_curvature_zero_zero_ne_gravityBFDensity :
    canonicalResponseField.gravityCurvature 0 0 ≠
      generatedGravityBFDensity canonicalResponseField := by
  rw [canonicalResponse_curvature_zero_zero_eq_neg_three_eighths,
    canonicalResponse_gravityBFDensity_eq_neg_seven_sixteenths]
  norm_num

theorem canonicalInput_gaugeCurvature_eq_reference :
    canonicalInputField.gaugeCurvature = referenceOriginField.gaugeCurvature := by
  have generated := positiveSourceP286AffineConnection_actualCurvature
    (installPositiveSourceNativeGravityKinematics
      residualLimitLorentzCarrierReader)
  change canonicalInputField.gaugeCurvature =
      sourceP286TargetCurvature positiveSmoothUnifiedSource.legacy at generated
  rw [generated]
  change sourceP286TargetCurvature positiveSmoothUnifiedSource.legacy =
    holonomicGaugeCurvature residualLimitLorentzCarrierReader 0
  exact (residualLimitExtension_gaugeCurvature_origin
    residualLimitLorentzCarrierReader
    residualLimitLorentzCarrierReader_extends).symm

theorem canonicalInput_gaugeAuxiliary_eq_reference :
    canonicalInputField.gaugeAuxiliary = referenceOriginField.gaugeAuxiliary := by
  change
    generatedP286GaugeConstitutiveAuxiliary positiveSmoothUnifiedSource
      (positiveSmoothUnifiedSource.legacy.coframeAt 0)
      (holonomicGaugeCurvature
        (positiveSourceNativeKinematicSeed
          residualLimitLorentzCarrierReader) 0) =
      positiveResidualLimitSixFieldCarrier.gaugeAuxiliary 0
  have generated := positiveSourceP286AffineConnection_actualCurvature
    (installPositiveSourceNativeGravityKinematics
      residualLimitLorentzCarrierReader)
  change holonomicGaugeCurvature
      (positiveSourceNativeKinematicSeed residualLimitLorentzCarrierReader) 0 =
    sourceP286TargetCurvature positiveSmoothUnifiedSource.legacy at generated
  rw [generated]
  rfl

theorem canonicalResponse_gaugeCurvature_eq_reference :
    canonicalResponseField.gaugeCurvature =
      referenceOriginField.gaugeCurvature := by
  exact canonicalInput_gaugeCurvature_eq_reference

theorem canonicalResponse_gaugeAuxiliary_eq_reference :
    canonicalResponseField.gaugeAuxiliary =
      referenceOriginField.gaugeAuxiliary := by
  exact canonicalInput_gaugeAuxiliary_eq_reference

theorem canonicalInput_gaugeSectorDensity_eq_reference
    (candidate : LorentzianCoframe) :
    coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        canonicalInputField candidate =
      coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        referenceOriginField candidate := by
  have volumeEquality :
      generatedVolumeDensity (withCoframe canonicalInputField candidate) =
        generatedVolumeDensity (withCoframe referenceOriginField candidate) := by
    simp only [generatedVolumeDensity, withCoframe]
  unfold coframeGaugeSectorLocalDensity
  rw [volumeEquality, canonicalInput_gaugeCurvature_eq_reference,
    canonicalInput_gaugeAuxiliary_eq_reference]

theorem canonicalResponse_gaugeSectorDensity_eq_reference
    (candidate : LorentzianCoframe) :
    coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        canonicalResponseField candidate =
      coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        referenceOriginField candidate := by
  have volumeEquality :
      generatedVolumeDensity (withCoframe canonicalResponseField candidate) =
        generatedVolumeDensity (withCoframe referenceOriginField candidate) := by
    simp only [generatedVolumeDensity, withCoframe]
  unfold coframeGaugeSectorLocalDensity
  rw [volumeEquality, canonicalResponse_gaugeCurvature_eq_reference,
    canonicalResponse_gaugeAuxiliary_eq_reference]

theorem canonicalInput_scalarSectorDensity_eq_reference
    (candidate : LorentzianCoframe) :
    coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
        canonicalInputField candidate =
      coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
        referenceOriginField candidate := by
  have derivativeEquality :
      canonicalInputField.scalarCovariantDerivative =
        referenceOriginField.scalarCovariantDerivative := by
    rfl
  have scalarEquality :
      canonicalInputField.scalar = referenceOriginField.scalar := by
    rfl
  unfold coframeScalarSectorLocalDensity generatedScalarKineticDensity
  simp only [withCoframe]
  rw [derivativeEquality, scalarEquality]
  simp [generatedVolumeDensity]

theorem canonicalResponse_scalarSectorDensity_eq_reference
    (candidate : LorentzianCoframe) :
    coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
        canonicalResponseField candidate =
      coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
        referenceOriginField candidate := by
  have derivativeEquality :
      canonicalResponseField.scalarCovariantDerivative =
        referenceOriginField.scalarCovariantDerivative := by
    rfl
  have scalarEquality :
      canonicalResponseField.scalar = referenceOriginField.scalar := by
    rfl
  unfold coframeScalarSectorLocalDensity generatedScalarKineticDensity
  simp only [withCoframe]
  rw [derivativeEquality, scalarEquality]
  simp [generatedVolumeDensity]

theorem canonicalInput_matterSectorDensity_zero
    (candidate : LorentzianCoframe) :
    coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        canonicalInputField candidate = 0 := by
  unfold coframeMatterSectorLocalDensity generatedContinuumMatterDensity
  have dualZero : canonicalInputField.conjugateMatter = 0 := by
    rfl
  simp only [withCoframe]
  rw [dualZero]
  simp [matterDualFrameRelative]

theorem canonicalResponse_matterSectorDensity_zero
    (candidate : LorentzianCoframe) :
    coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        canonicalResponseField candidate = 0 := by
  unfold coframeMatterSectorLocalDensity generatedContinuumMatterDensity
  have dualZero : canonicalResponseField.conjugateMatter = 0 := by
    rfl
  simp only [withCoframe]
  rw [dualZero]
  simp [matterDualFrameRelative]

theorem canonicalInput_matterSectorDensity_eq_reference
    (candidate : LorentzianCoframe) :
    coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        canonicalInputField candidate =
      coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        referenceOriginField candidate := by
  rw [canonicalInput_matterSectorDensity_zero,
    referenceOriginField_matterSectorLocalDensity_zero]

theorem canonicalResponse_matterSectorDensity_eq_reference
    (candidate : LorentzianCoframe) :
    coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        canonicalResponseField candidate =
      coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        referenceOriginField candidate := by
  rw [canonicalResponse_matterSectorDensity_zero,
    referenceOriginField_matterSectorLocalDensity_zero]

theorem canonicalInput_multiplier_zero :
    canonicalInputField.gravitySimplicityMultiplier = 0 := by
  rfl

theorem canonicalResponse_multiplier_zero :
    canonicalResponseField.gravitySimplicityMultiplier = 0 := by
  rfl

theorem canonicalInput_gravityBFDensity_radial
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    generatedGravityBFDensity
        (withCoframe canonicalInputField (radialCoframe scalar)) = 0 := by
  unfold generatedGravityBFDensity
  simp only [withCoframe]
  rw [gravitySpacetimeHodge_radial scalar nonzero,
    gravitySpacetimeHodge_radial scalar nonzero]
  rw [gravityCoframePairing_radial, gravityCoframePairing_radial]
  have base := canonicalInput_gravityBFDensity_eq_zero
  unfold generatedGravityBFDensity at base
  rw [canonicalInput_coframe_eq_one] at base
  linear_combination scalar ^ 4 * base

theorem canonicalResponse_gravityBFDensity_radial
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    generatedGravityBFDensity
        (withCoframe canonicalResponseField (radialCoframe scalar)) =
      scalar ^ 4 * (-(7 / 16 : ℝ)) := by
  unfold generatedGravityBFDensity
  simp only [withCoframe]
  rw [gravitySpacetimeHodge_radial scalar nonzero,
    gravitySpacetimeHodge_radial scalar nonzero]
  rw [gravityCoframePairing_radial, gravityCoframePairing_radial]
  have base := canonicalResponse_gravityBFDensity_eq_neg_seven_sixteenths
  unfold generatedGravityBFDensity at base
  rw [canonicalResponse_coframe_eq_one] at base
  linear_combination scalar ^ 4 * base

theorem canonicalInput_gravitySectorDensity_radial
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    coframeGravitySectorLocalDensity canonicalInputField
        (radialCoframe scalar) = 0 := by
  unfold coframeGravitySectorLocalDensity
  rw [generatedGravitySimplicityDensity_eq_zero_of_multiplier_eq_zero,
    canonicalInput_gravityBFDensity_radial scalar nonzero]
  · ring
  · exact canonicalInput_multiplier_zero

theorem canonicalResponse_gravitySectorDensity_radial
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    coframeGravitySectorLocalDensity canonicalResponseField
        (radialCoframe scalar) =
      scalar ^ 8 * (-(7 / 16 : ℝ)) := by
  unfold coframeGravitySectorLocalDensity
  rw [generatedGravitySimplicityDensity_eq_zero_of_multiplier_eq_zero,
    canonicalResponse_gravityBFDensity_radial scalar nonzero]
  · have volume := referenceOriginField_radial_volume scalar
    change generatedVolumeDensity
        (withCoframe referenceOriginField (radialCoframe scalar)) =
      scalar ^ 4 at volume
    change generatedVolumeDensity
        (withCoframe canonicalResponseField (radialCoframe scalar)) *
          (0 + scalar ^ 4 * (-(7 / 16 : ℝ))) = _
    rw [show generatedVolumeDensity
        (withCoframe canonicalResponseField (radialCoframe scalar)) =
      generatedVolumeDensity
        (withCoframe referenceOriginField (radialCoframe scalar)) by rfl,
      volume]
    ring
  · exact canonicalResponse_multiplier_zero

theorem canonicalInput_coframeLocalDensity_radial
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    coframeLocalDensity positiveSmoothUnifiedSource 0 canonicalInputField
        (radialCoframe scalar) =
      -(5 / 16 : ℝ) * scalar ^ 8 := by
  rw [coframeLocalDensity_eq_sector_sum,
    canonicalInput_gravitySectorDensity_radial scalar nonzero,
    canonicalInput_gaugeSectorDensity_eq_reference,
    referenceOriginField_gaugeSectorLocalDensity_radial scalar nonzero,
    canonicalInput_scalarSectorDensity_eq_reference,
    referenceOriginField_scalarSectorLocalDensity_zero,
    canonicalInput_matterSectorDensity_zero]
  ring

theorem canonicalResponse_coframeLocalDensity_radial
    (scalar : ℝ) (nonzero : scalar ≠ 0) :
    coframeLocalDensity positiveSmoothUnifiedSource 0 canonicalResponseField
        (radialCoframe scalar) =
      -(3 / 4 : ℝ) * scalar ^ 8 := by
  rw [coframeLocalDensity_eq_sector_sum,
    canonicalResponse_gravitySectorDensity_radial scalar nonzero,
    canonicalResponse_gaugeSectorDensity_eq_reference,
    referenceOriginField_gaugeSectorLocalDensity_radial scalar nonzero,
    canonicalResponse_scalarSectorDensity_eq_reference,
    referenceOriginField_scalarSectorLocalDensity_zero,
    canonicalResponse_matterSectorDensity_zero]
  ring

theorem canonicalInput_coframeStress_identity_eq_neg_five_halves :
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
        canonicalInputField (1 : LorentzianCoframe) =
      -(5 / 2 : ℝ) := by
  have nondegenerate : Matrix.det canonicalInputField.coframe ≠ 0 := by
    rw [canonicalInput_coframe_eq_one]
    simp
  have outer := coframeLocalDensity_hasFDerivAt
    positiveSmoothUnifiedSource 0 canonicalInputField nondegenerate
  have identityDerivative := hasDerivAt_id (x := (1 : ℝ))
  have radialDerivative := identityDerivative.smul_const
    (1 : LorentzianCoframe)
  have radialDerivativeValue :
      (1 : ℝ) • (1 : LorentzianCoframe) =
        (1 : LorentzianCoframe) := by
    simp
  have radialDerivativeAtOne :=
    radialDerivative.congr_deriv radialDerivativeValue
  have pointEquality :
      canonicalInputField.coframe = radialCoframe (1 : ℝ) := by
    rw [canonicalInput_coframe_eq_one]
    simp [radialCoframe]
  have composed := outer.comp_hasDerivAt_of_eq (1 : ℝ)
    radialDerivativeAtOne pointEquality
  have polynomial := (identityDerivative.pow 8).const_mul
    (-(5 / 16 : ℝ))
  have formulaEventually : Filter.EventuallyEq (nhds (1 : ℝ))
      (fun scalar : ℝ =>
        coframeLocalDensity positiveSmoothUnifiedSource 0
          canonicalInputField (radialCoframe scalar))
      (fun scalar : ℝ => -(5 / 16 : ℝ) * scalar ^ 8) := by
    filter_upwards [eventually_ne_nhds
        (one_ne_zero : (1 : ℝ) ≠ 0)] with scalar nonzero
    exact canonicalInput_coframeLocalDensity_radial scalar nonzero
  have exactDerivative := polynomial.congr_of_eventuallyEq formulaEventually
  have derivativeEquality := composed.unique exactDerivative
  norm_num at derivativeEquality
  exact derivativeEquality

theorem canonicalResponse_coframeStress_identity_eq_neg_six :
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
        canonicalResponseField (1 : LorentzianCoframe) = -6 := by
  have nondegenerate : Matrix.det canonicalResponseField.coframe ≠ 0 := by
    rw [canonicalResponse_coframe_eq_one]
    simp
  have outer := coframeLocalDensity_hasFDerivAt
    positiveSmoothUnifiedSource 0 canonicalResponseField nondegenerate
  have identityDerivative := hasDerivAt_id (x := (1 : ℝ))
  have radialDerivative := identityDerivative.smul_const
    (1 : LorentzianCoframe)
  have radialDerivativeValue :
      (1 : ℝ) • (1 : LorentzianCoframe) =
        (1 : LorentzianCoframe) := by
    simp
  have radialDerivativeAtOne :=
    radialDerivative.congr_deriv radialDerivativeValue
  have pointEquality :
      canonicalResponseField.coframe = radialCoframe (1 : ℝ) := by
    rw [canonicalResponse_coframe_eq_one]
    simp [radialCoframe]
  have composed := outer.comp_hasDerivAt_of_eq (1 : ℝ)
    radialDerivativeAtOne pointEquality
  have polynomial := (identityDerivative.pow 8).const_mul
    (-(3 / 4 : ℝ))
  have formulaEventually : Filter.EventuallyEq (nhds (1 : ℝ))
      (fun scalar : ℝ =>
        coframeLocalDensity positiveSmoothUnifiedSource 0
          canonicalResponseField (radialCoframe scalar))
      (fun scalar : ℝ => -(3 / 4 : ℝ) * scalar ^ 8) := by
    filter_upwards [eventually_ne_nhds
        (one_ne_zero : (1 : ℝ) ≠ 0)] with scalar nonzero
    exact canonicalResponse_coframeLocalDensity_radial scalar nonzero
  have exactDerivative := polynomial.congr_of_eventuallyEq formulaEventually
  have derivativeEquality := composed.unique exactDerivative
  norm_num at derivativeEquality
  exact derivativeEquality

theorem canonicalResponse_coframeActualDelta_identity_eq_neg_seven_halves :
    algebraicKeepResponseCoframeActualDelta
        residualLimitLorentzCarrierReader (1 : LorentzianCoframe) =
      -(7 / 2 : ℝ) := by
  change
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
          canonicalResponseField (1 : LorentzianCoframe) -
        coframeLocalStressCovector positiveSmoothUnifiedSource 0
          canonicalInputField (1 : LorentzianCoframe) = _
  rw [canonicalResponse_coframeStress_identity_eq_neg_six,
    canonicalInput_coframeStress_identity_eq_neg_five_halves]
  norm_num

theorem canonicalInputTrace_coframe_identity_eq_neg_five_fourths :
    (algebraicKeepResponseInputTrace residualLimitLorentzCarrierReader).eulerLagrange.coframe
        (1 : LorentzianCoframe) =
      -(5 / 4 : ℝ) := by
  unfold algebraicKeepResponseInputTrace currentJointShellResidualTrace
    currentJointShellResidualKeep linearResidualTrace scalarKeepLinearMap
  rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half]
  change
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
          canonicalInputField (1 : LorentzianCoframe) -
        (1 - (1 / 2 : ℝ)) *
          coframeLocalStressCovector positiveSmoothUnifiedSource 0
            canonicalInputField (1 : LorentzianCoframe) = _
  rw [canonicalInput_coframeStress_identity_eq_neg_five_halves]
  norm_num

theorem canonicalLiftDefect_coframe_identity_eq_neg_nineteen_fourths :
    (algebraicKeepResponseLiftDefect residualLimitLorentzCarrierReader).eulerLagrange.coframe
        (1 : LorentzianCoframe) =
      -(19 / 4 : ℝ) := by
  have split := congrArg
    (fun covector : LorentzianCoframe →L[ℝ] ℝ =>
      covector (1 : LorentzianCoframe))
    (algebraicKeepResponseLiftDefect_coframe_eq_actualDelta_add_trace
      residualLimitLorentzCarrierReader)
  change
    (algebraicKeepResponseLiftDefect residualLimitLorentzCarrierReader).eulerLagrange.coframe
        (1 : LorentzianCoframe) =
      algebraicKeepResponseCoframeActualDelta
          residualLimitLorentzCarrierReader (1 : LorentzianCoframe) +
        (algebraicKeepResponseInputTrace residualLimitLorentzCarrierReader).eulerLagrange.coframe
          (1 : LorentzianCoframe) at split
  rw [canonicalResponse_coframeActualDelta_identity_eq_neg_seven_halves,
    canonicalInputTrace_coframe_identity_eq_neg_five_fourths] at split
  norm_num at split ⊢
  exact split

theorem canonicalLiftDefect_coframe_ne_zero :
    (algebraicKeepResponseLiftDefect residualLimitLorentzCarrierReader).eulerLagrange.coframe ≠
      0 := by
  intro zero
  have evaluated := congrArg
    (fun covector : LorentzianCoframe →L[ℝ] ℝ =>
      covector (1 : LorentzianCoframe)) zero
  rw [canonicalLiftDefect_coframe_identity_eq_neg_nineteen_fourths]
    at evaluated
  norm_num at evaluated

theorem canonicalLiftDefect_ne_zero :
    algebraicKeepResponseLiftDefect residualLimitLorentzCarrierReader ≠ 0 := by
  intro zero
  have coframeZero := congrArg
    (fun residual : CurrentPointwiseJointShellResidualCarrier =>
      residual.eulerLagrange.coframe) zero
  change
    (algebraicKeepResponseLiftDefect residualLimitLorentzCarrierReader).eulerLagrange.coframe =
      0 at coframeZero
  exact canonicalLiftDefect_coframe_ne_zero coframeZero

end

end SaturationMonoid.PhysicsCore.StageNineGravityAlgebraicKeepResponseCoframeDefect
