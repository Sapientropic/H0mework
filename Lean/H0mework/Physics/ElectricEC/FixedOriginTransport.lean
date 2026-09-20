import H0mework.Physics.ElectricJoint.FixedOriginCoframeClosure
import H0mework.Physics.ElectricJoint.FixedOriginMatterAdjointClosure
import H0mework.Physics.ElectricJoint.FixedOriginUnconditionalClosure

/-!
# Fixed P506/L0 live-electric Einstein--Cartan origin transport

The final Einstein--Cartan action leg changes only the primitive Lorentz
connection away from the common contact and the two generated gravity
reaction fields.  This module transports the five unaffected origin Euler
readers from the preceding live-electric actual and closes the three
gravity/Cartan-owned readers directly on the Einstein--Cartan output.

Every comparison follows from whole primitive-field preservation and the
generated origin connection equality.  No residual, curvature support,
target field, branch, or zero-fiber receipt enters the producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport

open ProofFreeRicherAnholonomicSource
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginMatterAdjointClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginUnconditionalClosure
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeScalarVariation
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracKineticLocalSpinDensity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeMatterSpinThreeForm
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGaugeCurvatureTransport
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterPointwiseEquation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineScalarPointwiseEquation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

abbrev PreEC : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual

abbrev FinalEC : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

/-! ## Primitive-field seams -/

@[simp] theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC :
    FinalEC.coframe = PreEC.coframe := by
  change
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
      positiveSmoothUnifiedSource PreEC).coframe =
      PreEC.coframe
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe
      positiveSmoothUnifiedSource PreEC

@[simp] theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeConnection_eq_preEC :
    FinalEC.gaugeConnection = PreEC.gaugeConnection := by
  change
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
      positiveSmoothUnifiedSource PreEC).gaugeConnection =
      PreEC.gaugeConnection
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeConnection
      positiveSmoothUnifiedSource PreEC

@[simp] theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeAuxiliary_eq_preEC :
    FinalEC.gaugeAuxiliary = PreEC.gaugeAuxiliary := by
  change
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
      positiveSmoothUnifiedSource PreEC).gaugeAuxiliary =
      PreEC.gaugeAuxiliary
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeAuxiliary
      positiveSmoothUnifiedSource PreEC

@[simp] theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_eq_preEC :
    FinalEC.scalar = PreEC.scalar := by
  change
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
      positiveSmoothUnifiedSource PreEC).scalar =
      PreEC.scalar
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_scalar
      positiveSmoothUnifiedSource PreEC

@[simp] theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matter_eq_preEC :
    FinalEC.matter = PreEC.matter := by
  change
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
      positiveSmoothUnifiedSource PreEC).matter =
      PreEC.matter
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matter
      positiveSmoothUnifiedSource PreEC

@[simp] theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_eq_preEC :
    FinalEC.conjugateMatter = PreEC.conjugateMatter := by
  change
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
      positiveSmoothUnifiedSource PreEC).conjugateMatter =
      PreEC.conjugateMatter
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatter
      positiveSmoothUnifiedSource PreEC

theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gravityConnection_origin_eq_preEC :
    FinalEC.gravityConnection 0 = PreEC.gravityConnection 0 := by
  change
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
      positiveSmoothUnifiedSource PreEC).gravityConnection 0 =
      PreEC.gravityConnection 0
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connection_zero
      positiveSmoothUnifiedSource PreEC

private theorem finalEC_gravityAuxiliary_eq_preEC :
    FinalEC.gravityAuxiliary = PreEC.gravityAuxiliary := by
  funext point
  rfl

theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalarCovariantDerivative_eq_preEC :
    holonomicScalarCovariantDerivative FinalEC =
      holonomicScalarCovariantDerivative PreEC := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_eq_preEC,
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeConnection_eq_preEC]

theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matterCovariantDerivative_origin_eq_preEC :
    holonomicMatterCovariantDerivative FinalEC 0 =
      holonomicMatterCovariantDerivative PreEC 0 := by
  funext direction
  unfold holonomicMatterCovariantDerivative
  rw [
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matter_eq_preEC,
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gravityConnection_origin_eq_preEC,
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeConnection_eq_preEC]

/-! ## P286 auxiliary and connection readers -/

theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_p286GaugeAuxiliary_origin_residual_eq_preEC :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      FinalEC 0).p286GaugeAuxiliary =
      (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        PreEC 0).p286GaugeAuxiliary := by
  have curvatureEq :
      holonomicGaugeCurvature FinalEC 0 =
        holonomicGaugeCurvature PreEC 0 :=
    holonomicGaugeCurvature_eq_of_connection_eq FinalEC PreEC
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeConnection_eq_preEC
      0
  change
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (toContinuumPointField FinalEC 0) =
      formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (toContinuumPointField PreEC 0)
  unfold formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
  simp only [toContinuumPointField]
  rw [curvatureEq,
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC,
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeAuxiliary_eq_preEC]

private theorem
    finalEC_p286AuxiliaryExteriorCovariantDerivative_origin_eq_preEC :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative FinalEC 0 =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative PreEC 0 := by
  have connectionEq :
      holonomicP286GaugeConnectionCoordinate FinalEC 0 =
        holonomicP286GaugeConnectionCoordinate PreEC 0 := by
    unfold holonomicP286GaugeConnectionCoordinate
    rw [
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeConnection_eq_preEC]
  have auxiliaryEq :
      holonomicP286GaugeAuxiliaryCoordinate FinalEC =
        holonomicP286GaugeAuxiliaryCoordinate PreEC := by
    funext point pair
    unfold holonomicP286GaugeAuxiliaryCoordinate
    rw [
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeAuxiliary_eq_preEC]
  have derivativeEq :
      p286GaugeAuxiliaryDirectionalDerivative FinalEC 0 =
        p286GaugeAuxiliaryDirectionalDerivative PreEC 0 := by
    unfold p286GaugeAuxiliaryDirectionalDerivative
    rw [auxiliaryEq]
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
  rw [connectionEq, congrFun auxiliaryEq 0, derivativeEq]

private theorem finalEC_chargedGaugeThreeForm_origin_eq_preEC :
    formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField FinalEC 0) =
      formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField PreEC 0) := by
  apply formNativeChargedGaugeThreeForm_eq_of_actionData_eq
  · exact congrFun
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC
      0
  · exact congrFun
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_eq_preEC
      0
  · exact congrFun
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalarCovariantDerivative_eq_preEC
      0
  · exact congrFun
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matter_eq_preEC
      0
  · exact congrFun
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_eq_preEC
      0

theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_p286GaugeConnection_origin_residual_eq_preEC :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      FinalEC 0).p286GaugeConnection =
      (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        PreEC 0).p286GaugeConnection := by
  change
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        FinalEC 0 =
      holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        PreEC 0
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [finalEC_p286AuxiliaryExteriorCovariantDerivative_origin_eq_preEC,
    finalEC_chargedGaugeThreeForm_origin_eq_preEC]

/-! ## Scalar reader -/

private theorem finalEC_scalarDifferentialMomentum_eq_preEC
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource FinalEC direction
        derivativeDirection =
      scalarDifferentialMomentum positiveSmoothUnifiedSource PreEC direction
        derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC,
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalarCovariantDerivative_eq_preEC]

private theorem finalEC_scalarDifferentialMomentumDivergence_eq_preEC
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource FinalEC
        direction =
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource PreEC
        direction := by
  funext point
  unfold scalarDifferentialMomentumDivergence
  simp_rw [finalEC_scalarDifferentialMomentum_eq_preEC]

private theorem finalEC_scalarAlgebraic_origin_eq_preEC
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        FinalEC direction 0 =
      diracDualScalarAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource PreEC direction 0 := by
  have variationEquality :
      holonomicScalarVariationAlgebraicDirection FinalEC direction 0 =
        holonomicScalarVariationAlgebraicDirection PreEC direction 0 := by
    funext formDirection
    unfold holonomicScalarVariationAlgebraicDirection
    rw [
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeConnection_eq_preEC]
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    StageNineScalarVariation.scalarPotentialFirstVariation
    diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC,
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_eq_preEC,
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalarCovariantDerivative_eq_preEC,
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matter_eq_preEC,
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_eq_preEC,
    variationEquality]

theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_origin_residual_eq_preEC :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      FinalEC 0).scalar =
      (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        PreEC 0).scalar := by
  funext direction
  change
    diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource FinalEC direction 0 =
      diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource PreEC direction 0
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  rw [finalEC_scalarAlgebraic_origin_eq_preEC,
    congrFun
      (finalEC_scalarDifferentialMomentumDivergence_eq_preEC direction) 0]

/-! ## Matter and conjugate-matter readers -/

private theorem finalEC_matterDifferentialMomentum_eq_preEC
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum positiveSmoothUnifiedSource FinalEC direction
        derivativeDirection =
      matterDifferentialMomentum positiveSmoothUnifiedSource PreEC direction
        derivativeDirection := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC,
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_eq_preEC]

private theorem finalEC_matterDifferentialMomentumDivergence_origin_eq_preEC
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence positiveSmoothUnifiedSource FinalEC
        direction 0 =
      matterDifferentialMomentumDivergence positiveSmoothUnifiedSource PreEC
        direction 0 := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [finalEC_matterDifferentialMomentum_eq_preEC direction
    derivativeDirection]

private theorem finalEC_matterAlgebraic_origin_eq_preEC
    (direction : MatterCoordinateCarrier) :
    diracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        FinalEC direction 0 =
      diracDualMatterAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource PreEC direction 0 := by
  have variationEquality :
      holonomicMatterVariationAlgebraicDirection FinalEC direction 0 =
        holonomicMatterVariationAlgebraicDirection PreEC direction 0 := by
    funext formDirection
    unfold holonomicMatterVariationAlgebraicDirection
    rw [
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gravityConnection_origin_eq_preEC,
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeConnection_eq_preEC]
  unfold diracDualMatterAlgebraicDirectionalCoefficient
    diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC,
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_eq_preEC,
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_eq_preEC,
    variationEquality]

theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matter_origin_residual_eq_preEC :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      FinalEC 0).matter =
      (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        PreEC 0).matter := by
  funext direction
  change
    diracDualMatterEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource FinalEC direction 0 =
      diracDualMatterEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource PreEC direction 0
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
  rw [finalEC_matterAlgebraic_origin_eq_preEC,
    finalEC_matterDifferentialMomentumDivergence_origin_eq_preEC]

private theorem finalEC_generatedMatterVector_origin_eq_preEC :
    generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField FinalEC 0) =
      generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField PreEC 0) := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    generatedContinuumDiracDualYukawaVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [toContinuumPointField]
  rw [
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC,
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matterCovariantDerivative_origin_eq_preEC,
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_eq_preEC,
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matter_eq_preEC]

theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_origin_residual_eq_preEC :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      FinalEC 0).conjugateMatter =
      (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        PreEC 0).conjugateMatter := by
  funext direction
  change
    diracDualConjugateMatterDirectionalCoefficient
        positiveSmoothUnifiedSource FinalEC direction 0 =
      diracDualConjugateMatterDirectionalCoefficient
        positiveSmoothUnifiedSource PreEC direction 0
  unfold diracDualConjugateMatterDirectionalCoefficient
    generatedVolumeDensity
  change
    |Matrix.det (FinalEC.coframe 0)| *
        ((matterDualOfCoordinates direction)
          (generatedContinuumDiracDualMatterVector
            positiveSmoothUnifiedSource 0 0
            (toContinuumPointField FinalEC 0))).re =
      |Matrix.det (PreEC.coframe 0)| *
        ((matterDualOfCoordinates direction)
          (generatedContinuumDiracDualMatterVector
            positiveSmoothUnifiedSource 0 0
            (toContinuumPointField PreEC 0))).re
  rw [
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC,
    finalEC_generatedMatterVector_origin_eq_preEC]

/-! ## Direct Einstein--Cartan structural zeros -/

theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gravityMultiplier_origin_zero :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      FinalEC 0).gravityMultiplier =
      0 := by
  change
    formNativeGravityMultiplierEulerResidual
        (toContinuumPointField FinalEC 0) =
      0
  exact
    (formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity _).2
      (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simplicity
        positiveSmoothUnifiedSource PreEC 0)

theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gravityAuxiliary_origin_zero :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      FinalEC 0).gravityAuxiliary =
      0 := by
  change holonomicFormNativeGravityAuxiliaryEulerResidual FinalEC 0 = 0
  exact congrFun
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_auxiliaryEquation
      positiveSmoothUnifiedSource PreEC) 0

private theorem finalEC_matterSpin_origin_eq_preEC :
    formNativeMatterSpinThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField FinalEC 0) =
      formNativeMatterSpinThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField PreEC 0) := by
  have physicalSpinEquality :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      positiveSmoothUnifiedSource FinalEC PreEC 0
      (congrFun
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC
        0)
      (congrFun
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matter_eq_preEC
        0)
      (congrFun
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_eq_preEC
        0)
  unfold diracDualFormNativeActionSpinResponseAt
    formNativePhysicalSpinCurrentThreeForm at physicalSpinEquality
  exact neg_injective physicalSpinEquality

theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_lorentzConnection_origin_residual_eq_preEC :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      FinalEC 0).lorentzConnection =
      (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        PreEC 0).lorentzConnection := by
  change
    holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        FinalEC 0 =
      holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        PreEC 0
  unfold holonomicFormNativeLorentzEulerThreeForm
  have auxiliaryDerivativeEq :
      holonomicGravityAuxiliaryExteriorCovariantDerivative FinalEC 0 =
        holonomicGravityAuxiliaryExteriorCovariantDerivative PreEC 0 := by
    unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
      holonomicGravityAuxiliaryJet gravityAuxiliaryDirectionalDerivative
    rw [
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gravityConnection_origin_eq_preEC,
      finalEC_gravityAuxiliary_eq_preEC]
  rw [auxiliaryDerivativeEq, finalEC_matterSpin_origin_eq_preEC]

theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_lorentzConnection_origin_zero :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      FinalEC 0).lorentzConnection =
      0 := by
  rw [
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_lorentzConnection_origin_residual_eq_preEC]
  exact
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_lorentzConnection_origin_zero

theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_p286GaugeAuxiliary_origin_zero :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      FinalEC 0).p286GaugeAuxiliary =
      0 := by
  rw [
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_p286GaugeAuxiliary_origin_residual_eq_preEC]
  exact
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_p286GaugeAuxiliary_origin_zero

theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matter_origin_zero :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      FinalEC 0).matter =
      0 := by
  rw [
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matter_origin_residual_eq_preEC]
  exact
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_matter_origin_zero

theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_origin_zero :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      FinalEC 0).conjugateMatter =
      0 := by
  rw [
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_origin_residual_eq_preEC]
  exact
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_conjugateMatter_origin_zero

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
