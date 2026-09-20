import H0mework.Physics.ConstrainedCauchy.FixedGlobalOperator
import H0mework.Physics.GravityTail.FixedOriginClosure
import H0mework.Physics.Coframe.ScalarMomentumCoframeReadout

/-!
# Fixed P506/L0 constraint/Cauchy successor origin joint residual

The source-native constraint/Cauchy operator has already emitted one common
actual.  This module reads its complete nine-channel residual at the canonical
occurrence.  The gravity channels are discharged by the operator's own action
laws; unchanged P286, scalar, primal, and adjoint data are transported through
exact field and first-jet equalities from the previously closed action-selected
actual.  No residual coordinate, support branch, or zero-fiber witness enters
the writer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyOriginJointResidual

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionActualizationRegression
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracKineticLocalSpinDensity
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineCoframeFirstJet
open StageNineCoframeScalarMatterRegularity
open StageNineCoframeHolonomicSecondJetCarrier
open StageNineDiracDualFormNativeFixedP506ActionSelectedCartanECSynchronizedGravityTailLorentzPath
open StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailOriginClosure
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeIdentityECCartanRestartOriginFirstGerm
open StageNineDiracDualFormNativeIdentityECCartanRestartOriginCurvature
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineDiracDualFormNativeIdentityECNonlinearLeviCivitaFirstGerm
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGaugeCurvatureTransport
open StageNineHolonomicIdentityCoframeConjugateMatterActionAcceptance
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterPointwiseEquation
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionAcceptance
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeScalarVariation
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeGravityReactionInstallation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeMatterSpinThreeForm
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeAuxiliaryVariation
open StageNineScalarPointwiseEquation
open StageNineScalarMomentumCoframeReadout
open StageNineScalarVariation
open StageNineTopologicalP286GaugeThreeFormDuality
open StageNineTopologicalLorentzThreeFormDualInverse
open StageNineP286ActionCauchySplit

noncomputable section
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

private def Source : SmoothUnifiedSource := positiveSmoothUnifiedSource
private def Output : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchyGlobalActual
private def CartanBase : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECCauchyTemporalBase
private def Prepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintPreparedActual
private def Restart : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintRestartActual
private def Reference : StageNineHolonomicConfiguration :=
  fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPathGlobalActual

private theorem outputGaugeConnection_eq_reference :
    Output.gaugeConnection = Reference.gaugeConnection := by
  unfold Output Reference
  rfl

private theorem outputGaugeAuxiliary_eq_reference :
    Output.gaugeAuxiliary = Reference.gaugeAuxiliary := by
  unfold Output Reference
  rfl

private theorem outputScalar_eq_reference : Output.scalar = Reference.scalar := by
  unfold Output Reference
  rfl

private theorem outputMatter_eq_reference : Output.matter = Reference.matter := by
  unfold Output Reference
  rfl

private theorem outputConjugateMatter_eq_reference :
    Output.conjugateMatter = Reference.conjugateMatter := by
  unfold Output Reference
  rfl

private theorem outputCoframe_origin_eq_reference :
    Output.coframe 0 = Reference.coframe 0 := by
  unfold Output Reference
  rw [fixedP506L0CartanECConstraintCauchyGlobalActual_coframe_origin]
  rw [StageNineDiracDualFormNativeFixedP506ActionSelectedCartanECSynchronizedGravityTailLorentzPath.fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPath_coframe_eq_one]

private theorem outputCoframeFirstJet_origin_eq_reference :
    holonomicCoframeFirstJetAt Output.coframe 0 =
      holonomicCoframeFirstJetAt Reference.coframe 0 := by
  unfold Output Reference
  change
    holonomicCoframeFirstJetAt
        (sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
          Source CartanBase).coframe 0 = _
  unfold sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
  rw [identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_eq_quadratic
    CartanBase
    (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
      Source CartanBase)
    fixedP506L0CartanECCauchyTemporalBase_coframe_eq_one]
  rw [holonomicCoframeFirstJetAt_identityECQuadraticCoframeField]
  rw [fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPath_coframe_eq_one]
  apply StageNineCoframeFirstJet.coframeJet_eq_of_fields_eq
  · simp [identityECQuadraticCoframeJet, identityECQuadraticCoframeField,
      coframeFieldOfFirstAndSecondJet, identityECZeroCoframeFirstJet,
      holonomicCoframeFirstJetAt]
  · funext derivativeDirection internal coordinate
    simp [identityECQuadraticCoframeJet, holonomicCoframeFirstJetAt]

private theorem pointZero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem outputGravityConnection_origin_eq_reference :
    Output.gravityConnection 0 = Reference.gravityConnection 0 := by
  unfold Output Reference
  have outputRestart :=
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_connection_zeroSlice
      Source Prepared (0 : StageNineSpatialPoint)
  rw [pointZero] at outputRestart
  have cartanBaseSelfGenerated :
      CartanBase.gravityConnection = fun point =>
        diracDualFormNativeActionCartanConnectionAt Source CartanBase point := by
    funext point
    exact
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection_selfGenerated
        Source fixedP506L0CartanECCauchyTemporalInput point
  have restartPrepared : Restart.gravityConnection 0 = Prepared.gravityConnection 0 := by
    change
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source
        (identityECHolonomicCoframeHessianIncrementLocalActualLift CartanBase
          (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
            Source CartanBase))).gravityConnection 0 =
        (identityECHolonomicCoframeHessianIncrementLocalActualLift CartanBase
          (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
            Source CartanBase)).gravityConnection 0
    exact
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_identityECHessian_connection_origin
        Source CartanBase
        (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
          Source CartanBase)
        fixedP506L0CartanECCauchyTemporalBase_coframe_eq_one
        cartanBaseSelfGenerated
  calc
    Output.gravityConnection 0 = Restart.gravityConnection 0 := outputRestart
    _ = Prepared.gravityConnection 0 := restartPrepared
    _ = CartanBase.gravityConnection 0 := by
      change
        (identityECHolonomicCoframeHessianIncrementLocalActualLift CartanBase
          (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
            Source CartanBase)).gravityConnection 0 =
          CartanBase.gravityConnection 0
      exact
        identityECHolonomicCoframeHessianIncrementLocalActualLift_connection_origin
          CartanBase _
    _ = fixedActionCartanConnection := by
      rw [← pointZero]
      exact base_connection_zeroSlice_eq_fixedAction 0
    _ = Reference.gravityConnection 0 := by
      change fixedActionCartanConnection =
        fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPathGlobalActual.gravityConnection 0
      rw [fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPathGlobalActual_eq_actionWrite,
        sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_gravityConnection,
        cartanECSynchronizedGravityTailPathConnectionField_zero]
      exact
        fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_gravityConnection_origin_eq_fixedAction.symm

/-- The closed constraint/Cauchy current retains the exact fixed-lineage
Cartan connection at the canonical occurrence. -/
theorem
    fixedP506L0CartanECConstraintCauchyGlobalActual_gravityConnection_origin_eq_fixedAction :
    fixedP506L0CartanECConstraintCauchyGlobalActual.gravityConnection 0 =
      fixedActionCartanConnection := by
  change Output.gravityConnection 0 = fixedActionCartanConnection
  rw [outputGravityConnection_origin_eq_reference]
  unfold Reference
  rw [
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPathGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_gravityConnection,
    cartanECSynchronizedGravityTailPathConnectionField_zero]
  exact
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_gravityConnection_origin_eq_fixedAction

private theorem referenceResidualZero :
    diracDualFormNativePointwiseJointResidual Source Reference 0 = 0 :=
  fixedP506L0ActionSelectedGravityTail_residual_origin_zero

theorem fixedP506L0CartanECConstraintCauchyGlobalActual_gravityMultiplierResidual_origin_zero :
    (diracDualFormNativePointwiseJointResidual Source Output 0
      ).gravityMultiplier = 0 := by
  change
    formNativeGravityMultiplierEulerResidual
        (toContinuumPointField Output 0) = 0
  apply (formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity _).2
  exact fixedP506L0CartanECConstraintCauchyGlobalActual_simplicity 0

theorem fixedP506L0CartanECConstraintCauchyGlobalActual_gravityAuxiliaryResidual_origin_zero :
    (diracDualFormNativePointwiseJointResidual Source Output 0
      ).gravityAuxiliary = 0 := by
  change holonomicFormNativeGravityAuxiliaryEulerResidual Output 0 = 0
  exact congrFun
    (installFormNativeGravityReaction_auxiliaryEquation
      (cartanECCauchyTemporalConnectedActual Source Prepared)) 0

theorem fixedP506L0CartanECConstraintCauchyGlobalActual_p286GaugeAuxiliaryResidual_origin_zero :
    (diracDualFormNativePointwiseJointResidual Source Output 0
      ).p286GaugeAuxiliary = 0 := by
  change
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (toContinuumPointField Output 0) = 0
  have reference :
      formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
          (sourceGeneratedUnifiedCouplings Source)
          (toContinuumPointField Reference 0) = 0 := by
    have projected := congrArg
      DiracDualFormNativePointwiseJointResidualCarrier.p286GaugeAuxiliary
      referenceResidualZero
    change
      formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
          (sourceGeneratedUnifiedCouplings Source)
          (toContinuumPointField Reference 0) = 0 at projected
    exact projected
  unfold formNativeP286GaugeAuxiliaryEulerResidualAtBoundary at reference ⊢
  simp only [toContinuumPointField] at reference ⊢
  rw [outputCoframe_origin_eq_reference]
  rw [congrFun outputGaugeAuxiliary_eq_reference 0]
  rw [holonomicGaugeCurvature_eq_of_connection_eq Output Reference
    outputGaugeConnection_eq_reference 0]
  exact reference

private def OutputP286Euler : P286GaugeThreeForm :=
  holonomicFormNativeP286GaugeEulerThreeForm Source 0 Output 0

private def ReferenceP286Euler : P286GaugeThreeForm :=
  holonomicFormNativeP286GaugeEulerThreeForm Source 0 Reference 0

private theorem p286EulerAt_eq_reference :
    @Eq P286GaugeThreeForm OutputP286Euler ReferenceP286Euler := by
  unfold OutputP286Euler ReferenceP286Euler
  have connectionCoordinateEq :
      holonomicP286GaugeConnectionCoordinate Output 0 =
        holonomicP286GaugeConnectionCoordinate Reference 0 := by
    unfold holonomicP286GaugeConnectionCoordinate
    rw [outputGaugeConnection_eq_reference]
  have auxiliaryCoordinateEq :
      holonomicP286GaugeAuxiliaryCoordinate Output =
        holonomicP286GaugeAuxiliaryCoordinate Reference := by
    unfold holonomicP286GaugeAuxiliaryCoordinate
    rw [outputGaugeAuxiliary_eq_reference]
  have auxiliaryDerivativeEq :
      p286GaugeAuxiliaryDirectionalDerivative Output 0 =
        p286GaugeAuxiliaryDirectionalDerivative Reference 0 := by
    unfold p286GaugeAuxiliaryDirectionalDerivative
    rw [auxiliaryCoordinateEq]
  have covariantDerivativeEq :
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Output 0 =
        holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Reference 0 := by
    unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    rw [connectionCoordinateEq, congrFun auxiliaryCoordinateEq 0,
      auxiliaryDerivativeEq]
  have scalarCovariantDerivativeEq :
      holonomicScalarCovariantDerivative Output 0 =
        holonomicScalarCovariantDerivative Reference 0 := by
    unfold holonomicScalarCovariantDerivative
    rw [outputScalar_eq_reference, outputGaugeConnection_eq_reference]
  have chargedEq :
      formNativeChargedGaugeThreeForm Source 0 0
          (toContinuumPointField Output 0) =
        formNativeChargedGaugeThreeForm Source 0 0
          (toContinuumPointField Reference 0) := by
    apply formNativeChargedGaugeThreeForm_eq_of_actionData_eq
    · exact outputCoframe_origin_eq_reference
    · exact congrFun outputScalar_eq_reference 0
    · exact scalarCovariantDerivativeEq
    · exact congrFun outputMatter_eq_reference 0
    · exact congrFun outputConjugateMatter_eq_reference 0
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [covariantDerivativeEq, chargedEq]

theorem fixedP506L0CartanECConstraintCauchyGlobalActual_p286GaugeConnectionResidual_origin_zero :
    (diracDualFormNativePointwiseJointResidual Source Output 0
      ).p286GaugeConnection = 0 := by
  change holonomicFormNativeP286GaugeEulerThreeForm Source 0 Output 0 = 0
  change OutputP286Euler = 0
  rw [p286EulerAt_eq_reference]
  have projected := congrArg
    DiracDualFormNativePointwiseJointResidualCarrier.p286GaugeConnection
    referenceResidualZero
  change holonomicFormNativeP286GaugeEulerThreeForm Source 0 Reference 0 = 0
    at projected
  exact projected

private theorem preparedSmooth : Prepared.Smooth := by
  unfold Prepared fixedP506L0CartanECConstraintPreparedActual
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
  exact
    identityECHolonomicCoframeHessianIncrementLocalActualLift_smooth
      CartanBase
      (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
        Source CartanBase)
      fixedP506L0CartanECCauchyTemporalBase_smooth

private theorem preparedNondegenerateOrigin :
    Matrix.det (Prepared.coframe 0) ≠ 0 := by
  unfold Prepared
  rw [fixedP506L0CartanECConstraintPreparedActual_coframe_origin]
  norm_num

private theorem restartLorentzResidual_origin_zero :
    holonomicFormNativeLorentzEulerThreeForm Source 0 Restart 0 = 0 := by
  unfold Restart fixedP506L0CartanECConstraintRestartActual
    cartanECCauchyTemporalBase
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_lorentzEulerThreeForm_zero_at
      Source Prepared preparedSmooth 0 preparedNondegenerateOrigin

private theorem outputConnection_origin_eq_restart :
    Output.gravityConnection 0 = Restart.gravityConnection 0 := by
  unfold Output Restart
  have generated :=
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_connection_zeroSlice
      Source fixedP506L0CartanECConstraintPreparedActual
        (0 : StageNineSpatialPoint)
  rw [pointZero] at generated
  exact generated

private theorem outputGravityAuxiliary_eq_restart :
    Output.gravityAuxiliary = Restart.gravityAuxiliary := by
  unfold Output Restart fixedP506L0CartanECConstraintCauchyGlobalActual
    fixedP506L0CartanECConstraintRestartActual
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
    CartanECCauchyTemporalOccurrence.finalActual
    CartanECCauchyTemporalOccurrence.after
    cartanECCauchyTemporalFinalActual
    installFormNativeGravityReaction
    cartanECCauchyTemporalConnectedActual
  rfl

private theorem outputCoframe_eq_restart :
    Output.coframe = Restart.coframe := by
  unfold Output Restart fixedP506L0CartanECConstraintCauchyGlobalActual
    fixedP506L0CartanECConstraintRestartActual
  rw [sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_coframe]
  unfold cartanECCauchyTemporalBase
  exact
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
      Source fixedP506L0CartanECConstraintPreparedActual).symm

private theorem outputMatter_eq_restart :
    Output.matter = Restart.matter := by
  unfold Output Restart fixedP506L0CartanECConstraintCauchyGlobalActual
    fixedP506L0CartanECConstraintRestartActual
  rw [sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_matter]
  unfold cartanECCauchyTemporalBase
  exact
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter
      Source fixedP506L0CartanECConstraintPreparedActual).symm

private theorem outputConjugateMatter_eq_restart :
    Output.conjugateMatter = Restart.conjugateMatter := by
  unfold Output Restart fixedP506L0CartanECConstraintCauchyGlobalActual
    fixedP506L0CartanECConstraintRestartActual
  rw [sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_conjugateMatter]
  unfold cartanECCauchyTemporalBase
  exact
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter
      Source fixedP506L0CartanECConstraintPreparedActual).symm

/-- The constraint/Cauchy output retains the Cartan restart at the canonical
occurrence and remains a fixed readout of the same action-owned Cartan
connection. -/
theorem
    fixedP506L0CartanECConstraintCauchyGlobalActual_gravityConnection_origin_selfGenerated :
    fixedP506L0CartanECConstraintCauchyGlobalActual.gravityConnection 0 =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        fixedP506L0CartanECConstraintCauchyGlobalActual 0 := by
  change
    Output.gravityConnection 0 =
      diracDualFormNativeActionCartanConnectionAt Source Output 0
  rw [outputConnection_origin_eq_restart]
  change
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      Source Prepared).gravityConnection 0 =
        diracDualFormNativeActionCartanConnectionAt Source Output 0
  rw [
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection_selfGenerated
      Source Prepared 0]
  change
    diracDualFormNativeActionCartanConnectionAt Source Restart 0 =
      diracDualFormNativeActionCartanConnectionAt Source Output 0
  have spinEq :
      diracDualFormNativeActionSpinResponseAt Source Restart 0 =
        diracDualFormNativeActionSpinResponseAt Source Output 0 := by
    apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
    · exact (congrFun outputCoframe_eq_restart 0).symm
    · exact (congrFun outputMatter_eq_restart 0).symm
    · exact (congrFun outputConjugateMatter_eq_restart 0).symm
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [outputCoframe_eq_restart, spinEq]

private theorem outputGravityAuxiliaryExterior_origin_eq_restart :
    holonomicGravityAuxiliaryExteriorCovariantDerivative Output 0 =
      holonomicGravityAuxiliaryExteriorCovariantDerivative Restart 0 := by
  unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
    holonomicGravityAuxiliaryJet gravityAuxiliaryDirectionalDerivative
  rw [outputConnection_origin_eq_restart, outputGravityAuxiliary_eq_restart]

private theorem outputMatterSpin_origin_eq_restart :
    formNativeMatterSpinThreeForm Source 0 0
        (toContinuumPointField Output 0) =
      formNativeMatterSpinThreeForm Source 0 0
        (toContinuumPointField Restart 0) := by
  unfold formNativeMatterSpinThreeForm
  apply congrArg lorentzOneFormContinuousDualThreeForm
  apply ContinuousLinearMap.ext
  intro direction
  simp only [formNativeLorentzMatterFirstContinuousLinearMap_apply]
  unfold formNativeLorentzMatterFirstCoefficient generatedVolumeDensity
    matterCovariantDerivativeFirstVariationDensity
    pointwiseMatterLorentzConnectionVariation
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum matterDerivativeFrameRelative
  simp only [toContinuumPointField]
  rw [outputCoframe_eq_restart, outputMatter_eq_restart,
    outputConjugateMatter_eq_restart]

theorem fixedP506L0CartanECConstraintCauchyGlobalActual_lorentzResidual_origin_zero :
    (diracDualFormNativePointwiseJointResidual Source Output 0
      ).lorentzConnection = 0 := by
  change holonomicFormNativeLorentzEulerThreeForm Source 0 Output 0 = 0
  unfold holonomicFormNativeLorentzEulerThreeForm
  rw [outputGravityAuxiliaryExterior_origin_eq_restart,
    outputMatterSpin_origin_eq_restart]
  exact restartLorentzResidual_origin_zero

private theorem outputMatterCovariantDerivative_origin_eq_reference :
    holonomicMatterCovariantDerivative Output 0 =
      holonomicMatterCovariantDerivative Reference 0 := by
  funext direction
  unfold holonomicMatterCovariantDerivative
  rw [outputMatter_eq_reference,
    outputGravityConnection_origin_eq_reference,
    outputGaugeConnection_eq_reference]

private theorem outputGeneratedMatterVector_origin_eq_reference :
    generatedContinuumDiracDualMatterVector Source 0 0
        (toContinuumPointField Output 0) =
      generatedContinuumDiracDualMatterVector Source 0 0
        (toContinuumPointField Reference 0) := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    generatedContinuumDiracDualYukawaVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [toContinuumPointField]
  rw [outputCoframe_origin_eq_reference,
    outputMatterCovariantDerivative_origin_eq_reference,
    congrFun outputScalar_eq_reference 0,
    congrFun outputMatter_eq_reference 0]

private theorem outputConjugateMatterResidual_origin_eq_reference :
    (diracDualFormNativePointwiseJointResidual Source Output 0
      ).conjugateMatter =
      (diracDualFormNativePointwiseJointResidual Source Reference 0
        ).conjugateMatter := by
  funext direction
  change
    diracDualConjugateMatterDirectionalCoefficient Source Output direction 0 =
      diracDualConjugateMatterDirectionalCoefficient Source Reference
        direction 0
  unfold diracDualConjugateMatterDirectionalCoefficient generatedVolumeDensity
  change
    |Matrix.det (Output.coframe 0)| *
        ((matterDualOfCoordinates direction)
          (generatedContinuumDiracDualMatterVector Source 0 0
            (toContinuumPointField Output 0))).re =
      |Matrix.det (Reference.coframe 0)| *
        ((matterDualOfCoordinates direction)
          (generatedContinuumDiracDualMatterVector Source 0 0
            (toContinuumPointField Reference 0))).re
  rw [outputCoframe_origin_eq_reference,
    outputGeneratedMatterVector_origin_eq_reference]

theorem fixedP506L0CartanECConstraintCauchyGlobalActual_conjugateMatterResidual_origin_zero :
    (diracDualFormNativePointwiseJointResidual Source Output 0
      ).conjugateMatter = 0 := by
  rw [outputConjugateMatterResidual_origin_eq_reference]
  have projected := congrArg
    DiracDualFormNativePointwiseJointResidualCarrier.conjugateMatter
    referenceResidualZero
  change
    (diracDualFormNativePointwiseJointResidual Source Reference 0
      ).conjugateMatter = 0 at projected
  exact projected

private theorem referenceCoframeFirstJet_origin :
    holonomicCoframeFirstJetAt Reference.coframe 0 =
      identityCoframeMatterGeometry := by
  rw [show Reference.coframe = fun _ => (1 : LorentzianCoframe) by
    unfold Reference
    exact
      fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPath_coframe_eq_one]
  apply coframeJet_eq_of_fields_eq
  · rfl
  · funext derivativeDirection internal coordinate
    simp [holonomicCoframeFirstJetAt, identityCoframeMatterGeometry]

theorem fixedP506L0CartanECConstraintCauchyGlobalActual_coframeFirstJet_origin :
    holonomicCoframeFirstJetAt
        fixedP506L0CartanECConstraintCauchyGlobalActual.coframe 0 =
      identityCoframeMatterGeometry :=
  outputCoframeFirstJet_origin_eq_reference.trans
    referenceCoframeFirstJet_origin

private theorem outputCoframe_eq_prepared :
    Output.coframe = Prepared.coframe := by
  unfold Output Prepared
  exact
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_coframe
      Source fixedP506L0CartanECConstraintPreparedActual

private theorem outputConjugateMatter_eq_prepared :
    Output.conjugateMatter = Prepared.conjugateMatter := by
  unfold Output Prepared
  exact
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_conjugateMatter
      Source fixedP506L0CartanECConstraintPreparedActual

private theorem outputCoframe_differentiableAt_origin :
    DifferentiableAt ℝ Output.coframe 0 := by
  rw [outputCoframe_eq_prepared]
  exact
    (StageNineCoframeHolonomicRegularity.holonomicCoframe_contDiff
      Prepared preparedSmooth).differentiable (by simp) |>.differentiableAt

private theorem referenceCoframe_differentiableAt_origin :
    DifferentiableAt ℝ Reference.coframe 0 := by
  rw [show Reference.coframe = fun _ => (1 : LorentzianCoframe) by
    unfold Reference
    exact
      fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPath_coframe_eq_one]
  fun_prop

private theorem outputConjugateMatterCoordinates_differentiableAt_origin :
    DifferentiableAt ℝ (holonomicConjugateMatterCoordinates Output) 0 := by
  have coordinatesEq :
      holonomicConjugateMatterCoordinates Output =
        holonomicConjugateMatterCoordinates Prepared := by
    funext point
    unfold holonomicConjugateMatterCoordinates
    rw [outputConjugateMatter_eq_prepared]
  rw [coordinatesEq]
  exact
    (holonomicConjugateMatterCoordinates_contDiff Prepared preparedSmooth
      ).differentiable (by simp) |>.differentiableAt

private theorem referenceConjugateMatterCoordinates_differentiableAt_origin :
    DifferentiableAt ℝ (holonomicConjugateMatterCoordinates Reference) 0 := by
  have coordinatesEq :
      holonomicConjugateMatterCoordinates Reference =
        holonomicConjugateMatterCoordinates Output := by
    funext point
    unfold holonomicConjugateMatterCoordinates
    rw [outputConjugateMatter_eq_reference]
  rw [coordinatesEq]
  exact outputConjugateMatterCoordinates_differentiableAt_origin

private theorem identityComparison_matterDivergence_eq
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence Source
        (identityCoframeComparison Output) direction 0 =
      matterDifferentialMomentumDivergence Source
        (identityCoframeComparison Reference) direction 0 := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  unfold fieldDirectionalDerivative matterDifferentialMomentum
    matterDifferentialVariationVector generatedVolumeDensity
  simp only [toContinuumPointField]
  simp only [identityCoframeComparison_coframe,
    identityCoframeComparison_conjugateMatter]
  rw [outputConjugateMatter_eq_reference]

private theorem outputMatterDivergence_origin_eq_reference
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence Source Output direction 0 =
      matterDifferentialMomentumDivergence Source Reference direction 0 := by
  calc
    _ = matterDifferentialMomentumDivergence Source
          (identityCoframeComparison Output) direction 0 :=
      matterDifferentialMomentumDivergence_eq_identityCoframeComparison_of_identity_firstJet
        Source Output 0 outputCoframe_differentiableAt_origin
        outputConjugateMatterCoordinates_differentiableAt_origin
        fixedP506L0CartanECConstraintCauchyGlobalActual_coframeFirstJet_origin
        direction
    _ = matterDifferentialMomentumDivergence Source
          (identityCoframeComparison Reference) direction 0 :=
      identityComparison_matterDivergence_eq direction
    _ = matterDifferentialMomentumDivergence Source Reference direction 0 :=
      (matterDifferentialMomentumDivergence_eq_identityCoframeComparison_of_identity_firstJet
        Source Reference 0 referenceCoframe_differentiableAt_origin
        referenceConjugateMatterCoordinates_differentiableAt_origin
        referenceCoframeFirstJet_origin direction).symm

private theorem outputMatterAlgebraic_origin_eq_reference
    (direction : MatterCoordinateCarrier) :
    diracDualMatterAlgebraicDirectionalCoefficient Source Output direction 0 =
      diracDualMatterAlgebraicDirectionalCoefficient Source Reference
        direction 0 := by
  have variationEq :
      holonomicMatterVariationAlgebraicDirection Output direction 0 =
        holonomicMatterVariationAlgebraicDirection Reference direction 0 := by
    funext formDirection
    unfold holonomicMatterVariationAlgebraicDirection
    rw [outputGravityConnection_origin_eq_reference,
      outputGaugeConnection_eq_reference]
  unfold diracDualMatterAlgebraicDirectionalCoefficient
    diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [outputCoframe_origin_eq_reference,
    congrFun outputScalar_eq_reference 0,
    congrFun outputConjugateMatter_eq_reference 0, variationEq]

private theorem outputMatterResidual_origin_eq_reference :
    (diracDualFormNativePointwiseJointResidual Source Output 0).matter =
      (diracDualFormNativePointwiseJointResidual Source Reference 0).matter := by
  funext direction
  change
    diracDualMatterEulerLagrangeDirectionalCoefficient Source Output direction
        0 =
      diracDualMatterEulerLagrangeDirectionalCoefficient Source Reference
        direction 0
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
  rw [outputMatterAlgebraic_origin_eq_reference,
    outputMatterDivergence_origin_eq_reference]

theorem fixedP506L0CartanECConstraintCauchyGlobalActual_matterResidual_origin_zero :
    (diracDualFormNativePointwiseJointResidual Source Output 0).matter = 0 := by
  rw [outputMatterResidual_origin_eq_reference]
  simpa using congrArg
    DiracDualFormNativePointwiseJointResidualCarrier.matter
    referenceResidualZero

private theorem outputScalar_eq_prepared : Output.scalar = Prepared.scalar := by
  unfold Output Prepared
  exact
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_scalar
      Source fixedP506L0CartanECConstraintPreparedActual

private theorem outputGaugeConnection_eq_prepared :
    Output.gaugeConnection = Prepared.gaugeConnection := by
  unfold Output Prepared
  exact
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_gaugeConnection
      Source fixedP506L0CartanECConstraintPreparedActual

private theorem outputScalarCovariantDerivative_eq_prepared :
    holonomicScalarCovariantDerivative Output =
      holonomicScalarCovariantDerivative Prepared := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [outputScalar_eq_prepared, outputGaugeConnection_eq_prepared]

private theorem outputScalarCovariantDerivative_eq_reference :
    holonomicScalarCovariantDerivative Output =
      holonomicScalarCovariantDerivative Reference := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [outputScalar_eq_reference, outputGaugeConnection_eq_reference]

private theorem preparedScalarCovariantDerivative_differentiableAt_origin :
    DifferentiableAt ℝ (holonomicScalarCovariantDerivative Prepared) 0 := by
  rw [differentiableAt_pi]
  intro direction
  exact
    ((holonomicScalarCovariantDerivative_contDiff_local
      Prepared preparedSmooth direction).differentiable (by simp)
      ).differentiableAt

private theorem outputScalarCovariantDerivative_differentiableAt_origin :
    DifferentiableAt ℝ (holonomicScalarCovariantDerivative Output) 0 := by
  rw [outputScalarCovariantDerivative_eq_prepared]
  exact preparedScalarCovariantDerivative_differentiableAt_origin

private theorem referenceScalarCovariantDerivative_differentiableAt_origin :
    DifferentiableAt ℝ
      (holonomicScalarCovariantDerivative Reference) 0 := by
  rw [← outputScalarCovariantDerivative_eq_reference]
  exact outputScalarCovariantDerivative_differentiableAt_origin

private theorem outputCoframe_fderiv_origin_zero :
    fderiv ℝ Output.coframe 0 = 0 := by
  rw [outputCoframe_eq_prepared]
  exact
    (identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_hasFDerivAt_origin
      CartanBase
      (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
        Source CartanBase)
      fixedP506L0CartanECCauchyTemporalBase_coframe_eq_one).fderiv

private theorem referenceCoframe_fderiv_origin_zero :
    fderiv ℝ Reference.coframe 0 = 0 := by
  rw [show Reference.coframe = fun _ => (1 : LorentzianCoframe) by
    unfold Reference
    exact
      fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPath_coframe_eq_one]
  simp

private theorem outputCoframe_fderiv_origin_eq_reference :
    fderiv ℝ Output.coframe 0 = fderiv ℝ Reference.coframe 0 := by
  rw [outputCoframe_fderiv_origin_zero,
    referenceCoframe_fderiv_origin_zero]

private def scalarMomentumInner
    (configuration : StageNineHolonomicConfiguration) :
    BasePoint →
      LorentzianCoframe ×
        (LorentzianIndex → ScalarCoordinateCarrier) :=
  fun point =>
    (configuration.coframe point,
      holonomicScalarCovariantDerivative configuration point)

private theorem outputScalarMomentumInner_differentiableAt_origin :
    DifferentiableAt ℝ (scalarMomentumInner Output) 0 := by
  unfold scalarMomentumInner
  exact outputCoframe_differentiableAt_origin.prodMk
    outputScalarCovariantDerivative_differentiableAt_origin

private theorem referenceScalarMomentumInner_differentiableAt_origin :
    DifferentiableAt ℝ (scalarMomentumInner Reference) 0 := by
  unfold scalarMomentumInner
  exact referenceCoframe_differentiableAt_origin.prodMk
    referenceScalarCovariantDerivative_differentiableAt_origin

private theorem outputScalarMomentumInner_origin_eq_reference :
    scalarMomentumInner Output 0 = scalarMomentumInner Reference 0 := by
  apply Prod.ext
  · exact outputCoframe_origin_eq_reference
  · exact congrFun outputScalarCovariantDerivative_eq_reference 0

private theorem outputScalarMomentumInner_fderiv_origin :
    fderiv ℝ (scalarMomentumInner Output) 0 =
      (fderiv ℝ Output.coframe 0).prod
        (fderiv ℝ (holonomicScalarCovariantDerivative Output) 0) := by
  unfold scalarMomentumInner
  exact outputCoframe_differentiableAt_origin.fderiv_prodMk
    outputScalarCovariantDerivative_differentiableAt_origin

private theorem referenceScalarMomentumInner_fderiv_origin :
    fderiv ℝ (scalarMomentumInner Reference) 0 =
      (fderiv ℝ Reference.coframe 0).prod
        (fderiv ℝ (holonomicScalarCovariantDerivative Reference) 0) := by
  unfold scalarMomentumInner
  exact referenceCoframe_differentiableAt_origin.fderiv_prodMk
    referenceScalarCovariantDerivative_differentiableAt_origin

private theorem outputScalarMomentumInner_fderiv_origin_eq_reference :
    fderiv ℝ (scalarMomentumInner Output) 0 =
      fderiv ℝ (scalarMomentumInner Reference) 0 := by
  rw [outputScalarMomentumInner_fderiv_origin,
    referenceScalarMomentumInner_fderiv_origin,
    outputCoframe_fderiv_origin_eq_reference,
    outputScalarCovariantDerivative_eq_reference]

private theorem scalarMomentumReadout_differentiableAt_referenceInner
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    DifferentiableAt ℝ
      (scalarMomentumCoframeCovariantReadout direction derivativeDirection)
      (scalarMomentumInner Reference 0) := by
  have referenceCoframeOrigin : Reference.coframe 0 = 1 := by
    rw [show Reference.coframe = fun _ => (1 : LorentzianCoframe) by
      unfold Reference
      exact
        fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPath_coframe_eq_one]
  change DifferentiableAt ℝ
    (scalarMomentumCoframeCovariantReadout direction derivativeDirection)
    (Reference.coframe 0,
      holonomicScalarCovariantDerivative Reference 0)
  rw [referenceCoframeOrigin]
  exact
    (scalarMomentumCoframeCovariantReadout_contDiffAt_one direction
      derivativeDirection
      (holonomicScalarCovariantDerivative Reference 0)).differentiableAt
      (by simp)

private theorem outputScalarMomentumComposition_fderiv_origin_eq_reference
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fderiv ℝ
        (scalarMomentumCoframeCovariantReadout direction derivativeDirection ∘
          scalarMomentumInner Output) 0 =
      fderiv ℝ
        (scalarMomentumCoframeCovariantReadout direction derivativeDirection ∘
          scalarMomentumInner Reference) 0 := by
  let outer :=
    scalarMomentumCoframeCovariantReadout direction derivativeDirection
  have outerAtReference : DifferentiableAt ℝ outer
      (scalarMomentumInner Reference 0) :=
    scalarMomentumReadout_differentiableAt_referenceInner direction
      derivativeDirection
  have outerAtOutput : DifferentiableAt ℝ outer
      (scalarMomentumInner Output 0) := by
    rw [outputScalarMomentumInner_origin_eq_reference]
    exact outerAtReference
  change
    fderiv ℝ (outer ∘ scalarMomentumInner Output) 0 =
      fderiv ℝ (outer ∘ scalarMomentumInner Reference) 0
  rw [fderiv_comp 0 outerAtOutput
      outputScalarMomentumInner_differentiableAt_origin,
    fderiv_comp 0 outerAtReference
      referenceScalarMomentumInner_differentiableAt_origin,
    outputScalarMomentumInner_origin_eq_reference]
  exact congrArg
    (fun innerDerivative :
        BasePoint →L[ℝ]
          (LorentzianCoframe ×
            (LorentzianIndex → ScalarCoordinateCarrier)) =>
      (fderiv ℝ outer (scalarMomentumInner Reference 0)).comp
        innerDerivative)
    outputScalarMomentumInner_fderiv_origin_eq_reference

private theorem outputScalarMomentum_diagonalDerivative_eq_reference
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (scalarDifferentialMomentum Source Output direction
          derivativeDirection) 0 derivativeDirection =
      fieldDirectionalDerivative
        (scalarDifferentialMomentum Source Reference direction
          derivativeDirection) 0 derivativeDirection := by
  unfold fieldDirectionalDerivative
  rw [scalarDifferentialMomentum_eq_readout,
    scalarDifferentialMomentum_eq_readout]
  change
    (fderiv ℝ
        (scalarMomentumCoframeCovariantReadout direction derivativeDirection ∘
          scalarMomentumInner Output) 0)
        (coordinateDirection derivativeDirection) =
      (fderiv ℝ
        (scalarMomentumCoframeCovariantReadout direction derivativeDirection ∘
          scalarMomentumInner Reference) 0)
        (coordinateDirection derivativeDirection)
  rw [outputScalarMomentumComposition_fderiv_origin_eq_reference]

private theorem outputScalarDivergence_origin_eq_reference
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence Source Output direction 0 =
      scalarDifferentialMomentumDivergence Source Reference direction 0 := by
  unfold scalarDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  exact outputScalarMomentum_diagonalDerivative_eq_reference direction
    derivativeDirection

private theorem outputScalarAlgebraic_origin_eq_reference
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient Source Output direction 0 =
      diracDualScalarAlgebraicDirectionalCoefficient Source Reference
        direction 0 := by
  have variationEq :
      holonomicScalarVariationAlgebraicDirection Output direction 0 =
        holonomicScalarVariationAlgebraicDirection Reference direction 0 := by
    funext formDirection
    unfold holonomicScalarVariationAlgebraicDirection
    rw [outputGaugeConnection_eq_reference]
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    StageNineScalarVariation.scalarPotentialFirstVariation
    diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [outputCoframe_origin_eq_reference,
    congrFun outputScalarCovariantDerivative_eq_reference 0,
    variationEq, congrFun outputScalar_eq_reference 0,
    congrFun outputMatter_eq_reference 0,
    congrFun outputConjugateMatter_eq_reference 0]

private theorem outputScalarResidual_origin_eq_reference :
    (diracDualFormNativePointwiseJointResidual Source Output 0).scalar =
      (diracDualFormNativePointwiseJointResidual Source Reference 0).scalar := by
  funext direction
  change
    diracDualScalarEulerLagrangeDirectionalCoefficient Source Output direction
        0 =
      diracDualScalarEulerLagrangeDirectionalCoefficient Source Reference
        direction 0
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  rw [outputScalarAlgebraic_origin_eq_reference,
    outputScalarDivergence_origin_eq_reference]

theorem fixedP506L0CartanECConstraintCauchyGlobalActual_scalarResidual_origin_zero :
    (diracDualFormNativePointwiseJointResidual Source Output 0).scalar = 0 := by
  rw [outputScalarResidual_origin_eq_reference]
  simpa using congrArg
    DiracDualFormNativePointwiseJointResidualCarrier.scalar
    referenceResidualZero

/-- The one source-native constraint/Cauchy successor closes all nine joint
action channels at the canonical P506/L0 occurrence. -/
theorem fixedP506L0CartanECConstraintCauchyGlobalActual_residual_origin_zero :
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      fixedP506L0CartanECConstraintCauchyGlobalActual 0 = 0 := by
  change diracDualFormNativePointwiseJointResidual Source Output 0 = 0
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact
      fixedP506L0CartanECConstraintCauchyGlobalActual_gravityMultiplierResidual_origin_zero
  · exact
      fixedP506L0CartanECConstraintCauchyGlobalActual_gravityAuxiliaryResidual_origin_zero
  · exact
      fixedP506L0CartanECConstraintCauchyGlobalActual_p286GaugeAuxiliaryResidual_origin_zero
  · exact fixedP506L0CartanECConstraintCauchyGlobalActual_lorentzResidual_origin_zero
  · exact
      fixedP506L0CartanECConstraintCauchyGlobalActual_p286GaugeConnectionResidual_origin_zero
  · exact fixedP506L0CartanECConstraintCauchyGlobalActual_scalarResidual_origin_zero
  · exact fixedP506L0CartanECConstraintCauchyGlobalActual_matterResidual_origin_zero
  · exact
      fixedP506L0CartanECConstraintCauchyGlobalActual_conjugateMatterResidual_origin_zero
  · exact
      fixedP506L0CartanECConstraintCauchyGlobalActual_coframeResidual_origin_zero

theorem fixedP506L0CartanECConstraintCauchyGlobalActual_zeroFiber_origin :
    OnDiracDualFormNativePointwiseJointZeroFiber positiveSmoothUnifiedSource
      fixedP506L0CartanECConstraintCauchyGlobalActual 0 :=
  fixedP506L0CartanECConstraintCauchyGlobalActual_residual_origin_zero

end
end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyOriginJointResidual
