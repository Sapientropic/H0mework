import H0mework.Physics.JointVariation.GlobalDevelopmentOperator
import H0mework.Physics.JointVariation.GlobalDevelopmentFixedP286Compatibility
import H0mework.Physics.TimePrimitive.SecondAmbientJetRegularity
import H0mework.Physics.ActualGerms.FixedFullOccurrenceAdjointTemporalRegularity
import H0mework.Physics.ActualGerms.FixedFullOccurrenceMatterTemporalRegularity
import H0mework.Physics.ScalarJets.FixedFullOccurrenceScalarAccelerationRegularity
import H0mework.Physics.DualVariation.PointwiseP286RequiredExteriorProfileRegularity
import H0mework.Physics.GaugeAction.P286GaugeConnectionAlgebraicCurrentRegularity

/-!
# Fixed P506/L0 complete-joint P286 required-profile regularity

This module closes the local analytic mouth of the source/current-only global
development at the common P506/L0 occurrence:

```text
fixed source/current
→ action-generated matter and adjoint time primitives
→ action-generated scalar acceleration and canonical second primitive
→ live algebraic P286 connection and constitutive auxiliary
→ continuous complete required exterior profile.
```

The scalar step uses the generic ambient theorem for the canonical second
primitive, so both the scalar value and its full covariant first-jet action
data are controlled at the same occurrence.  The final theorem consumes the
exact pointwise mother-action read `J_charged - [A,B]`.  No residual,
support coordinate, target field, response, equation receipt, branch, or
free parameter enters any producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointP286RequiredExteriorProfileRegularity

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeHolonomicRegularity
open StageNineDiracDualFormNativeCanonicalTimeSecondPrimitiveAmbientFirstJetRegularity
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility
open StageNineDiracDualFormNativeCompleteJointActionP286TemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeFixedP506FullOccurrenceAdjointTemporalRegularity
open StageNineDiracDualFormNativeFixedP506FullOccurrenceMatterTemporalRegularity
open StageNineDiracDualFormNativeFixedP506FullOccurrenceScalarAccelerationRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonGlobalRegularity
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualP286AuxiliaryFirstJet
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativePointwiseP286RequiredExteriorProfileRegularity
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineP286ActionCauchySplit
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineP286GaugeConnectionAlgebraicCurrentRegularity
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286HolonomicSecondJetCarrier
open StageNineDiracDualFormNativeCompleteJointActionP286RequiredExteriorProfileNaturality
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance fixedTemporalRegularityP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance fixedTemporalRegularityP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev FixedTemporalCurrent : StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource FixedInput

private abbrev FixedAlgebraicCurrent : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent positiveSmoothUnifiedSource
    FixedInput

private abbrev FixedScalarAcceleration : BasePoint → ScalarCoordinateCarrier :=
  completeJointScalarAccelerationProfile positiveSmoothUnifiedSource
    FixedInput

private abbrev FixedScalarSecondPrimitive :
    BasePoint → ScalarCoordinateCarrier :=
  canonicalTimeSecondPrimitive FixedScalarAcceleration

private theorem fixedInput_matterCoordinate_contDiff :
    ContDiff ℝ ∞
      (fun point => matterCoordinateEquiv (FixedInput.matter point)) := by
  exact
    fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.1

theorem fixedP506L0CompleteJointGlobalTemporalCurrent_matterCoordinate_continuousAt_origin :
    ContinuousAt
      (fun point => matterCoordinateEquiv (FixedTemporalCurrent.matter point))
      0 := by
  have currentContinuous :
      ContinuousAt
        (fun point => matterCoordinateEquiv (FixedInput.matter point)) 0 :=
    fixedInput_matterCoordinate_contDiff.continuous.continuousAt
  have generated :=
    currentContinuous.add
      fixedP506L0FullOccurrenceMatterTemporalPrimitive_hasFDerivAt_origin.continuousAt
  rw [show
    (fun point =>
      matterCoordinateEquiv (FixedTemporalCurrent.matter point)) =
      (fun point => matterCoordinateEquiv (FixedInput.matter point)) +
        canonicalTimePrimitive
          (completeJointMatterTemporalCoordinateCorrection
            positiveSmoothUnifiedSource
            FixedP506FormNativeJointActionSolvedSuccessor) by
    funext point
    simp [FixedTemporalCurrent, completeJointGlobalTemporalCurrent,
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator]]
  exact generated

private theorem fixedInput_conjugateMatterCoordinates_contDiff :
    ContDiff ℝ ∞
      (holonomicConjugateMatterCoordinates FixedInput) :=
  holonomicConjugateMatterCoordinates_contDiff FixedInput
    fixedP506FormNativeJointActionSolvedSuccessor_smooth

theorem
    fixedP506L0CompleteJointGlobalTemporalCurrent_conjugateMatterCoordinates_continuousAt_origin :
    ContinuousAt
      (holonomicConjugateMatterCoordinates FixedTemporalCurrent)
      0 := by
  have currentContinuous :
      ContinuousAt
        (holonomicConjugateMatterCoordinates FixedInput) 0 :=
    fixedInput_conjugateMatterCoordinates_contDiff.continuous.continuousAt
  have generated :=
    currentContinuous.add
      fixedP506L0FullOccurrenceAdjointTemporalPrimitive_hasFDerivAt_origin.continuousAt
  rw [show
    holonomicConjugateMatterCoordinates FixedTemporalCurrent =
      holonomicConjugateMatterCoordinates FixedInput +
        canonicalTimePrimitive
          (completeJointAdjointTemporalCoordinateCorrection
            positiveSmoothUnifiedSource
            FixedP506FormNativeJointActionSolvedSuccessor) by
    funext point
    simp [FixedTemporalCurrent, completeJointGlobalTemporalCurrent,
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator,
      holonomicConjugateMatterCoordinates, matterDualCoordinates_add]]
  exact generated

theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_matterCoordinate_continuousAt_origin :
    ContinuousAt
      (fun point =>
        matterCoordinateEquiv (FixedAlgebraicCurrent.matter point))
      0 := by
  change ContinuousAt
    (fun point =>
      matterCoordinateEquiv (FixedTemporalCurrent.matter point)) 0
  exact
    fixedP506L0CompleteJointGlobalTemporalCurrent_matterCoordinate_continuousAt_origin

theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_conjugateMatterCoordinates_continuousAt_origin :
    ContinuousAt
      (holonomicConjugateMatterCoordinates FixedAlgebraicCurrent)
      0 := by
  have conjugateMatterEq :
      FixedAlgebraicCurrent.conjugateMatter =
        FixedTemporalCurrent.conjugateMatter := by
    rfl
  unfold holonomicConjugateMatterCoordinates
  rw [conjugateMatterEq]
  exact
    fixedP506L0CompleteJointGlobalTemporalCurrent_conjugateMatterCoordinates_continuousAt_origin

private theorem fixedAlgebraicCurrent_scalar_eq :
    FixedAlgebraicCurrent.scalar =
      fun point =>
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource +
          FixedScalarSecondPrimitive point := by
  funext point
  change
    FixedInput.scalar point +
        canonicalTimeSecondPrimitive
          (completeJointScalarAccelerationProfile positiveSmoothUnifiedSource
            FixedInput)
          point =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource +
        FixedScalarSecondPrimitive point
  rw [fixedP506FormNativeJointActionSolvedSuccessor_scalar,
    fixedP506JointActionSuccessor_scalar,
    fixedP506JointActual_scalar_vacuum]

private theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalar_continuousAt_origin_of_secondPrimitive
    (primitiveContinuous :
      ContinuousAt FixedScalarSecondPrimitive 0) :
    ContinuousAt FixedAlgebraicCurrent.scalar 0 := by
  rw [fixedAlgebraicCurrent_scalar_eq]
  exact continuousAt_const.add primitiveContinuous

private theorem fixedAlgebraicCurrent_scalar_fderiv_eq_secondPrimitive
    (point : BasePoint) :
    fderiv ℝ FixedAlgebraicCurrent.scalar point =
      fderiv ℝ FixedScalarSecondPrimitive point := by
  rw [fixedAlgebraicCurrent_scalar_eq]
  exact fderiv_const_add _

private abbrev FixedCanonicalInput : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalActionInput

private abbrev FixedCanonicalConnectionActual :
    StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalConnectionCandidate
    fixedP506L0P286CanonicalGeneratedWrite

private theorem fixedCanonicalConnectionActual_smooth :
    FixedCanonicalConnectionActual.Smooth :=
  installP286HolonomicConnectionSecondJet_smooth FixedCanonicalInput
    (fixedP506L0FinalCommonActionActual_smooth 0)
    (p286CanonicalDiagonalResponseSecondJet
      fixedP506L0P286CanonicalGeneratedWrite) 1

private theorem
    fixedAlgebraicCurrent_gaugeConnectionCoordinate_continuousAt_origin :
    ContinuousAt
      (holonomicP286GaugeConnectionCoordinate FixedAlgebraicCurrent) 0 := by
  rw [show
    holonomicP286GaugeConnectionCoordinate FixedAlgebraicCurrent =
      holonomicP286GaugeConnectionCoordinate
        FixedCanonicalConnectionActual by
    funext point
    unfold holonomicP286GaugeConnectionCoordinate
    rw [
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_gaugeConnection_eq_canonical]
    rfl]
  exact
    (holonomicP286GaugeConnectionCoordinate_contDiff
      FixedCanonicalConnectionActual
      fixedCanonicalConnectionActual_smooth).continuous.continuousAt

private theorem fixedAlgebraicCurrent_coframe_continuousAt_origin :
    ContinuousAt FixedAlgebraicCurrent.coframe 0 := by
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_coframe_eq_canonical]
  change ContinuousAt FixedCanonicalInput.coframe 0
  exact
    (holonomicCoframe_contDiff FixedCanonicalInput
      (fixedP506L0FinalCommonActionActual_smooth 0)).continuous.continuousAt

private theorem fixedAlgebraicCurrent_coframe_nondegenerate_origin :
    Matrix.det (FixedAlgebraicCurrent.coframe 0) ≠ 0 := by
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_coframe_eq_canonical,
    fixedP506L0P286CanonicalGeneratedActual_coframe_origin]
  norm_num

private theorem fixedAlgebraicCurrent_auxiliary_continuousAt_origin :
    ContinuousAt
      (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent) 0 := by
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_auxiliaryCoordinate_eq_canonical]
  exact
    (fixedP506L0P286CanonicalGeneratedActual_gaugeAuxiliaryCoordinate_differentiableAt
      0 (by
        rw [fixedP506L0FinalCommonActionActual_coframe_origin]
        norm_num)).continuousAt

private theorem scalarP286RawAction_apply_continuousAt
    (matrix : BasePoint → P286CoordinateCarrier)
    (scalar : BasePoint → ScalarCoordinateCarrier)
    (point : BasePoint)
    (matrixContinuous : ContinuousAt matrix point)
    (scalarContinuous : ContinuousAt scalar point) :
    ContinuousAt
      (fun candidate =>
        scalarMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm (matrix candidate)))
          (scalar candidate))
      point := by
  change ContinuousAt
    (fun candidate =>
      scalarP286ActionBilinear (matrix candidate) (scalar candidate))
    point
  exact
    (scalarP286ActionBilinear.toContinuousBilinearMap.continuous.continuousAt
      |>.comp' matrixContinuous).clm_apply scalarContinuous

private theorem
    holonomicScalarCovariantDerivative_continuousAt_of_actionData
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (scalarContinuous :
      ContinuousAt configuration.scalar point)
    (scalarFderivContinuous :
      ContinuousAt (fderiv ℝ configuration.scalar) point)
    (connectionContinuous :
      ContinuousAt
        (holonomicP286GaugeConnectionCoordinate configuration) point) :
    ContinuousAt
      (holonomicScalarCovariantDerivative configuration) point := by
  apply continuousAt_pi.mpr
  intro direction
  have derivativeContinuous : ContinuousAt
      (fun candidate =>
        fieldDirectionalDerivative configuration.scalar candidate direction)
      point := by
    unfold fieldDirectionalDerivative
    exact scalarFderivContinuous.clm_apply continuousAt_const
  have actionContinuous :=
    scalarP286RawAction_apply_continuousAt
      (fun candidate =>
        holonomicP286GaugeConnectionCoordinate configuration candidate
          direction)
      configuration.scalar point
      ((continuous_apply direction).continuousAt.comp'
        connectionContinuous)
      scalarContinuous
  have actionContinuous' : ContinuousAt
      (fun candidate =>
        scalarMotherLieAction
          (p286LieBlockEmbed
            (configuration.gaugeConnection candidate direction))
          (configuration.scalar candidate))
      point := by
    simpa only [holonomicP286GaugeConnectionCoordinate,
      p286CoordinateEquiv.symm_apply_apply] using actionContinuous
  unfold holonomicScalarCovariantDerivative
  change ContinuousAt
    ((fun candidate =>
      fieldDirectionalDerivative configuration.scalar candidate direction) +
    fun candidate =>
      scalarMotherLieAction
        (p286LieBlockEmbed
          (configuration.gaugeConnection candidate direction))
        (configuration.scalar candidate))
    point
  exact derivativeContinuous.add actionContinuous'

private theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarCovariantDerivative_continuousAt_origin_of_secondPrimitive
    (primitiveContinuous :
      ContinuousAt FixedScalarSecondPrimitive 0)
    (primitiveFderivContinuous :
      ContinuousAt (fderiv ℝ FixedScalarSecondPrimitive) 0) :
    ContinuousAt
      (holonomicScalarCovariantDerivative FixedAlgebraicCurrent)
      0 := by
  have scalarContinuous :=
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalar_continuousAt_origin_of_secondPrimitive
      primitiveContinuous
  have scalarFderivContinuous :
      ContinuousAt (fderiv ℝ FixedAlgebraicCurrent.scalar) 0 := by
    rw [show
      fderiv ℝ FixedAlgebraicCurrent.scalar =
        fderiv ℝ FixedScalarSecondPrimitive by
      funext point
      exact
        fixedAlgebraicCurrent_scalar_fderiv_eq_secondPrimitive point]
    exact primitiveFderivContinuous
  exact
    holonomicScalarCovariantDerivative_continuousAt_of_actionData
      FixedAlgebraicCurrent 0 scalarContinuous scalarFderivContinuous
      fixedAlgebraicCurrent_gaugeConnectionCoordinate_continuousAt_origin

private theorem
    fixedP506L0CompleteJointP286RequiredExteriorProfile_continuousAt_origin_of_secondPrimitive
    (primitiveContinuous :
      ContinuousAt FixedScalarSecondPrimitive 0)
    (primitiveFderivContinuous :
      ContinuousAt (fderiv ℝ FixedScalarSecondPrimitive) 0) :
    ContinuousAt
      (completeJointP286RequiredExteriorProfile positiveSmoothUnifiedSource
        FixedAlgebraicCurrent)
      0 := by
  rw [show
    completeJointP286RequiredExteriorProfile positiveSmoothUnifiedSource
        FixedAlgebraicCurrent =
      pointwiseDirectP286RequiredExteriorDerivative
        positiveSmoothUnifiedSource FixedAlgebraicCurrent by
    funext contact
    exact
      completeJointP286RequiredExteriorProfile_eq_pointwiseDirect_of_constitutiveAt
        positiveSmoothUnifiedSource FixedAlgebraicCurrent contact
        (completeJointGlobalP286AlgebraicCurrent_constitutiveAuxiliary
          positiveSmoothUnifiedSource FixedInput contact)]
  exact
    pointwiseDirectP286RequiredExteriorDerivative_continuousAt_of_actionData
      positiveSmoothUnifiedSource FixedAlgebraicCurrent 0
      fixedAlgebraicCurrent_coframe_continuousAt_origin
      fixedAlgebraicCurrent_coframe_nondegenerate_origin
      fixedAlgebraicCurrent_gaugeConnectionCoordinate_continuousAt_origin
      fixedAlgebraicCurrent_auxiliary_continuousAt_origin
      (fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalar_continuousAt_origin_of_secondPrimitive
        primitiveContinuous)
      (fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarCovariantDerivative_continuousAt_origin_of_secondPrimitive
        primitiveContinuous primitiveFderivContinuous)
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_matterCoordinate_continuousAt_origin
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_conjugateMatterCoordinates_continuousAt_origin

theorem fixedP506L0CompleteJointScalarSecondPrimitive_hasFDerivAt_origin :
    HasFDerivAt FixedScalarSecondPrimitive
      (0 : BasePoint →L[ℝ] ScalarCoordinateCarrier) 0 :=
  canonicalTimeSecondPrimitive_hasFDerivAt_zero_of_contDiffAt
    FixedScalarAcceleration
    (fixedP506L0CompleteJointScalarAccelerationProfile_contDiffAt_origin.of_le
      (by simp))

theorem
    fixedP506L0CompleteJointScalarSecondPrimitive_fderiv_continuousAt_origin :
    ContinuousAt (fderiv ℝ FixedScalarSecondPrimitive) 0 :=
  canonicalTimeSecondPrimitive_continuousAt_fderiv_zero_of_contDiffAt
    FixedScalarAcceleration
    (fixedP506L0CompleteJointScalarAccelerationProfile_contDiffAt_origin.of_le
      (by simp))

theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalar_continuousAt_origin :
    ContinuousAt FixedAlgebraicCurrent.scalar 0 :=
  fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalar_continuousAt_origin_of_secondPrimitive
    fixedP506L0CompleteJointScalarSecondPrimitive_hasFDerivAt_origin.continuousAt

theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarCovariantDerivative_continuousAt_origin :
    ContinuousAt
      (holonomicScalarCovariantDerivative FixedAlgebraicCurrent)
      0 :=
  fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarCovariantDerivative_continuousAt_origin_of_secondPrimitive
    fixedP506L0CompleteJointScalarSecondPrimitive_hasFDerivAt_origin.continuousAt
    fixedP506L0CompleteJointScalarSecondPrimitive_fderiv_continuousAt_origin

theorem
    fixedP506L0CompleteJointP286RequiredExteriorProfile_continuousAt_origin :
    ContinuousAt
      (completeJointP286RequiredExteriorProfile positiveSmoothUnifiedSource
        FixedAlgebraicCurrent)
      0 :=
  fixedP506L0CompleteJointP286RequiredExteriorProfile_continuousAt_origin_of_secondPrimitive
    fixedP506L0CompleteJointScalarSecondPrimitive_hasFDerivAt_origin.continuousAt
    fixedP506L0CompleteJointScalarSecondPrimitive_fderiv_continuousAt_origin

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointP286RequiredExteriorProfileRegularity
