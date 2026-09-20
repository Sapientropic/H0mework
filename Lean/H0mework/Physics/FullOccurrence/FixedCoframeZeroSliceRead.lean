import H0mework.Physics.FullOccurrence.FixedGravityCoframeVerdict
import H0mework.Physics.FullOccurrence.FixedP286Verdict
import H0mework.Physics.ElectricEC.FixedGlobalDevelopmentMatterZeroSliceActionRead
import H0mework.Physics.DualVariation.RepairedMatterEquationReadout
import H0mework.Physics.ScalarJets.FixedJointP286AlgebraicMatterScalarDelta
import H0mework.Physics.JointVariation.MatterTemporalLocalRegularity
import H0mework.Physics.TimePrimitive.SecondAmbientJetRegularity
import H0mework.Physics.ActualGerms.FixedJointTemporalMatterTimeAxisRegularity
import H0mework.Physics.ElectricEC.FixedSecondSweepMatterTemporalRegularity
import H0mework.Physics.ElectricEC.FixedTemporalScalarAmbientFirstJetRegularity

/-!
# Fixed P506/L0 U6 coframe zero-slice read

This module evaluates the complete gauge-plus-matter coframe load on the one
full-occurrence actual generated from the fixed P506/L0 source and current.
It transports the already generated contact action jet to each zero-slice
occurrence, discharges the required local regularity from the same actual's
explicit normal form, and reads the coframe component of the joint residual as
zero.

No residual coordinate, target jet, regularity receipt, branch choice, or free
coefficient enters the write or the readout.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalCoframeZeroSliceRead

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeVariation
open StageNineDiracKineticLocalSpinDensity
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeCompleteJointMatterTemporalLocalRegularity
open StageNineDiracDualFormNativeCanonicalTimeSecondPrimitiveAmbientFirstJetRegularity
open StageNineDiracDualFormNativeFixedP506CompleteJointTemporalMatterTimeAxisRegularity
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCoframeVerdict
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286Verdict
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECGlobalDevelopmentMatterZeroSliceActionRead
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECSecondSweepMatterTemporalRegularity
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECTemporalScalarAmbientFirstJetRegularity
open StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicMatterScalarDelta
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceOriginSettlement
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeRepairedMatterEquationReadout
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeCoframeLocalVariation
open StageNineFormNativeMotherAction
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineMatterVariation
open StageNineMatterCovariantDerivativeAffine
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286ActionCauchySplit
open StageNineScalarLocalSpinDensity
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Temporal : StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source FixedInput

private abbrev Existing : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointGlobalDevelopmentActual

private abbrev Global : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private abbrev Contact (point : BasePoint) : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact point

private abbrev GlobalField (point : BasePoint) : StageNineContinuumPointField :=
  toContinuumPointField Global point

private abbrev ContactField (point : BasePoint) : StageNineContinuumPointField :=
  toContinuumPointField (Contact point) 0

private theorem global_coframe_one_zeroSlice
    (space : StageNineSpatialPoint) :
    Global.coframe (canonicalCauchySlicePoint 0 space) = 1 := by
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source Current).coframe (canonicalCauchySlicePoint 0 space) = 1
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe,
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing]
  exact fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_zeroSlice space

private theorem globalField_coframe_eq_contactField
    (point : BasePoint) :
    (GlobalField point).coframe = (ContactField point).coframe := by
  change Global.coframe point = (Contact point).coframe 0
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe_at
      Source Current point

private theorem globalField_gaugeAuxiliary_eq_contactField
    (point : BasePoint) :
    (GlobalField point).gaugeAuxiliary =
      (ContactField point).gaugeAuxiliary := by
  change Global.gaugeAuxiliary point = (Contact point).gaugeAuxiliary 0
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gaugeAuxiliary_at
      Source Current point

private theorem globalField_gravityConnection_eq_contactField
    (point : BasePoint) :
    Global.gravityConnection point =
      (Contact point).gravityConnection 0 := by
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityConnection_at
      Source Current point

private theorem globalField_gaugeConnection_eq_contactField
    (point : BasePoint) :
    Global.gaugeConnection point =
      (Contact point).gaugeConnection 0 := by
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gaugeConnection_at
      Source Current point

private theorem globalField_multiplier_eq_contactField
    (point : BasePoint) :
    (GlobalField point).gravitySimplicityMultiplier =
      (ContactField point).gravitySimplicityMultiplier := by
  change
    Global.gravitySimplicityMultiplier point =
      (Contact point).gravitySimplicityMultiplier 0
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_multiplier_at
      Source Current point

private theorem globalField_scalar_eq_contactField
    (point : BasePoint) :
    (GlobalField point).scalar = (ContactField point).scalar := by
  change Global.scalar point = (Contact point).scalar 0
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_at
      Source Current point

private theorem globalField_matter_eq_contactField
    (point : BasePoint) :
    (GlobalField point).matter = (ContactField point).matter := by
  change Global.matter point = (Contact point).matter 0
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_matter_at
      Source Current point

private theorem globalField_conjugateMatter_eq_contactField
    (point : BasePoint) :
    (GlobalField point).conjugateMatter =
      (ContactField point).conjugateMatter := by
  change Global.conjugateMatter point = (Contact point).conjugateMatter 0
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_conjugateMatter_at
      Source Current point

/-! The gauge-curvature part of the zero-slice coframe load has no assembly
seam.  Both already generated actuals satisfy the same faithful algebraic
P286 equation and carry the same coframe and auxiliary value. -/
theorem globalField_gaugeCurvature_eq_contactField_zeroSlice
    (space : StageNineSpatialPoint) :
    (GlobalField (canonicalCauchySlicePoint 0 space)).gaugeCurvature =
      (ContactField (canonicalCauchySlicePoint 0 space)).gaugeCurvature := by
  let point := canonicalCauchySlicePoint 0 space
  have globalNondegenerate :
      Matrix.det ((GlobalField point).coframe) ≠ 0 := by
    rw [show (GlobalField point).coframe = 1 by
      exact global_coframe_one_zeroSlice space]
    simp
  have globalZero :=
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_p286AuxiliaryResidual_zero
      point globalNondegenerate
  have inDomain :
      (0 : ℝ) ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space := by
    exact fixedP506L0FinalCommonTimeAxis_zero_mem_originDomain space
  have contactZero :=
    fixedP506L0CompleteJointLiveElectricECFullOccurrence_p286Auxiliary_origin_zero
      0 space inDomain
  change
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings Source) (GlobalField point) = 0
      at globalZero
  change
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings Source) (ContactField point) = 0
      at contactZero
  unfold formNativeP286GaugeAuxiliaryEulerResidualAtBoundary at globalZero contactZero
  rw [globalField_coframe_eq_contactField point,
    globalField_gaugeAuxiliary_eq_contactField point] at globalZero
  exact (sub_eq_zero.mp globalZero).trans (sub_eq_zero.mp contactZero).symm

private theorem globalField_gaugeDensity_eq_contactField_zeroSlice
    (space : StageNineSpatialPoint) :
    diracDualFormNativeCoframeGaugeDensity Source
        (GlobalField (canonicalCauchySlicePoint 0 space)) =
      diracDualFormNativeCoframeGaugeDensity Source
        (ContactField (canonicalCauchySlicePoint 0 space)) := by
  let point := canonicalCauchySlicePoint 0 space
  funext candidate
  unfold diracDualFormNativeCoframeGaugeDensity
    generatedFormNativeGaugeDensityAtBoundary
  simp only [withCoframe]
  rw [globalField_gaugeCurvature_eq_contactField_zeroSlice space,
    globalField_gaugeAuxiliary_eq_contactField point]

theorem globalField_gaugeEuler_eq_contactField_zeroSlice
    (space : StageNineSpatialPoint) :
    diracDualFormNativeCoframeGaugeEulerCovector Source
        (GlobalField (canonicalCauchySlicePoint 0 space)) =
      diracDualFormNativeCoframeGaugeEulerCovector Source
        (ContactField (canonicalCauchySlicePoint 0 space)) := by
  unfold diracDualFormNativeCoframeGaugeEulerCovector
  rw [globalField_gaugeDensity_eq_contactField_zeroSlice,
    globalField_coframe_eq_contactField]

private theorem globalField_coframe_nondegenerate_onDomain
    (time : ℝ) (space : StageNineSpatialPoint)
    (inDomain : time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    Matrix.det
        ((GlobalField (canonicalCauchySlicePoint time space)).coframe) ≠ 0 := by
  change
    Matrix.det (Global.coframe (canonicalCauchySlicePoint time space)) ≠ 0
  rw [show Global.coframe = Current.coframe by
      exact
        sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe
          Source Current,
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing]
  exact
    fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_nondegenerate
      space inDomain

private theorem contactField_coframe_nondegenerate_onDomain
    (time : ℝ) (space : StageNineSpatialPoint)
    (inDomain : time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    Matrix.det
        ((ContactField (canonicalCauchySlicePoint time space)).coframe) ≠ 0 := by
  rw [show
    (ContactField (canonicalCauchySlicePoint time space)).coframe =
      (GlobalField (canonicalCauchySlicePoint time space)).coframe by
        exact
          (globalField_coframe_eq_contactField
            (canonicalCauchySlicePoint time space)).symm]
  exact globalField_coframe_nondegenerate_onDomain time space inDomain

/-- Arbitrary-time exact coframe read on the canonical fixed-lineage domain.
The global residual is the matching contact residual plus one joint
gauge+matter load difference.  No assembly seam or sector repair is assumed. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobal_coframe_onDomain_normalForm
    (time : ℝ) (space : StageNineSpatialPoint)
    (inDomain : time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    let point := canonicalCauchySlicePoint time space
    (diracDualFormNativePointwiseJointResidual Source Global point).coframe =
      (diracDualFormNativePointwiseJointResidual Source
          (Contact point) 0).coframe +
        ((diracDualFormNativeCoframeGaugeEulerCovector Source
              (GlobalField point) +
            diracDualFormNativeCoframeMatterEulerCovector Source point
              (GlobalField point)) -
          (diracDualFormNativeCoframeGaugeEulerCovector Source
              (ContactField point) +
            diracDualFormNativeCoframeMatterEulerCovector Source 0
              (ContactField point))) := by
  dsimp only
  let point := canonicalCauchySlicePoint time space
  have reactionEq :
      formNativeCoframeConstraintReaction (GlobalField point) =
        formNativeCoframeConstraintReaction (ContactField point) := by
    funext variation
    unfold formNativeCoframeConstraintReaction
    rw [globalField_multiplier_eq_contactField,
      globalField_coframe_eq_contactField]
  change
    diracDualFormNativeCoframeEulerCovector Source point
        (GlobalField point) =
      diracDualFormNativeCoframeEulerCovector Source 0
          (ContactField point) +
        ((diracDualFormNativeCoframeGaugeEulerCovector Source
              (GlobalField point) +
            diracDualFormNativeCoframeMatterEulerCovector Source point
              (GlobalField point)) -
          (diracDualFormNativeCoframeGaugeEulerCovector Source
              (ContactField point) +
            diracDualFormNativeCoframeMatterEulerCovector Source 0
              (ContactField point)))
  apply ContinuousLinearMap.ext
  intro variation
  rw [diracDualFormNativeCoframeEulerCovector_apply_eq_gauge_add_matter_sub_reaction
      Source point (GlobalField point)
      (globalField_coframe_nondegenerate_onDomain time space inDomain)
      variation]
  simp only [add_apply, sub_apply]
  rw [diracDualFormNativeCoframeEulerCovector_apply_eq_gauge_add_matter_sub_reaction
      Source 0 (ContactField point)
      (contactField_coframe_nondegenerate_onDomain time space inDomain)
      variation]
  rw [congrFun reactionEq variation]
  ring

private theorem coframeMatterDensity_point_independent
    (point : BasePoint) (field : StageNineContinuumPointField) :
    diracDualFormNativeCoframeMatterDensity Source point field =
      diracDualFormNativeCoframeMatterDensity Source 0 field := by
  funext candidate
  unfold diracDualFormNativeCoframeMatterDensity
    generatedDiracDualFormNativeMatterDensity
    generatedDensitizedContinuumScalarDensity
    generatedDensitizedContinuumDiracDualMatterDensity
    generatedDensitizedContinuumMatterKineticDensity
    generatedDensitizedContinuumDiracDualYukawaDensity
    generatedVolumeDensity
    generatedScalarKineticDensity scalarFrameRelativeCovariantDerivative
    generatedScalarPotential
    generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum matterDerivativeFrameRelative
    generatedContinuumDiracDualYukawaVector
  simp

private theorem coframeMatterDensity_eq_of_actionFields
    (first second : StageNineContinuumPointField)
    (_coframeEq : first.coframe = second.coframe)
    (scalarEq : first.scalar = second.scalar)
    (scalarDerivativeEq :
      first.scalarCovariantDerivative = second.scalarCovariantDerivative)
    (matterEq : first.matter = second.matter)
    (matterDerivativeEq :
      first.matterCovariantDerivative = second.matterCovariantDerivative)
    (conjugateEq : first.conjugateMatter = second.conjugateMatter) :
    diracDualFormNativeCoframeMatterDensity Source 0 first =
      diracDualFormNativeCoframeMatterDensity Source 0 second := by
  funext candidate
  unfold diracDualFormNativeCoframeMatterDensity
    generatedDiracDualFormNativeMatterDensity
    generatedDensitizedContinuumScalarDensity
    generatedDensitizedContinuumDiracDualMatterDensity
    generatedDensitizedContinuumMatterKineticDensity
    generatedDensitizedContinuumDiracDualYukawaDensity
    generatedVolumeDensity
    generatedScalarKineticDensity scalarFrameRelativeCovariantDerivative
    generatedScalarPotential
    generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum matterDerivativeFrameRelative
    generatedContinuumDiracDualYukawaVector
  simp only [withCoframe, scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart, matterDualFrameRelative_zeroChart]
  rw [scalarEq, scalarDerivativeEq, matterEq,
    matterDerivativeEq, conjugateEq]

private theorem current_matter_eq_temporal :
    Current.matter = Temporal.matter := by
  calc
    Current.matter =
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.matter :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matter_eq_preEC
    _ = Existing.matter :=
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_matter_eq_existing
    _ = Temporal.matter := by
      rfl

private theorem current_scalar_eq_temporal :
    Current.scalar = Temporal.scalar := by
  calc
    Current.scalar =
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.scalar :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_eq_preEC
    _ = Existing.scalar :=
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_scalar_eq_existing
    _ = Temporal.scalar := by
      rfl

private theorem current_conjugateMatter_eq_temporal :
    Current.conjugateMatter = Temporal.conjugateMatter := by
  calc
    Current.conjugateMatter =
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.conjugateMatter :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_eq_preEC
    _ = Existing.conjugateMatter :=
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_conjugateMatter_eq_existing
    _ = Temporal.conjugateMatter := by
      rfl

private theorem current_coframe_eq_fixedInput :
    Current.coframe = FixedInput.coframe := by
  calc
    Current.coframe =
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.coframe :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC
    _ = Existing.coframe :=
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing
    _ = FixedInput.coframe :=
      fixedP506L0CompleteJointGlobalDevelopmentActual_coframe

private theorem current_gaugeConnection_eq_fixedInput :
    Current.gaugeConnection = FixedInput.gaugeConnection := by
  calc
    Current.gaugeConnection =
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.gaugeConnection :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeConnection_eq_preEC
    _ = Existing.gaugeConnection :=
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gaugeConnection_eq_existing
    _ = (completeJointGlobalP286AlgebraicCurrent Source FixedInput
          ).gaugeConnection :=
      sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_gaugeConnection_eq_p286Algebraic
        Source FixedInput
    _ = Temporal.gaugeConnection := by
      have generated := congrArg
        (fun actual : StageNineHolonomicConfiguration => actual.gaugeConnection)
        fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate
      change
        (completeJointGlobalP286AlgebraicCurrent
            positiveSmoothUnifiedSource
            FixedP506FormNativeJointActionSolvedSuccessor).gaugeConnection =
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource
            (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
              FixedP506FormNativeJointActionSolvedSuccessor) 0
            ).gaugeConnection at generated
      simpa only [diracDualFormNativeP286CanonicalJointCandidate,
        formNativeP286GaugeConstitutiveReadout_gaugeConnection,
        diracDualFormNativeP286CanonicalConnectionCandidate_zero] using generated
    _ = FixedInput.gaugeConnection := by
      rfl

private theorem current_scalar_zeroSlice_eq_fixedInput
    (space : StageNineSpatialPoint) :
    Current.scalar (canonicalCauchySlicePoint 0 space) =
      FixedInput.scalar (canonicalCauchySlicePoint 0 space) := by
  rw [congrFun current_scalar_eq_temporal
    (canonicalCauchySlicePoint 0 space)]
  exact
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
      Source FixedInput space

private theorem current_matter_zeroSlice_eq_fixedInput
    (space : StageNineSpatialPoint) :
    Current.matter (canonicalCauchySlicePoint 0 space) =
      FixedInput.matter (canonicalCauchySlicePoint 0 space) := by
  rw [congrFun current_matter_eq_temporal
    (canonicalCauchySlicePoint 0 space)]
  exact
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
      Source FixedInput space

private theorem current_conjugateMatter_zeroSlice_eq_fixedInput
    (space : StageNineSpatialPoint) :
    Current.conjugateMatter (canonicalCauchySlicePoint 0 space) =
      FixedInput.conjugateMatter (canonicalCauchySlicePoint 0 space) := by
  rw [congrFun current_conjugateMatter_eq_temporal
    (canonicalCauchySlicePoint 0 space)]
  exact
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
      Source FixedInput space

private theorem canonicalTimePrimitive_comp_spatialTranslation
    (profile : BasePoint → MatterCoordinateCarrier)
    (space : StageNineSpatialPoint) :
    canonicalTimePrimitive profile ∘ canonicalSpatialContactTranslation space =
      canonicalTimePrimitive
        (profile ∘ canonicalSpatialContactTranslation space) := by
  funext point
  unfold canonicalTimePrimitive Function.comp
  simp only
  rw [show
    canonicalTimeProjection (canonicalSpatialContactTranslation space point) =
      canonicalTimeProjection point by
        simp [canonicalSpatialContactTranslation, canonicalTimeProjection,
          canonicalCauchySlicePoint, canonicalLorentzianTimeDirection]]
  apply intervalIntegral.integral_congr
  intro time _
  apply congrArg profile
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalSpatialContactTranslation, canonicalSpatialProjection,
      canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem canonicalTimePrimitive_comp_zeroSliceTranslation
    (profile : BasePoint → MatterCoordinateCarrier)
    (space : StageNineSpatialPoint) :
    canonicalTimePrimitive profile ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space) =
      canonicalTimePrimitive
        (profile ∘ canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space)) := by
  rw [show
    canonicalSpacetimeContactTranslation (canonicalCauchySlicePoint 0 space) =
      canonicalSpatialContactTranslation space by
        funext point
        exact canonicalSpacetimeContactTranslation_timeZero space point]
  exact canonicalTimePrimitive_comp_spatialTranslation profile space

private theorem fixedInput_matterCorrection_contDiffAt_zeroSlice
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ 1
      (completeJointMatterTemporalCoordinateCorrection Source FixedInput)
      (canonicalCauchySlicePoint 0 space) := by
  exact
    (fixedP506L0CompleteJointTemporalMatterCorrection_contDiffAt_on_timeAxisDomain
      0 space (fixedP506L0FinalCommonTimeAxis_zero_mem_originDomain space)).of_le
      (by norm_num)

private theorem recenteredFixedInput_matterCorrection_contDiffAt_origin
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ 1
      (completeJointMatterTemporalCoordinateCorrection Source FixedInput ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space)) 0 := by
  have outer :
      ContDiffAt ℝ 1
        (completeJointMatterTemporalCoordinateCorrection Source FixedInput)
        (canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space) 0) := by
    simpa using fixedInput_matterCorrection_contDiffAt_zeroSlice space
  exact outer.comp 0 (by
    unfold canonicalSpacetimeContactTranslation
    fun_prop)

private theorem fixedInput_matterPrimitive_recentered_hasFDerivAt
    (space : StageNineSpatialPoint) :
    HasFDerivAt
      (canonicalTimePrimitive
          (completeJointMatterTemporalCoordinateCorrection Source FixedInput) ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space))
      (canonicalTimeProjection.smulRight
        (completeJointMatterTemporalCoordinateCorrection Source FixedInput
          (canonicalCauchySlicePoint 0 space))) 0 := by
  rw [canonicalTimePrimitive_comp_zeroSliceTranslation]
  simpa using
    canonicalTimePrimitive_hasFDerivAt_zero_of_contDiffAt
      (completeJointMatterTemporalCoordinateCorrection Source FixedInput ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space))
      (recenteredFixedInput_matterCorrection_contDiffAt_origin space)

private theorem recenteredCurrent_matterCoordinates_hasFDerivAt
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    let translation := canonicalSpacetimeContactTranslation point
    let inputCoordinates : BasePoint → MatterCoordinateCarrier :=
      fun localPoint => matterCoordinateEquiv
        (FixedInput.matter (translation localPoint))
    HasFDerivAt
      (fun localPoint => matterCoordinateEquiv
        ((fullyRecenterHolonomicConfiguration Current point).matter localPoint))
      (fderiv ℝ inputCoordinates 0 +
        canonicalTimeProjection.smulRight
          (completeJointMatterTemporalCoordinateCorrection
            Source FixedInput point)) 0 := by
  dsimp only
  let point := canonicalCauchySlicePoint 0 space
  let translation := canonicalSpacetimeContactTranslation point
  let inputCoordinates : BasePoint → MatterCoordinateCarrier :=
    fun localPoint => matterCoordinateEquiv
      (FixedInput.matter (translation localPoint))
  have translationContDiff : ContDiff ℝ ∞ translation := by
    dsimp [translation, point]
    unfold canonicalSpacetimeContactTranslation
    fun_prop
  have inputCoordinatesContDiff : ContDiff ℝ ∞ inputCoordinates := by
    dsimp [inputCoordinates]
    exact
      fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.1.comp
        translationContDiff
  have inputDerivative :
      HasFDerivAt inputCoordinates (fderiv ℝ inputCoordinates 0) 0 :=
    ((inputCoordinatesContDiff.differentiable (by simp)).differentiableAt
      ).hasFDerivAt
  have primitiveDerivative :=
    fixedInput_matterPrimitive_recentered_hasFDerivAt space
  have totalDerivative := inputDerivative.add primitiveDerivative
  have fieldEquality :
      (fun localPoint => matterCoordinateEquiv
        ((fullyRecenterHolonomicConfiguration Current point).matter localPoint)) =
      fun localPoint => inputCoordinates localPoint +
        (canonicalTimePrimitive
          (completeJointMatterTemporalCoordinateCorrection Source FixedInput) ∘
            translation) localPoint := by
    funext localPoint
    change
      matterCoordinateEquiv
          (Current.matter
            (canonicalSpacetimeContactTranslation point localPoint)) = _
    rw [congrFun current_matter_eq_temporal
      (canonicalSpacetimeContactTranslation point localPoint)]
    change
      matterCoordinateEquiv
          (FixedInput.matter
              (canonicalSpacetimeContactTranslation point localPoint) +
            matterCoordinateEquiv.symm
              (canonicalTimePrimitive
                (completeJointMatterTemporalCoordinateCorrection
                  Source FixedInput)
                (canonicalSpacetimeContactTranslation point localPoint))) = _
    rw [map_add, matterCoordinateEquiv.apply_symm_apply]
    rfl
  rw [fieldEquality]
  exact totalDerivative

private theorem recenteredCurrent_matterCoordinateDerivative_normalForm
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    let point := canonicalCauchySlicePoint 0 space
    fieldDirectionalDerivative
        (fun localPoint => matterCoordinateEquiv
          ((fullyRecenterHolonomicConfiguration Current point).matter
            localPoint)) 0 direction =
      fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (FixedInput.matter point))
          point direction +
        canonicalTimeProjection (coordinateDirection direction) •
          completeJointMatterTemporalCoordinateCorrection
            Source FixedInput point := by
  dsimp only
  let point := canonicalCauchySlicePoint 0 space
  let translation := canonicalSpacetimeContactTranslation point
  let inputCoordinates : BasePoint → MatterCoordinateCarrier :=
    fun localPoint => matterCoordinateEquiv
      (FixedInput.matter (translation localPoint))
  unfold fieldDirectionalDerivative
  rw [(recenteredCurrent_matterCoordinates_hasFDerivAt space).fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply]
  have translatedDerivative :=
    fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
      (fun point => matterCoordinateEquiv (FixedInput.matter point))
      point 0 direction
  change
    (fderiv ℝ inputCoordinates 0) (coordinateDirection direction) + _ = _
  change
    fieldDirectionalDerivative
        ((fun point => matterCoordinateEquiv (FixedInput.matter point)) ∘
          canonicalSpacetimeContactTranslation point) 0 direction + _ = _
  rw [translatedDerivative]
  simp [canonicalSpacetimeContactTranslation]
  rfl

private theorem
    recenteredCurrent_matterCoordinateTimeDerivative_eq_fixedInputProfile
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    fieldDirectionalDerivative
        (fun localPoint => matterCoordinateEquiv
          ((fullyRecenterHolonomicConfiguration Current point).matter
            localPoint)) 0 canonicalLorentzianTimeDirection =
      matterCoordinateEquiv
        ((sourceActionGeneratedDiracDualCompleteJointProfiles
          Source FixedInput point).matterVelocity) := by
  dsimp only
  rw [recenteredCurrent_matterCoordinateDerivative_normalForm]
  rw [show
    canonicalTimeProjection
        (coordinateDirection canonicalLorentzianTimeDirection) = 1 by
      simp [canonicalTimeProjection, canonicalLorentzianTimeDirection,
        coordinateDirection]]
  simp only [one_smul]
  unfold completeJointMatterTemporalCoordinateCorrection
  module

private theorem recenteredCurrent_coframe_eq_fixedInput
    (space : StageNineSpatialPoint) :
    (fullyRecenterHolonomicConfiguration Current
        (canonicalCauchySlicePoint 0 space)).coframe =
      (fullyRecenterHolonomicConfiguration FixedInput
        (canonicalCauchySlicePoint 0 space)).coframe := by
  funext localPoint
  change
    Current.coframe
        (canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space) localPoint) =
      FixedInput.coframe
        (canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space) localPoint)
  rw [current_coframe_eq_fixedInput]

private theorem recenteredCurrent_gaugeConnection_eq_fixedInput
    (space : StageNineSpatialPoint) :
    (fullyRecenterHolonomicConfiguration Current
        (canonicalCauchySlicePoint 0 space)).gaugeConnection =
      (fullyRecenterHolonomicConfiguration FixedInput
        (canonicalCauchySlicePoint 0 space)).gaugeConnection := by
  funext localPoint
  change
    Current.gaugeConnection
        (canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space) localPoint) =
      FixedInput.gaugeConnection
        (canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space) localPoint)
  rw [current_gaugeConnection_eq_fixedInput]

private theorem recenteredCurrent_matter_origin_eq_fixedInput
    (space : StageNineSpatialPoint) :
    (fullyRecenterHolonomicConfiguration Current
        (canonicalCauchySlicePoint 0 space)).matter 0 =
      (fullyRecenterHolonomicConfiguration FixedInput
        (canonicalCauchySlicePoint 0 space)).matter 0 := by
  calc
    _ = Current.matter (canonicalCauchySlicePoint 0 space) :=
      fullyRecenterHolonomicConfiguration_matter_origin _ _
    _ = FixedInput.matter (canonicalCauchySlicePoint 0 space) :=
      current_matter_zeroSlice_eq_fixedInput space
    _ = _ :=
      (fullyRecenterHolonomicConfiguration_matter_origin _ _).symm

private theorem recenteredCurrent_scalar_origin_eq_fixedInput
    (space : StageNineSpatialPoint) :
    (fullyRecenterHolonomicConfiguration Current
        (canonicalCauchySlicePoint 0 space)).scalar 0 =
      (fullyRecenterHolonomicConfiguration FixedInput
        (canonicalCauchySlicePoint 0 space)).scalar 0 := by
  calc
    _ = Current.scalar (canonicalCauchySlicePoint 0 space) :=
      fullyRecenterHolonomicConfiguration_scalar_origin _ _
    _ = FixedInput.scalar (canonicalCauchySlicePoint 0 space) :=
      current_scalar_zeroSlice_eq_fixedInput space
    _ = _ :=
      (fullyRecenterHolonomicConfiguration_scalar_origin _ _).symm

private theorem actionCartanConnectionAt_eq_of_fields_at_local
    (first second : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeEqual : first.coframe = second.coframe)
    (matterEqual : first.matter point = second.matter point)
    (conjugateEqual :
      first.conjugateMatter point = second.conjugateMatter point) :
    diracDualFormNativeActionCartanConnectionAt Source first point =
      diracDualFormNativeActionCartanConnectionAt Source second point := by
  have spinEqual :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      Source first second point (congrFun coframeEqual point)
      matterEqual conjugateEqual
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [coframeEqual, spinEqual]

private theorem recenteredRestart_gravityConnection_origin_eq_fixedInput
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source
        (fullyRecenterHolonomicConfiguration Current point)
      ).gravityConnection 0 =
      (completeJointGeneratedProfileRestartCurrent Source FixedInput point
        ).gravityConnection 0 := by
  dsimp only
  let point := canonicalCauchySlicePoint 0 space
  change
    diracDualFormNativeActionCartanConnectionAt Source
        (fullyRecenterHolonomicConfiguration Current point) 0 =
      diracDualFormNativeActionCartanConnectionAt Source
        (fullyRecenterHolonomicConfiguration FixedInput point) 0
  apply actionCartanConnectionAt_eq_of_fields_at_local
  · exact recenteredCurrent_coframe_eq_fixedInput space
  · simpa [point] using current_matter_zeroSlice_eq_fixedInput space
  · simpa [point] using
      current_conjugateMatter_zeroSlice_eq_fixedInput space

private theorem recenteredCurrent_matterCoordinateDerivative_spatial_eq_fixedInput
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    let point := canonicalCauchySlicePoint 0 space
    fieldDirectionalDerivative
        (fun localPoint => matterCoordinateEquiv
          ((fullyRecenterHolonomicConfiguration Current point).matter
            localPoint)) 0 direction.succ =
      fieldDirectionalDerivative
        (fun localPoint => matterCoordinateEquiv
          ((fullyRecenterHolonomicConfiguration FixedInput point).matter
            localPoint)) 0 direction.succ := by
  dsimp only
  rw [recenteredCurrent_matterCoordinateDerivative_normalForm]
  have translatedDerivative :=
    fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
      (fun point => matterCoordinateEquiv (FixedInput.matter point))
      (canonicalCauchySlicePoint 0 space) 0 direction.succ
  change
    _ = fieldDirectionalDerivative
      ((fun point => matterCoordinateEquiv (FixedInput.matter point)) ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space)) 0 direction.succ
  rw [translatedDerivative]
  fin_cases direction <;>
    simp [canonicalSpacetimeContactTranslation, canonicalTimeProjection,
      coordinateDirection, canonicalLorentzianTimeDirection]

private theorem
    recenteredRestart_matterCovariantDerivative_spatial_eq_fixedInput
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    let point := canonicalCauchySlicePoint 0 space
    holonomicMatterCovariantDerivative
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source
          (fullyRecenterHolonomicConfiguration Current point))
        0 direction.succ =
      holonomicMatterCovariantDerivative
        (completeJointGeneratedProfileRestartCurrent Source FixedInput point)
        0 direction.succ := by
  dsimp only
  unfold completeJointGeneratedProfileRestartCurrent
  unfold holonomicMatterCovariantDerivative
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    recenteredCurrent_matterCoordinateDerivative_spatial_eq_fixedInput,
    recenteredRestart_gravityConnection_origin_eq_fixedInput,
    recenteredCurrent_gaugeConnection_eq_fixedInput,
    recenteredCurrent_matter_origin_eq_fixedInput]
  rfl

private theorem recenteredRestart_knownVector_origin_eq_fixedInput
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    holonomicDiracDualCurrentCoframeMatterKnownVector
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source
          (fullyRecenterHolonomicConfiguration Current point)) 0 =
      holonomicDiracDualCurrentCoframeMatterKnownVector
        (completeJointGeneratedProfileRestartCurrent Source FixedInput point) 0 := by
  dsimp only
  unfold completeJointGeneratedProfileRestartCurrent
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    congrFun (recenteredCurrent_coframe_eq_fixedInput space) 0,
    recenteredCurrent_scalar_origin_eq_fixedInput,
    recenteredCurrent_matter_origin_eq_fixedInput]
  simp_rw [recenteredRestart_matterCovariantDerivative_spatial_eq_fixedInput
    space]
  rfl

private theorem recenteredRestart_rawTimeVelocity_origin_eq_fixedInput
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source
          (fullyRecenterHolonomicConfiguration Current point)) 0 =
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        (completeJointGeneratedProfileRestartCurrent Source FixedInput point) 0 := by
  dsimp only
  unfold completeJointGeneratedProfileRestartCurrent
  unfold
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
    holonomicMatterConnectionAction
  rw [congrFun
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
        Source (fullyRecenterHolonomicConfiguration Current
          (canonicalCauchySlicePoint 0 space))) 0,
    congrFun (recenteredCurrent_coframe_eq_fixedInput space) 0,
    recenteredRestart_knownVector_origin_eq_fixedInput,
    recenteredRestart_gravityConnection_origin_eq_fixedInput,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    recenteredCurrent_gaugeConnection_eq_fixedInput,
    recenteredCurrent_matter_origin_eq_fixedInput]
  rfl

private theorem contact_matterTemporalCorrection_zeroSlice
    (space : StageNineSpatialPoint) :
    completeJointMatterTemporalCoordinateCorrection Source
        (fullyRecenterHolonomicConfiguration Current
          (canonicalCauchySlicePoint 0 space)) 0 =
      0 := by
  rw [completeJointMatterTemporalCoordinateCorrection_normalForm,
    recenteredRestart_rawTimeVelocity_origin_eq_fixedInput,
    ← sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity,
    recenteredCurrent_matterCoordinateTimeDerivative_eq_fixedInputProfile]
  simp

private theorem canonicalCauchySlicePoint_zero_zero_local :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem completeJointLiveElectricGlobalP286Current_coframe_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (completeJointLiveElectricGlobalP286Current source current).coframe =
      current.coframe := by
  rw [completeJointLiveElectricGlobalP286Current]
  change
    (diracDualFormNativeP286CanonicalGeneratedActual source
      (completeJointGlobalTemporalCurrent source current)).coframe = _
  rw [diracDualFormNativeP286CanonicalGeneratedActual_coframe,
    completeJointGlobalTemporalCurrent,
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_coframe]

private theorem completeJointLiveElectricGlobalP286Current_matter_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (completeJointLiveElectricGlobalP286Current source current).matter 0 =
      current.matter 0 := by
  rw [← canonicalCauchySlicePoint_zero_zero_local]
  change
    (completeJointGlobalTemporalCurrent source current).matter
        (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) =
      current.matter
        (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint))
  exact
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
      source current 0

private theorem
    completeJointLiveElectricGlobalP286Current_conjugateMatter_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (completeJointLiveElectricGlobalP286Current source current
      ).conjugateMatter 0 = current.conjugateMatter 0 := by
  rw [← canonicalCauchySlicePoint_zero_zero_local]
  change
    (completeJointGlobalTemporalCurrent source current).conjugateMatter
        (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) =
      current.conjugateMatter
        (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint))
  exact
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
      source current 0

private theorem
    global_gravityConnection_zeroSlice_eq_recenteredCurrentRestart
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    Global.gravityConnection point =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source
        (fullyRecenterHolonomicConfiguration Current point)
        ).gravityConnection 0 := by
  dsimp only
  let point := canonicalCauchySlicePoint 0 space
  let recentered := fullyRecenterHolonomicConfiguration Current point
  rw [globalField_gravityConnection_eq_contactField point]
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
      Source recentered).gravityConnection 0 = _
  rw [sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connection_zero]
  change
    diracDualFormNativeActionCartanConnectionAt Source
        (completeJointLiveElectricGlobalP286Current Source recentered) 0 =
      diracDualFormNativeActionCartanConnectionAt Source recentered 0
  apply actionCartanConnectionAt_eq_of_fields_at_local
  · exact completeJointLiveElectricGlobalP286Current_coframe_eq Source recentered
  · exact completeJointLiveElectricGlobalP286Current_matter_origin Source recentered
  · exact
      completeJointLiveElectricGlobalP286Current_conjugateMatter_origin
        Source recentered

private theorem contact_scalar_eq_temporalRecentered
    (point : BasePoint) :
    (Contact point).scalar =
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
        Source (fullyRecenterHolonomicConfiguration Current point)).scalar := by
  rfl

private theorem contact_matter_eq_temporalRecentered
    (point : BasePoint) :
    (Contact point).matter =
      (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
        Source (fullyRecenterHolonomicConfiguration Current point)).matter := by
  rfl

private theorem recenteredCurrent_scalarDirectionalDerivative_zero
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    let point := canonicalCauchySlicePoint 0 space
    fieldDirectionalDerivative
        (fullyRecenterHolonomicConfiguration Current point).scalar
        0 direction = 0 := by
  dsimp only
  unfold fieldDirectionalDerivative
  rw [
    (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_recentered_scalar_hasFDerivAt
      space).fderiv,
    fixedP506FormNativeJointActionSolvedSuccessor_scalar,
    fixedP506JointActionSuccessor_scalar,
    fixedP506JointActual_scalar_vacuum]
  change
    (fderiv ℝ (fun _ : BasePoint =>
      sourceGeneratedVacuumCoordinates Source) 0)
        (coordinateDirection direction) = 0
  simp only [fderiv_const_apply, zero_apply]

private theorem contact_matterCoordinates_hasFDerivAt_zeroSlice
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    let input := fullyRecenterHolonomicConfiguration Current point
    HasFDerivAt
      (fun localPoint => matterCoordinateEquiv
        ((Contact point).matter localPoint))
      (fderiv ℝ
        (fun localPoint => matterCoordinateEquiv
          (input.matter localPoint)) 0) 0 := by
  dsimp only
  let point := canonicalCauchySlicePoint 0 space
  let input := fullyRecenterHolonomicConfiguration Current point
  have inputDerivative := recenteredCurrent_matterCoordinates_hasFDerivAt space
  have generated :=
    completeJointTemporalMatterCoordinates_hasFDerivAt_zero_of_contDiffAt
      Source input inputDerivative.differentiableAt
      (by simpa [input, point] using
        (fixedP506L0CompleteJointLiveElectricECSecondSweepMatterTemporalCorrection_recentered_contDiffAt
          space))
  rw [← contact_matter_eq_temporalRecentered point] at generated
  rw [show
    completeJointMatterTemporalCoordinateCorrection Source input 0 = 0 by
      simpa [input, point] using
        contact_matterTemporalCorrection_zeroSlice space] at generated
  simpa using generated

private theorem global_scalar_eq_current : Global.scalar = Current.scalar := by
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_eq_current
      Source Current

private theorem global_matter_eq_current : Global.matter = Current.matter := by
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_matter_eq_current
      Source Current

private theorem global_coframe_eq_current : Global.coframe = Current.coframe := by
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe
      Source Current

private theorem global_gaugeConnection_eq_current :
    Global.gaugeConnection = Current.gaugeConnection := by
  exact
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gaugeConnection_eq_current

private theorem global_scalarDirectionalDerivative_eq_recenteredInput
    (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative Global.scalar point direction =
      fieldDirectionalDerivative
        (fullyRecenterHolonomicConfiguration Current point).scalar
        0 direction := by
  rw [global_scalar_eq_current]
  change
    fieldDirectionalDerivative Current.scalar point direction =
      fieldDirectionalDerivative
        (Current.scalar ∘ canonicalSpacetimeContactTranslation point)
        0 direction
  symm
  simpa [canonicalSpacetimeContactTranslation] using
    fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
      Current.scalar point 0 direction

private theorem global_matterDirectionalDerivative_eq_recenteredInput
    (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => matterCoordinateEquiv (Global.matter candidate))
        point direction =
      fieldDirectionalDerivative
        (fun localPoint => matterCoordinateEquiv
          ((fullyRecenterHolonomicConfiguration Current point).matter
            localPoint)) 0 direction := by
  rw [global_matter_eq_current]
  change
    fieldDirectionalDerivative
        (fun candidate => matterCoordinateEquiv (Current.matter candidate))
        point direction =
      fieldDirectionalDerivative
        ((fun candidate => matterCoordinateEquiv (Current.matter candidate)) ∘
          canonicalSpacetimeContactTranslation point) 0 direction
  symm
  simpa [canonicalSpacetimeContactTranslation] using
    fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
      (fun candidate => matterCoordinateEquiv (Current.matter candidate))
      point 0 direction

private theorem global_coframe_zeroSlice_eq_recenteredCurrentRestart
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    Global.coframe point =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source
        (fullyRecenterHolonomicConfiguration Current point)).coframe 0 := by
  dsimp only
  rw [global_coframe_eq_current,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    fullyRecenterHolonomicConfiguration_coframe_origin]

private theorem global_scalar_zeroSlice_eq_recenteredCurrentRestart
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    Global.scalar point =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source
        (fullyRecenterHolonomicConfiguration Current point)).scalar 0 := by
  dsimp only
  rw [global_scalar_eq_current,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    fullyRecenterHolonomicConfiguration_scalar_origin]

private theorem global_matter_zeroSlice_eq_recenteredCurrentRestart
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    Global.matter point =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source
        (fullyRecenterHolonomicConfiguration Current point)).matter 0 := by
  dsimp only
  rw [global_matter_eq_current,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    fullyRecenterHolonomicConfiguration_matter_origin]

private theorem global_gaugeConnection_zeroSlice_eq_recenteredCurrentRestart
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    Global.gaugeConnection point =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source
        (fullyRecenterHolonomicConfiguration Current point)
        ).gaugeConnection 0 := by
  dsimp only
  rw [global_gaugeConnection_eq_current,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    fullyRecenterHolonomicConfiguration_gaugeConnection_origin]

private theorem
    global_matterCovariantDerivative_spatial_eq_recenteredCurrentRestart
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    let point := canonicalCauchySlicePoint 0 space
    holonomicMatterCovariantDerivative Global point direction.succ =
      holonomicMatterCovariantDerivative
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source
          (fullyRecenterHolonomicConfiguration Current point))
        0 direction.succ := by
  dsimp only
  unfold holonomicMatterCovariantDerivative
  rw [global_matterDirectionalDerivative_eq_recenteredInput,
    global_gravityConnection_zeroSlice_eq_recenteredCurrentRestart,
    global_gaugeConnection_zeroSlice_eq_recenteredCurrentRestart,
    global_matter_zeroSlice_eq_recenteredCurrentRestart,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter]

private theorem knownVector_eq_of_actionFields
    (first second : StageNineHolonomicConfiguration)
    (firstPoint secondPoint : BasePoint)
    (coframeEq : first.coframe firstPoint = second.coframe secondPoint)
    (scalarEq : first.scalar firstPoint = second.scalar secondPoint)
    (matterEq : first.matter firstPoint = second.matter secondPoint)
    (spatialCovariantEq : ∀ direction : Fin 3,
      holonomicMatterCovariantDerivative first firstPoint direction.succ =
        holonomicMatterCovariantDerivative second secondPoint
          direction.succ) :
    holonomicDiracDualCurrentCoframeMatterKnownVector first firstPoint =
      holonomicDiracDualCurrentCoframeMatterKnownVector second secondPoint := by
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
  rw [coframeEq, scalarEq, matterEq]
  congr 1
  apply congrArg
    (fun value : DiracExteriorMatterAction.DiracExteriorMatterCarrier =>
      Complex.I • value)
  apply Finset.sum_congr rfl
  intro direction _
  rw [spatialCovariantEq direction]

private theorem global_knownVector_zeroSlice_eq_fixedInputRestart
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    holonomicDiracDualCurrentCoframeMatterKnownVector Global point =
      holonomicDiracDualCurrentCoframeMatterKnownVector
        (completeJointGeneratedProfileRestartCurrent Source FixedInput point)
        0 := by
  dsimp only
  let point := canonicalCauchySlicePoint 0 space
  let currentRestart :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source
      (fullyRecenterHolonomicConfiguration Current point)
  calc
    holonomicDiracDualCurrentCoframeMatterKnownVector Global point =
        holonomicDiracDualCurrentCoframeMatterKnownVector currentRestart 0 := by
      exact knownVector_eq_of_actionFields Global currentRestart point 0
        (global_coframe_zeroSlice_eq_recenteredCurrentRestart space)
        (global_scalar_zeroSlice_eq_recenteredCurrentRestart space)
        (global_matter_zeroSlice_eq_recenteredCurrentRestart space)
        (global_matterCovariantDerivative_spatial_eq_recenteredCurrentRestart
          space)
    _ = _ := recenteredRestart_knownVector_origin_eq_fixedInput space

private theorem global_coframe_zeroSlice_eq_fixedInputRestart
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    Global.coframe point =
      (completeJointGeneratedProfileRestartCurrent Source FixedInput point
        ).coframe 0 := by
  dsimp only
  let point := canonicalCauchySlicePoint 0 space
  calc
    Global.coframe point =
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source
          (fullyRecenterHolonomicConfiguration Current point)).coframe 0 :=
      global_coframe_zeroSlice_eq_recenteredCurrentRestart space
    _ = _ := by
      unfold completeJointGeneratedProfileRestartCurrent
      rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
        sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe]
      exact congrFun (recenteredCurrent_coframe_eq_fixedInput space) 0

private theorem global_gravityConnection_zeroSlice_eq_fixedInputRestart
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    Global.gravityConnection point =
      (completeJointGeneratedProfileRestartCurrent Source FixedInput point
        ).gravityConnection 0 := by
  dsimp only
  exact
    (global_gravityConnection_zeroSlice_eq_recenteredCurrentRestart space).trans
      (recenteredRestart_gravityConnection_origin_eq_fixedInput space)

private theorem global_gaugeConnection_zeroSlice_eq_fixedInputRestart
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    Global.gaugeConnection point =
      (completeJointGeneratedProfileRestartCurrent Source FixedInput point
        ).gaugeConnection 0 := by
  dsimp only
  let point := canonicalCauchySlicePoint 0 space
  calc
    Global.gaugeConnection point =
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source
          (fullyRecenterHolonomicConfiguration Current point)
          ).gaugeConnection 0 :=
      global_gaugeConnection_zeroSlice_eq_recenteredCurrentRestart space
    _ = _ := by
      unfold completeJointGeneratedProfileRestartCurrent
      rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
        sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection]
      exact congrFun (recenteredCurrent_gaugeConnection_eq_fixedInput space) 0

private theorem global_matter_zeroSlice_eq_fixedInputRestart
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    Global.matter point =
      (completeJointGeneratedProfileRestartCurrent Source FixedInput point
        ).matter 0 := by
  dsimp only
  let point := canonicalCauchySlicePoint 0 space
  calc
    Global.matter point =
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source
          (fullyRecenterHolonomicConfiguration Current point)).matter 0 :=
      global_matter_zeroSlice_eq_recenteredCurrentRestart space
    _ = _ := by
      unfold completeJointGeneratedProfileRestartCurrent
      rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
        sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter]
      exact recenteredCurrent_matter_origin_eq_fixedInput space

private theorem global_matterConnectionAction_time_zeroSlice_eq_fixedInputRestart
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    holonomicMatterConnectionAction Global point
        canonicalLorentzianTimeDirection =
      holonomicMatterConnectionAction
        (completeJointGeneratedProfileRestartCurrent Source FixedInput point)
        0 canonicalLorentzianTimeDirection := by
  dsimp only
  unfold holonomicMatterConnectionAction
  rw [global_gravityConnection_zeroSlice_eq_fixedInputRestart,
    global_gaugeConnection_zeroSlice_eq_fixedInputRestart,
    global_matter_zeroSlice_eq_fixedInputRestart]

private theorem global_matterCoordinateTimeDerivative_zeroSlice_eq_fixedInputProfile
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    fieldDirectionalDerivative
        (fun candidate => matterCoordinateEquiv (Global.matter candidate))
        point canonicalLorentzianTimeDirection =
      matterCoordinateEquiv
        (sourceActionGeneratedDiracDualCompleteJointProfiles Source FixedInput
          point).matterVelocity := by
  dsimp only
  rw [global_matter_eq_current]
  exact
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matterTimeDerivative_zeroSlice_eq_profileVelocity
      space

private theorem global_matterCovariantDerivative_time_zeroSlice_eq_generated
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    holonomicMatterCovariantDerivative Global point
        canonicalLorentzianTimeDirection =
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
        (completeJointGeneratedProfileRestartCurrent Source FixedInput point)
        0 := by
  dsimp only
  let point := canonicalCauchySlicePoint 0 space
  let fixedRestart :=
    completeJointGeneratedProfileRestartCurrent Source FixedInput point
  unfold holonomicMatterCovariantDerivative
  rw [global_matterCoordinateTimeDerivative_zeroSlice_eq_fixedInputProfile,
    sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity,
    matterCoordinateEquiv.symm_apply_apply,
    global_gravityConnection_zeroSlice_eq_fixedInputRestart,
    global_gaugeConnection_zeroSlice_eq_fixedInputRestart,
    global_matter_zeroSlice_eq_fixedInputRestart]
  unfold actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    holonomicMatterConnectionAction
  module

/-- The fixed full-occurrence actual obeys the primal Dirac action law on
the complete zero slice.  The law is transported from the same-source
profile restart through exact primitive and first-jet equalities; it is not
used as an input to the writer. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_primalActionLaw_zeroSlice
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw Global point
      (holonomicMatterCovariantDerivative Global point
        canonicalLorentzianTimeDirection) := by
  dsimp only
  let point := canonicalCauchySlicePoint 0 space
  let fixedRestart :=
    completeJointGeneratedProfileRestartCurrent Source FixedInput point
  have noncharacteristic :
      coframeTemporalPrincipalScalar (fixedRestart.coframe 0) ≠ 0 := by
    unfold fixedRestart completeJointGeneratedProfileRestartCurrent
    rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
      fullyRecenterHolonomicConfiguration_coframe_origin,
      fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice]
    simp
  have generated :=
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
      fixedRestart 0 noncharacteristic
  unfold HolonomicDiracDualCurrentCoframeMatterTimeActionLaw at generated ⊢
  rw [global_coframe_zeroSlice_eq_fixedInputRestart,
    global_knownVector_zeroSlice_eq_fixedInputRestart,
    global_matterCovariantDerivative_time_zeroSlice_eq_generated]
  exact generated

/-- Direct zero-fiber readout of the primal Dirac law on the same `U6`
actual at every zero-slice occurrence. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_conjugateMatterResidual_zeroSlice
    (space : StageNineSpatialPoint) :
    (diracDualFormNativePointwiseJointResidual Source Global
      (canonicalCauchySlicePoint 0 space)).conjugateMatter = 0 := by
  funext direction
  change
    diracDualConjugateMatterDirectionalCoefficient Source Global direction
        (canonicalCauchySlicePoint 0 space) = 0
  unfold diracDualConjugateMatterDirectionalCoefficient
  rw [generatedContinuumDiracDualMatterVector_zero_of_repairedActionLaw
    Source Global (canonicalCauchySlicePoint 0 space)
    (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_primalActionLaw_zeroSlice
      space)]
  simp

private theorem contact_scalarDirectionalDerivative_eq_recenteredInput
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    let point := canonicalCauchySlicePoint 0 space
    fieldDirectionalDerivative (Contact point).scalar 0 direction =
      fieldDirectionalDerivative
        (fullyRecenterHolonomicConfiguration Current point).scalar
        0 direction := by
  dsimp only
  let point := canonicalCauchySlicePoint 0 space
  let input := fullyRecenterHolonomicConfiguration Current point
  by_cases generatedDifferentiable :
      DifferentiableAt ℝ (Contact point).scalar 0
  · have generated :=
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_firstJet_zeroSlice
        Source input 0
        (by simpa [input, point, canonicalCauchySlicePoint_zero_zero_local] using
          (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_recentered_scalar_differentiableAt
            space))
        (by simpa [input, point, contact_scalar_eq_temporalRecentered,
            canonicalCauchySlicePoint_zero_zero_local] using
          generatedDifferentiable)
        direction
    simpa [input, point, contact_scalar_eq_temporalRecentered,
      canonicalCauchySlicePoint_zero_zero_local] using generated
  · have generatedDerivativeZero :
        fieldDirectionalDerivative (Contact point).scalar 0 direction = 0 := by
      unfold fieldDirectionalDerivative
      rw [fderiv_zero_of_not_differentiableAt generatedDifferentiable]
      rfl
    rw [generatedDerivativeZero]
    simpa [input, point] using
      (recenteredCurrent_scalarDirectionalDerivative_zero space direction).symm

private theorem contact_matterDirectionalDerivative_eq_recenteredInput
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    let point := canonicalCauchySlicePoint 0 space
    fieldDirectionalDerivative
        (fun localPoint => matterCoordinateEquiv
          ((Contact point).matter localPoint)) 0 direction =
      fieldDirectionalDerivative
        (fun localPoint => matterCoordinateEquiv
          ((fullyRecenterHolonomicConfiguration Current point).matter
            localPoint)) 0 direction := by
  dsimp only
  unfold fieldDirectionalDerivative
  rw [(contact_matterCoordinates_hasFDerivAt_zeroSlice space).fderiv]

private theorem
    globalField_scalarCovariantDerivative_eq_contactField_zeroSlice
    (space : StageNineSpatialPoint) :
    (GlobalField (canonicalCauchySlicePoint 0 space)
      ).scalarCovariantDerivative =
      (ContactField (canonicalCauchySlicePoint 0 space)
        ).scalarCovariantDerivative := by
  let point := canonicalCauchySlicePoint 0 space
  funext direction
  change
    holonomicScalarCovariantDerivative Global point direction =
      holonomicScalarCovariantDerivative (Contact point) 0 direction
  unfold holonomicScalarCovariantDerivative
  have scalarValueEq :
      Global.scalar point = (Contact point).scalar 0 :=
    globalField_scalar_eq_contactField point
  rw [global_scalarDirectionalDerivative_eq_recenteredInput,
    contact_scalarDirectionalDerivative_eq_recenteredInput space,
    globalField_gaugeConnection_eq_contactField point,
    scalarValueEq]

private theorem
    globalField_matterCovariantDerivative_eq_contactField_zeroSlice
    (space : StageNineSpatialPoint) :
    (GlobalField (canonicalCauchySlicePoint 0 space)
      ).matterCovariantDerivative =
      (ContactField (canonicalCauchySlicePoint 0 space)
        ).matterCovariantDerivative := by
  let point := canonicalCauchySlicePoint 0 space
  funext direction
  change
    holonomicMatterCovariantDerivative Global point direction =
      holonomicMatterCovariantDerivative (Contact point) 0 direction
  unfold holonomicMatterCovariantDerivative
  have matterValueEq :
      Global.matter point = (Contact point).matter 0 :=
    globalField_matter_eq_contactField point
  rw [global_matterDirectionalDerivative_eq_recenteredInput,
    contact_matterDirectionalDerivative_eq_recenteredInput space,
    globalField_gravityConnection_eq_contactField point,
    globalField_gaugeConnection_eq_contactField point,
    matterValueEq]

private theorem
    globalField_matterDensity_eq_contactField_zeroSlice
    (space : StageNineSpatialPoint) :
    diracDualFormNativeCoframeMatterDensity Source
        (canonicalCauchySlicePoint 0 space)
        (GlobalField (canonicalCauchySlicePoint 0 space)) =
      diracDualFormNativeCoframeMatterDensity Source 0
        (ContactField (canonicalCauchySlicePoint 0 space)) := by
  let point := canonicalCauchySlicePoint 0 space
  calc
    diracDualFormNativeCoframeMatterDensity Source point
        (GlobalField point) =
        diracDualFormNativeCoframeMatterDensity Source 0
          (GlobalField point) :=
      coframeMatterDensity_point_independent point (GlobalField point)
    _ = diracDualFormNativeCoframeMatterDensity Source 0
          (ContactField point) := by
      apply coframeMatterDensity_eq_of_actionFields
      · exact globalField_coframe_eq_contactField point
      · exact globalField_scalar_eq_contactField point
      · exact
          globalField_scalarCovariantDerivative_eq_contactField_zeroSlice space
      · exact globalField_matter_eq_contactField point
      · exact
          globalField_matterCovariantDerivative_eq_contactField_zeroSlice space
      · exact globalField_conjugateMatter_eq_contactField point

theorem globalField_matterEuler_eq_contactField_zeroSlice
    (space : StageNineSpatialPoint) :
    diracDualFormNativeCoframeMatterEulerCovector Source
        (canonicalCauchySlicePoint 0 space)
        (GlobalField (canonicalCauchySlicePoint 0 space)) =
      diracDualFormNativeCoframeMatterEulerCovector Source 0
        (ContactField (canonicalCauchySlicePoint 0 space)) := by
  unfold diracDualFormNativeCoframeMatterEulerCovector
  rw [globalField_matterDensity_eq_contactField_zeroSlice space,
    globalField_coframe_eq_contactField]

/-- Joint readout theorem: the gauge and matter loads are kept together at
the public mouth of the already generated second contact write. -/
theorem globalField_nonGravityLoad_eq_contactField_zeroSlice
    (space : StageNineSpatialPoint) :
    diracDualFormNativeCoframeGaugeEulerCovector Source
          (GlobalField (canonicalCauchySlicePoint 0 space)) +
        diracDualFormNativeCoframeMatterEulerCovector Source
          (canonicalCauchySlicePoint 0 space)
          (GlobalField (canonicalCauchySlicePoint 0 space)) =
      diracDualFormNativeCoframeGaugeEulerCovector Source
          (ContactField (canonicalCauchySlicePoint 0 space)) +
        diracDualFormNativeCoframeMatterEulerCovector Source 0
          (ContactField (canonicalCauchySlicePoint 0 space)) := by
  rw [globalField_gaugeEuler_eq_contactField_zeroSlice,
    globalField_matterEuler_eq_contactField_zeroSlice space]

/-- Exact zero-slice coframe verdict for the fixed P506/L0 U6 actual. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobal_coframe_zeroSlice_zero
    (space : StageNineSpatialPoint) :
    (diracDualFormNativePointwiseJointResidual Source Global
      (canonicalCauchySlicePoint 0 space)).coframe = 0 := by
  exact
    (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobal_coframe_zeroSlice_eq_zero_iff_nonGravityLoad_eq_contact
      space).2
      (globalField_nonGravityLoad_eq_contactField_zeroSlice space)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalCoframeZeroSliceRead
