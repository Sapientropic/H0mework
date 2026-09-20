import H0mework.Physics.SynchronizedJoint.FixedActionSelectedJointSuccessorMatterAdjointClosure

/-!
# Zero-slice hard-gate reduction for the action-selected successor

The one source/current-only successor already closes four structural channels
at every point and the matter, adjoint, and complete P286 action channels on
the canonical zero slice.  This module packages those machine facts into the
exact remaining zero-fiber criterion: gravity assembly, scalar, and coframe
are the only unresolved coordinates of that same residual.

This is a whole-carrier readout.  No residual coordinate, support branch, or
zero-fiber receipt is consumed by an action writer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorZeroSliceReduction

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalNaturality
open StageNineDiracDualFormNativeECFullCauchyConnectionJetReadout
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorMatterAdjointClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorP286Readback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorStructuralReduction
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Successor : StageNineHolonomicConfiguration :=
  fixedP506L0LorentzPathActionSelectedJointSuccessor

private abbrev Coupled : StageNineHolonomicConfiguration :=
  completeJointActionSelectedCoupledTemporalActual Source
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev Point (space : StageNineSpatialPoint) : BasePoint :=
  canonicalCauchySlicePoint 0 space

private abbrev Residual
    (space : StageNineSpatialPoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  diracDualFormNativePointwiseJointResidual Source Successor (Point space)

/-- On the complete fixed zero slice, the full nine-channel zero-fiber gate is
equivalent to simultaneous closure of exactly three remaining readers on the
same successor.  The complete P286 three-form is discharged by its
source/current-only action-selected producer.  The gravity condition uses the
faithful raw assembly seam, not its normalized presentation. -/
theorem successor_zeroSlice_residual_eq_zero_iff_remainingReaders_zero
    (space : StageNineSpatialPoint) :
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        fixedP506L0LorentzPathActionSelectedJointSuccessor
        (canonicalCauchySlicePoint 0 space) = 0 ↔
      (completeJointLiveElectricECFullOccurrenceAssemblySeam
          positiveSmoothUnifiedSource
          (completeJointActionSelectedCoupledTemporalActual
            positiveSmoothUnifiedSource
            fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual)
          (canonicalCauchySlicePoint 0 space)).gravityCurvature = 0 ∧
      (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
          fixedP506L0LorentzPathActionSelectedJointSuccessor
          (canonicalCauchySlicePoint 0 space)).scalar = 0 ∧
      (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
          fixedP506L0LorentzPathActionSelectedJointSuccessor
          (canonicalCauchySlicePoint 0 space)).coframe = 0 := by
  change Residual space = 0 ↔
    (completeJointLiveElectricECFullOccurrenceAssemblySeam Source Coupled
      (Point space)).gravityCurvature = 0 ∧
    (Residual space).scalar = 0 ∧
    (Residual space).coframe = 0
  constructor
  · intro residualZero
    have gravityAuxiliaryZero : (Residual space).gravityAuxiliary = 0 := by
      exact congrArg
        DiracDualFormNativePointwiseJointResidualCarrier.gravityAuxiliary
        residualZero
    have scalarZero : (Residual space).scalar = 0 := by
      exact congrArg
        DiracDualFormNativePointwiseJointResidualCarrier.scalar residualZero
    have coframeZero : (Residual space).coframe = 0 := by
      exact congrArg
        DiracDualFormNativePointwiseJointResidualCarrier.coframe residualZero
    exact ⟨
      (successor_gravityAuxiliary_eq_zero_iff_gravityCurvatureSeam_zero
        (Point space)).1 gravityAuxiliaryZero,
      scalarZero, coframeZero⟩
  · rintro ⟨gravitySeamZero, scalarZero, coframeZero⟩
    apply DiracDualFormNativePointwiseJointResidualCarrier.ext
    · exact successor_gravityMultiplier_zero (Point space)
    · exact
        (successor_gravityAuxiliary_eq_zero_iff_gravityCurvatureSeam_zero
          (Point space)).2 gravitySeamZero
    · exact successor_p286GaugeAuxiliary_zero (Point space)
    · exact successor_lorentzConnection_zero (Point space)
    · change
        holonomicFormNativeP286GaugeEulerThreeForm Source 0 Successor
          (Point space) = 0
      exact successor_p286EulerThreeForm_zeroSlice space
    · exact scalarZero
    · exact successor_matterResidual_zeroSlice space
    · exact successor_conjugateMatterResidual_zeroSlice space
    · exact coframeZero

/-- Action-jurisdiction form of the same hard gate.  Gravity is equality of
the Cartan whole-field curvature and the matching EC Full-Cauchy target;
scalar and coframe remain exact readers of the same successor. -/
theorem successor_zeroSlice_residual_eq_zero_iff_remainingActionRelations
    (space : StageNineSpatialPoint) :
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        fixedP506L0LorentzPathActionSelectedJointSuccessor
        (canonicalCauchySlicePoint 0 space) = 0 ↔
      holonomicGravityCurvature
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            positiveSmoothUnifiedSource
            (completeJointActionSelectedCoupledTemporalActual
              positiveSmoothUnifiedSource
              fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual))
          (canonicalCauchySlicePoint 0 space) =
        sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget
          positiveSmoothUnifiedSource
          (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
            positiveSmoothUnifiedSource
            (fullyRecenterHolonomicConfiguration
              (completeJointActionSelectedCoupledTemporalActual
                positiveSmoothUnifiedSource
                fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual)
              (canonicalCauchySlicePoint 0 space))) ∧
      (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
          fixedP506L0LorentzPathActionSelectedJointSuccessor
          (canonicalCauchySlicePoint 0 space)).scalar = 0 ∧
      (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
          fixedP506L0LorentzPathActionSelectedJointSuccessor
          (canonicalCauchySlicePoint 0 space)).coframe = 0 := by
  rw [successor_zeroSlice_residual_eq_zero_iff_remainingReaders_zero,
    successor_gravityCurvatureSeam_eq_cartan_sub_target, sub_eq_zero]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorZeroSliceReduction
