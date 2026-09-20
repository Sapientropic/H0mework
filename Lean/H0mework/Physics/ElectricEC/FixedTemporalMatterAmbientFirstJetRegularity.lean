import H0mework.Physics.TimePrimitive.FirstAmbientJetRegularity
import H0mework.Physics.ActualGerms.FixedJointTemporalMatterTimeAxisRegularity
import H0mework.Physics.ElectricJoint.FixedOriginCoframeClosure

/-!
# Fixed P506/L0 live-electric EC temporal matter ambient first jet

The first complete-joint temporal action leg is locally `C¹` after recentering
at every fixed-lineage zero-slice occurrence.  Its source-free canonical
primitive is therefore locally `C¹` as well, and the matter field carried by
the later live-electric Einstein--Cartan current has a legitimate ambient
first jet at the same occurrence.

This module transports regularity of the already generated action write.  It
does not accept a residual, target jet, zero-fiber receipt, branch, or free
coefficient.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECTemporalMatterAmbientFirstJetRegularity

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCanonicalTimePrimitiveAmbientFirstJetRegularity
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointTemporalMatterTimeAxisRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Input : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Temporal : StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source Input

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private theorem canonicalSpacetimeContactTranslation_contDiff
    (point : BasePoint) :
    ContDiff ℝ ∞ (canonicalSpacetimeContactTranslation point) := by
  unfold canonicalSpacetimeContactTranslation
  fun_prop

/-- The fixed first-sweep matter action profile is locally `C¹` after
recentring at every generated zero-slice occurrence. -/
theorem
    fixedP506L0CompleteJointMatterTemporalCorrection_recentered_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ 1
      (completeJointMatterTemporalCoordinateCorrection Source Input ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space)) 0 := by
  let point := canonicalCauchySlicePoint 0 space
  have profileAtPoint :
      ContDiffAt ℝ 1
        (completeJointMatterTemporalCoordinateCorrection Source Input)
        point :=
    (fixedP506L0CompleteJointTemporalMatterCorrection_contDiffAt_on_timeAxisDomain
      0 space
      (fixedP506L0FinalCommonTimeAxis_zero_mem_originDomain space)).of_le
      (by norm_num)
  have translationRegular :
      ContDiffAt ℝ 1 (canonicalSpacetimeContactTranslation point) 0 :=
    (canonicalSpacetimeContactTranslation_contDiff point).contDiffAt.of_le
      (by norm_num)
  have profileAtTranslated :
      ContDiffAt ℝ 1
        (completeJointMatterTemporalCoordinateCorrection Source Input)
        (canonicalSpacetimeContactTranslation point 0) := by
    simpa [canonicalSpacetimeContactTranslation] using profileAtPoint
  have composed := profileAtTranslated.comp 0 translationRegular
  simpa [point] using composed

/-- The source-free matter primitive installed by the first sweep is locally
`C¹` in the full ambient recentered carrier. -/
theorem
    fixedP506L0CompleteJointMatterTemporalPrimitive_recentered_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ 1
      (canonicalTimePrimitive
          (completeJointMatterTemporalCoordinateCorrection Source Input) ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space)) 0 := by
  rw [
    canonicalTimePrimitive_comp_canonicalSpacetimeContactTranslation_zeroSlice]
  exact
    canonicalTimePrimitive_contDiffAt_of_contDiffAt
      (completeJointMatterTemporalCoordinateCorrection Source Input ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space))
      (fixedP506L0CompleteJointMatterTemporalCorrection_recentered_contDiffAt
        space)

private theorem current_matter_eq_temporal :
    Current.matter = Temporal.matter := by
  calc
    Current.matter =
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.matter :=
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matter
        Source fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual
    _ = fixedP506L0CompleteJointGlobalDevelopmentActual.matter :=
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_matter_eq_existing
    _ = Temporal.matter := by
      rfl

/-- The matter coordinates of the U5 current consumed by the full-occurrence
second sweep are locally `C¹` at every recentered zero-slice occurrence. -/
theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_recentered_matterCoordinates_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ 1
      (fun localPoint =>
        matterCoordinateEquiv
          ((fullyRecenterHolonomicConfiguration Current
            (canonicalCauchySlicePoint 0 space)).matter localPoint)) 0 := by
  let point := canonicalCauchySlicePoint 0 space
  let translation := canonicalSpacetimeContactTranslation point
  let inputCoordinates : BasePoint → MatterCoordinateCarrier :=
    fun localPoint =>
      matterCoordinateEquiv (Input.matter (translation localPoint))
  have translationSmooth : ContDiff ℝ ∞ translation :=
    canonicalSpacetimeContactTranslation_contDiff point
  have inputSmooth : ContDiff ℝ ∞ inputCoordinates := by
    dsimp [inputCoordinates]
    exact
      fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.1.comp
        translationSmooth
  have primitiveRegular :=
    fixedP506L0CompleteJointMatterTemporalPrimitive_recentered_contDiffAt
      space
  have fieldEquality :
      (fun localPoint =>
        matterCoordinateEquiv
          ((fullyRecenterHolonomicConfiguration Current point).matter
            localPoint)) =
        fun localPoint =>
          inputCoordinates localPoint +
            (canonicalTimePrimitive
                (completeJointMatterTemporalCoordinateCorrection Source Input) ∘
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
          (Input.matter
              (canonicalSpacetimeContactTranslation point localPoint) +
            matterCoordinateEquiv.symm
              (canonicalTimePrimitive
                (completeJointMatterTemporalCoordinateCorrection Source Input)
                (canonicalSpacetimeContactTranslation point localPoint))) = _
    rw [map_add, matterCoordinateEquiv.apply_symm_apply]
    rfl
  rw [fieldEquality]
  exact
    inputSmooth.contDiffAt.of_le (by norm_num) |>.add primitiveRegular

/-- The same fixed-lineage calculation identifies the complete ambient
first derivative, not only its regularity.  The generated summand is exactly
the source-owned matter correction at the matching occurrence. -/
theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_recentered_matterCoordinates_hasFDerivAt
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    let translation := canonicalSpacetimeContactTranslation point
    let inputCoordinates : BasePoint → MatterCoordinateCarrier :=
      fun localPoint => matterCoordinateEquiv (Input.matter (translation localPoint))
    HasFDerivAt
      (fun localPoint =>
        matterCoordinateEquiv
          ((fullyRecenterHolonomicConfiguration Current point).matter
            localPoint))
      (fderiv ℝ inputCoordinates 0 +
        canonicalTimeProjection.smulRight
          (completeJointMatterTemporalCoordinateCorrection Source Input point))
      0 := by
  dsimp only
  let point := canonicalCauchySlicePoint 0 space
  let translation := canonicalSpacetimeContactTranslation point
  let inputCoordinates : BasePoint → MatterCoordinateCarrier :=
    fun localPoint => matterCoordinateEquiv (Input.matter (translation localPoint))
  have translationSmooth : ContDiff ℝ ∞ translation :=
    canonicalSpacetimeContactTranslation_contDiff point
  have inputSmooth : ContDiff ℝ ∞ inputCoordinates := by
    dsimp [inputCoordinates]
    exact
      fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.1.comp
        translationSmooth
  have inputDerivative :
      HasFDerivAt inputCoordinates (fderiv ℝ inputCoordinates 0) 0 :=
    inputSmooth.differentiable (by simp) |>.differentiableAt.hasFDerivAt
  have correctionRegular :=
    fixedP506L0CompleteJointMatterTemporalCorrection_recentered_contDiffAt
      space
  have primitiveDerivative :
      HasFDerivAt
        (canonicalTimePrimitive
            (completeJointMatterTemporalCoordinateCorrection Source Input) ∘
          translation)
        (canonicalTimeProjection.smulRight
          (completeJointMatterTemporalCoordinateCorrection Source Input point))
        0 := by
    rw [show
      canonicalTimePrimitive
            (completeJointMatterTemporalCoordinateCorrection Source Input) ∘
          translation =
        canonicalTimePrimitive
          (completeJointMatterTemporalCoordinateCorrection Source Input ∘
            translation) by
      simpa [translation, point] using
        canonicalTimePrimitive_comp_canonicalSpacetimeContactTranslation_zeroSlice
          (completeJointMatterTemporalCoordinateCorrection Source Input) space]
    have generated :=
      canonicalTimePrimitive_hasFDerivAt_zero_of_contDiffAt
        (completeJointMatterTemporalCoordinateCorrection Source Input ∘
          translation) correctionRegular
    simpa [translation, point, canonicalSpacetimeContactTranslation] using
      generated
  have totalDerivative := inputDerivative.add primitiveDerivative
  have fieldEquality :
      (fun localPoint =>
        matterCoordinateEquiv
          ((fullyRecenterHolonomicConfiguration Current point).matter
            localPoint)) =
        inputCoordinates +
          (canonicalTimePrimitive
              (completeJointMatterTemporalCoordinateCorrection Source Input) ∘
            translation) := by
    funext localPoint
    change
      matterCoordinateEquiv
          (Current.matter
            (canonicalSpacetimeContactTranslation point localPoint)) = _
    rw [congrFun current_matter_eq_temporal
      (canonicalSpacetimeContactTranslation point localPoint)]
    change
      matterCoordinateEquiv
          (Input.matter
              (canonicalSpacetimeContactTranslation point localPoint) +
            matterCoordinateEquiv.symm
              (canonicalTimePrimitive
                (completeJointMatterTemporalCoordinateCorrection Source Input)
                (canonicalSpacetimeContactTranslation point localPoint))) = _
    rw [map_add, matterCoordinateEquiv.apply_symm_apply]
    rfl
  rw [fieldEquality]
  exact totalDerivative

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECTemporalMatterAmbientFirstJetRegularity
