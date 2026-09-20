import H0mework.Physics.TimePrimitive.SecondAmbientJetRegularity
import H0mework.Physics.ElectricEC.FixedOriginTransport
import H0mework.Physics.ScalarJets.FixedFullOccurrenceScalarAccelerationRegularity

/-!
# Fixed P506/L0 live-electric EC temporal scalar ambient first jet

The first complete-joint scalar action profile is locally smooth at every
fixed-lineage zero-slice occurrence.  Its canonical second primitive therefore
has zero ambient first derivative after recentering, so the U5 scalar carried
into the full-occurrence second sweep is genuinely differentiable there.

This module verifies regularity of the already generated action write.  It
accepts no residual, target jet, zero-fiber receipt, branch, or free
coefficient.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECTemporalScalarAmbientFirstJetRegularity

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCanonicalTimeSecondPrimitiveAmbientFirstJetRegularity
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricFieldTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506FullOccurrenceScalarAccelerationRegularity
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286ActionCauchySplit

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

private theorem current_scalar_eq_temporal :
    Current.scalar = Temporal.scalar := by
  calc
    Current.scalar =
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.scalar :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_eq_preEC
    _ = fixedP506L0CompleteJointGlobalDevelopmentActual.scalar :=
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_scalar_eq_existing
    _ = Temporal.scalar := by
      rfl

/-- The first-sweep scalar acceleration remains locally `C¹` after the exact
zero-slice recentering selected by the occurrence. -/
theorem fixedP506L0CompleteJointScalarAccelerationProfile_recentered_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ 1
      (completeJointScalarAccelerationProfile Source Input ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space)) 0 := by
  let point := canonicalCauchySlicePoint 0 space
  have profileAtPoint :
      ContDiffAt ℝ 1
        (completeJointScalarAccelerationProfile Source Input) point :=
    (fixedP506L0CompleteJointScalarAccelerationProfile_contDiffAt_zeroSlice
      space).of_le (by norm_num)
  have profileAtTranslated :
      ContDiffAt ℝ 1
        (completeJointScalarAccelerationProfile Source Input)
        (canonicalSpacetimeContactTranslation point 0) := by
    simpa [point, canonicalSpacetimeContactTranslation] using profileAtPoint
  exact profileAtTranslated.comp 0
    ((canonicalSpacetimeContactTranslation_contDiff point).contDiffAt.of_le
      (by norm_num))

/-- The first-sweep canonical second primitive contributes zero to the full
ambient first jet at every recentered zero-slice occurrence. -/
theorem fixedP506L0CompleteJointScalarSecondPrimitive_recentered_hasFDerivAt
    (space : StageNineSpatialPoint) :
    HasFDerivAt
      (canonicalTimeSecondPrimitive
          (completeJointScalarAccelerationProfile Source Input) ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space))
      (0 : BasePoint →L[ℝ] ScalarCoordinateCarrier) 0 := by
  rw [
    canonicalTimeSecondPrimitive_comp_canonicalSpacetimeContactTranslation_zeroSlice]
  exact
    canonicalTimeSecondPrimitive_hasFDerivAt_zero_of_contDiffAt
      (completeJointScalarAccelerationProfile Source Input ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space))
      (fixedP506L0CompleteJointScalarAccelerationProfile_recentered_contDiffAt
        space)

/-- The same explicit second primitive is locally `C¹`, not merely
differentiable at the recentered origin.  This is the regularity consumed by
the next action leg. -/
theorem fixedP506L0CompleteJointScalarSecondPrimitive_recentered_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ 1
      (canonicalTimeSecondPrimitive
          (completeJointScalarAccelerationProfile Source Input) ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space)) 0 := by
  rw [
    canonicalTimeSecondPrimitive_comp_canonicalSpacetimeContactTranslation_zeroSlice]
  exact
    canonicalTimeSecondPrimitive_contDiffAt_of_contDiffAt
      (completeJointScalarAccelerationProfile Source Input ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space))
      (fixedP506L0CompleteJointScalarAccelerationProfile_recentered_contDiffAt
        space)

/-- The literal U5 scalar consumed by the second full-occurrence sweep is
locally `C¹` in the recentered ambient carrier. -/
theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_recentered_scalar_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ 1
      (fullyRecenterHolonomicConfiguration Current
        (canonicalCauchySlicePoint 0 space)).scalar 0 := by
  let point := canonicalCauchySlicePoint 0 space
  let translation := canonicalSpacetimeContactTranslation point
  have inputSmooth : ContDiff ℝ ∞ (Input.scalar ∘ translation) :=
    fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1.comp
      (canonicalSpacetimeContactTranslation_contDiff point)
  have fieldEquality :
      (fullyRecenterHolonomicConfiguration Current point).scalar =
        (Input.scalar ∘ translation) +
          (canonicalTimeSecondPrimitive
              (completeJointScalarAccelerationProfile Source Input) ∘
            translation) := by
    funext localPoint
    unfold fullyRecenterHolonomicConfiguration
    rw [current_scalar_eq_temporal]
    rfl
  rw [fieldEquality]
  exact (inputSmooth.contDiffAt.of_le (by norm_num)).add
    (fixedP506L0CompleteJointScalarSecondPrimitive_recentered_contDiffAt space)

/-- Exact ambient first-jet normal form of the U5 scalar consumed by the
second full-occurrence sweep. -/
theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_recentered_scalar_hasFDerivAt
    (space : StageNineSpatialPoint) :
    let point := canonicalCauchySlicePoint 0 space
    let translation := canonicalSpacetimeContactTranslation point
    HasFDerivAt
      ((fullyRecenterHolonomicConfiguration Current point).scalar)
      (fderiv ℝ (Input.scalar ∘ translation) 0) 0 := by
  dsimp only
  let point := canonicalCauchySlicePoint 0 space
  let translation := canonicalSpacetimeContactTranslation point
  have inputSmooth : ContDiff ℝ ∞ (Input.scalar ∘ translation) :=
    fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1.comp
      (canonicalSpacetimeContactTranslation_contDiff point)
  have inputDerivative :
      HasFDerivAt (Input.scalar ∘ translation)
        (fderiv ℝ (Input.scalar ∘ translation) 0) 0 :=
    inputSmooth.differentiable (by simp) |>.differentiableAt.hasFDerivAt
  have generated := inputDerivative.add
    (fixedP506L0CompleteJointScalarSecondPrimitive_recentered_hasFDerivAt
      space)
  have fieldEquality :
      (fullyRecenterHolonomicConfiguration Current point).scalar =
        (Input.scalar ∘ translation) +
          (canonicalTimeSecondPrimitive
              (completeJointScalarAccelerationProfile Source Input) ∘
            translation) := by
    funext localPoint
    unfold fullyRecenterHolonomicConfiguration
    rw [current_scalar_eq_temporal]
    rfl
  rw [fieldEquality]
  simpa using generated

/-- Ordinary differentiability form consumed by later fixed-lineage action
readers. -/
theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_recentered_scalar_differentiableAt
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ
      (fullyRecenterHolonomicConfiguration Current
        (canonicalCauchySlicePoint 0 space)).scalar 0 :=
  (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_recentered_scalar_hasFDerivAt
    space).differentiableAt

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECTemporalScalarAmbientFirstJetRegularity
