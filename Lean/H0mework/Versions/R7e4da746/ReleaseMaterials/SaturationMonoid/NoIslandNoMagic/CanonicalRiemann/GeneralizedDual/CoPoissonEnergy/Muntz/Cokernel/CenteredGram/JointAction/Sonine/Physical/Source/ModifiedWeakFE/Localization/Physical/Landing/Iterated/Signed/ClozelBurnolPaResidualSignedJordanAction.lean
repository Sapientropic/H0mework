import H0mework.Versions.R7e4da746.Arithmetic.RiemannResolvent.QuarterCompletionSignedBoundary
import H0mework.Versions.R7e4da746.Arithmetic.RiemannResolvent.SignedSourceOrbit
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Landing.Iterated.ClozelBurnolPaResidualJordanAction

/-! # Signed residual Jordan action -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory Set
open SourceGeneratedComplexFeaturePerfectification
open SourceGeneratedHilbertCokernel
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState
open scoped ENNReal

noncomputable section

local instance signedPart2PaAmbientComplete :
    CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

local instance (priority := 10000) signedPart2PaResidualRealModule :
    Module ℝ BurnolPaResidual :=
  Module.restrictScalars ℝ ℂ BurnolPaResidual

local instance (priority := 10000) signedPart2PaResidualRealNormedSpace :
    NormedSpace ℝ BurnolPaResidual :=
  NormedSpace.restrictScalars ℝ ℂ BurnolPaResidual

local instance signedPart2PaResidualComplete : CompleteSpace BurnolPaResidual := by
  apply IsComplete.completeSpace_coe
  exact burnolPaOrthogonalClosedFace.isClosed.isComplete

private theorem burnolPaResidualRead_intervalIntegral_comp_comm
    (z : ℂ) (path : ℝ → HilbertAmbient (quarterMellinL2Feature z))
    (shift : ℝ) (integrable : IntervalIntegrable path volume 0 shift) :
    (∫ base : ℝ in (0 : ℝ)..shift, burnolPaResidualRead z (path base)) =
      burnolPaResidualRead z (∫ base : ℝ in (0 : ℝ)..shift, path base) := by
  simp only [intervalIntegral]
  rw [burnolPaResidualRead_integral_comp_comm z integrable.1,
    burnolPaResidualRead_integral_comp_comm z integrable.2, map_sub]

/-- One signed resolvent step exposes the preceding oriented boundary in the
orthogonal residual. -/
theorem burnolPaResidualRead_signed_resolvent_recurrence
    (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (value : HilbertAmbient (quarterMellinL2Feature z))
    (shift : ℝ) :
    burnolPaResidualRead z
        (quarterFeatureCompletionTranslation z shift
          (quarterFeatureCompletionRightResolvent z value)) -
      positiveMellinQuarterRightResolventCharacter z shift •
        burnolPaResidualRead z
          (quarterFeatureCompletionRightResolvent z value) =
      positiveMellinQuarterRightResolventCharacter z shift •
        burnolPaResidualRead z
          (quarterCompletionRightResolventSignedBoundary z value shift) := by
  have boundary := quarterCompletionRightResolvent_signedSourceBoundary
    z rightQuarter value shift
  simpa only [map_sub, map_smul] using
    congrArg (burnolPaResidualRead z) boundary

/-- Signed Jordan action of the same resolvent tower and the same recursive
Jordan coordinate already used on the positive segment. -/
theorem burnolPaResidualRead_resolventIterate_signed_jordanAction
    (source : burnolCompactAnnulusSource)
    (segment : BurnolCompactAnnulusSignedDilationSegment source)
    (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (order : Nat) :
    ∀ (shift : ℝ),
      -Real.log (16 / 9 : ℝ) ≤ shift → shift ≤ Real.log 16 →
      burnolPaResidualRead z
          (quarterFeatureCompletionTranslation z shift
            (quarterFeatureCompletionRightResolventIterate z order
              (burnolSourceQuarterCompletionValue
                source z positive belowHalf))) =
        positiveMellinQuarterRightResolventCharacter z shift •
          burnolPaResidualJordanCoordinate z
            (burnolSourceQuarterCompletionValue source z positive belowHalf)
            order shift := by
  induction order with
  | zero =>
      intro shift shiftLower shiftUpper
      simpa [quarterFeatureCompletionRightResolventIterate,
        burnolPaResidualJordanCoordinate] using
        burnolPaResidualRead_source_translation_eq_zero_signed
          source segment z positive belowHalf shift shiftLower shiftUpper
  | succ order ih =>
      intro shift shiftLower shiftUpper
      let sourceValue := burnolSourceQuarterCompletionValue
        source z positive belowHalf
      let previous := quarterFeatureCompletionRightResolventIterate
        z order sourceValue
      let boundary := quarterCompletionRightResolventSignedBoundary z previous shift
      have recurrence := burnolPaResidualRead_signed_resolvent_recurrence
        z rightQuarter previous shift
      have boundaryPathContinuous : Continuous
          (quarterFeatureCompletionRightResolventIntegrand z previous) :=
        quarterFeatureCompletionRightResolventIntegrand_continuous z previous
      have boundaryPathIntegrable : IntervalIntegrable
          (quarterFeatureCompletionRightResolventIntegrand z previous)
          volume 0 shift :=
        boundaryPathContinuous.intervalIntegrable 0 shift
      have boundaryRead :
          burnolPaResidualRead z boundary =
            ∫ base : ℝ in (0 : ℝ)..shift,
              burnolPaResidualJordanCoordinate z sourceValue order base := by
        calc
          burnolPaResidualRead z boundary =
              ∫ base : ℝ in (0 : ℝ)..shift,
                burnolPaResidualRead z
                  (quarterFeatureCompletionRightResolventIntegrand
                    z previous base) := by
            unfold boundary quarterCompletionRightResolventSignedBoundary
            exact (burnolPaResidualRead_intervalIntegral_comp_comm
              z _ shift boundaryPathIntegrable).symm
          _ = ∫ base : ℝ in (0 : ℝ)..shift,
                burnolPaResidualJordanCoordinate
                  z sourceValue order base := by
            apply intervalIntegral.integral_congr
            intro base baseMem
            have baseBounds :
                -Real.log (16 / 9 : ℝ) ≤ base ∧
                  base ≤ Real.log 16 := by
              rcases Set.mem_uIcc.mp baseMem with baseForward | baseBackward
              · exact ⟨burnolSignedDilation_lower_le_zero.trans baseForward.1,
                  baseForward.2.trans shiftUpper⟩
              · exact ⟨shiftLower.trans baseBackward.1,
                  baseBackward.2.trans burnolSignedDilation_zero_le_upper⟩
            calc
              burnolPaResidualRead z
                  (quarterFeatureCompletionRightResolventIntegrand
                    z previous base) =
                  positiveMellinQuarterRightResolventWeight z base •
                    burnolPaResidualRead z
                      (quarterFeatureCompletionTranslation z base previous) := by
                simp [quarterFeatureCompletionRightResolventIntegrand]
              _ = positiveMellinQuarterRightResolventWeight z base •
                    (positiveMellinQuarterRightResolventCharacter z base •
                      burnolPaResidualJordanCoordinate
                        z sourceValue order base) := by
                rw [ih base baseBounds.1 baseBounds.2]
              _ = burnolPaResidualJordanCoordinate
                    z sourceValue order base := by
                rw [smul_smul,
                  positiveMellinQuarterRightResolventWeight_mul_character,
                  one_smul]
      have recurrence' :
          burnolPaResidualRead z
              (quarterFeatureCompletionTranslation z shift
                (quarterFeatureCompletionRightResolvent z previous)) -
            positiveMellinQuarterRightResolventCharacter z shift •
              burnolPaResidualRead z
                (quarterFeatureCompletionRightResolvent z previous) =
            positiveMellinQuarterRightResolventCharacter z shift •
              burnolPaResidualRead z boundary := by
        simpa only [boundary] using recurrence
      calc
        burnolPaResidualRead z
            (quarterFeatureCompletionTranslation z shift
              (quarterFeatureCompletionRightResolventIterate z
                (order + 1) sourceValue)) =
            positiveMellinQuarterRightResolventCharacter z shift •
                burnolPaResidualRead z
                  (quarterFeatureCompletionRightResolventIterate z
                    (order + 1) sourceValue) +
              positiveMellinQuarterRightResolventCharacter z shift •
                burnolPaResidualRead z boundary := by
          change burnolPaResidualRead z
              (quarterFeatureCompletionTranslation z shift
                (quarterFeatureCompletionRightResolvent z previous)) =
            positiveMellinQuarterRightResolventCharacter z shift •
                burnolPaResidualRead z
                  (quarterFeatureCompletionRightResolvent z previous) +
              positiveMellinQuarterRightResolventCharacter z shift •
                burnolPaResidualRead z boundary
          let action := burnolPaResidualRead z
            (quarterFeatureCompletionTranslation z shift
              (quarterFeatureCompletionRightResolvent z previous))
          let diagonal := positiveMellinQuarterRightResolventCharacter z shift •
            burnolPaResidualRead z
              (quarterFeatureCompletionRightResolvent z previous)
          let lower := positiveMellinQuarterRightResolventCharacter z shift •
            burnolPaResidualRead z boundary
          change action = diagonal + lower
          calc
            action = (action - diagonal) + diagonal :=
              (sub_add_cancel action diagonal).symm
            _ = lower + diagonal := by rw [recurrence']
            _ = diagonal + lower := add_comm _ _
        _ = positiveMellinQuarterRightResolventCharacter z shift •
            (burnolPaResidualRead z
                (quarterFeatureCompletionRightResolventIterate z
                  (order + 1) sourceValue) +
              ∫ base : ℝ in (0 : ℝ)..shift,
                burnolPaResidualJordanCoordinate
                  z sourceValue order base) := by
          rw [boundaryRead, smul_add]
        _ = positiveMellinQuarterRightResolventCharacter z shift •
            burnolPaResidualJordanCoordinate z sourceValue
              (order + 1) shift := by
          rfl


end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
