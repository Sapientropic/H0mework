import H0mework.Versions.Y.Arithmetic.RiemannAnnulus.AnalyticComplementSignedAnnulusSource
import H0mework.Versions.Y.Arithmetic.RiemannResolvent.PaResidualBoundary

/-! # Signed source orbit in the physical closed range -/

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

local instance signedPart1PaAmbientComplete :
    CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

local instance (priority := 10000) signedPart1PaResidualRealModule :
    Module ℝ BurnolPaResidual :=
  Module.restrictScalars ℝ ℂ BurnolPaResidual

local instance (priority := 10000) signedPart1PaResidualRealNormedSpace :
    NormedSpace ℝ BurnolPaResidual :=
  NormedSpace.restrictScalars ℝ ℂ BurnolPaResidual

local instance signedPart1PaResidualComplete : CompleteSpace BurnolPaResidual := by
  apply IsComplete.completeSpace_coe
  exact burnolPaOrthogonalClosedFace.isClosed.isComplete

/-- The physical image of every signed source-orbit integrand is an actual
compact co-Poisson generator. -/
theorem burnolSignedSourceFeatureCompletionPhysicalMap_orbit
    (source : burnolCompactAnnulusSource)
    (segment : BurnolCompactAnnulusSignedDilationSegment source)
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (base : ℝ)
    (baseLower : -Real.log (16 / 9 : ℝ) ≤ base)
    (baseUpper : base ≤ Real.log 16) :
    burnolSourceFeatureCompletionPhysicalMap z
        (quarterFeatureCompletionRightResolventIntegrand z
          (burnolSourceQuarterCompletionValue source z positive belowHalf)
          base) =
      (2 * positiveMellinQuarterRightResolventWeight z base) •
        burnolCompactAdditivePhysicalState
          (segment.sourceAt base baseLower baseUpper) := by
  unfold quarterFeatureCompletionRightResolventIntegrand
    burnolSourceQuarterCompletionValue
    burnolSourceFeatureCompletionPhysicalMap
  rw [map_smul, quarterFeatureCompletionTranslation_source,
    ContinuousLinearMap.comp_apply,
    quarterMellinFeatureCompletionEvenAdditive_source, map_smul]
  have relationSquare := LinearMap.congr_fun
    (quarterDilation_muntzRelation_square z positive belowHalf
      (Real.exp base) (Real.exp_pos base)) source.1
  change quarterDilationTestAction z (Real.exp base) (Real.exp_pos base)
      (burnolSourceQuarterRelation source z positive belowHalf) =
    coPoissonQuarterMellinConvergentMap z positive belowHalf
      (quarterMuntzSchwartzDilationAction
        (Real.exp base) (Real.exp_pos base) source.1) at relationSquare
  rw [relationSquare]
  rw [← segment.sourceAt_coe base baseLower baseUpper]
  change positiveMellinQuarterRightResolventWeight z base •
      ((2 : ℂ) • quarterMellinAdditiveProjectedPhysicalState
        (coPoissonQuarterMellinConvergentMap z positive belowHalf
          (segment.sourceAt base baseLower baseUpper).1)) = _
  rw [compactQuarterMellinAdditiveProjectedPhysicalState_eq]
  simp only [smul_smul]
  congr 1
  ring

/-- Every translated point of a signed source orbit is zero in `P_a⊥`. -/
theorem burnolPaResidualRead_source_translation_eq_zero_signed
    (source : burnolCompactAnnulusSource)
    (segment : BurnolCompactAnnulusSignedDilationSegment source)
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (shift : ℝ)
    (shiftLower : -Real.log (16 / 9 : ℝ) ≤ shift)
    (shiftUpper : shift ≤ Real.log 16) :
    burnolPaResidualRead z
        (quarterFeatureCompletionTranslation z shift
          (burnolSourceQuarterCompletionValue source z positive belowHalf)) = 0 := by
  let sourceValue := burnolSourceQuarterCompletionValue source z positive belowHalf
  let translated := quarterFeatureCompletionTranslation z shift sourceValue
  let integrand := quarterFeatureCompletionRightResolventIntegrand
    z sourceValue shift
  have orbit := burnolSignedSourceFeatureCompletionPhysicalMap_orbit
    source segment z positive belowHalf shift shiftLower shiftUpper
  have orbitMem :
      burnolSourceFeatureCompletionPhysicalMap z integrand ∈
        burnolCompactCoPoissonClosedRange := by
    rw [show burnolSourceFeatureCompletionPhysicalMap z integrand =
        (2 * positiveMellinQuarterRightResolventWeight z shift) •
          burnolCompactAdditivePhysicalState
            (segment.sourceAt shift shiftLower shiftUpper) by
      simpa only [sourceValue, integrand] using orbit]
    apply burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem
    simpa [burnolCompactCoPoissonGenerator] using
      burnolCompactCoPoissonGenerator_mem_closedRange
        (segment.sourceAt shift shiftLower shiftUpper, (0 : Fin 2))
  have killed : residual burnolCompactCoPoissonLanding
      (burnolSourceFeatureCompletionPhysicalMap z integrand) = 0 :=
    (residual_eq_zero_iff burnolCompactCoPoissonLanding _).2 orbitMem
  have weightNe : positiveMellinQuarterRightResolventWeight z shift ≠ 0 := by
    unfold positiveMellinQuarterRightResolventWeight
    exact Complex.exp_ne_zero _
  have expanded : residual burnolCompactCoPoissonLanding
      (burnolSourceFeatureCompletionPhysicalMap z integrand) =
      positiveMellinQuarterRightResolventWeight z shift •
        burnolPaResidualRead z translated := by
    simp only [integrand, translated,
      quarterFeatureCompletionRightResolventIntegrand,
      burnolPaResidualRead, ContinuousLinearMap.comp_apply, map_smul]
  rw [expanded] at killed
  exact (smul_eq_zero.mp killed).resolve_left weightNe

theorem burnolSignedDilation_lower_le_zero :
    -Real.log (16 / 9 : ℝ) ≤ 0 := by
  exact (neg_nonpos.mpr (Real.log_nonneg (by norm_num)))

theorem burnolSignedDilation_zero_le_upper :
    0 ≤ Real.log 16 := by
  exact Real.log_nonneg (by norm_num)


end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
