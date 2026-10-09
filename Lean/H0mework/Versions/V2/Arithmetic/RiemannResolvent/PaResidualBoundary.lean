import H0mework.Versions.V2.Arithmetic.RiemannResolvent.StableAnnulusResolventLanding

/-! # Stable-source boundaries in the Burnol residual -/

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

local instance burnolIteratedPaAmbientComplete :
    CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

abbrev BurnolPaResidual :=
  OrthogonalResidual burnolCompactCoPoissonLanding

local instance (priority := 10000) burnolPaResidualRealModule :
    Module ℝ BurnolPaResidual :=
  Module.restrictScalars ℝ ℂ BurnolPaResidual

local instance (priority := 10000) burnolPaResidualRealNormedSpace :
    NormedSpace ℝ BurnolPaResidual :=
  NormedSpace.restrictScalars ℝ ℂ BurnolPaResidual

local instance burnolPaResidualComplete : CompleteSpace BurnolPaResidual := by
  apply IsComplete.completeSpace_coe
  exact burnolPaOrthogonalClosedFace.isClosed.isComplete

/-- Read a quarter-feature completion value in the fixed `P_a⊥` carrier. -/
def burnolPaResidualRead (z : ℂ) :
    HilbertAmbient (quarterMellinL2Feature z) →L[ℂ] BurnolPaResidual :=
  (residual burnolCompactCoPoissonLanding).comp
    (burnolSourceFeatureCompletionPhysicalMap z)

theorem burnolPaResidualRead_integral_comp_comm
    (z : ℂ) {μ : Measure ℝ}
    {path : ℝ → HilbertAmbient (quarterMellinL2Feature z)}
    (pathIntegrable : Integrable path μ) :
    (∫ base : ℝ, burnolPaResidualRead z (path base) ∂μ) =
      burnolPaResidualRead z (∫ base : ℝ, path base ∂μ) := by
  exact @ContinuousLinearMap.integral_comp_comm
    ℝ (HilbertAmbient (quarterMellinL2Feature z)) BurnolPaResidual
    inferInstance μ ℂ inferInstance inferInstance inferInstance
    inferInstance inferInstance burnolPaResidualRealNormedSpace
    burnolPaResidualComplete inferInstance inferInstance
    (burnolPaResidualRead z) path pathIntegrable

/-- Finite right-resolvent boundary for an arbitrary completion value. -/
def quarterCompletionRightResolventBoundary
    (z : ℂ) (value : HilbertAmbient (quarterMellinL2Feature z))
    (shift : ℝ) : HilbertAmbient (quarterMellinL2Feature z) :=
  ∫ base : ℝ in Ioc (0 : ℝ) shift,
    quarterFeatureCompletionRightResolventIntegrand z value base

theorem quarterCompletionRightResolventBoundary_realization
    (z : ℂ) (value : HilbertAmbient (quarterMellinL2Feature z))
    (shift : ℝ) :
    hilbertAmbientRealization (quarterMellinL2Feature z)
        (quarterCompletionRightResolventBoundary z value shift) =
      positiveMellinQuarterRightResolventBoundarySource z
        (hilbertAmbientRealization (quarterMellinL2Feature z) value) shift := by
  unfold quarterCompletionRightResolventBoundary
    positiveMellinQuarterRightResolventBoundarySource
  rw [← LinearIsometry.integral_comp_comm
    (hilbertAmbientRealization (quarterMellinL2Feature z))]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro base _
  exact quarterFeatureCompletionRightResolventIntegrand_realization z value base

/-- The source-boundary equation holds before physical projection. -/
theorem quarterCompletionRightResolvent_sourceBoundary
    (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (value : HilbertAmbient (quarterMellinL2Feature z))
    (shift : ℝ) (shiftNonnegative : 0 ≤ shift) :
    quarterFeatureCompletionTranslation z shift
        (quarterFeatureCompletionRightResolvent z value) -
      positiveMellinQuarterRightResolventCharacter z shift •
        quarterFeatureCompletionRightResolvent z value =
      positiveMellinQuarterRightResolventCharacter z shift •
        quarterCompletionRightResolventBoundary z value shift := by
  apply (hilbertAmbientRealization (quarterMellinL2Feature z)).injective
  rw [map_sub, map_smul, map_smul,
    quarterFeatureCompletionTranslation_realization,
    quarterFeatureCompletionRightResolvent_realization,
    quarterCompletionRightResolventBoundary_realization]
  exact positiveMellinQuarterRightResolvent_sourceBoundary
    z rightQuarter _ shift shiftNonnegative

/-- A stable annulus kills every translated point of its source orbit in
`P_a⊥`; this is the base case of the iterated action law. -/
theorem burnolPaResidualRead_source_translation_eq_zero
    (source : burnolCompactAnnulusSource)
    (segment : BurnolCompactAnnulusDilationSegment source)
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (shift : ℝ) (shiftNonnegative : 0 ≤ shift)
    (shiftBounded : shift ≤ Real.log 16) :
    burnolPaResidualRead z
        (quarterFeatureCompletionTranslation z shift
          (burnolSourceQuarterCompletionValue source z positive belowHalf)) = 0 := by
  let sourceValue := burnolSourceQuarterCompletionValue source z positive belowHalf
  let translated := quarterFeatureCompletionTranslation z shift sourceValue
  let integrand := quarterFeatureCompletionRightResolventIntegrand z sourceValue shift
  have orbit := burnolSourceFeatureCompletionPhysicalMap_orbit
    source segment z positive belowHalf shift shiftNonnegative shiftBounded
  have orbitMem :
      burnolSourceFeatureCompletionPhysicalMap z integrand ∈
        burnolCompactCoPoissonClosedRange := by
    rw [show burnolSourceFeatureCompletionPhysicalMap z integrand =
        (2 * positiveMellinQuarterRightResolventWeight z shift) •
          burnolCompactAdditivePhysicalState
            (segment.sourceAt shift shiftNonnegative shiftBounded) by
      simpa only [sourceValue, integrand] using orbit]
    apply burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem
    simpa [burnolCompactCoPoissonGenerator] using
      burnolCompactCoPoissonGenerator_mem_closedRange
        (segment.sourceAt shift shiftNonnegative shiftBounded, (0 : Fin 2))
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

/-- One resolvent step exposes its preceding finite boundary in `P_a⊥`. -/
theorem burnolPaResidualRead_resolvent_recurrence
    (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (value : HilbertAmbient (quarterMellinL2Feature z))
    (shift : ℝ) (shiftNonnegative : 0 ≤ shift) :
    burnolPaResidualRead z
        (quarterFeatureCompletionTranslation z shift
          (quarterFeatureCompletionRightResolvent z value)) -
      positiveMellinQuarterRightResolventCharacter z shift •
        burnolPaResidualRead z
          (quarterFeatureCompletionRightResolvent z value) =
      positiveMellinQuarterRightResolventCharacter z shift •
        burnolPaResidualRead z
          (quarterCompletionRightResolventBoundary z value shift) := by
  have boundary := quarterCompletionRightResolvent_sourceBoundary
    z rightQuarter value shift shiftNonnegative
  simpa only [map_sub, map_smul] using
    congrArg (burnolPaResidualRead z) boundary

theorem positiveMellinQuarterRightResolventWeight_mul_character
    (z : ℂ) (shift : ℝ) :
    positiveMellinQuarterRightResolventWeight z shift *
        positiveMellinQuarterRightResolventCharacter z shift = 1 := by
  unfold positiveMellinQuarterRightResolventCharacter
  rw [← positiveMellinQuarterRightResolventWeight_add]
  simp [positiveMellinQuarterRightResolventWeight]

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
