import H0mework.Versions.V2.Arithmetic.RiemannResolvent.PaResidualBoundary

/-! # Oriented source boundary of the right resolvent -/

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

local instance signedPart0PaAmbientComplete :
    CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

local instance (priority := 10000) signedPart0PaResidualRealModule :
    Module ℝ BurnolPaResidual :=
  Module.restrictScalars ℝ ℂ BurnolPaResidual

local instance (priority := 10000) signedPart0PaResidualRealNormedSpace :
    NormedSpace ℝ BurnolPaResidual :=
  NormedSpace.restrictScalars ℝ ℂ BurnolPaResidual

local instance signedPart0PaResidualComplete : CompleteSpace BurnolPaResidual := by
  apply IsComplete.completeSpace_coe
  exact burnolPaOrthogonalClosedFace.isClosed.isComplete

/-- Oriented finite boundary of an arbitrary completion value. -/
def quarterCompletionRightResolventSignedBoundary
    (z : ℂ) (value : HilbertAmbient (quarterMellinL2Feature z))
    (shift : ℝ) : HilbertAmbient (quarterMellinL2Feature z) :=
  ∫ base : ℝ in (0 : ℝ)..shift,
    quarterFeatureCompletionRightResolventIntegrand z value base

theorem quarterCompletionRightResolventSignedBoundary_eq_positiveBoundary
    (z : ℂ) (value : HilbertAmbient (quarterMellinL2Feature z))
    (shift : ℝ) (shiftNonnegative : 0 ≤ shift) :
    quarterCompletionRightResolventSignedBoundary z value shift =
      quarterCompletionRightResolventBoundary z value shift := by
  unfold quarterCompletionRightResolventSignedBoundary
    quarterCompletionRightResolventBoundary
  rw [intervalIntegral.integral_of_le shiftNonnegative]

/-- Completion translation group law. -/
theorem quarterFeatureCompletionTranslation_comp
    (z : ℂ) (first second : ℝ)
    (value : HilbertAmbient (quarterMellinL2Feature z)) :
    quarterFeatureCompletionTranslation z first
        (quarterFeatureCompletionTranslation z second value) =
      quarterFeatureCompletionTranslation z (second + first) value := by
  apply (hilbertAmbientRealization (quarterMellinL2Feature z)).injective
  rw [quarterFeatureCompletionTranslation_realization,
    quarterFeatureCompletionTranslation_realization,
    quarterFeatureCompletionTranslation_realization]
  exact LinearMap.congr_fun
    (positiveMellinQuarterEnergyTranslation_comp first second)
    (hilbertAmbientRealization (quarterMellinL2Feature z) value)

theorem quarterFeatureCompletionTranslation_zero
    (z : ℂ) (value : HilbertAmbient (quarterMellinL2Feature z)) :
    quarterFeatureCompletionTranslation z 0 value = value := by
  apply (hilbertAmbientRealization (quarterMellinL2Feature z)).injective
  rw [quarterFeatureCompletionTranslation_realization,
    positiveMellinQuarterEnergyTranslation_zero]

/-- The completion resolvent integrand transforms by the reciprocal weight
for every signed shift. -/
theorem quarterFeatureCompletionTranslation_resolventIntegrand
    (z : ℂ) (value : HilbertAmbient (quarterMellinL2Feature z))
    (base shift : ℝ) :
    quarterFeatureCompletionTranslation z shift
        (quarterFeatureCompletionRightResolventIntegrand z value base) =
      positiveMellinQuarterRightResolventCharacter z shift •
        quarterFeatureCompletionRightResolventIntegrand z value
          (base + shift) := by
  apply (hilbertAmbientRealization (quarterMellinL2Feature z)).injective
  rw [quarterFeatureCompletionTranslation_realization, map_smul,
    quarterFeatureCompletionRightResolventIntegrand_realization,
    quarterFeatureCompletionRightResolventIntegrand_realization]
  exact positiveMellinQuarterEnergyTranslation_resolventIntegrand
    z (hilbertAmbientRealization (quarterMellinL2Feature z) value)
      base shift

theorem positiveMellinQuarterRightResolventCharacter_mul_neg
    (z : ℂ) (shift : ℝ) :
    positiveMellinQuarterRightResolventCharacter z shift *
        positiveMellinQuarterRightResolventCharacter z (-shift) = 1 := by
  unfold positiveMellinQuarterRightResolventCharacter
  rw [neg_neg, ← positiveMellinQuarterRightResolventWeight_add]
  simp [positiveMellinQuarterRightResolventWeight]

/-- Translating the opposite oriented boundary reverses its orientation. -/
theorem quarterCompletionRightResolventSignedBoundary_translate_neg
    (z : ℂ) (value : HilbertAmbient (quarterMellinL2Feature z))
    (shift : ℝ) :
    quarterFeatureCompletionTranslation z shift
        (quarterCompletionRightResolventSignedBoundary z value (-shift)) =
      -positiveMellinQuarterRightResolventCharacter z shift •
        quarterCompletionRightResolventSignedBoundary z value shift := by
  unfold quarterCompletionRightResolventSignedBoundary
  rw [← LinearIsometry.intervalIntegral_comp_comm
    (quarterFeatureCompletionTranslation z shift)
    (fun base : ℝ =>
      quarterFeatureCompletionRightResolventIntegrand z value base)]
  calc
    (∫ base : ℝ in (0 : ℝ)..-shift,
        quarterFeatureCompletionTranslation z shift
          (quarterFeatureCompletionRightResolventIntegrand z value base)) =
        ∫ base : ℝ in (0 : ℝ)..-shift,
          positiveMellinQuarterRightResolventCharacter z shift •
            quarterFeatureCompletionRightResolventIntegrand z value
              (base + shift) := by
      apply intervalIntegral.integral_congr
      intro base _
      exact quarterFeatureCompletionTranslation_resolventIntegrand
        z value base shift
    _ = positiveMellinQuarterRightResolventCharacter z shift •
        ∫ base : ℝ in (0 : ℝ)..-shift,
          quarterFeatureCompletionRightResolventIntegrand z value
            (base + shift) := by
      rw [intervalIntegral.integral_smul]
    _ = positiveMellinQuarterRightResolventCharacter z shift •
        ∫ base : ℝ in shift..0,
          quarterFeatureCompletionRightResolventIntegrand z value base := by
      rw [intervalIntegral.integral_comp_add_right]
      ring_nf
    _ = -positiveMellinQuarterRightResolventCharacter z shift •
        ∫ base : ℝ in (0 : ℝ)..shift,
          quarterFeatureCompletionRightResolventIntegrand z value base := by
      rw [intervalIntegral.integral_symm]
      module

/-- The right-resolvent source-boundary identity with an oriented boundary,
valid for every real shift. -/
theorem quarterCompletionRightResolvent_signedSourceBoundary
    (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (value : HilbertAmbient (quarterMellinL2Feature z))
    (shift : ℝ) :
    quarterFeatureCompletionTranslation z shift
        (quarterFeatureCompletionRightResolvent z value) -
      positiveMellinQuarterRightResolventCharacter z shift •
        quarterFeatureCompletionRightResolvent z value =
      positiveMellinQuarterRightResolventCharacter z shift •
        quarterCompletionRightResolventSignedBoundary z value shift := by
  by_cases shiftNonnegative : 0 ≤ shift
  · rw [quarterCompletionRightResolventSignedBoundary_eq_positiveBoundary
      z value shift shiftNonnegative]
    exact quarterCompletionRightResolvent_sourceBoundary
      z rightQuarter value shift shiftNonnegative
  · have shiftNegative : shift < 0 := lt_of_not_ge shiftNonnegative
    have oppositeNonnegative : 0 ≤ -shift := by linarith
    have positive := quarterCompletionRightResolvent_sourceBoundary
      z rightQuarter value (-shift) oppositeNonnegative
    rw [← quarterCompletionRightResolventSignedBoundary_eq_positiveBoundary
      z value (-shift) oppositeNonnegative] at positive
    have acted := congrArg
      (quarterFeatureCompletionTranslation z shift) positive
    simp only [map_sub, map_smul] at acted
    rw [quarterFeatureCompletionTranslation_comp,
      show -shift + shift = 0 by ring,
      quarterFeatureCompletionTranslation_zero,
      quarterCompletionRightResolventSignedBoundary_translate_neg] at acted
    have characterInverse :=
      positiveMellinQuarterRightResolventCharacter_mul_neg z shift
    have characterInverseReverse :
        positiveMellinQuarterRightResolventCharacter z (-shift) *
          positiveMellinQuarterRightResolventCharacter z shift = 1 := by
      rw [mul_comm]
      exact characterInverse
    have coefficient :
        positiveMellinQuarterRightResolventCharacter z (-shift) *
          -positiveMellinQuarterRightResolventCharacter z shift = -1 := by
      rw [mul_neg, characterInverseReverse]
    rw [smul_smul, coefficient, neg_one_smul] at acted
    have scaled :
        positiveMellinQuarterRightResolventCharacter z shift •
              quarterFeatureCompletionRightResolvent z value -
            (positiveMellinQuarterRightResolventCharacter z shift *
                positiveMellinQuarterRightResolventCharacter z (-shift)) •
              quarterFeatureCompletionTranslation z shift
                (quarterFeatureCompletionRightResolvent z value) =
          -(positiveMellinQuarterRightResolventCharacter z shift •
            quarterCompletionRightResolventSignedBoundary z value shift) := by
      calc
        _ = positiveMellinQuarterRightResolventCharacter z shift •
            (quarterFeatureCompletionRightResolvent z value -
              positiveMellinQuarterRightResolventCharacter z (-shift) •
                quarterFeatureCompletionTranslation z shift
                  (quarterFeatureCompletionRightResolvent z value)) := by
            module
        _ = positiveMellinQuarterRightResolventCharacter z shift •
            (-quarterCompletionRightResolventSignedBoundary z value shift) := by
              rw [acted]
        _ = _ := by module
    rw [characterInverse, one_smul] at scaled
    calc
      quarterFeatureCompletionTranslation z shift
            (quarterFeatureCompletionRightResolvent z value) -
          positiveMellinQuarterRightResolventCharacter z shift •
            quarterFeatureCompletionRightResolvent z value =
        -(positiveMellinQuarterRightResolventCharacter z shift •
              quarterFeatureCompletionRightResolvent z value -
            quarterFeatureCompletionTranslation z shift
              (quarterFeatureCompletionRightResolvent z value)) := by
          module
      _ = -(-(positiveMellinQuarterRightResolventCharacter z shift •
            quarterCompletionRightResolventSignedBoundary z value shift)) := by
          rw [scaled]
      _ = positiveMellinQuarterRightResolventCharacter z shift •
          quarterCompletionRightResolventSignedBoundary z value shift := by
          exact neg_neg _


end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
