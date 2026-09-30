import H0mework.Arithmetic.MellinBoundary.ProperMellinL1StarInversion

/-!
# Stage-zero proper Mellin low/high support

The selected and reversal normalized-low elements are literal weighted `L¹`
source faces.  Conjugate inversion sends the selected low chart to the high
chart, while the reversal element remains supported in the stage-zero low
window `Ioc 0 (1/3)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex MeasureTheory Set
open QRich
open CanonicalUnitArithmeticCoordinateProjectionObstruction

noncomputable section

def selectedStageZeroMellinSource
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinConvergentSubmodule (observation.coordinate / 2) :=
  positiveMellinDilation (observation.coordinate / 2)
    (blockQRichSuccessorScale 0 : ℝ) (by
      rw [blockQRichSuccessorScale_eq_stage_add_three]
      positivity)
    ((observation.coordinate / 2 : ℂ) •
      positiveClozelLowCorrectionElement
        (observation.coordinate / 2)
        (selectedPositiveParameter_re_pos observation nontrivial))

def reversalStageZeroMellinSource
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinConvergentSubmodule
      (coordinateReversal observation.coordinate / 2) :=
  positiveMellinDilation
    (coordinateReversal observation.coordinate / 2)
    (blockQRichSuccessorScale 0 : ℝ) (by
      rw [blockQRichSuccessorScale_eq_stage_add_three]
      positivity)
    ((coordinateReversal observation.coordinate / 2 : ℂ) •
      positiveClozelLowCorrectionElement
        (coordinateReversal observation.coordinate / 2)
        (reversalPositiveParameter_re_pos observation nontrivial))

def selectedStageZeroProperMellinL1
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PositiveMellinL1 :=
  positiveMellinWeightedL1 (observation.coordinate / 2)
    (selectedStageZeroMellinSource observation nontrivial)

def reversalStageZeroProperMellinL1
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PositiveMellinL1 :=
  positiveMellinWeightedL1
    (coordinateReversal observation.coordinate / 2)
    (reversalStageZeroMellinSource observation nontrivial)

@[simp] theorem selectedStageZeroProperMellinL1_integral
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinL1Integral
        (selectedStageZeroProperMellinL1 observation nontrivial) =
      generatedZeroSelectedProperMellinReadback observation nontrivial 0 :=
  rfl

@[simp] theorem reversalStageZeroProperMellinL1_integral
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinL1Integral
        (reversalStageZeroProperMellinL1 observation nontrivial) =
      generatedZeroReversalProperMellinReadback observation nontrivial 0 :=
  rfl

theorem reversalStageZeroProperMellinL1_integral_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinL1Integral
        (reversalStageZeroProperMellinL1 observation nontrivial) ≠ 0 := by
  rw [reversalStageZeroProperMellinL1_integral,
    generatedZeroReversalProperMellinReadback_eq_character]
  apply cpow_ne_zero_iff.mpr
  left
  rw [blockQRichSuccessorScale_eq_stage_add_three]
  norm_num

def stageZeroLowWindow : Set ℝ := Ioc 0 (1 / 3 : ℝ)

theorem stageZeroLowWindow_measurable : MeasurableSet stageZeroLowWindow :=
  measurableSet_Ioc

theorem stageZeroLowWindow_subset_positive :
    stageZeroLowWindow ⊆ Ioi (0 : ℝ) :=
  Ioc_subset_Ioi_self

theorem selectedStageZeroWeightedStarInverse_zero_on_lowWindow
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (t : ℝ) (ht : t ∈ stageZeroLowWindow) :
    (t ^ (-2 : ℝ)) • star
        (positiveMellinWeightedFunction (observation.coordinate / 2)
          (selectedStageZeroMellinSource observation nontrivial)
          (t ^ (-1 : ℝ))) = 0 := by
  have tPositive : 0 < t := ht.1
  have tUpper : t ≤ (1 / 3 : ℝ) := ht.2
  have invPositive : 0 < t⁻¹ := inv_pos.mpr tPositive
  have inverseLower : (3 : ℝ) ≤ t⁻¹ := by
    have inverseComparison :=
      (inv_le_inv₀ (a := (1 / 3 : ℝ)) (b := t)
        (by norm_num) tPositive).2 tUpper
    norm_num at inverseComparison ⊢
    exact inverseComparison
  have scaledTooLarge : ¬ (3 * t⁻¹ : ℝ) ∈ Ioc 0 1 := by
    intro membership
    nlinarith [membership.2]
  rw [Real.rpow_neg_one]
  simp [positiveMellinWeightedFunction, selectedStageZeroMellinSource,
    positiveMellinExtension, positiveMellinDilation,
    positiveClozelLowCorrectionElement, restrictPositiveMellin,
    clozelLowCorrectionElement, clozelLowCorrection,
    invPositive, scaledTooLarge,
    blockQRichSuccessorScale_eq_stage_add_three]

theorem positiveMellinL1StarInversion_selected_zero_on_lowWindow
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (positiveMellinL1StarInversion
        (selectedStageZeroProperMellinL1 observation nontrivial) :
          ℝ → ℂ) =ᵐ[volume.restrict stageZeroLowWindow] 0 := by
  let selected := selectedStageZeroProperMellinL1 observation nontrivial
  let source := selectedStageZeroMellinSource observation nontrivial
  have selectedRead :
      (selected : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        positiveMellinWeightedFunction
          (observation.coordinate / 2) source := by
    exact positiveMellinWeightedL1_coeFn
      (observation.coordinate / 2) source
  have inverseRead := positiveInverse_ae_congr
    (L1.integrable_coeFn selected)
    (positiveMellinWeightedFunction_integrable
      (observation.coordinate / 2) source) selectedRead
  have inversionRead := positiveMellinL1StarInversionValue_ae selected
  have windowMeasureLe :
      volume.restrict stageZeroLowWindow ≤
        volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_mono stageZeroLowWindow_subset_positive le_rfl
  have inversionReadWindow :
      (positiveMellinL1StarInversionValue selected : ℝ → ℂ) =ᵐ[
        volume.restrict stageZeroLowWindow]
        positiveMellinL1StarInversionFunction selected :=
    (ae_mono windowMeasureLe) inversionRead
  have inverseReadWindow :
      (fun t : ℝ => (selected : ℝ → ℂ) (t ^ (-1 : ℝ))) =ᵐ[
        volume.restrict stageZeroLowWindow]
        (fun t : ℝ => positiveMellinWeightedFunction
          (observation.coordinate / 2) source (t ^ (-1 : ℝ))) :=
    (ae_mono windowMeasureLe) inverseRead
  filter_upwards [inversionReadWindow, inverseReadWindow,
      ae_restrict_mem stageZeroLowWindow_measurable]
    with t hinversion hinverse ht
  change (positiveMellinL1StarInversionValue selected : ℝ → ℂ) t = 0
  rw [hinversion]
  simp only [positiveMellinL1StarInversionFunction]
  rw [hinverse]
  exact selectedStageZeroWeightedStarInverse_zero_on_lowWindow
    observation nontrivial t ht

theorem reversalStageZeroWeighted_zero_outside_lowWindow
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (t : ℝ) (tPositive : 0 < t) (outside : t ∉ stageZeroLowWindow) :
    positiveMellinWeightedFunction
        (coordinateReversal observation.coordinate / 2)
        (reversalStageZeroMellinSource observation nontrivial) t = 0 := by
  have tLarge : (1 / 3 : ℝ) < t := by
    by_contra notLarge
    exact outside ⟨tPositive, le_of_not_gt notLarge⟩
  have scaledTooLarge : ¬ (3 * t : ℝ) ∈ Ioc 0 1 := by
    intro membership
    nlinarith [membership.2]
  simp [positiveMellinWeightedFunction, reversalStageZeroMellinSource,
    positiveMellinExtension, positiveMellinDilation,
    positiveClozelLowCorrectionElement, restrictPositiveMellin,
    clozelLowCorrectionElement, clozelLowCorrection,
    tPositive, scaledTooLarge,
    blockQRichSuccessorScale_eq_stage_add_three]

theorem reversalStageZeroProperMellinL1_lowWindow_integral
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (∫ t : ℝ in stageZeroLowWindow,
        (reversalStageZeroProperMellinL1 observation nontrivial :
          ℝ → ℂ) t) =
      positiveMellinL1Integral
        (reversalStageZeroProperMellinL1 observation nontrivial) := by
  let reversal := reversalStageZeroProperMellinL1 observation nontrivial
  let source := reversalStageZeroMellinSource observation nontrivial
  let weighted : ℝ → ℂ := positiveMellinWeightedFunction
    (coordinateReversal observation.coordinate / 2) source
  have read : (reversal : ℝ → ℂ) =ᵐ[
      volume.restrict (Ioi (0 : ℝ))] weighted := by
    exact positiveMellinWeightedL1_coeFn
      (coordinateReversal observation.coordinate / 2) source
  have windowMeasureLe :
      volume.restrict stageZeroLowWindow ≤
        volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_mono stageZeroLowWindow_subset_positive le_rfl
  have readWindow : (reversal : ℝ → ℂ) =ᵐ[
      volume.restrict stageZeroLowWindow] weighted :=
    (ae_mono windowMeasureLe) read
  calc
    (∫ t : ℝ in stageZeroLowWindow, (reversal : ℝ → ℂ) t) =
        ∫ t : ℝ in stageZeroLowWindow, weighted t :=
      integral_congr_ae readWindow
    _ = ∫ t : ℝ in Ioi 0, stageZeroLowWindow.indicator weighted t := by
      symm
      rw [integral_indicator stageZeroLowWindow_measurable,
        Measure.restrict_restrict_of_subset
          stageZeroLowWindow_subset_positive]
    _ = ∫ t : ℝ in Ioi 0, weighted t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change 0 < t at ht
      by_cases inWindow : t ∈ stageZeroLowWindow
      · simp [inWindow]
      · rw [Set.indicator_of_notMem inWindow]
        change 0 = positiveMellinWeightedFunction
          (coordinateReversal observation.coordinate / 2)
          (reversalStageZeroMellinSource observation nontrivial) t
        exact (reversalStageZeroWeighted_zero_outside_lowWindow
          observation nontrivial t ht inWindow).symm
    _ = ∫ t : ℝ in Ioi 0, (reversal : ℝ → ℂ) t :=
      integral_congr_ae read.symm
    _ = positiveMellinL1Integral reversal :=
      (positiveMellinL1Integral_eq_setIntegral reversal).symm

theorem starInversionSelectedStageZero_lowWindow_integral_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (∫ t : ℝ in stageZeroLowWindow,
        (positiveMellinL1StarInversion
          (selectedStageZeroProperMellinL1 observation nontrivial) :
            ℝ → ℂ) t) = 0 := by
  rw [integral_congr_ae
    (positiveMellinL1StarInversion_selected_zero_on_lowWindow
      observation nontrivial)]
  simp

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
