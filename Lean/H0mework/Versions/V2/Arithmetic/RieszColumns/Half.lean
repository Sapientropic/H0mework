import H0mework.Versions.V2.Arithmetic.RieszColumns.Columns
import H0mework.Versions.V2.Arithmetic.RieszColumns.FirstSample

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteColumns

open Complex MeasureTheory Set
open OriginalPaPhysicalGreen OriginalRieszFiniteSource
noncomputable section

private theorem cutoff_enlarge_self (small large : ℝ) (value : BurnolL2) (order : small ≤ large)
    (supported : originalPhysicalCutoff small value = value) :
    originalPhysicalCutoff large value = value := by
  apply cutoff_eq_self_of_ae_zero
  filter_upwards [originalPhysicalCutoff_coeFn small value] with x read
  intro outside
  have smallOutside : x ∉ symmetricInterval small := by
    intro inside
    exact outside ⟨(neg_le_neg order).trans inside.1, inside.2.trans order⟩
  rw [supported, Set.indicator_of_notMem smallOutside] at read
  exact read

private theorem radius_le_half (shift : ℝ) (bounded : |shift| ≤ Real.log 2) :
    (1 / 4 : ℝ) * Real.exp |shift| ≤ 1 / 2 := by
  have expBound := Real.exp_le_exp.mpr bounded
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at expBound
  linarith

theorem positionColumn_half (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (bounded : |shift| ≤ Real.log 2) :
    originalPhysicalCutoff (1 / 2 : ℝ) (positionColumn coordinate shift) =
      positionColumn coordinate shift :=
  cutoff_enlarge_self _ _ _ (radius_le_half shift bounded) (positionColumn_cutoff_self coordinate shift)

theorem fourierColumn_half (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (bounded : |shift| ≤ Real.log 2) :
    originalPhysicalCutoff (1 / 2 : ℝ) (fourierColumn coordinate shift) =
      fourierColumn coordinate shift :=
  cutoff_enlarge_self _ _ _ (radius_le_half shift bounded) (fourierColumn_cutoff_self coordinate shift)

theorem fixedShift_small : |Real.log stageZeroSonineQ| ≤ Real.log 2 := by
  have square : stageZeroSonineQ ^ 2 = (3 : ℝ) := by
    unfold stageZeroSonineQ
    exact Real.sq_sqrt (by norm_num)
  have positive := stageZeroSonineQ_pos
  have lower : (1 : ℝ) ≤ stageZeroSonineQ := by nlinarith
  have upper : stageZeroSonineQ ≤ (2 : ℝ) := by nlinarith
  rw [abs_of_nonneg (Real.log_nonneg lower)]
  exact Real.log_le_log positive upper

end
end OriginalRieszFiniteColumns
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
