import H0mework.Probability.SourceShift.Word
import Mathlib.Analysis.SpecificLimits.Basic

/-! Consecutive finite source words have unit mass while their Hilbert means tend to zero. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceSuccessorBoundary

open SourceOwnedObservationHistory.SourceShift Filter
open scoped Topology

noncomputable section

def meanWord (bound : Nat) : Nat →₀ ℂ :=
  ((bound + 1 : Nat) : ℂ)⁻¹ •
    ∑ source ∈ Finset.range (bound + 1), Finsupp.single source (1 : ℂ)

def mean (bound : Nat) : H := readWord (meanWord bound)

theorem mass_meanWord (bound : Nat) : mass ℂ (meanWord bound) = 1 := by
  have countNeZero : ((bound + 1 : Nat) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero bound)
  simp only [meanWord, map_smul, map_sum, mass_single, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  exact inv_mul_cancel₀ countNeZero

theorem mean_formula (bound : Nat) :
    mean bound = ((bound + 1 : Nat) : ℂ)⁻¹ •
      ∑ source ∈ Finset.range (bound + 1), basis source := by
  simp only [mean, meanWord, map_smul, map_sum, readWord_single, one_smul]

theorem prefix_norm_sq (count : Nat) :
    ‖∑ source ∈ Finset.range count, basis source‖ ^ 2 = (count : ℝ) := by
  simpa [basis, Real.rpow_two] using
    (lp.norm_sum_single (E := fun _ : Nat => ℂ) (p := 2) (by norm_num)
      (fun _ => (1 : ℂ)) (Finset.range count))

theorem mean_norm_sq (bound : Nat) : ‖mean bound‖ ^ 2 = 1 / (bound + 1 : ℝ) := by
  rw [mean_formula, norm_smul, mul_pow, norm_inv, Complex.norm_natCast, prefix_norm_sq]
  simp only [Nat.cast_add, Nat.cast_one]
  have countNeZero : (bound : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem mean_tendsto_zero : Tendsto mean atTop (𝓝 (0 : H)) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have squares : Tendsto (fun bound => ‖mean bound‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mean_norm_sq] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have roots := Real.continuous_sqrt.continuousAt.tendsto.comp squares
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using roots

end
end SourceSuccessorBoundary
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
