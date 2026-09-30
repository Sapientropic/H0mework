import H0mework.Versions.X.Fock.SourceHistoryClock.ComplexSource
import H0mework.Probability.Information.Lattice

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceClockComplex

open SourceSuccessorBoundary SourceUniformFibreVariance Filter
open scoped Topology
noncomputable section

private theorem clock_sum (count : Nat) :
    (∑ index ∈ Finset.range count, (SourceClockModel.rawClock index : ℂ)) =
      (count : ℂ) * ((count : ℂ) + 1) / 2 := by
  have sumIndex := congrArg (fun value : ℝ => (value : ℂ)) (Lattice.index_sum count)
  push_cast at sumIndex
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [SourceClockModel.rawClock, Int.cast_add, Int.cast_natCast, Int.cast_one,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [sumIndex]
  ring

theorem clock_mean (bound : Nat) : clock (meanWord bound) = (bound + 2 : ℂ) / 2 := by
  simp only [meanWord, map_smul, map_sum, clock_single, one_mul, smul_eq_mul]
  rw [clock_sum]
  have countNonzero : ((bound + 1 : Nat) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero bound)
  field_simp
  push_cast
  ring

def densityScale (bound : Nat) : ℝ := 2 / (bound + 2 : ℝ)

theorem density_scale_pos (bound : Nat) : 0 < densityScale bound := by
  unfold densityScale
  positivity

theorem density_clock (bound : Nat) :
    clock (densityScale bound • meanWord bound) = 1 := by
  rw [LinearMap.map_smul_of_tower, clock_mean]
  simp only [densityScale, Complex.real_smul]
  push_cast
  have nonzero : (bound + 2 : ℂ) ≠ 0 := by exact_mod_cast (show (bound + 2 : Nat) ≠ 0 by omega)
  field_simp

theorem density_scale_tendsto : Tendsto densityScale atTop (𝓝 (0 : ℝ)) := by
  have shifted := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have scaled := shifted.const_mul 2
  change Tendsto (fun bound : Nat => 2 / (bound + 2 : ℝ)) atTop (𝓝 (0 : ℝ))
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two,
    mul_zero, mul_one_div, densityScale] using scaled

theorem scaled_joint_tendsto :
    Tendsto (fun bound => SourceMassCompletion.jointRead (densityScale bound • meanWord bound)) atTop
      (𝓝 (0 : SourceMassCompletion.Joint)) := by
  have actual := density_scale_tendsto.smul SourceMassCompletion.source_mean_tendsto
  simpa only [LinearMap.map_smul_of_tower, zero_smul] using actual

end
end SourceClockComplex
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
