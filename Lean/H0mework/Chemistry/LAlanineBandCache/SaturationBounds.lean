import H0mework.Chemistry.LAlanineExponential.RangeReduction

/-! Uniform bounds for the original range-reduced Taylor evaluator. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandSaturation

open SourceExponential

theorem roundUp_mono {a b : ℚ} (h : a ≤ b) : roundUp a ≤ roundUp b := by
  unfold roundUp
  apply div_le_div_of_nonneg_right _ scale_positive.le
  exact_mod_cast Int.ceil_mono (mul_le_mul_of_nonneg_left h scale_positive.le)

theorem remainder_le_half {x : ℚ} (small : |x| ≤ 1/2) :
    remainder x ≤ remainder (1/2) := by
  unfold remainder
  rw [abs_of_pos (by norm_num : (0:ℚ) < 1/2)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg x) small 16)
    (by norm_num : (0:ℚ) ≤ 17 / ((16:ℕ).factorial * 16 : ℚ))

/-- Monotonicity of the actual exponential supplies a uniform upper Taylor bound. -/
theorem initialUpper_le {x u : ℚ} (small : |x| ≤ 1/2)
    (upper : x ≤ u) (smallUpper : |u| ≤ 1/2) :
    initialUpper x ≤ roundUp (taylor u + remainder u + 2 * remainder (1/2)) := by
  have hx := (abs_le.mp (taylor_remainder_bound x small)).1
  have hu := (abs_le.mp (taylor_remainder_bound u smallUpper)).2
  have mono : Real.exp (x : ℝ) ≤ Real.exp (u : ℝ) :=
    Real.exp_le_exp.mpr (by exact_mod_cast upper)
  have rem : (remainder x : ℝ) ≤ (remainder (1/2) : ℝ) :=
    by exact_mod_cast remainder_le_half small
  apply roundUp_mono
  have bound : (taylor x : ℝ) + (remainder x : ℝ) ≤
      (taylor u : ℝ) + (remainder u : ℝ) + 2 * (remainder (1/2) : ℝ) := by linarith
  exact_mod_cast bound

theorem initialUpper_le_eight {x : ℚ} (small : |x| ≤ 1/2) (upper : x ≤ -7/16) :
    initialUpper x ≤ 331/512 := by
  exact (initialUpper_le small upper (by norm_num)).trans (by decide +kernel)

theorem initialUpper_le_nine {x : ℚ} (small : |x| ≤ 1/2) (upper : x ≤ -7/32) :
    initialUpper x ≤ 103/128 := by
  exact (initialUpper_le small upper (by norm_num)).trans (by decide +kernel)

end LAlanine40K2025.BasinRefinement.WholeBandSaturation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
