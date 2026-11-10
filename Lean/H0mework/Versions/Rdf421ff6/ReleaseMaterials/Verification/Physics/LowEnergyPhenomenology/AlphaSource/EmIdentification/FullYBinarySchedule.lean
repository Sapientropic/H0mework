import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic

set_option autoImplicit false

namespace LowEnergy.ActualQuantitativePreparedFrameOwn

theorem fullY_geometric_weighted (m : ℕ) :
    (915 / 916 : ℝ) ^ m * ((m : ℝ) + 915) ≤ 915 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have step : (915 / 916 : ℝ) * ((m : ℝ) + 1 + 915) ≤ (m : ℝ) + 915 := by
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      nlinarith
    calc
      _ = (915 / 916 : ℝ) ^ m * ((915 / 916) * ((m : ℝ) + 1 + 915)) := by
        rw [pow_succ, Nat.cast_succ]
        ring
      _ ≤ (915 / 916 : ℝ) ^ m * ((m : ℝ) + 915) :=
        mul_le_mul_of_nonneg_left step (pow_nonneg (by norm_num) m)
      _ ≤ 915 := ih

theorem fullY_block_half : (915 / 916 : ℝ) ^ 916 ≤ 1 / 2 := by
  have h := fullY_geometric_weighted 916
  norm_num only [Nat.cast_ofNat] at h
  generalize (915 / 916 : ℝ) ^ 916 = x at h ⊢
  linarith

-- Each 916-source-step block pays at least one binary precision bit.
theorem fullY_binary_schedule (bits : ℕ) :
    (915 / 916 : ℝ) ^ (916 * bits + 1) ≤ (1 / 2 : ℝ) ^ bits := by
  calc
    _ = ((915 / 916 : ℝ) ^ 916) ^ bits * (915 / 916) := by
      rw [pow_add, pow_mul, pow_one]
    _ ≤ (1 / 2 : ℝ) ^ bits * 1 := mul_le_mul
      (pow_le_pow_left₀ (pow_nonneg (by norm_num) _) fullY_block_half bits)
      (by norm_num) (by norm_num) (pow_nonneg (by norm_num) _)
    _ = _ := mul_one _

end LowEnergy.ActualQuantitativePreparedFrameOwn
