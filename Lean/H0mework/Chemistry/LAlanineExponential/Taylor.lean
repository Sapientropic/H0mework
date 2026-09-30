import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceExponential

open scoped BigOperators

def scale : ℚ := 2 ^ 160

def taylor (x : ℚ) : ℚ := ∑ i ∈ Finset.range 16, x ^ i / (i.factorial : ℚ)

def remainder (x : ℚ) : ℚ := |x| ^ 16 * (17 / ((16 : ℕ).factorial * 16 : ℚ))

def roundDown (x : ℚ) : ℚ := (⌊scale * x⌋ : ℚ) / scale
def roundUp (x : ℚ) : ℚ := (⌈scale * x⌉ : ℚ) / scale

def initialLower (x : ℚ) : ℚ := roundDown (max 0 (taylor x - remainder x))
def initialUpper (x : ℚ) : ℚ := roundUp (taylor x + remainder x)

theorem scale_positive : 0 < scale := by unfold scale; positivity

theorem roundDown_le (x : ℚ) : roundDown x ≤ x := by
  apply (div_le_iff₀ scale_positive).mpr
  simpa only [mul_comm] using Int.floor_le (scale * x)

theorem le_roundUp (x : ℚ) : x ≤ roundUp x := by
  apply (le_div_iff₀ scale_positive).mpr
  simpa only [mul_comm] using Int.le_ceil (scale * x)

theorem roundDown_nonnegative (x : ℚ) (hx : 0 ≤ x) : 0 ≤ roundDown x := by
  apply div_nonneg _ scale_positive.le
  exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg scale_positive.le hx)

theorem taylor_remainder_bound (x : ℚ) (small : |x| ≤ 1 / 2) :
    |Real.exp (x : ℝ) - (taylor x : ℝ)| ≤ (remainder x : ℝ) := by
  have smallReal : |(x : ℝ)| ≤ 1 := by
    have h : |x| ≤ 1 := small.trans (by norm_num)
    exact_mod_cast h
  have h := Real.exp_bound smallReal (n := 16) (by norm_num)
  norm_num only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at h
  norm_num only [taylor, remainder, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_abs, Rat.cast_mul, Rat.cast_ofNat]
  exact h

theorem initial_contains (x : ℚ) (small : |x| ≤ 1 / 2) :
    0 ≤ initialLower x ∧
      (initialLower x : ℝ) ≤ Real.exp (x : ℝ) ∧ Real.exp (x : ℝ) ≤ (initialUpper x : ℝ) := by
  have h := (abs_le.mp (taylor_remainder_bound x small))
  have hlo : ((max 0 (taylor x - remainder x) : ℚ) : ℝ) ≤ Real.exp (x : ℝ) := by
    rw [Rat.cast_max, Rat.cast_zero, Rat.cast_sub]
    exact max_le (Real.exp_pos _).le (by linarith [h.1])
  have hup : Real.exp (x : ℝ) ≤ ((taylor x + remainder x : ℚ) : ℝ) := by
    push_cast
    linarith [h.2]
  refine ⟨roundDown_nonnegative _ (le_max_left _ _), ?_, ?_⟩
  · have hd : (roundDown (max 0 (taylor x - remainder x)) : ℝ) ≤
        ((max 0 (taylor x - remainder x) : ℚ) : ℝ) := by
      exact_mod_cast roundDown_le (max 0 (taylor x - remainder x))
    exact hd.trans hlo
  · exact hup.trans (by exact_mod_cast le_roundUp (taylor x + remainder x))

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceExponential
