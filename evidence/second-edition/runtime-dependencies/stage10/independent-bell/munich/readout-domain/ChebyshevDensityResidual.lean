import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option autoImplicit false

namespace BellChebyshevDensity
noncomputable section

def shifted (n : ℕ) (u : ℝ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (2*u-1)

theorem shifted_abs_le_one (n : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |shifted n u| ≤ 1 := by
  have hz0 : -1 ≤ 2*u-1 := by linarith
  have hz1 : 2*u-1 ≤ 1 := by linarith
  unfold shifted
  rw [← Real.cos_arccos hz0 hz1, Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

theorem shifted_at_right (n : ℕ) : shifted n 1 = 1 := by
  norm_num [shifted]

theorem shifted_at_left (n : ℕ) : shifted n 0 = (n : ℤ).negOnePow := by
  simp [shifted]

theorem Gaussian_exp_growth_majorant (radius : ℝ) (n : ℕ) (h : radius ≤ n) :
    Real.exp radius ≤ (3 : ℝ)^n := by
  calc
    _ ≤ Real.exp (n : ℝ) := Real.exp_le_exp.mpr h
    _ = (Real.exp 1)^n := by rw [← Real.exp_nat_mul, mul_one]
    _ ≤ _ := pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_three) n

theorem complete_residual_coefficient_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (coefficients : Fin n → E) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖∑ i : Fin n, shifted (i : ℕ) u • coefficients i‖ ≤ ∑ i, ‖coefficients i‖ := by
  calc
    _ ≤ ∑ i : Fin n, ‖shifted (i : ℕ) u • coefficients i‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (shifted_abs_le_one (i : ℕ) u hu0 hu1)

end
end BellChebyshevDensity
