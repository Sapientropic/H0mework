import H0mework.Chemistry.LAlanineRefinementDensity.GaussianPrimitive
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource

open GaussianPrimitive Polynomial Finset MeasureTheory
open scoped BigOperators
noncomputable section

theorem absolute_linear_le_quadratic {alpha : ℝ} (positive : 0 < alpha) (x : ℝ) :
    |x| ≤ alpha / 2 * x ^ 2 + 1 / (2 * alpha) := by
  have square := sq_nonneg (alpha * |x| - 1)
  have identity : (alpha * |x| - 1) ^ 2 = alpha ^ 2 * x ^ 2 - 2 * alpha * |x| + 1 := by
    nlinarith [sq_abs x]
  rw [identity] at square
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * alpha by positivity)).mp
  field_simp
  nlinarith

/-- A global Gaussian tail is retained after paying for each polynomial monomial. -/
theorem monomial_gaussian_tail {alpha : ℝ} (positive : 0 < alpha) (n : ℕ) (x : ℝ) :
    |x| ^ n * Real.exp (-alpha * x ^ 2) ≤
      (n.factorial : ℝ) * Real.exp (1 / (2 * alpha)) * Real.exp (-(alpha / 2) * x ^ 2) := by
  have factorialPositive : (0 : ℝ) < n.factorial := by positivity
  have power : |x| ^ n ≤ (n.factorial : ℝ) * Real.exp |x| := by
    have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) n
    exact (div_le_iff₀ factorialPositive).mp h |>.trans_eq (mul_comm _ _)
  calc
    _ ≤ ((n.factorial : ℝ) * Real.exp |x|) * Real.exp (-alpha * x ^ 2) :=
      mul_le_mul_of_nonneg_right power (Real.exp_nonneg _)
    _ = (n.factorial : ℝ) * Real.exp (|x| - alpha * x ^ 2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (n.factorial : ℝ) * Real.exp (1 / (2 * alpha) + -(alpha / 2) * x ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ factorialPositive.le
      apply Real.exp_le_exp.mpr
      linarith [absolute_linear_le_quadratic positive x]
    _ = _ := by rw [Real.exp_add, ← mul_assoc]

def polynomialMass (p : Polynomial ℝ) : ℝ :=
  ∑ k ∈ range (p.natDegree + 1), |p.coeff k| * (k.factorial : ℝ)

def gaussianBound (alpha : ℝ) (p : Polynomial ℝ) : ℝ :=
  polynomialMass p * Real.exp (1 / (2 * alpha))

theorem gaussianBound_nonnegative (alpha : ℝ) (p : Polynomial ℝ) : 0 ≤ gaussianBound alpha p := by
  unfold gaussianBound polynomialMass
  positivity

theorem gaussian_tail {alpha : ℝ} (positive : 0 < alpha) (p : Polynomial ℝ) (x : ℝ) :
    |gaussian alpha p x| ≤ gaussianBound alpha p * Real.exp (-(alpha / 2) * x ^ 2) := by
  rw [gaussian, abs_mul, abs_of_pos (Real.exp_pos _), Polynomial.eval_eq_sum_range]
  calc
    _ ≤ (∑ k ∈ range (p.natDegree + 1), |p.coeff k * x ^ k|) * Real.exp (-alpha * x ^ 2) :=
      mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Real.exp_nonneg _)
    _ = ∑ k ∈ range (p.natDegree + 1),
        |p.coeff k| * (|x| ^ k * Real.exp (-alpha * x ^ 2)) := by
      simp only [Finset.sum_mul, abs_mul, abs_pow, mul_assoc]
    _ ≤ ∑ k ∈ range (p.natDegree + 1), |p.coeff k| *
        ((k.factorial : ℝ) * Real.exp (1 / (2 * alpha)) * Real.exp (-(alpha / 2) * x ^ 2)) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (monomial_gaussian_tail positive k x) (abs_nonneg _)
    _ = _ := by simp only [gaussianBound, polynomialMass, Finset.sum_mul, mul_assoc]

theorem gaussian_uniform_bound {alpha : ℝ} (positive : 0 < alpha) (p : Polynomial ℝ) (x : ℝ) :
    |gaussian alpha p x| ≤ gaussianBound alpha p := by
  have decay : Real.exp (-(alpha / 2) * x ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg x))
  exact (gaussian_tail positive p x).trans
    ((mul_le_mul_of_nonneg_left decay (gaussianBound_nonnegative alpha p)).trans_eq (mul_one _))

theorem gaussian_integrable {alpha : ℝ} (positive : 0 < alpha) (p : Polynomial ℝ) :
    Integrable (gaussian alpha p) := by
  apply ((integrable_exp_neg_mul_sq (show 0 < alpha / 2 by positivity)).const_mul
    (gaussianBound alpha p)).mono' (gaussian_contDiff p alpha 0).continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs] using gaussian_tail positive p x)

end
end LAlanine40K2025.BasinRefinement.GlobalSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
