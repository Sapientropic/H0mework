import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.GaussianPrimitive

open Polynomial Finset

noncomputable section

def jetPolynomial {R : Type*} [CommRing R] (alpha : R) (polynomial : Polynomial R) : Polynomial R :=
  polynomial.derivative - C (2 * alpha) * X * polynomial

def gaussian (alpha : ℝ) (polynomial : Polynomial ℝ) (x : ℝ) : ℝ :=
  polynomial.eval x * Real.exp (-alpha * x ^ 2)

/-- The exact polynomial recurrence used by the source's Gaussian jet compiler. -/
theorem gaussian_hasDerivAt (polynomial : Polynomial ℝ) (alpha x : ℝ) :
    HasDerivAt (gaussian alpha polynomial) (gaussian alpha (jetPolynomial alpha polynomial) x) x := by
  have exponential := (((hasDerivAt_id x).pow 2).const_mul (-alpha)).exp
  have product := (polynomial.hasDerivAt x).mul exponential
  apply product.congr_deriv
  simp only [gaussian, jetPolynomial, eval_sub, eval_mul, eval_C, eval_X, Pi.pow_apply, id_eq]
  ring

theorem gaussian_contDiff (polynomial : Polynomial ℝ) (alpha : ℝ) (order : WithTop ℕ∞) :
    ContDiff ℝ order (gaussian alpha polynomial) := by
  have polynomialSmooth : ContDiff ℝ order (fun x : ℝ => polynomial.eval x) := by
    convert! polynomial.contDiff_aeval order using 1
  exact polynomialSmooth.mul (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_id.pow 2)))

theorem gaussian_deriv (polynomial : Polynomial ℝ) (alpha : ℝ) :
    deriv (gaussian alpha polynomial) = gaussian alpha (jetPolynomial alpha polynomial) := by
  funext x
  exact (gaussian_hasDerivAt polynomial alpha x).deriv

theorem gaussian_iteratedDeriv (polynomial : Polynomial ℝ) (alpha : ℝ) (order : Nat) :
    iteratedDeriv order (gaussian alpha polynomial) =
      gaussian alpha ((jetPolynomial alpha)^[order] polynomial) := by
  induction order with
  | zero => simp
  | succ order ih =>
    rw [iteratedDeriv_succ, ih, gaussian_deriv, Function.iterate_succ_apply']

/-- This tail factor is exact rational arithmetic when `level` is source-generated. -/
theorem exp_neg_le_two_inv_pow (beta : ℝ) (level : Nat) (below : (level : ℝ) ≤ beta) :
    Real.exp (-beta) ≤ 1 / (2 : ℝ) ^ level := by
  have base : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have power : (2 : ℝ) ^ level ≤ Real.exp (level : ℝ) := by
    simpa only [← Real.exp_nat_mul, mul_one] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) base level
  have total : (2 : ℝ) ^ level ≤ Real.exp beta := power.trans (Real.exp_le_exp.mpr below)
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) total

def coefficientEnvelope {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (polynomial : Polynomial K) (radius : K) : K :=
  ∑ k ∈ range (polynomial.natDegree + 1), |polynomial.coeff k| * radius ^ k

theorem eval_le_coefficientEnvelope (polynomial : Polynomial ℝ) {x radius : ℝ}
    (inside : |x| ≤ radius) : |polynomial.eval x| ≤ coefficientEnvelope polynomial radius := by
  rw [Polynomial.eval_eq_sum_range]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg x) inside k) (abs_nonneg _)

theorem gaussian_abs_bound (polynomial : Polynomial ℝ) (alpha x radius : ℝ) (level : Nat)
    (inside : |x| ≤ radius) (below : (level : ℝ) ≤ alpha * x ^ 2) :
    |gaussian alpha polynomial x| ≤ coefficientEnvelope polynomial radius / (2 : ℝ) ^ level := by
  rw [gaussian, abs_mul, abs_of_pos (Real.exp_pos _)]
  have poly := eval_le_coefficientEnvelope polynomial inside
  have tail := exp_neg_le_two_inv_pow (alpha * x ^ 2) level below
  calc
    |polynomial.eval x| * Real.exp (-alpha * x ^ 2) ≤
        coefficientEnvelope polynomial radius * (1 / (2 : ℝ) ^ level) := by
      exact mul_le_mul poly (by simpa only [neg_mul] using tail) (Real.exp_nonneg _)
        ((abs_nonneg _).trans poly)
    _ = _ := by ring

theorem jetPolynomial_ratCast (alpha : ℚ) (polynomial : Polynomial ℚ) :
    jetPolynomial (alpha : ℝ) (polynomial.map (algebraMap ℚ ℝ)) =
      (jetPolynomial alpha polynomial).map (algebraMap ℚ ℝ) := by
  simp [jetPolynomial]

theorem coefficientEnvelope_ratCast (polynomial : Polynomial ℚ) (radius : ℚ) :
    coefficientEnvelope (polynomial.map (algebraMap ℚ ℝ)) (radius : ℝ) =
      ((coefficientEnvelope polynomial radius : ℚ) : ℝ) := by
  simp only [coefficientEnvelope,
    Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective,
    Polynomial.coeff_map, Rat.cast_sum, Rat.cast_mul, Rat.cast_abs, Rat.cast_pow]
  rfl

theorem rationalGaussian_abs_bound (polynomial : Polynomial ℚ) (alpha radius : ℚ) (x : ℝ)
    (level : Nat) (inside : |x| ≤ (radius : ℝ)) (below : (level : ℝ) ≤ (alpha : ℝ) * x ^ 2) :
    |gaussian (alpha : ℝ) (polynomial.map (algebraMap ℚ ℝ)) x| ≤
      ((coefficientEnvelope polynomial radius / (2 : ℚ) ^ level : ℚ) : ℝ) := by
  have bound := gaussian_abs_bound (polynomial.map (algebraMap ℚ ℝ)) (alpha : ℝ) x radius level inside below
  simpa only [coefficientEnvelope_ratCast, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using bound

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.GaussianPrimitive
