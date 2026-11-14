import H0mework.Versions.R1abd7da9.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.CayleyWindow
import Mathlib.Algebra.Polynomial.Derivative

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyWindow

open Finset Polynomial
open scoped BigOperators Polynomial

open private meanPolynomial average average_eval power_norm average_contracts average_action_bound from
  H0mework.Versions.R1abd7da9.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.CayleyWindow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private def cayleyLetter (d : ℝ) : ℂ[X] := 1 + C (d : ℂ) * X

/-- A second pass of the same finite mean makes its first source moment small. -/
def smoothPolynomial (d : ℝ) (cutoff length : Nat) : ℂ[X] :=
  (1 - (meanPolynomial d length)^2)^cutoff

def smoothWeights (d : ℝ) (cutoff length : Nat) : ℂ[X] :=
  ((1 - (meanPolynomial d length)^2).divX)^cutoff

theorem smooth_factor (d : ℝ) (cutoff length : Nat) (positive : 0 < length) :
    smoothPolynomial d cutoff length = smoothWeights d cutoff length * X^cutoff := by
  let q : ℂ[X] := 1 - (meanPolynomial d length)^2
  have len : (length : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt positive)
  have zero : q.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    change eval (0 : ℂ) (1 - (meanPolynomial d length)^2) = 0
    simp only [meanPolynomial, eval_sub, eval_pow, eval_mul, eval_C, eval_one, eval_finsetSum]
    simp [len]
  have factor : q.divX * X = q := by
    simpa only [zero, C_0, add_zero] using divX_mul_X_add q
  change q^cutoff = q.divX^cutoff * X^cutoff
  rw [← mul_pow, factor]

private theorem letter_eval (a u : E →L[ℂ] E) (d : ℝ)
    (source : u = 1 + (d : ℂ) • a) : aeval a (cayleyLetter d) = u := by
  rw [cayleyLetter, map_add, map_one, map_mul, aeval_C, aeval_X,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← source]

private theorem mean_telescope (d : ℝ) (dpos : 0 < d) (length : Nat) :
    X * meanPolynomial d length =
      C (((length : ℂ)*(d : ℂ))⁻¹) * ((cayleyLetter d)^length - 1) := by
  let C₀ := cayleyLetter d
  let M := meanPolynomial d length
  let s := ∑ k ∈ range length, C₀^k
  have damp : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr dpos.ne'
  have telescopes := geom_sum_mul C₀ length
  rw [show C₀ - 1 = C (d : ℂ) * X by simp [C₀, cayleyLetter]] at telescopes
  have scalar : C (((length : ℂ)*(d : ℂ))⁻¹) * C (d : ℂ) = C ((length : ℂ)⁻¹) := by
    rw [← C_mul, mul_inv_rev]
    congr 1
    rw [mul_comm ((d : ℂ)⁻¹) ((length : ℂ)⁻¹), mul_assoc, inv_mul_cancel₀ damp, mul_one]
  change X * M = C (((length : ℂ)*(d : ℂ))⁻¹) * (C₀^length - 1)
  rw [← telescopes]
  change X * (C ((length : ℂ)⁻¹) * s) = _
  rw [← scalar]
  ring

private theorem first_moment (d : ℝ) (dpos : 0 < d) (length : Nat) (positive : 0 < length) :
    X * derivative (meanPolynomial d length) =
      (cayleyLetter d)^(length-1) - meanPolynomial d length := by
  let C₀ := cayleyLetter d
  let M := meanPolynomial d length
  have len : (length : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt positive)
  have damp : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr dpos.ne'
  have identity : X * M = C (((length : ℂ)*(d : ℂ))⁻¹) * (C₀^length - 1) :=
    mean_telescope d dpos length
  have slope : derivative C₀ = C (d : ℂ) := by
    simp only [C₀, cayleyLetter, derivative_add, derivative_one, derivative_C_mul_X, zero_add]
  have differentiates := congrArg derivative identity
  change derivative (X * M) =
    derivative (C (((length : ℂ)*(d : ℂ))⁻¹) * (C₀^length - 1)) at differentiates
  simp only [derivative_mul, derivative_X, one_mul, derivative_C, zero_mul, zero_add,
    derivative_sub, derivative_one, sub_zero, derivative_pow, slope] at differentiates
  have normalize : C (((length : ℂ)*(d : ℂ))⁻¹) * C (length : ℂ) * C (d : ℂ) = 1 := by
    rw [mul_assoc, ← C_mul, ← C_mul, inv_mul_cancel₀ (mul_ne_zero len damp), C_1]
  have rhs : C (((length : ℂ)*(d : ℂ))⁻¹) *
      (C (length : ℂ) * C₀^(length-1) * C (d : ℂ)) = C₀^(length-1) := by
    calc
      _ = (C (((length : ℂ)*(d : ℂ))⁻¹) * C (length : ℂ) * C (d : ℂ)) * C₀^(length-1) := by ring
      _ = _ := by rw [normalize, one_mul]
  rw [rhs] at differentiates
  exact eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact differentiates)

private theorem square_moment_bound (a u : E →L[ℂ] E) (d : ℝ)
    (source : u = 1 + (d : ℂ) • a) (preserves : ∀ x : E, ‖u x‖ = ‖x‖)
    (dpos : 0 < d) (length : Nat) (positive : 0 < length) (x : E) :
    ‖(aeval a (derivative ((meanPolynomial d length)^2))) ((a^2) x)‖ ≤
      4 * (2 * ‖x‖ / ((length : ℝ) * d)) := by
  let M := meanPolynomial d length
  let z := average u length (a x)
  have fact : derivative (M^2) * X^2 =
      C 2 * ((cayleyLetter d)^(length-1) - M) * (M * X) := by
    change derivative (M^2) * X^2 =
      C 2 * ((cayleyLetter d)^(length-1) - meanPolynomial d length) * (M * X)
    rw [derivative_sq, ← first_moment d dpos length positive]
    change C 2 * M * derivative M * X^2 = C 2 * (X * derivative M) * (M * X)
    ring
  have written := congrArg (fun p : ℂ[X] => aeval a p x) fact
  have result :
      (aeval a (derivative (M^2))) ((a^2) x) =
        (2 : ℂ) • ((u^(length-1)) z - average u length z) := by
    simpa only [map_mul, map_sub, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, mul_apply_eq_comp, smul_apply, sub_apply, M,
      letter_eval a u d source, average_eval a u d length source, z] using written
  change ‖(aeval a (derivative (M^2))) ((a^2) x)‖ ≤ _
  rw [result, norm_smul, show ‖(2 : ℂ)‖ = 2 by norm_num]
  calc
    _ ≤ 2 * (‖(u^(length-1)) z‖ + ‖average u length z‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ ≤ 4 * ‖z‖ := by
      rw [power_norm u preserves]
      calc
        _ ≤ 2 * (‖z‖ + ‖z‖) := mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (average_contracts u preserves length positive z)) (by norm_num)
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (average_action_bound a u d source preserves dpos length positive x) (by norm_num)

private theorem double_mean_contracts (u : E →L[ℂ] E) (preserves : ∀ x : E, ‖u x‖ = ‖x‖)
    (length : Nat) (positive : 0 < length) (x : E) :
    ‖((average u length)^2) x‖ ≤ ‖x‖ := by
  rw [pow_two, mul_apply_eq_comp]
  exact (average_contracts u preserves length positive _).trans
    (average_contracts u preserves length positive _)

private theorem power_bound (b : E →L[ℂ] E) (step : ∀ x : E, ‖b x‖ ≤ 2 * ‖x‖)
    (n : Nat) (x : E) : ‖(b^n) x‖ ≤ (2:ℝ)^n * ‖x‖ := by
  induction n with
  | zero => simp
  | succ n prior =>
    rw [pow_succ', mul_apply_eq_comp, pow_succ', mul_assoc]
    exact (step _).trans (mul_le_mul_of_nonneg_left prior (by norm_num))

private theorem removed_square_error (u : E →L[ℂ] E) (preserves : ∀ x : E, ‖u x‖ = ‖x‖)
    (cutoff length : Nat) (positive : 0 < length) (x : E) :
    ‖(((1-(average u length)^2 : E →L[ℂ] E)^cutoff)) x - x‖ ≤
      ((2 : ℝ)^cutoff-1) * ‖((average u length)^2) x‖ := by
  let b : E →L[ℂ] E := 1-(average u length)^2
  have step (y : E) : ‖b y‖ ≤ 2 * ‖y‖ := by
    change ‖y-((average u length)^2) y‖ ≤ _
    rw [two_mul]
    exact (norm_sub_le _ _).trans
      (add_le_add le_rfl (double_mean_contracts u preserves length positive y))
  change ‖(b^cutoff) x - x‖ ≤ _
  have raw := congrArg (fun f : E →L[ℂ] E => f x) (geom_sum_mul b cutoff)
  have write : (∑ j ∈ range cutoff, (b^j) (-((average u length)^2) x)) = (b^cutoff) x - x := by
    have diff : (b-1) x = -((average u length)^2) x := by
      change (x - ((average u length)^2) x) - x = _
      abel
    simpa only [mul_apply_eq_comp, diff, _root_.sum_apply, sub_apply, one_apply_eq_self] using raw
  rw [← write]
  have total := geom_sum_mul (2 : ℝ) cutoff
  rw [show (2 : ℝ)-1 = 1 by norm_num, mul_one] at total
  calc
    _ ≤ ∑ j ∈ range cutoff, ‖(b^j) (-((average u length)^2) x)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range cutoff, (2:ℝ)^j * ‖((average u length)^2) x‖ :=
      sum_le_sum fun j _ => by simpa only [norm_neg] using power_bound b step j (-((average u length)^2) x)
    _ = _ := by rw [← sum_mul, total]

/-- The smooth source polynomial controls both the field and its first directed moment. -/
theorem smooth_window_error (a u : E →L[ℂ] E) (d : ℝ)
    (source : u = 1 + (d : ℂ) • a) (preserves : ∀ x : E, ‖u x‖ = ‖x‖)
    (dpos : 0 < d) (cutoff length : Nat) (positive : 0 < length) (w x : E) :
    let p := smoothPolynomial d cutoff length
    ‖aeval a p (a w) - a w‖ ≤ ((2 : ℝ)^cutoff-1) * (2 * ‖w‖ / ((length : ℝ) * d)) ∧
    ‖aeval a (derivative p) ((a^2) x)‖ ≤
      ((cutoff : ℝ) * (2:ℝ)^(cutoff-1)) * (4 * (2 * ‖x‖ / ((length : ℝ) * d))) := by
  let A := average u length
  let b : E →L[ℂ] E := 1 - A^2
  let M := meanPolynomial d length
  have step (y : E) : ‖b y‖ ≤ 2 * ‖y‖ := by
    change ‖y-(A^2) y‖ ≤ _
    rw [two_mul]
    exact (norm_sub_le _ _).trans
      (add_le_add le_rfl (double_mean_contracts u preserves length positive y))
  have read : aeval a (1 - M^2) = b := by
    simp only [map_sub, map_one, map_pow, M, average_eval a u d length source, b, A]
  have form : aeval a (smoothPolynomial d cutoff length) = b^cutoff := by
    change aeval a ((1-M^2)^cutoff) = _
    rw [map_pow, read]
  refine ⟨?_, ?_⟩
  · rw [form]
    have price : ‖(A^2) (a w)‖ ≤ 2 * ‖w‖ / ((length : ℝ) * d) := by
      rw [pow_two, mul_apply_eq_comp]
      exact (average_contracts u preserves length positive _).trans
        (average_action_bound a u d source preserves dpos length positive w)
    exact (removed_square_error u preserves cutoff length positive (a w)).trans
      (mul_le_mul_of_nonneg_left price (sub_nonneg.mpr (one_le_pow₀ (by norm_num))))
  · let y := aeval a (derivative (M^2)) ((a^2) x)
    have formula : aeval a (derivative (smoothPolynomial d cutoff length)) ((a^2) x) =
        -(cutoff : ℂ) • (b^(cutoff-1)) y := by
      change aeval a (derivative ((1-M^2)^cutoff)) ((a^2) x) = _
      simp only [derivative_pow, derivative_sub, derivative_one, zero_sub, map_mul,
        map_pow, map_neg, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
        read, mul_apply_eq_comp, smul_apply, neg_apply, neg_smul, smul_neg, y]
    rw [formula, norm_smul, norm_neg, Complex.norm_natCast]
    calc
      _ ≤ (cutoff : ℝ) * ((2 : ℝ)^(cutoff-1) * ‖y‖) :=
        mul_le_mul_of_nonneg_left (power_bound b step _ y) (Nat.cast_nonneg _)
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left (square_moment_bound a u d source preserves dpos length positive x)
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _))

end SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyWindow
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
