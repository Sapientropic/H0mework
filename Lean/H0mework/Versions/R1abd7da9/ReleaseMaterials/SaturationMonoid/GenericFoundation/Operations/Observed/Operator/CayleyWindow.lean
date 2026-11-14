import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyWindow

open Finset Polynomial
open scoped BigOperators Polynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private def meanPolynomial (d : ℝ) (length : Nat) : ℂ[X] :=
  C ((length : ℂ)⁻¹) * ∑ k ∈ range length, (1 + C (d : ℂ) * X)^k

/-- Removing the finite Cayley mean exposes one true action factor per cutoff step. -/
def weights (d : ℝ) (cutoff length : Nat) : ℂ[X] :=
  ((1 - meanPolynomial d length).divX)^cutoff

private def average (u : E →L[ℂ] E) (length : Nat) : E →L[ℂ] E :=
  (length : ℂ)⁻¹ • ∑ k ∈ range length, u^k

private theorem average_eval (a u : E →L[ℂ] E) (d : ℝ) (length : Nat)
    (source : u = 1 + (d : ℂ) • a) :
    aeval a (meanPolynomial d length) = average u length := by
  have letter : aeval a (1 + C (d : ℂ) * X) = u := by
    rw [map_add, map_one, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, ← source]
  simp only [meanPolynomial, map_mul, map_sum, map_pow, letter, aeval_C,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, average]

private theorem weights_write (a u : E →L[ℂ] E) (d : ℝ) (cutoff length : Nat)
    (source : u = 1 + (d : ℂ) • a) (positive : 0 < length) (v : E) :
    let p := weights d cutoff length
    (∑ k ∈ range (p.natDegree+1), p.coeff k • ((a^(cutoff+k)) v)) =
      (((1 - average u length)^cutoff) v) := by
  let q : ℂ[X] := 1 - meanPolynomial d length
  have len : (length : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt positive)
  have zero : q.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    change eval (0 : ℂ) (1 - meanPolynomial d length) = 0
    simp only [meanPolynomial, eval_sub, eval_mul, eval_C, eval_one, eval_finsetSum]
    simp [len]
  have factor : q.divX * X = q := by
    simpa only [zero, C_0, add_zero] using divX_mul_X_add q
  have effect := congrArg (fun poly : ℂ[X] => aeval a (poly^cutoff)) factor
  change aeval a ((q.divX * X)^cutoff) = aeval a ((1 - meanPolynomial d length)^cutoff) at effect
  simp only [map_pow, map_mul, aeval_X, map_sub, map_one, average_eval a u d length source, mul_pow] at effect
  rw [← map_pow (aeval a) q.divX] at effect
  change aeval a (weights d cutoff length) * a^cutoff = (1 - average u length)^cutoff at effect
  rw [aeval_eq_sum_range, Finset.sum_mul] at effect
  have written := congrArg (fun map : E →L[ℂ] E => map v) effect
  simpa only [smul_mul_assoc, ← pow_add, Nat.add_comm, _root_.sum_apply,
    smul_apply] using written

private theorem power_norm (u : E →L[ℂ] E) (preserves : ∀ x : E, ‖u x‖ = ‖x‖)
    (n : Nat) (x : E) : ‖(u^n) x‖ = ‖x‖ := by
  induction n with
  | zero => rw [pow_zero, one_apply_eq_self]
  | succ n previous => rw [pow_succ', mul_apply_eq_comp, preserves, previous]

private theorem average_contracts (u : E →L[ℂ] E) (preserves : ∀ x : E, ‖u x‖ = ‖x‖)
    (length : Nat) (positive : 0 < length) (x : E) : ‖average u length x‖ ≤ ‖x‖ := by
  have len : (length : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt positive)
  rw [average, smul_apply, _root_.sum_apply,
    norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (length : ℝ)⁻¹ * ∑ k ∈ range length, ‖(u^k) x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = ‖x‖ := by
      simp only [power_norm u preserves, sum_const, card_range, nsmul_eq_mul,
        ← mul_assoc, inv_mul_cancel₀ len, one_mul]

private theorem average_action_bound (a u : E →L[ℂ] E) (d : ℝ)
    (source : u = 1 + (d : ℂ) • a) (preserves : ∀ x : E, ‖u x‖ = ‖x‖)
    (dpos : 0 < d) (length : Nat) (positive : 0 < length) (w : E) :
    ‖average u length (a w)‖ ≤ 2 * ‖w‖ / ((length : ℝ) * d) := by
  have dnonzero : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr dpos.ne'
  have telescopes := geom_sum_mul u length
  rw [show u - 1 = (d : ℂ) • a by rw [source, add_sub_cancel_left], mul_smul_comm] at telescopes
  have acted := congrArg (fun map : E →L[ℂ] E => map w) telescopes
  change (d : ℂ) • ((∑ k ∈ range length, u^k) (a w)) = (u^length) w - w at acted
  have exactMean : average u length (a w) =
      ((length : ℂ)⁻¹ * (d : ℂ)⁻¹) • ((u^length) w - w) := by
    rw [← acted, smul_smul, mul_assoc, inv_mul_cancel₀ dnonzero, mul_one]
    rfl
  rw [exactMean, norm_smul, norm_mul, norm_inv, norm_inv, Complex.norm_natCast,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos dpos]
  have len : 0 < (length : ℝ) := Nat.cast_pos.mpr positive
  calc
    _ ≤ ((length : ℝ)⁻¹ * d⁻¹) * (‖(u^length) w‖ + ‖w‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _)
        (mul_nonneg (inv_nonneg.mpr len.le) (inv_nonneg.mpr dpos.le))
    _ = _ := by
      rw [power_norm u preserves, div_eq_mul_inv, mul_inv_rev]
      ring

private theorem removed_mean_bound (u : E →L[ℂ] E) (preserves : ∀ x : E, ‖u x‖ = ‖x‖)
    (cutoff length : Nat) (positive : 0 < length) (v : E) :
    ‖((1 - average u length)^cutoff) v - v‖ ≤
      ((2 : ℝ)^cutoff - 1) * ‖average u length v‖ := by
  let A := average u length
  let B : E →L[ℂ] E := 1 - A
  change ‖(B^cutoff) v - v‖ ≤ ((2 : ℝ)^cutoff - 1) * ‖A v‖
  have contracts (x : E) : ‖B x‖ ≤ 2 * ‖x‖ := by
    change ‖x - A x‖ ≤ _
    rw [two_mul]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (average_contracts u preserves length positive x))
  induction cutoff with
  | zero => simp
  | succ n previous =>
    rw [pow_succ', mul_apply_eq_comp]
    have error : B ((B^n) v) - v = B ((B^n) v - v) - A v := by
      rw [map_sub, show B v = v - A v from rfl]
      abel
    calc
      _ ≤ ‖B ((B^n) v - v)‖ + ‖A v‖ := by rw [error]; exact norm_sub_le _ _
      _ ≤ 2 * ‖(B^n) v - v‖ + ‖A v‖ := add_le_add (contracts _) le_rfl
      _ ≤ 2 * (((2 : ℝ)^n - 1) * ‖A v‖) + ‖A v‖ :=
        add_le_add (mul_le_mul_of_nonneg_left previous (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
      _ = _ := by rw [pow_succ]; ring

/-- The generated finite tail word approximates the original action image with a direct range budget. -/
theorem finite_tail_error (a u : E →L[ℂ] E) (d : ℝ)
    (source : u = 1 + (d : ℂ) • a) (preserves : ∀ x : E, ‖u x‖ = ‖x‖)
    (dpos : 0 < d) (cutoff length : Nat) (positive : 0 < length) (w : E) :
    let p := weights d cutoff length
    ‖(∑ k ∈ range (p.natDegree+1), p.coeff k • ((a^(cutoff+k)) (a w))) - a w‖ ≤
      ((2 : ℝ)^cutoff - 1) * (2 * ‖w‖ / ((length : ℝ) * d)) := by
  dsimp only
  rw [weights_write a u d cutoff length source positive]
  have factor : 0 ≤ (2 : ℝ)^cutoff - 1 :=
    sub_nonneg.mpr (one_le_pow₀ (by norm_num))
  exact (removed_mean_bound u preserves cutoff length positive (a w)).trans
    (mul_le_mul_of_nonneg_left (average_action_bound a u d source preserves dpos length positive w) factor)

end SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyWindow
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
