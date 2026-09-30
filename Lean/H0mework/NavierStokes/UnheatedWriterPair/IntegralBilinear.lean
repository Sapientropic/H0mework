import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Normed.Operator.Bilinear

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeUnheatedIntegralBilinear

open Set Filter MeasureTheory AbsolutelyContinuousOnInterval

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {a b : ℝ}

omit [NormedSpace ℝ E] [CompleteSpace E] [NormedSpace ℝ F] [CompleteSpace F] in
theorem dominated {f : ℝ → E} {g : ℝ → F} (continuous : AbsolutelyContinuousOnInterval g a b)
    (constant : ℝ) (bound : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, dist (f x) (f y) ≤ constant * dist (g x) (g y)) :
    AbsolutelyContinuousOnInterval f a b := by
  unfold AbsolutelyContinuousOnInterval at continuous ⊢
  apply squeeze_zero' (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg) _
    (by simpa using continuous.const_mul constant)
  rw [eventually_inf_principal]
  filter_upwards with intervals inside
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro index member
  exact bound _ (inside.1 index member).1 _ (inside.1 index member).2

omit [CompleteSpace E] in
theorem primitive_ac (f : ℝ → E) (integrable : IntervalIntegrable f volume a b) :
    AbsolutelyContinuousOnInterval (fun t => ∫ x in a..t, f x) a b := by
  apply dominated (integrable.norm.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc) 1
  intro x hx y hy
  have toX := integrable.mono_set (uIcc_subset_uIcc left_mem_uIcc hx)
  have toY := integrable.mono_set (uIcc_subset_uIcc left_mem_uIcc hy)
  rw [dist_eq_norm, Real.dist_eq,
    intervalIntegral.integral_interval_sub_left toX toY,
    intervalIntegral.integral_interval_sub_left toX.norm toY.norm, one_mul]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

omit [CompleteSpace E] in
theorem written_ac (f rate : ℝ → E) (integrable : IntervalIntegrable rate volume a b)
    (written : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, f y - f x = ∫ t in x..y, rate t) :
    AbsolutelyContinuousOnInterval f a b := by
  apply dominated (primitive_ac rate integrable) 1
  intro x hx y hy
  rw [dist_eq_norm, dist_eq_norm,
    written y hy x hx, intervalIntegral.integral_interval_sub_left
      (integrable.mono_set (uIcc_subset_uIcc left_mem_uIcc hx))
      (integrable.mono_set (uIcc_subset_uIcc left_mem_uIcc hy)), one_mul]

omit [CompleteSpace E] [CompleteSpace G] in
theorem diagonal_ac (B : E →L[ℝ] E →L[ℝ] G) {f : ℝ → E}
    (continuous : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => B (f t) (f t)) a b := by
  obtain ⟨bound, bounded⟩ := continuous.exists_bound
  apply dominated continuous (2*‖B‖*bound)
  intro x hx y hy
  rw [dist_eq_norm, dist_eq_norm]
  have equal : B (f x) (f x) - B (f y) (f y) = B (f x) (f x-f y) + B (f x-f y) (f y) := by
    simp only [map_sub, sub_apply]
    abel
  rw [equal]
  apply (norm_add_le _ _).trans
  have first := (B.le_opNorm₂ (f x) (f x-f y)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (bounded x hx) (norm_nonneg B)) (norm_nonneg _))
  have second := (B.le_opNorm₂ (f x-f y) (f y)).trans
    (mul_le_mul_of_nonneg_left (bounded y hy) (mul_nonneg (norm_nonneg B) (norm_nonneg _)))
  exact (add_le_add first second).trans_eq (by ring)

theorem integral_of_ac_derivative (f rate : ℝ → E) (continuous : AbsolutelyContinuousOnInterval f a b)
    (integrable : IntervalIntegrable rate volume a b)
    (derivative : ∀ᵐ time : ℝ, time ∈ uIcc a b → HasDerivAt f (rate time) time) :
    f b - f a = ∫ time in a..b, rate time := by
  have subAC := continuous.sub (primitive_ac rate integrable)
  have zero : ∀ᵐ time : ℝ, time ∈ uIcc a b →
      HasDerivAt (fun t => f t - ∫ x in a..t, rate x) 0 time := by
    filter_upwards [derivative, integrable.ae_hasDerivAt_integral] with time actual primitive
    intro inside
    simpa only [sub_self, Pi.sub_apply] using! (actual inside).sub (primitive inside a left_mem_uIcc)
  obtain ⟨constant, same⟩ := subAC.const_of_ae_hasDerivAt_zero zero
  have left := same a left_mem_uIcc
  have right := same b right_mem_uIcc
  simp only [Pi.sub_apply, intervalIntegral.integral_same, sub_zero] at left right
  rw [← left] at right
  exact (sub_eq_iff_eq_add.mp right).trans (add_comm _ _) |> fun h => sub_eq_iff_eq_add.mpr h

end SaturationMonoid.NavierStokes.NativeUnheatedIntegralBilinear
