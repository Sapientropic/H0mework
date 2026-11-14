import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.RelativeCell

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedRelativeCell

open MeasureTheory Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A source quadratic remainder pays an explicit error for its full scaled cell. -/
theorem integral_error {f : ℝ → E} (rate : E) {budget N : ℝ}
    (nonnegative : 0 ≤ budget) (large : 1 ≤ N)
    (continuous : ContinuousOn f (Icc 0 1))
    (remainder : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t - t • rate‖ ≤ budget * t^2) :
    ‖(∫ t : ℝ in (0 : ℝ)..1, N • f (t/N)) - (1/2 : ℝ) • rate‖ ≤ budget/N := by
  have positive := zero_lt_one.trans_le large
  have first : IntervalIntegrable (fun t : ℝ => N • f (t/N)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    apply continuousOn_const.smul
    refine continuous.comp (continuous_id.div_const _).continuousOn ?_
    intro t inside
    exact ⟨div_nonneg inside.1 positive.le, (div_le_one positive).mpr (inside.2.trans large)⟩
  have second : IntervalIntegrable (fun t : ℝ => t • rate) volume 0 1 :=
    (continuous_id.smul continuous_const).intervalIntegrable _ _
  have linear : (∫ t : ℝ in (0 : ℝ)..1, t • rate) = (1/2 : ℝ) • rate := by
    rw [intervalIntegral.integral_smul_const, integral_id]
    norm_num
  rw [← linear, ← intervalIntegral.integral_sub first second]
  have bound : ∀ t ∈ uIoc (0 : ℝ) 1, ‖N • f (t/N) - t • rate‖ ≤ budget/N := by
    rw [uIoc_of_le zero_le_one]
    intro t inside
    have cut : t/N ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg inside.1.le positive.le, (div_le_one positive).mpr (inside.2.trans large)⟩
    have actual : N • f (t/N) - t • rate = N • (f (t/N) - (t/N) • rate) := by
      rw [smul_sub, smul_smul, ← mul_div_assoc, mul_div_cancel_left₀ _ positive.ne']
    rw [actual, norm_smul, Real.norm_of_nonneg positive.le]
    calc
      _ ≤ N * (budget*(t/N)^2) := mul_le_mul_of_nonneg_left (remainder _ cut) positive.le
      _ = (budget/N)*t^2 := by field_simp
      _ ≤ budget/N := (mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ inside.1.le zero_le_one).mpr inside.2 |>.trans_eq (one_pow 2))
        (div_nonneg nonnegative positive.le)).trans_eq (mul_one _)
  simpa only [sub_zero, abs_one, mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const bound

end
end SourceGeneratedRelativeCell
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
