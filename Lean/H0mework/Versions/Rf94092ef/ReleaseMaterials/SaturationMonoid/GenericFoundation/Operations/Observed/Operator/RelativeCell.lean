import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedRelativeCell

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The whole unit cell consumes the first derivative of its actual local trajectory. -/
theorem integral_tendsto {f : ℝ → E} {rate : E} (zero : f 0 = 0)
    (derivative : HasDerivAt f rate 0) (continuous : ContinuousOn f (Icc 0 1)) :
    Tendsto (fun n : Nat => ∫ t : ℝ in (0 : ℝ)..1, (n+1 : ℝ) • f (t / (n+1 : ℝ)))
      atTop (𝓝 ((1/2 : ℝ) • rate)) := by
  have normError := derivative.isLittleO
  apply Metric.tendsto_nhds.mpr
  intro eps positive
  have halfPositive : 0 < eps/2 := by positivity
  have localBound : ∀ᶠ x : ℝ in 𝓝 0, ‖f x - x • rate‖ ≤ (eps/2) * ‖x‖ := by
    simpa only [zero, sub_zero] using normError.def halfPositive
  obtain ⟨radius, radiusPositive, within⟩ := Metric.eventually_nhds_iff.mp localBound
  have index : Tendsto (fun n : Nat => ((n : ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
  have small : ∀ᶠ n : Nat in atTop, ((n : ℝ)+1)⁻¹ < radius :=
    (tendsto_order.mp index).2 radius radiusPositive
  filter_upwards [small] with n nSmall
  let nReal : ℝ := (n : ℝ)+1
  have nPositive : 0 < nReal := by positivity
  have nLarge : 1 ≤ nReal := by dsimp only [nReal]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have first : IntervalIntegrable (fun t : ℝ => nReal • f (t/nReal)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    apply continuousOn_const.smul
    refine continuous.comp (continuous_id.div_const _).continuousOn ?_
    intro t inside
    exact ⟨div_nonneg inside.1 nPositive.le,
      (div_le_one nPositive).mpr (inside.2.trans nLarge)⟩
  have second : IntervalIntegrable (fun t : ℝ => t • rate) volume 0 1 :=
    (continuous_id.smul continuous_const).intervalIntegrable _ _
  have linear : (∫ t : ℝ in (0 : ℝ)..1, t • rate) = (1/2 : ℝ) • rate := by
    rw [intervalIntegral.integral_smul_const, integral_id]
    norm_num
  change dist (∫ t : ℝ in (0 : ℝ)..1, nReal • f (t/nReal)) ((1/2 : ℝ) • rate) < eps
  rw [dist_eq_norm, ← linear, ← intervalIntegral.integral_sub first second]
  have whole : ‖∫ t : ℝ in (0 : ℝ)..1, nReal • f (t/nReal) - t • rate‖ ≤ eps/2 := by
    have bound : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖nReal • f (t/nReal) - t • rate‖ ≤ eps/2 := by
      rw [uIoc_of_le zero_le_one]
      intro t inside
      have positiveT : 0 ≤ t/nReal := div_nonneg inside.1.le nPositive.le
      have near : dist (t/nReal) 0 < radius := by
        rw [Real.dist_0_eq_abs, abs_of_nonneg positiveT]
        exact ((div_le_div_of_nonneg_right inside.2 nPositive.le).trans_eq (one_div _)).trans_lt nSmall
      have slope := within near
      rw [Real.norm_eq_abs, abs_of_nonneg positiveT] at slope
      have error : nReal • f (t/nReal) - t • rate = nReal • (f (t/nReal) - (t/nReal) • rate) := by
        rw [smul_sub, smul_smul, ← mul_div_assoc, mul_div_cancel_left₀ _ nPositive.ne']
      rw [error, norm_smul, Real.norm_of_nonneg nPositive.le]
      calc
        _ ≤ nReal * ((eps/2) * (t/nReal)) := mul_le_mul_of_nonneg_left slope nPositive.le
        _ = (eps/2) * t := by field_simp
        _ ≤ eps/2 := (mul_le_mul_of_nonneg_left inside.2 halfPositive.le).trans_eq (mul_one _)
    simpa only [sub_zero, abs_one, mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const bound
  exact whole.trans_lt (by linarith)

end
end SourceGeneratedRelativeCell
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
