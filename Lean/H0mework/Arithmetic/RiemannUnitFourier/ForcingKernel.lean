import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import H0mework.Arithmetic.Tempered.MuntzTheta

/-! The actual integer-comb remainder kernel is continuous at every positive scale. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter FourierTransform
open scoped InnerProductSpace Topology
noncomputable section

theorem burnolRemainderKernel_continuousAt (test : SchwartzMap ℝ ℂ)
    (radius : ℝ) (positive : 0 < radius) :
    ContinuousAt (coPoissonMuntzScaleRemainder test) radius := by
  let a := radius / 2
  have aPos : 0 < a := half_pos positive
  let C := (SchwartzMap.seminorm ℝ 2 0 test) / a ^ 2
  let bound : {n : ℤ // n ≠ 0} → ℝ := fun n => C * (1 / (n.val : ℝ) ^ 2)
  have sumBound : Summable bound := by
    exact ((Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))).subtype
      (fun n : ℤ => n ≠ 0)).mul_left C
  have uniform : ∀ n : {n : ℤ // n ≠ 0}, ∀ r : ℝ, r ∈ Ioi a →
      ‖test (r * (n.val : ℝ))‖ ≤ bound n := by
    intro n r hr
    change a < r at hr
    have nNonzero : (n.val : ℝ) ≠ 0 := Int.cast_ne_zero.mpr n.property
    have rPos := aPos.trans hr
    have primitive := test.norm_pow_mul_le_seminorm ℝ 2 (r * (n.val : ℝ))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos rPos, mul_pow, sq_abs] at primitive
    change ‖test (r * (n.val : ℝ))‖ ≤ C * (1 / (n.val : ℝ) ^ 2)
    rw [← div_eq_mul_one_div, le_div_iff₀ (sq_pos_of_ne_zero nNonzero)]
    dsimp only [C]
    rw [le_div_iff₀ (sq_pos_of_pos aPos)]
    have ordered : a ^ 2 ≤ r ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right ordered
      (mul_nonneg (sq_nonneg (n.val : ℝ)) (norm_nonneg (test (r * (n.val : ℝ)))))]
  have theta : ContinuousOn (coPoissonMuntzThetaNonzero test) (Ioi a) := by
    exact continuousOn_tsum (fun n => (test.continuous.comp (continuous_id.mul continuous_const)).continuousOn)
      sumBound uniform
  have localLaw : ContinuousAt (fun r : ℝ => coPoissonMuntzThetaNonzero test r -
      (r⁻¹ : ℝ) • ∫ x : ℝ, test x) radius :=
    (theta.continuousAt (Ioi_mem_nhds (by dsimp only [a]; linarith))).sub
      ((continuousAt_inv₀ positive.ne').smul continuousAt_const)
  apply localLaw.congr
  filter_upwards [Ioi_mem_nhds positive] with r hr
  exact (coPoissonMuntzScaleRemainder_eq test hr).symm

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
