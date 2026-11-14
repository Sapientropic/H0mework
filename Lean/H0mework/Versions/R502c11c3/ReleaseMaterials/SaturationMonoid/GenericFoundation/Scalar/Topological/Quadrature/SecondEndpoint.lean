import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedQuadrature

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private def weight (t : ℝ) : ℝ := t * (1 - t) / 2

private theorem weight_derivative (t : ℝ) :
    HasDerivAt weight (1/2-t) t := by
  unfold weight
  have other := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
  have deriv := ((hasDerivAt_id t).mul other).div_const 2
  simp only [id_eq, Pi.sub_apply, zero_sub] at deriv
  convert deriv using 1 <;> try rfl
  ring

private theorem integral_weight : (∫ t : ℝ in (0 : ℝ)..1, weight t) = 1/12 := by
  have expansion : weight = fun t => (1/2 : ℝ) * (t - t^2) := by funext t; unfold weight; ring
  rw [expansion]
  have lin : IntervalIntegrable (fun x : ℝ => x) volume 0 1 := continuous_id.intervalIntegrable _ _
  have sq : IntervalIntegrable (fun x : ℝ => x ^ 2) volume 0 1 := (continuous_id.pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub lin sq,
    integral_id, integral_pow]
  norm_num

/-- The two original endpoint corrections leave the zero-mean kernel acting on
the actual second derivative on that same cell. -/
theorem second_endpoint_cell (f f' f'' : ℝ → E)
    (first : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (second : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f' (f'' t) t)
    (continuous : ContinuousOn f'' (Icc (0 : ℝ) 1)) :
    (1/2 : ℝ) • (f 0 + f 1) - (∫ t : ℝ in (0 : ℝ)..1, f t) +
      (1/12 : ℝ) • (f' 0 - f' 1) =
    ∫ t : ℝ in (0 : ℝ)..1, weight t • (f'' t - f'' 0) -
      (1/12 : ℝ) • (f'' t - f'' 0) := by
  have ordered : (0 : ℝ) ≤ 1 := zero_le_one
  have within : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le ordered
  have c₁ : ContinuousOn f' (Icc (0 : ℝ) 1) := fun t ht =>
    (second t ht).continuousAt.continuousWithinAt
  have int₁ : IntervalIntegrable f' volume 0 1 := c₁.intervalIntegrable_of_Icc ordered
  have int₂ : IntervalIntegrable f'' volume 0 1 := continuous.intervalIntegrable_of_Icc ordered
  have linear (t : ℝ) : HasDerivAt (fun x : ℝ => 1/2-x) (-1) t := by
    have h := (hasDerivAt_const t (1/2 : ℝ)).sub (hasDerivAt_id t)
    convert h using 1 <;> first | rfl | norm_num
  have wCont : Continuous weight := by unfold weight; fun_prop
  have lCont : Continuous (fun x : ℝ => 1/2-x) := by fun_prop
  have firstIBP := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (u := fun x : ℝ => 1/2-x) (u' := fun _ => (-1 : ℝ))
    (v := f) (v' := f') (a := 0) (b := 1)
    (fun t _ => linear t) (fun t ht => first t (within ▸ ht))
    intervalIntegrable_const int₁
  have secondIBP := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (u := weight) (u' := fun t : ℝ => 1/2-t)
    (v := f') (v' := f'') (a := 0) (b := 1)
    (fun t _ => weight_derivative t) (fun t ht => second t (within ▸ ht))
    (lCont.intervalIntegrable _ _) int₂
  have firstFTC : (∫ t : ℝ in (0 : ℝ)..1, f'' t) = f' 1 - f' 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => second t (within ▸ ht)) int₂
  have kernelConst : (∫ t : ℝ in (0 : ℝ)..1, weight t • f'' 0) = (1/12 : ℝ) • f'' 0 := by
    rw [intervalIntegral.integral_smul_const, integral_weight]
  have intWeight : IntervalIntegrable (fun t : ℝ => weight t • f'' t) volume 0 1 :=
    (wCont.continuousOn.smul continuous).intervalIntegrable_of_Icc ordered
  have intWeightConst : IntervalIntegrable (fun t : ℝ => weight t • f'' 0) volume 0 1 :=
    (wCont.smul continuous_const).intervalIntegrable _ _
  have diff := int₂.sub (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f'' 0) volume 0 1)
  rw [show (fun t : ℝ => weight t • (f'' t-f'' 0) - (1/12 : ℝ) • (f'' t-f'' 0)) =
    (fun t : ℝ => (weight t • f'' t - weight t • f'' 0) -
      (1/12 : ℝ) • (f'' t-f'' 0)) by funext t; rw [smul_sub]]
  have scaled : IntervalIntegrable (fun t : ℝ => (1/12 : ℝ) • (f'' t-f'' 0)) volume 0 1 :=
    diff.smul (1/12 : ℝ)
  rw [intervalIntegral.integral_sub (intWeight.sub intWeightConst) scaled,
    intervalIntegral.integral_sub intWeight intWeightConst, kernelConst,
    intervalIntegral.integral_smul, intervalIntegral.integral_sub int₂ intervalIntegrable_const,
    firstFTC, intervalIntegral.integral_const, sub_zero, one_smul, secondIBP, firstIBP]
  have neg : (∫ t : ℝ in (0 : ℝ)..1, (-1 : ℝ) • f t) =
      -(∫ t : ℝ in (0 : ℝ)..1, f t) := by rw [intervalIntegral.integral_smul, neg_one_smul]
  rw [neg]
  norm_num [weight]
  module

/-- The source correction is controlled solely by its local second-derivative variation. -/
theorem second_endpoint_bound (f f' f'' : ℝ → E)
    (first : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (second : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f' (f'' t) t)
    (continuous : ContinuousOn f'' (Icc (0 : ℝ) 1)) {error : ℝ}
    (oscillation : ∀ t ∈ Icc (0 : ℝ) 1, ‖f'' t - f'' 0‖ ≤ error) :
    ‖(1/2 : ℝ) • (f 0 + f 1) - (∫ t : ℝ in (0 : ℝ)..1, f t) +
      (1/12 : ℝ) • (f' 0 - f' 1)‖ ≤ error := by
  rw [second_endpoint_cell f f' f'' first second continuous]
  have integrand (t : ℝ) (ht : t ∈ uIoc (0 : ℝ) 1) :
      ‖weight t • (f'' t - f'' 0) - (1/12 : ℝ) • (f'' t - f'' 0)‖ ≤ error := by
    have inside : t ∈ Icc (0 : ℝ) 1 :=
      Ioc_subset_Icc_self (by simpa only [uIoc_of_le zero_le_one] using ht)
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    have small : |weight t-1/12| ≤ 1 := by
      have lo : 0 ≤ weight t := by unfold weight; positivity [inside.1, sub_nonneg.mpr inside.2]
      have hi : weight t ≤ 1/2 := by
        unfold weight
        have product := mul_le_mul inside.2 (sub_le_self 1 inside.1)
          (sub_nonneg.mpr inside.2) (by norm_num : (0 : ℝ) ≤ 1)
        norm_num at product
        linarith
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    exact (mul_le_mul_of_nonneg_right small (norm_nonneg _)).trans (by simpa only [one_mul] using oscillation t inside)
  exact (intervalIntegral.norm_integral_le_of_norm_le_const integrand).trans_eq (by norm_num)

end SourceGeneratedQuadrature
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
