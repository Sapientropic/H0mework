import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeSlidingPrimitive

open Set MeasureTheory

theorem integral_increment_le {value : ℝ → ℝ} {bound left right shift : ℝ}
    (continuous : ContinuousOn value (Icc 0 1))
    (range : ∀ time ∈ Icc (0 : ℝ) 1, 0 ≤ value time ∧ value time ≤ bound)
    (ordered : left ≤ right) (positive : 0 ≤ shift) (leftInside : 0 ≤ left)
    (rightInside : right + shift ≤ 1) :
    (∫ time in left..right, value (time + shift) - value time) ≤ shift * bound := by
  have sample {a b : ℝ} (first : a ∈ Icc (0 : ℝ) 1) (last : b ∈ Icc (0 : ℝ) 1) :
      IntervalIntegrable value volume a b :=
    (continuous.mono (uIcc_subset_Icc first last)).intervalIntegrable
  have leftMem : left ∈ Icc (0 : ℝ) 1 := ⟨leftInside, by linarith⟩
  have rightMem : right ∈ Icc (0 : ℝ) 1 := ⟨leftInside.trans ordered, by linarith⟩
  have leftShift : left + shift ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have rightShift : right + shift ∈ Icc (0 : ℝ) 1 := ⟨by linarith, rightInside⟩
  have shifted : IntervalIntegrable (fun time => value (time + shift)) volume left right := by
    apply ContinuousOn.intervalIntegrable_of_Icc ordered
    exact continuous.comp (continuousOn_id.add continuousOn_const) (fun time inside => ⟨by linarith [inside.1], by linarith [inside.2]⟩)
  rw [intervalIntegral.integral_sub shifted (sample leftMem rightMem), intervalIntegral.integral_comp_add_right]
  have first := intervalIntegral.integral_add_adjacent_intervals (sample leftMem rightMem) (sample rightMem rightShift)
  have last := intervalIntegral.integral_add_adjacent_intervals (sample leftMem leftShift) (sample leftShift rightShift)
  have nonnegative : 0 ≤ ∫ time in left..(left + shift), value time :=
    intervalIntegral.integral_nonneg (by linarith) (fun time inside =>
      (range time ⟨by linarith [inside.1], by linarith [inside.2]⟩).1)
  have upper := intervalIntegral.integral_mono_on (show right ≤ right + shift by linarith)
    (sample rightMem rightShift) (intervalIntegrable_const : IntervalIntegrable (fun _ => bound) volume right (right + shift))
    (fun time inside => (range time ⟨by linarith [inside.1], inside.2.trans rightInside⟩).2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at upper
  linarith

end SaturationMonoid.NavierStokes.NativeSlidingPrimitive
