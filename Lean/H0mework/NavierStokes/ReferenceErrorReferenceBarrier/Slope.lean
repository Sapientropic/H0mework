import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Continuous integral subsolutions supply the right-slope mouth of Mathlib's fencing theorem. -/

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.ReferenceBarrier

open Set Filter MeasureTheory
open scoped Topology

theorem liminf_slope_of_increments {f g : Real → Real} {a b : Real} (ordered : a ≤ b)
    (continuous : ContinuousOn g (Icc a b))
    (increments : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      f t - f s ≤ ∫ u in s..t, g u) :
    ∀ x ∈ Ico a b, ∀ r, g x < r → ∃ᶠ z in 𝓝[>] x, slope f x z < r := by
  let extension : Real → Real := fun t => g (projIcc a b ordered t)
  have extensionContinuous : Continuous extension :=
    (continuousOn_iff_continuous_domRestrict.mp continuous).comp continuous_projIcc
  let primitive : Real → Real := fun t => ∫ u in a..t, extension u
  have derivative (x : Real) : HasDerivAt primitive (extension x) x :=
    intervalIntegral.integral_hasDerivAt_right (extensionContinuous.intervalIntegrable a x)
      extensionContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter extensionContinuous.continuousAt
  intro x within r upper
  have extensionAt : extension x = g x := by
    simp only [extension, projIcc_of_mem _ (Ico_subset_Icc_self within)]
  have primitiveSlope : ∃ᶠ z in 𝓝[>] x, slope primitive x z < r :=
    (derivative x).hasDerivWithinAt.liminf_right_slope_le (by rwa [extensionAt])
  apply (primitiveSlope.and_eventually (Ioc_mem_nhdsGT within.2)).mono
  intro z both
  have zWithin : z ∈ Icc a b := ⟨within.1.trans both.2.1.le, both.2.2⟩
  have integralEq : (∫ u in x..z, g u) = primitive z - primitive x := by
    calc
      _ = ∫ u in x..z, extension u := by
        apply intervalIntegral.integral_congr
        intro u member
        rw [uIcc_of_le both.2.1.le] at member
        have included : u ∈ Icc a b := ⟨within.1.trans member.1, member.2.trans both.2.2⟩
        simp only [extension, projIcc_of_mem _ included]
      _ = _ := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => derivative u)
        (extensionContinuous.intervalIntegrable x z)
  have estimate := increments x (Ico_subset_Icc_self within) z zWithin both.2.1.le
  rw [integralEq] at estimate
  have slopeLe : slope f x z ≤ slope primitive x z := by
    rw [slope_def_field, slope_def_field]
    exact (div_le_div_iff_of_pos_right (sub_pos.mpr both.2.1)).mpr estimate
  exact slopeLe.trans_lt both.1

end SaturationMonoid.NavierStokes.ReferenceBarrier
