import H0mework.Versions.Y.Arithmetic.MellinProjection.GapTailDilation
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Actual Mellin tail integration by parts, including its generated boundary value. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace SchwartzMap Topology
noncomputable section

theorem burnolMellinTailWeight_schwartz_integrable
    {radius : ℝ} (positive : 0 < radius) (exponent : ℂ)
    (rightHalf : 1 / 2 < exponent.re) (test : SchwartzMap ℝ ℂ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-exponent) * test x) (Ioi radius) := by
  have native := burnolRadiusMellinWeight_integrableOn_tail radius positive
    exponent rightHalf (test.toLp 2 volume)
  apply native.congr
  filter_upwards [ae_restrict_of_ae (test.coeFn_toLp 2 (volume : Measure ℝ))] with x read
  rw [read]

theorem burnolMellinTailPower_hasDerivAt (exponent : ℂ) {x : ℝ} (positive : 0 < x) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ (-exponent))
      ((-exponent) * (x : ℂ) ^ (-(exponent + 1))) x := by
  have native := (Complex.hasStrictDerivAt_cpow_const
    (c := -exponent) (Complex.ofReal_mem_slitPlane.mpr positive)).hasDerivAt.comp_ofReal
  rw [show -exponent - 1 = -(exponent + 1) by ring] at native
  exact native

theorem burnolMellinTailPower_tendsto_zero
    (exponent : ℂ) (positiveRe : 0 < exponent.re) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ (-exponent)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have native := tendsto_rpow_neg_atTop (show 0 < exponent.re from positiveRe)
  apply native.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with x positive
  rw [Complex.norm_cpow_eq_rpow_re_of_pos positive, Complex.neg_re]

theorem burnolMellinTail_schwartz_IBP
    {radius : ℝ} (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ in Ioi radius, (x : ℂ) ^ (-star coordinate.value) * deriv test x) =
      -(radius : ℂ) ^ (-star coordinate.value) * test radius +
        star coordinate.value *
          ∫ x : ℝ in Ioi radius, (x : ℂ) ^ (-(star coordinate.value + 1)) * test x := by
  have half : 1 / 2 < (star coordinate.value).re := by
    simpa only [Complex.star_def, Complex.conj_re] using coordinate.rightHalf
  have derivativeHalf : 1 / 2 < (star coordinate.value + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have derivativeInt := burnolMellinTailWeight_schwartz_integrable positive
    (star coordinate.value + 1) derivativeHalf test
  have right : Tendsto (fun x : ℝ => (x : ℂ) ^ (-star coordinate.value) * test x)
      (𝓝[>] radius) (𝓝 ((radius : ℂ) ^ (-star coordinate.value) * test radius)) :=
    ((burnolMellinTailPower_hasDerivAt (star coordinate.value) positive).continuousAt.mul
      test.continuous.continuousAt).continuousWithinAt
  have infinity : Tendsto (fun x : ℝ => (x : ℂ) ^ (-star coordinate.value) * test x)
      atTop (𝓝 0) := by
    apply (burnolMellinTailPower_tendsto_zero (star coordinate.value)
      (by linarith)).zero_mul_isBoundedUnder_le
    apply isBoundedUnder_of_eventually_le
    exact Filter.Eventually.of_forall fun x => SchwartzMap.norm_le_seminorm ℂ test x
  have native := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => (x : ℂ) ^ (-star coordinate.value))
    (u' := fun x : ℝ => (-star coordinate.value) *
      (x : ℂ) ^ (-(star coordinate.value + 1)))
    (v := fun x : ℝ => test x) (v' := fun x : ℝ => deriv test x)
    (a := radius) (a' := (radius : ℂ) ^ (-star coordinate.value) * test radius) (b' := 0)
    (fun x inside => burnolMellinTailPower_hasDerivAt _ (positive.trans inside))
    (fun x _ => test.hasDerivAt x)
    (burnolMellinTailWeight_schwartz_integrable positive (star coordinate.value) half
      (SchwartzMap.derivCLM ℂ ℂ test))
    (by
      apply (derivativeInt.const_mul (-star coordinate.value)).congr
      filter_upwards with x
      simp only [Pi.mul_apply]
      ring) right infinity
  simp_rw [mul_assoc] at native
  rw [integral_const_mul] at native
  convert native using 1
  ring

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
