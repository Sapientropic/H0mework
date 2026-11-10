import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.Continuum.Spacetime.Domain.Translation
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! Pointwise FTC enters L¹ through set-integral separation and Fubini.
The existing Banach-valued FTC then generates the strong L¹ derivative. -/

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace SaturationMonoid.PhysicsCore.YangMills.Spacetime.Domain.Translation
open Terminal
noncomputable section

private def setRead (s : Set Terminal.Spacetime) : L1 →L[ℝ] ℂ :=
  MeasureTheory.L1.integralCLM.comp (LpToLpRestrictCLM Terminal.Spacetime ℂ ℝ volume 1 s)

private theorem setRead_value (s : Set Terminal.Spacetime) (f : L1) :
    setRead s f = ∫ p in s, f p := by
  rw [setRead, ContinuousLinearMap.comp_apply, ← MeasureTheory.L1.integral_def,
    MeasureTheory.L1.integral_eq_integral]
  exact integral_congr_ae (LpToLpRestrictCLM_coeFn ℝ s f)

private theorem setRead_translated (s : Set Terminal.Spacetime) (f : Test) (t : ℝ) :
    setRead s (translated f t) = ∫ p in s, f (p + timeLine t) := by
  rw [setRead_value]
  exact integral_congr_ae (ae_restrict_of_ae (translated_ae f t))

theorem integral_identity (f : Test) (a b : ℝ) :
    ∫ t in a..b, translated (testDerivative 0 f) t = translated f b - translated f a := by
  apply Lp.ext
  refine Lp.ae_eq_of_forall_setIntegral_eq _ _ (by simp) (by simp)
    (fun _ _ _ => (MeasureTheory.L1.integrable_coeFn _).integrableOn)
    (fun _ _ _ => (MeasureTheory.L1.integrable_coeFn _).integrableOn) ?_
  intro s _ _
  rw [← setRead_value, ← setRead_value,
    ← (setRead s).intervalIntegral_comp_comm ((translated_continuous (testDerivative 0 f)).intervalIntegrable a b),
    map_sub, setRead_translated, setRead_translated]
  simp_rw [setRead_translated]
  rw [intervalIntegral_integral_swap ((product_integrable (testDerivative 0 f) a b).mono_measure
    (Measure.prod_mono le_rfl Measure.restrict_le_self))]
  simp_rw [pointwise_integral]
  have integrable_shift (t : ℝ) : Integrable (fun p : Terminal.Spacetime => f (p + timeLine t)) :=
    memLp_one_iff_integrable.mp ((f.memLp 1 volume).comp_measurePreserving
      (measurePreserving_add_right volume (timeLine t)))
  exact integral_sub (integrable_shift b).integrableOn (integrable_shift a).integrableOn

theorem translated_hasDerivAt (f : Test) (t : ℝ) :
    HasDerivAt (translated f) (translated (testDerivative 0 f) t) t := by
  have continuous := translated_continuous (testDerivative 0 f)
  have generated := intervalIntegral.integral_hasDerivAt_right (continuous.intervalIntegrable 0 t)
    continuous.aestronglyMeasurable.stronglyMeasurableAtFilter continuous.continuousAt
  convert! generated.add_const (translated f 0) using 1
  funext s
  rw [integral_identity, sub_add_cancel]

theorem toLp_hasDerivAt (test : Test) :
    HasDerivAt (fun t : ℝ => (translateTest (timeLine t) test).toLp 1 volume)
      ((testDerivative 0 test).toLp 1 volume) 0 := by
  have generated := translated_hasDerivAt test 0
  have same : translated test = fun t : ℝ => (translateTest (timeLine t) test).toLp 1 volume := rfl
  rw [same, translated_zero] at generated
  exact generated

end
end SaturationMonoid.PhysicsCore.YangMills.Spacetime.Domain.Translation
