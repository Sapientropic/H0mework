import H0mework.Versions.R7e4da746.Arithmetic.RieszResponse.ResponseRead
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Dilation

open Complex Filter MeasureTheory Set
open scoped Topology ENNReal
open GapEuler
attribute [local instance 1100] NormedSpace.complexToReal

open private eulerCotest eulerCotest_apply eulerCotest_read from
  H0mework.Versions.R7e4da746.Arithmetic.RieszResponse.ResponseRead
open private complexExp_cpow_half_for_directDilation from
  H0mework.Versions.R7e4da746.Arithmetic.BurnolPhysical.L2DirectDilation

local notation "T" => coPoissonSchwartzEnergyTranslation
local notation "S'" => TemperedDistribution ℝ ℂ

private theorem translation_apply (h : ℝ) (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    T h test x = (Real.exp (h/2) : ℂ)*test (Real.exp h*x) := by
  change (Real.exp h : ℂ)^(1/2 : ℂ)*test (Real.exp h*x) = _
  rw [complexExp_cpow_half_for_directDilation]

private theorem inverse_test_derivative (test : SchwartzMap ℝ ℂ) (h x : ℝ) :
    HasDerivAt (fun t : ℝ => T (-t) test x)
      ((Real.exp (-h/2) : ℂ)*eulerCotest test (Real.exp (-h)*x)) h := by
  have flow := ((Real.hasDerivAt_exp (-h)).comp h (hasDerivAt_id h).neg).mul_const x
  have moved := (test.hasDerivAt (Real.exp (-h)*x)).scomp h flow
  have scaleReal := (Real.hasDerivAt_exp (-h/2)).comp h ((hasDerivAt_id h).neg.div_const 2)
  have scale := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt h scaleReal
  have product := scale.mul moved
  have path : (fun t : ℝ => T (-t) test x) =
      fun t => (Real.exp (-t/2) : ℂ)*test (Real.exp (-t)*x) :=
    funext (fun t => translation_apply (-t) test x)
  rw [path]
  have derivative :
      (Real.exp (-h/2) : ℂ) •
        ((Real.exp (-h)*(-1 : ℝ)*x) • deriv test (Real.exp (-h)*x)) +
      (↑(Real.exp (-h/2)*(-(1 : ℝ)/2)) : ℂ)*test (Real.exp (-h)*x) =
      (Real.exp (-h/2) : ℂ)*eulerCotest test (Real.exp (-h)*x) := by
    rw [eulerCotest_apply]
    simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  rw [← derivative]
  simpa only [Function.comp_def, Pi.neg_apply, id_eq, smul_eq_mul, Complex.ofRealCLM_apply, add_comm] using! product

/-- The same native Euler cotest differentiates the translated read of an
integrable field, including fields outside the original Hilbert space. -/
theorem integrable_weak_at_zero (field : Lp ℂ 1 (volume : Measure ℝ)) (test : SchwartzMap ℝ ℂ) :
    HasDerivAt (fun h : ℝ => (field : S') (T (-h) test))
      (euler (field : S') test) 0 := by
  let value := fun h x : ℝ => T (-h) test x*field x
  let speed := fun h x : ℝ => (Real.exp (-h/2) : ℂ)*eulerCotest test (Real.exp (-h)*x)*field x
  let budget := Real.exp (1/2)*(SchwartzMap.seminorm ℂ 0 0) (eulerCotest test)
  have fieldInt : Integrable (field : ℝ → ℂ) volume := memLp_one_iff_integrable.mp (Lp.memLp field)
  have domain (h : ℝ) : Integrable (value h) volume :=
    fieldInt.mul_of_top_right (T (-h) test).memLp_top
  have speedAtZero : speed 0 = fun x => eulerCotest test x*field x := by
    funext x
    simp only [speed, neg_zero, zero_div, Real.exp_zero, Complex.ofReal_one, one_mul]
  have speedDomain : Integrable (speed 0) volume := by
    rw [speedAtZero]
    exact fieldInt.mul_of_top_right (eulerCotest test).memLp_top
  have bound : ∀ᵐ x : ℝ ∂volume, ∀ h ∈ Ioo (-1 : ℝ) 1, ‖speed h x‖ ≤ budget*‖field x‖ := by
    filter_upwards with x h within
    dsimp only [speed, budget]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact mul_le_mul (Real.exp_le_exp.mpr (by linarith [within.1]))
      (SchwartzMap.norm_le_seminorm ℂ _ _) (norm_nonneg _) (Real.exp_nonneg _)
  have derivative : ∀ᵐ x : ℝ ∂volume, ∀ h ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun t => value t x) (speed h x) h :=
    Eventually.of_forall fun x h _ => (inverse_test_derivative test h x).mul_const (field x)
  have actual := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := value) (F' := speed) (bound := fun x => budget*‖field x‖)
    (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall fun h => (domain h).aestronglyMeasurable) (domain 0)
    speedDomain.aestronglyMeasurable bound (fieldInt.norm.const_mul budget) derivative).2
  have argument : (fun h => ∫ x, value h x) = fun h => (field : S') (T (-h) test) := by
    funext h
    rw [Lp.toTemperedDistribution_apply]
    rfl
  have read : (∫ x, speed 0 x) = euler (field : S') test := by
    rw [speedAtZero, eulerCotest_read, Lp.toTemperedDistribution_apply]
    rfl
  rw [argument, read] at actual
  exact actual

end OriginalRieszSource.Dilation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
