import H0mework.Arithmetic.RieszForcing.WeakIntervalPairing

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Translator.WeakInterval

open Complex Filter MeasureTheory Set Function
open scoped Topology Convolution ContDiff
noncomputable section

local notation "q" => (1 / 4 : ℝ)

private theorem cutoff_complex_smooth (n : ℕ) :
    ContDiff ℝ ∞ (fun x : ℝ => (cutoff n x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (cutoff_contDiff n)

private theorem cutoff_complex_compact (n : ℕ) :
    HasCompactSupport (fun x : ℝ => (cutoff n x : ℂ)) := by
  simpa only [Function.comp_def] using
    (cutoff_compact n).comp_left (g := Complex.ofReal) Complex.ofReal_zero

private def cutoffTest (n : ℕ) (test : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  ((cutoff_complex_compact n).mul_right :
      HasCompactSupport (fun x : ℝ => (cutoff n x : ℂ) * test x)).toSchwartzMap
    ((cutoff_complex_smooth n).mul (test.smooth ⊤))

private theorem cutoffTest_apply (n : ℕ) (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    cutoffTest n test x = (cutoff n x : ℂ) * test x := rfl

private theorem cutoffTest_deriv (n : ℕ) (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (cutoffTest n test) x =
      ((deriv (cutoff n) x : ℝ) : ℂ) * test x + (cutoff n x : ℂ) * deriv test x := by
  change deriv (fun x : ℝ => (cutoff n x : ℂ) * test x) x = _
  exact (((cutoff_contDiff n).differentiable (by simp) x).hasDerivAt.ofReal_comp.mul
    (test.hasDerivAt x)).deriv

private theorem cutoff_mul_integrable (n : ℕ) (value : ℝ → ℂ)
    (localIntegral : LocallyIntegrable value) :
    Integrable (fun x : ℝ => (cutoff n x : ℂ) * value x) := by
  simpa only [Function.comp_apply, smul_eq_mul] using localIntegral.integrable_smul_left_of_hasCompactSupport
    (cutoff_complex_smooth n).continuous (cutoff_complex_compact n)

private theorem cutoff_deriv_mul_integrable (n : ℕ) (value : ℝ → ℂ)
    (localIntegral : LocallyIntegrable value) :
    Integrable (fun x : ℝ => ((deriv (cutoff n) x : ℝ) : ℂ) * value x) := by
  simpa only [Function.comp_apply, smul_eq_mul] using localIntegral.integrable_smul_left_of_hasCompactSupport
    (Complex.continuous_ofReal.comp ((cutoff_contDiff n).continuous_deriv (by simp)))
    ((cutoff_compact n).deriv.comp_left (g := Complex.ofReal) Complex.ofReal_zero)

private theorem rotate_equation (a b c : ℂ) (equation : a + b = -c) : b + c = -a := by
  linear_combination equation

private theorem cutoff_weak_eq (value rhs : ℝ → ℂ)
    (valueLocal : LocallyIntegrable value) (rhsLocal : LocallyIntegrable rhs)
    (weak : ∀ test : SchwartzMap ℝ ℂ,
      (∫ x : ℝ, value x * deriv test x) = -(∫ x : ℝ, rhs x * test x))
    (test : SchwartzMap ℝ ℂ) (n : ℕ) :
    (∫ x : ℝ, (cutoff n x : ℂ) * (value x * deriv test x + rhs x * test x)) =
      -(∫ x : ℝ, ((deriv (cutoff n) x : ℝ) : ℂ) * (value x * test x)) := by
  have testDerivContinuous : Continuous (fun x : ℝ => deriv test x) :=
    (SchwartzMap.derivCLM ℂ ℂ test).continuous
  have boundaryLocal : LocallyIntegrable (fun x : ℝ => value x * test x) :=
    LocallyIntegrable.mul_continuous test.continuous valueLocal
  have bulkLocal : LocallyIntegrable (fun x : ℝ => value x * deriv test x) :=
    LocallyIntegrable.mul_continuous testDerivContinuous valueLocal
  have rhsTestLocal : LocallyIntegrable (fun x : ℝ => rhs x * test x) :=
    LocallyIntegrable.mul_continuous test.continuous rhsLocal
  have leftIntegrable : Integrable (fun x : ℝ =>
      ((deriv (cutoff n) x : ℝ) : ℂ) * (value x * test x)) :=
    cutoff_deriv_mul_integrable n _ boundaryLocal
  have middleIntegrable : Integrable (fun x : ℝ =>
      (cutoff n x : ℂ) * (value x * deriv test x)) :=
    cutoff_mul_integrable n _ bulkLocal
  have rightIntegrable : Integrable (fun x : ℝ =>
      (cutoff n x : ℂ) * (rhs x * test x)) :=
    cutoff_mul_integrable n _ rhsTestLocal
  have leftRead : (∫ x : ℝ, value x * deriv (cutoffTest n test) x) =
      (∫ x : ℝ, ((deriv (cutoff n) x : ℝ) : ℂ) * (value x * test x)) +
      ∫ x : ℝ, (cutoff n x : ℂ) * (value x * deriv test x) := by
    rw [← integral_add leftIntegrable middleIntegrable]
    apply integral_congr_ae
    filter_upwards with x
    rw [cutoffTest_deriv]
    ring
  have rightRead : (∫ x : ℝ, rhs x * cutoffTest n test x) =
      ∫ x : ℝ, (cutoff n x : ℂ) * (rhs x * test x) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [cutoffTest_apply]
    ring
  have source := weak (cutoffTest n test)
  rw [leftRead, rightRead] at source
  calc
    _ = (∫ x : ℝ, (cutoff n x : ℂ) * (value x * deriv test x)) +
        ∫ x : ℝ, (cutoff n x : ℂ) * (rhs x * test x) := by
      rw [← integral_add middleIntegrable rightIntegrable]
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = _ := rotate_equation _ _ _ source

theorem schwartz_interval_ibp (value rhs : ℝ → ℂ)
    (valueLocal : LocallyIntegrable value) (rhsLocal : LocallyIntegrable rhs)
    (weak : ∀ test : SchwartzMap ℝ ℂ,
      (∫ x : ℝ, value x * deriv test x) = -(∫ x : ℝ, rhs x * test x))
    (continuousLeft : ContinuousAt value (-q)) (continuousRight : ContinuousAt value q)
    (test : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ in Ioc (-q) q, value x * deriv test x + rhs x * test x) =
      value q * test q - value (-q) * test (-q) := by
  have boundaryLocal : LocallyIntegrable (fun x : ℝ => value x * test x) :=
    LocallyIntegrable.mul_continuous test.continuous valueLocal
  have bulkLocal : LocallyIntegrable (fun x : ℝ => value x * deriv test x + rhs x * test x) :=
    (LocallyIntegrable.mul_continuous (SchwartzMap.derivCLM ℂ ℂ test).continuous valueLocal).add
      (LocallyIntegrable.mul_continuous test.continuous rhsLocal)
  have bulk := cutoff_integral_tendsto _ bulkLocal
  have boundary := (cutoff_deriv_pair_tendsto _ boundaryLocal
    (continuousLeft.mul test.continuous.continuousAt)
    (continuousRight.mul test.continuous.continuousAt)).neg
  have same := bulk.congr (cutoff_weak_eq value rhs valueLocal rhsLocal weak test)
  have limit := tendsto_nhds_unique same boundary
  linear_combination limit

end
end OriginalRieszSource.Translator.WeakInterval
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
