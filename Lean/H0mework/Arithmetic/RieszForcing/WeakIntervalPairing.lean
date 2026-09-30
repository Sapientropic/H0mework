import H0mework.Arithmetic.RieszForcing.Pulse

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Translator.WeakInterval

open Complex Filter MeasureTheory Set Function
open scoped Topology Convolution ContDiff
noncomputable section

local notation "q" => (1 / 4 : ℝ)

theorem cutoff_integral_tendsto (value : ℝ → ℂ) (localIntegral : LocallyIntegrable value) :
    Tendsto (fun n => ∫ x : ℝ, (cutoff n x : ℂ) * value x) atTop
      (𝓝 (∫ x : ℝ in Ioc (-q) q, value x)) := by
  let bound := (Icc (-q - 1) (q + 1)).indicator (fun x : ℝ => ‖value x‖)
  have integrableBound : Integrable bound := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Icc
    exact (localIntegral.integrableOn_isCompact isCompact_Icc).norm
  have measurable : ∀ n, AEStronglyMeasurable (fun x : ℝ => (cutoff n x : ℂ) * value x) := by
    intro n
    exact (Complex.continuous_ofReal.comp (cutoff_contDiff n).continuous).aestronglyMeasurable.mul
      localIntegral.aestronglyMeasurable
  have bounded : ∀ n, ∀ᵐ x : ℝ ∂volume, ‖(cutoff n x : ℂ) * value x‖ ≤ bound x := by
    intro n
    filter_upwards with x
    by_cases inside : x ∈ Icc (-q - 1) (q + 1)
    · change _ ≤ (Icc (-q - 1) (q + 1)).indicator (fun x : ℝ => ‖value x‖) x
      rw [indicator_of_mem inside, norm_mul, Complex.norm_real]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (cutoff_norm_le_one n x) (norm_nonneg (value x))
    · have zero : cutoff n x = 0 := notMem_support.mp fun membership =>
        inside (cutoff_support n membership)
      change _ ≤ (Icc (-q - 1) (q + 1)).indicator (fun x : ℝ => ‖value x‖) x
      rw [zero, Complex.ofReal_zero, zero_mul, norm_zero, indicator_of_notMem inside]
  have limit : ∀ᵐ x : ℝ ∂volume,
      Tendsto (fun n => (cutoff n x : ℂ) * value x) atTop
        (𝓝 ((Ioc (-q) q).indicator value x)) := by
    filter_upwards [cutoff_ae_tendsto] with x rawLimit
    have castLimit := Complex.continuous_ofReal.continuousAt.tendsto.comp rawLimit
    have final := castLimit.mul_const (value x)
    by_cases inside : x ∈ Ioc (-q) q
    · simpa only [Function.comp_apply, intervalOne, indicator_of_mem inside,
        Complex.ofReal_one, one_mul] using final
    · simpa only [Function.comp_apply, intervalOne, indicator_of_notMem inside,
        Complex.ofReal_zero, zero_mul] using final
  have result := tendsto_integral_of_dominated_convergence bound measurable integrableBound bounded limit
  rw [integral_indicator measurableSet_Ioc] at result
  exact result

private theorem pulse_reflection (n : ℕ) (point x : ℝ) :
    (pulse n).normed volume (point - x) = (pulse n).normed volume (x - point) := by
  rw [show point - x = -(x - point) by ring, ContDiffBump.normed_neg]

theorem pulse_pair_integrable (n : ℕ) (point : ℝ) (value : ℝ → ℂ)
    (localIntegral : LocallyIntegrable value) :
    Integrable (fun x : ℝ => ((pulse n).normed volume (x - point) : ℂ) * value x) := by
  have compact : HasCompactSupport ((pulse n).normed (volume : Measure ℝ)) :=
    (pulse n).hasCompactSupport_normed
  have source := compact.convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (pulse n).continuous_normed localIntegral point
  have swapped := (MeasureTheory.convolutionExistsAt_iff_integrable_swap).mp source
  apply swapped.congr
  filter_upwards with x
  simp only [ContinuousLinearMap.lsmul_apply, pulse_reflection, Complex.real_smul]

theorem pulse_pair_eq_convolution (n : ℕ) (point : ℝ) (value : ℝ → ℂ) :
    (∫ x : ℝ, ((pulse n).normed volume (x - point) : ℂ) * value x) =
      MeasureTheory.convolution ((pulse n).normed volume) value
        (ContinuousLinearMap.lsmul ℝ ℝ) volume point := by
  rw [MeasureTheory.convolution_eq_swap]
  apply integral_congr_ae
  filter_upwards with x
  simp only [ContinuousLinearMap.lsmul_apply, pulse_reflection, Complex.real_smul]

theorem pulse_pair_tendsto (point : ℝ) (value : ℝ → ℂ)
    (localIntegral : LocallyIntegrable value) (continuous : ContinuousAt value point) :
    Tendsto (fun n => ∫ x : ℝ, ((pulse n).normed volume (x - point) : ℂ) * value x)
      atTop (𝓝 (value point)) := by
  have source : Tendsto (fun n => MeasureTheory.convolution ((pulse n).normed volume) value
      (ContinuousLinearMap.lsmul ℝ ℝ) volume point) atTop (𝓝 (value point)) := by
    exact ContDiffBump.convolution_tendsto_right pulse_tendsto
      (Eventually.of_forall fun _ => localIntegral.aestronglyMeasurable)
      (continuous.tendsto.comp tendsto_snd) tendsto_const_nhds
  simpa only [pulse_pair_eq_convolution] using source

theorem cutoff_deriv_pair_tendsto (value : ℝ → ℂ)
    (localIntegral : LocallyIntegrable value)
    (continuousLeft : ContinuousAt value (-q)) (continuousRight : ContinuousAt value q) :
    Tendsto (fun n => ∫ x : ℝ, ((deriv (cutoff n) x : ℝ) : ℂ) * value x) atTop
      (𝓝 (value (-q) - value q)) := by
  have source := (pulse_pair_tendsto (-q) value localIntegral continuousLeft).sub
    (pulse_pair_tendsto q value localIntegral continuousRight)
  apply source.congr
  intro n
  rw [← integral_sub (pulse_pair_integrable n (-q) value localIntegral)
    (pulse_pair_integrable n q value localIntegral)]
  apply integral_congr_ae
  filter_upwards with x
  rw [cutoff_deriv]
  push_cast
  ring

end
end OriginalRieszSource.Translator.WeakInterval
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
