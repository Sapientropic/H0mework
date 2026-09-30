import H0mework.Arithmetic.RieszForcing.WeakIntervalPairing
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSourceGreen

open Complex Filter MeasureTheory Set Function
open scoped Topology Convolution ContDiff
open OriginalRieszSource.Translator.WeakInterval

noncomputable section

private theorem pulse_weak_derivative (value rhs : ℝ → ℂ)
    (weak : ∀ test : SchwartzMap ℝ ℂ,
      (∫ y : ℝ, value y * deriv test y) = -(∫ y : ℝ, rhs y * test y))
    (n : ℕ) (x : ℝ) :
    convolution (deriv ((pulse n).normed volume)) value (ContinuousLinearMap.lsmul ℝ ℝ) volume x =
      convolution ((pulse n).normed volume) rhs (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  let raw := fun y : ℝ => (((pulse n).normed volume (x - y) : ℝ) : ℂ)
  have compact : HasCompactSupport raw := by
    exact ((pulse n).hasCompactSupport_normed.comp_homeomorph
      (Homeomorph.subLeft x)).comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have smooth : ContDiff ℝ ∞ raw := by
    exact Complex.ofRealCLM.contDiff.comp
      ((pulse n).contDiff_normed.comp (contDiff_const.sub contDiff_id))
  let test : SchwartzMap ℝ ℂ := compact.toSchwartzMap smooth
  have pulseSmooth : ContDiff ℝ ∞ ((pulse n).normed (volume : Measure ℝ)) :=
    (pulse n).contDiff_normed
  have derivative (y : ℝ) : deriv test y =
      -((deriv ((pulse n).normed volume) (x - y) : ℝ) : ℂ) := by
    have actual := (((pulseSmooth.differentiable (by simp))
      (x - y)).hasDerivAt.comp y ((hasDerivAt_id y).const_sub x)).ofReal_comp
    have normalized : HasDerivAt raw
        (-((deriv ((pulse n).normed volume) (x - y) : ℝ) : ℂ)) y := by
      simpa only [raw, Function.comp_apply, mul_neg_one, Complex.ofReal_neg] using actual
    exact normalized.deriv
  have source := weak test
  have leftRead : (∫ y : ℝ, value y * deriv test y) =
      -convolution (deriv ((pulse n).normed volume)) value
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
    rw [convolution_eq_swap, ← integral_neg]
    apply integral_congr_ae
    filter_upwards with y
    rw [derivative]
    simp only [ContinuousLinearMap.lsmul_apply, Complex.real_smul]
    ring
  have rightRead : (∫ y : ℝ, rhs y * test y) =
      convolution ((pulse n).normed volume) rhs (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
    rw [convolution_eq_swap]
    apply integral_congr_ae
    filter_upwards with y
    change rhs y * ((pulse n).normed volume (x - y) : ℂ) = _
    simp only [ContinuousLinearMap.lsmul_apply, Complex.real_smul]
    ring
  rw [leftRead, rightRead] at source
  exact neg_injective source

/-- A continuous local representative inherits the continuous weak derivative via the original pulses. -/
theorem weak_hasDerivAt (value rhs : ℝ → ℂ)
    (valueLocal : LocallyIntegrable value) (rhsLocal : LocallyIntegrable rhs)
    (weak : ∀ test : SchwartzMap ℝ ℂ,
      (∫ y : ℝ, value y * deriv test y) = -(∫ y : ℝ, rhs y * test y))
    (x : ℝ) (valueContinuous : ∀ᶠ y in 𝓝 x, ContinuousAt value y)
    (rhsContinuous : ContinuousAt rhs x) : HasDerivAt value (rhs x) x := by
  let values := fun n : ℕ =>
    convolution ((pulse n).normed volume) value (ContinuousLinearMap.lsmul ℝ ℝ) volume
  let derivatives := fun n : ℕ =>
    convolution ((pulse n).normed volume) rhs (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have derivative (n : ℕ) (y : ℝ) : HasDerivAt (values n) (derivatives n y) y := by
    have pulseCompact : HasCompactSupport ((pulse n).normed (volume : Measure ℝ)) :=
      (pulse n).hasCompactSupport_normed
    have pulseSmooth : ContDiff ℝ 1 ((pulse n).normed (volume : Measure ℝ)) :=
      (pulse n).contDiff_normed
    have actual := pulseCompact.hasDerivAt_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) pulseSmooth valueLocal y
    rw [pulse_weak_derivative value rhs weak] at actual
    exact actual
  have joint : Tendsto (fun p : ℕ × ℝ => derivatives p.1 p.2)
      (atTop ×ˢ 𝓝 x) (𝓝 (rhs x)) := by
    exact ContDiffBump.convolution_tendsto_right (pulse_tendsto.comp tendsto_fst)
      (Eventually.of_forall fun _ => rhsLocal.aestronglyMeasurable)
      (rhsContinuous.tendsto.comp tendsto_snd) tendsto_snd
  have uniform : TendstoUniformlyOnFilter derivatives rhs atTop (𝓝 x) := by
    rw [Metric.tendstoUniformlyOnFilter_iff]
    intro ε positive
    have distance : Tendsto (fun p : ℕ × ℝ => dist (rhs p.2) (derivatives p.1 p.2))
        (atTop ×ˢ 𝓝 x) (𝓝 0) := by
      simpa only [dist_self, Function.comp_apply] using
        (rhsContinuous.tendsto.comp tendsto_snd).dist joint
    exact (tendsto_order.mp distance).2 ε positive
  apply hasDerivAt_of_tendstoUniformlyOnFilter uniform
    (Eventually.of_forall fun p => derivative p.1 p.2)
  filter_upwards [valueContinuous] with y continuous
  exact ContDiffBump.convolution_tendsto_right pulse_tendsto
    (Eventually.of_forall fun _ => valueLocal.aestronglyMeasurable)
    (continuous.tendsto.comp tendsto_snd) tendsto_const_nhds

end
end OriginalRieszSourceGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
