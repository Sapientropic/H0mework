import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Translator.WeakInterval

open Complex Filter MeasureTheory Set Function
open scoped Topology Convolution ContDiff
noncomputable section

local notation "q" => (1 / 4 : ℝ)

def pulse (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1 / ((n : ℝ) + 1) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have positive : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

theorem pulse_tendsto :
    Tendsto (fun n => (pulse n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def intervalOne : ℝ → ℝ := (Ioc (-q) q).indicator (fun _ => 1)

theorem intervalOne_integrable : Integrable intervalOne := by
  exact (continuous_const.integrableOn_Icc : IntegrableOn (fun _ : ℝ => (1 : ℝ))
    (Icc (-q) q)).mono_set Ioc_subset_Icc_self |>.integrable_indicator measurableSet_Ioc

def cutoff (n : ℕ) : ℝ → ℝ :=
  MeasureTheory.convolution ((pulse n).normed volume) intervalOne
    (ContinuousLinearMap.mul ℝ ℝ) volume

theorem cutoff_contDiff (n : ℕ) : ContDiff ℝ ∞ (cutoff n) := by
  exact (pulse n).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.mul ℝ ℝ) (pulse n).contDiff_normed intervalOne_integrable.locallyIntegrable

private theorem convolution_intervalOne (value : ℝ → ℝ) (x : ℝ) :
    MeasureTheory.convolution value intervalOne (ContinuousLinearMap.mul ℝ ℝ) volume x =
      ∫ y : ℝ in (x - q)..(x + q), value y := by
  rw [MeasureTheory.convolution_eq_swap]
  simp only [ContinuousLinearMap.mul_apply', intervalOne]
  have pointwise : (fun y : ℝ => value (x - y) *
      (Ioc (-q) q).indicator (fun _ => 1) y) =
      (Ioc (-q) q).indicator (fun y => value (x - y)) := by
    funext y
    by_cases inside : y ∈ Ioc (-q) q
    · simp only [indicator_of_mem inside, mul_one]
    · simp only [indicator_of_notMem inside, mul_zero]
  rw [pointwise, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : -q ≤ q),
    intervalIntegral.integral_comp_sub_left]
  congr 1
  ring

theorem cutoff_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (cutoff n)
      ((pulse n).normed volume (x + q) - (pulse n).normed volume (x - q)) x := by
  have smooth : ContDiff ℝ 1 ((pulse n).normed volume) := (pulse n).contDiff_normed
  have derivative := (pulse n).hasCompactSupport_normed.hasDerivAt_convolution_left
    (ContinuousLinearMap.mul ℝ ℝ) smooth
    intervalOne_integrable.locallyIntegrable x
  have integralDerivative := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y (_hy : y ∈ uIcc (x - q) (x + q)) =>
      (smooth.differentiable (by norm_num) y).hasDerivAt)
    (smooth.continuous_deriv le_rfl
      |>.intervalIntegrable (x - q) (x + q))
  rw [convolution_intervalOne, integralDerivative] at derivative
  exact derivative

theorem cutoff_deriv (n : ℕ) (x : ℝ) :
    deriv (cutoff n) x =
      (pulse n).normed volume (x + q) - (pulse n).normed volume (x - q) :=
  (cutoff_hasDerivAt n x).deriv

theorem cutoff_norm_le_one (n : ℕ) (x : ℝ) : ‖cutoff n x‖ ≤ 1 := by
  have bound : ∀ y ∈ Metric.ball x (pulse n).rOut, dist (intervalOne y) 0 ≤ (1 : ℝ) := by
    intro y _
    by_cases inside : y ∈ Ioc (-q) q
    · simp only [intervalOne, indicator_of_mem inside, dist_zero_right, norm_one, le_refl]
    · simp only [intervalOne, indicator_of_notMem inside, dist_self]
      norm_num
  have source := MeasureTheory.dist_convolution_le (μ := (volume : Measure ℝ))
    (by norm_num : (0 : ℝ) ≤ 1) (pulse n).support_normed_eq.subset
    (pulse n).nonneg_normed (pulse n).integral_normed
    intervalOne_integrable.aestronglyMeasurable bound
  simpa only [cutoff, dist_zero_right, MeasureTheory.convolution_def,
    ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.mul_apply', smul_eq_mul] using source

theorem cutoff_support (n : ℕ) :
    Function.support (cutoff n) ⊆ Icc (-q - 1) (q + 1) := by
  intro x nonzero
  have source := MeasureTheory.support_convolution_subset
    (f := (pulse n).normed volume) (g := intervalOne)
    (ContinuousLinearMap.mul ℝ ℝ) nonzero
  obtain ⟨h, hKernel, t, hInterval, same⟩ := source
  have small : |h| < (pulse n).rOut := by
    rw [(pulse n).support_normed_eq] at hKernel
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hKernel
  have radiusBound : (pulse n).rOut ≤ 1 := by
    change 1 / ((n : ℝ) + 1) ≤ 1
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have interval : t ∈ Ioc (-q) q := by
    by_contra outside
    exact hInterval (indicator_of_notMem outside (fun _ => (1 : ℝ)))
  change h + t = x at same
  constructor <;> linarith [(abs_lt.mp small).1, (abs_lt.mp small).2, interval.1, interval.2]

theorem cutoff_compact (n : ℕ) : HasCompactSupport (cutoff n) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (cutoff_support n)

theorem cutoff_ae_tendsto : ∀ᵐ x : ℝ ∂volume,
    Tendsto (fun n => cutoff n x) atTop (𝓝 (intervalOne x)) := by
  have ratio : ∀ᶠ n : ℕ in atTop, (pulse n).rOut ≤ 2 * (pulse n).rIn := by
    filter_upwards with n
    change 1 / ((n : ℝ) + 1) ≤ 2 * (1 / ((n : ℝ) + 1) / 2)
    linarith
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    pulse_tendsto ratio intervalOne_integrable.locallyIntegrable

end
end OriginalRieszSource.Translator.WeakInterval
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
