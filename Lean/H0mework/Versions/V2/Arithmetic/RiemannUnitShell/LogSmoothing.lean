import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.StepRealization
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! Logarithmic smoothing preserves the actual source and generates compact annulus Schwartz sources. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ContDiff
noncomputable section

def burnolReciprocalStepLogInterval (lower upper : ℝ) : ℝ → ℝ :=
  (Ioc (-Real.log upper) (-Real.log lower)).indicator (fun _ => 1)

def burnolReciprocalStepLogBump (pulse : ContDiffBump (0 : ℝ)) (x : ℝ) : ℝ :=
  pulse.normed volume x * Real.exp (x / 2)

def burnolReciprocalStepLogSmooth (pulse : ContDiffBump (0 : ℝ)) (lower upper : ℝ) : ℝ → ℝ :=
  MeasureTheory.convolution (burnolReciprocalStepLogBump pulse) (burnolReciprocalStepLogInterval lower upper)
    (ContinuousLinearMap.mul ℝ ℝ) volume

def burnolReciprocalStepSmoothSourceRaw (pulse : ContDiffBump (0 : ℝ)) (lower upper x : ℝ) : ℂ :=
  ↑(|x|⁻¹ * burnolReciprocalStepLogSmooth pulse lower upper (Real.log |x|))

private theorem burnolReciprocalStepLogBump_compact (pulse : ContDiffBump (0 : ℝ)) :
    HasCompactSupport (burnolReciprocalStepLogBump pulse) := pulse.hasCompactSupport_normed.mul_right

private theorem burnolReciprocalStepLogInterval_integrable (lower upper : ℝ) :
    Integrable (burnolReciprocalStepLogInterval lower upper) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Ioc
  exact (continuous_const.continuousOn.integrableOn_compact
    (show IsCompact (Icc (-Real.log upper) (-Real.log lower)) from isCompact_Icc)).mono_set
      Ioc_subset_Icc_self

theorem burnolReciprocalStepLogSmooth_contDiff (pulse : ContDiffBump (0 : ℝ)) (lower upper : ℝ) :
    ContDiff ℝ ∞ (burnolReciprocalStepLogSmooth pulse lower upper) := by
  apply (burnolReciprocalStepLogBump_compact pulse).contDiff_convolution_left
  · exact pulse.contDiff_normed.mul (by fun_prop)
  · exact (burnolReciprocalStepLogInterval_integrable lower upper).locallyIntegrable

theorem burnolReciprocalStepLogSmooth_support (pulse : ContDiffBump (0 : ℝ)) (lower upper : ℝ) {x : ℝ}
    (nonzero : burnolReciprocalStepLogSmooth pulse lower upper x ≠ 0) :
    -Real.log upper - pulse.rOut < x ∧ x < -Real.log lower + pulse.rOut := by
  have support := MeasureTheory.support_convolution_subset
    (f := burnolReciprocalStepLogBump pulse) (g := burnolReciprocalStepLogInterval lower upper) (ContinuousLinearMap.mul ℝ ℝ)
      (show x ∈ Function.support (burnolReciprocalStepLogSmooth pulse lower upper) from nonzero)
  obtain ⟨h, hKernel, t, hInterval, same⟩ := support
  have pulseNonzero : pulse.normed volume h ≠ 0 := by
    intro zero
    apply hKernel
    change pulse.normed volume h * Real.exp (h / 2) = 0
    rw [zero, zero_mul]
  have small : |h| < pulse.rOut := by
    have belongs : h ∈ Function.support (pulse.normed volume) := pulseNonzero
    rw [pulse.support_normed_eq] at belongs
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using belongs
  have interval : t ∈ Ioc (-Real.log upper) (-Real.log lower) := by
    by_contra outside
    exact hInterval (indicator_of_notMem outside _)
  rcases abs_lt.mp small with ⟨hLower, hUpper⟩
  constructor <;> linarith [interval.1, interval.2]

theorem burnolReciprocalStepSmoothSource_support (pulse : ContDiffBump (0 : ℝ)) (lower upper : ℝ) {x : ℝ}
    (nonzero : burnolReciprocalStepSmoothSourceRaw pulse lower upper x ≠ 0) :
    Real.exp (-Real.log upper - pulse.rOut) < |x| ∧
      |x| < Real.exp (-Real.log lower + pulse.rOut) := by
  have productNonzero : |x|⁻¹ * burnolReciprocalStepLogSmooth pulse lower upper (Real.log |x|) ≠ 0 := by
    exact fun zero => nonzero (by rw [burnolReciprocalStepSmoothSourceRaw, zero, Complex.ofReal_zero])
  have xNonzero : x ≠ 0 := by
    intro zero
    simp [zero] at productNonzero
  have rawNonzero := (mul_ne_zero_iff.mp productNonzero).2
  have support := burnolReciprocalStepLogSmooth_support pulse lower upper rawNonzero
  have positive : 0 < |x| := abs_pos.mpr xNonzero
  constructor
  · exact (Real.lt_log_iff_exp_lt positive).mp support.1
  · exact (Real.log_lt_iff_lt_exp positive).mp support.2

theorem burnolReciprocalStepSmoothSource_contDiff (pulse : ContDiffBump (0 : ℝ)) (lower upper : ℝ) :
    ContDiff ℝ ∞ (burnolReciprocalStepSmoothSourceRaw pulse lower upper) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases zero : x = 0
  · subst x
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (Real.exp_pos (-Real.log upper - pulse.rOut))]
      with x hx
    have small : |x| < Real.exp (-Real.log upper - pulse.rOut) := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hx
    by_contra active
    have sourceLower := (burnolReciprocalStepSmoothSource_support pulse lower upper active).1
    linarith
  · unfold burnolReciprocalStepSmoothSourceRaw
    apply Complex.ofRealCLM.contDiff.contDiffAt.comp
    have absolute : ContDiffAt ℝ ∞ (fun y : ℝ => |y|) x := contDiffAt_abs zero
    exact (absolute.inv (abs_ne_zero.mpr zero)).mul
      ((burnolReciprocalStepLogSmooth_contDiff pulse lower upper).contDiffAt.comp x
        (absolute.log (abs_ne_zero.mpr zero)))

def burnolReciprocalStepSmoothedSource (pulse : ContDiffBump (0 : ℝ)) (lower upper : ℝ) : SchwartzMap ℝ ℂ :=
  (HasCompactSupport.intro (K := symmetricInterval (Real.exp (-Real.log lower + pulse.rOut)))
    isCompact_Icc (fun x outside => by
      by_contra nonzero
      exact outside (abs_le.mp (burnolReciprocalStepSmoothSource_support pulse lower upper nonzero).2.le))).toSchwartzMap
    (burnolReciprocalStepSmoothSource_contDiff pulse lower upper)

private theorem burnolReciprocalStepSource_logRead (lower upper x : ℝ) (lowerPositive : 0 < lower)
    (upperPositive : 0 < upper) (nonzero : x ≠ 0) :
    burnolReciprocalStepSourceRaw lower upper x =
      ((|x| : ℝ) : ℂ)⁻¹ * (burnolReciprocalStepLogInterval lower upper (Real.log |x|) : ℂ) := by
  have positive : 0 < |x| := abs_pos.mpr nonzero
  have lowerRead : lower ≤ |x|⁻¹ ↔ Real.log |x| ≤ -Real.log lower := by
    rw [← Real.log_le_log_iff lowerPositive (inv_pos.mpr positive), Real.log_inv]
    constructor <;> intro h <;> linarith
  have upperRead : |x|⁻¹ < upper ↔ -Real.log upper < Real.log |x| := by
    rw [← Real.log_lt_log_iff (inv_pos.mpr positive) upperPositive, Real.log_inv]
    constructor <;> intro h <;> linarith
  unfold burnolReciprocalStepSourceRaw burnolReciprocalStepLogInterval
  simp only [lowerRead, upperRead, and_comm, indicator_apply, mem_Ioc]
  split_ifs <;> simp

private theorem burnolReciprocalStep_dilation_logRead (lower upper x h : ℝ) (lowerPositive : 0 < lower)
    (upperPositive : 0 < upper) (nonzero : x ≠ 0) :
    (Real.exp (-h / 2) : ℂ) * burnolReciprocalStepSourceRaw lower upper (Real.exp (-h) * x) =
      (Real.exp (h / 2) : ℂ) * ((|x| : ℝ) : ℂ)⁻¹ *
        (burnolReciprocalStepLogInterval lower upper (Real.log |x| - h) : ℂ) := by
  have positive : 0 < |x| := abs_pos.mpr nonzero
  have moved : Real.exp (-h) * x ≠ 0 := mul_ne_zero (Real.exp_ne_zero _) nonzero
  rw [burnolReciprocalStepSource_logRead lower upper _ lowerPositive upperPositive moved,
    abs_mul, abs_of_pos (Real.exp_pos (-h)),
    Real.log_mul (Real.exp_ne_zero _) positive.ne', Real.log_exp]
  have same : -h + Real.log |x| = Real.log |x| - h := by ring
  rw [same, Complex.ofReal_mul, mul_inv_rev]
  have coefficient : (Real.exp (-h / 2) : ℂ) * (Real.exp (-h) : ℂ)⁻¹ =
      (Real.exp (h / 2) : ℂ) := by
    rw [← Complex.ofReal_inv, ← Real.exp_neg, neg_neg, ← Complex.ofReal_mul,
      ← Real.exp_add, show -h / 2 + h = h / 2 by ring]
  rw [← coefficient]
  ring

theorem burnolReciprocalStepSmoothSource_rawOrbit (pulse : ContDiffBump (0 : ℝ)) (lower upper x : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) :
    burnolReciprocalStepSmoothSourceRaw pulse lower upper x =
      ∫ h : ℝ, (pulse.normed volume h : ℂ) *
        ((Real.exp (-h / 2) : ℂ) * burnolReciprocalStepSourceRaw lower upper (Real.exp (-h) * x)) := by
  by_cases zero : x = 0
  · subst x
    have sourceZero : burnolReciprocalStepSourceRaw lower upper 0 = 0 := by
      simp [burnolReciprocalStepSourceRaw, lowerPositive.not_ge]
    simp only [burnolReciprocalStepSmoothSourceRaw, abs_zero, inv_zero, zero_mul, Complex.ofReal_zero,
      mul_zero, sourceZero, integral_zero]
  · unfold burnolReciprocalStepSmoothSourceRaw burnolReciprocalStepLogSmooth
    rw [MeasureTheory.convolution_def, Complex.ofReal_mul, Complex.ofReal_inv,
      ← integral_complex_ofReal, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with h
    rw [burnolReciprocalStep_dilation_logRead lower upper x h lowerPositive upperPositive zero]
    simp only [burnolReciprocalStepLogBump, ContinuousLinearMap.mul_apply', Complex.ofReal_mul]
    ring

def burnolReciprocalStepAnnulusSmoothedSource (pulse : ContDiffBump (0 : ℝ)) (lower upper : ℝ)
    (innerMargin : (1 / 4 : ℝ) ≤ Real.exp (-Real.log upper - pulse.rOut))
    (outerMargin : Real.exp (-Real.log lower + pulse.rOut) ≤ 4) : burnolCompactAnnulusSource := by
  refine ⟨burnolReciprocalStepSmoothedSource pulse lower upper, ?_, ?_, ?_⟩
  · intro x
    change burnolReciprocalStepSmoothSourceRaw pulse lower upper (-x) = burnolReciprocalStepSmoothSourceRaw pulse lower upper x
    simp only [burnolReciprocalStepSmoothSourceRaw, abs_neg]
  · intro x small
    change burnolReciprocalStepSmoothSourceRaw pulse lower upper x = 0
    by_contra active
    have forced := (burnolReciprocalStepSmoothSource_support pulse lower upper active).1
    linarith
  · intro x outside
    change burnolReciprocalStepSmoothSourceRaw pulse lower upper x = 0
    by_contra active
    have forced := (burnolReciprocalStepSmoothSource_support pulse lower upper active).2
    linarith

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
