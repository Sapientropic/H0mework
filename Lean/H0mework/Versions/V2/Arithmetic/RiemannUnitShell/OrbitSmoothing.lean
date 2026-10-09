import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.LogSmoothing
import H0mework.Versions.V2.Arithmetic.RemainderSource.BochnerPairing

/-! Pointwise source smoothing is the Bochner average of the original unitary orbit. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ContDiff
noncomputable section

def burnolReciprocalStepSmoothedValue (pulse : ContDiffBump (0 : ℝ)) (value : BurnolL2) : BurnolL2 :=
  MeasureTheory.convolution (pulse.normed volume) (fun h => burnolMultiplicativeDilation h value)
    (ContinuousLinearMap.lsmul ℝ ℝ) volume 0

theorem burnolReciprocalStepSmoothOrbit_integrable (pulse : ContDiffBump (0 : ℝ)) (value : BurnolL2) :
    Integrable (fun h : ℝ => pulse.normed volume h • burnolMultiplicativeDilation (-h) value) := by
  have continuousOrbit : Continuous (fun h : ℝ => burnolMultiplicativeDilation (-h) value) :=
    (burnolMultiplicativeDilation_stronglyContinuous value).comp continuous_neg
  apply (pulse.integrable_normed.norm.mul_const ‖value‖).mono'
    (pulse.continuous_normed.smul continuousOrbit).aestronglyMeasurable
  filter_upwards with h
  change ‖pulse.normed volume h • burnolMultiplicativeDilation (-h) value‖ ≤
    ‖pulse.normed volume h‖ * ‖value‖
  rw [norm_smul, (burnolMultiplicativeDilation (-h)).norm_map]

theorem burnolReciprocalStepSmoothedValue_integral (pulse : ContDiffBump (0 : ℝ)) (value : BurnolL2) :
    burnolReciprocalStepSmoothedValue pulse value =
      ∫ h : ℝ, pulse.normed volume h • burnolMultiplicativeDilation (-h) value := by
  simp only [burnolReciprocalStepSmoothedValue, MeasureTheory.convolution_def,
    ContinuousLinearMap.lsmul_apply, zero_sub]

private def rawOrbit (pulse : ContDiffBump (0 : ℝ)) (raw : ℝ → ℂ) (point : ℝ × ℝ) : ℂ :=
  (pulse.normed volume point.1 : ℂ) *
    ((Real.exp (-point.1 / 2) : ℂ) * raw (Real.exp (-point.1) * point.2))

private theorem rawOrbit_measurable (pulse : ContDiffBump (0 : ℝ))
    (raw : ℝ → ℂ) (measured : Measurable raw) : Measurable (rawOrbit pulse raw) := by
  have source : Measurable (fun point : ℝ × ℝ => raw (Real.exp (-point.1) * point.2)) :=
    measured.comp (by fun_prop)
  have pulseMeasurable : Measurable (fun point : ℝ × ℝ => (pulse.normed volume point.1 : ℂ)) :=
    Complex.measurable_ofReal.comp (pulse.continuous_normed.measurable.comp measurable_fst)
  exact pulseMeasurable.mul ((by fun_prop : Measurable (fun point : ℝ × ℝ =>
    (Real.exp (-point.1 / 2) : ℂ))).mul source)

private theorem rawOrbit_read (pulse : ContDiffBump (0 : ℝ))
    (source : BurnolL2) (raw : ℝ → ℂ) (rawRead : source =ᵐ[volume] raw) (h : ℝ) :
    (pulse.normed volume h • burnolMultiplicativeDilation (-h) source : BurnolL2) =ᵐ[volume]
      fun x : ℝ => rawOrbit pulse raw (h, x) := by
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp (-h) * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp (-h)) (Real.exp_ne_zero _))
  filter_upwards [qmp.ae rawRead, burnolMultiplicativeDilation_coeFn (-h) source,
    Lp.coeFn_smul (pulse.normed volume h) (burnolMultiplicativeDilation (-h) source)]
      with x sourceAt dilationAt smulAt
  rw [smulAt]
  change (pulse.normed volume h : ℂ) * burnolMultiplicativeDilation (-h) source x = _
  rw [dilationAt]
  unfold burnolL2RawNormalizedDilation rawOrbit
  rw [sourceAt]

theorem burnolReciprocalStepSmoothedSource_toLp (pulse : ContDiffBump (0 : ℝ)) (lower upper : ℝ)
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper) :
    (burnolReciprocalStepSmoothedSource pulse lower upper).toLp 2 volume =
      burnolReciprocalStepSmoothedValue pulse (burnolReciprocalStepSourceL2 lower upper lowerPositive ordered) := by
  let source := burnolReciprocalStepSourceL2 lower upper lowerPositive ordered
  have rawRead : (source : ℝ → ℂ) =ᵐ[volume] burnolReciprocalStepSourceRaw lower upper :=
    (burnolReciprocalStepSource_memLp lower upper lowerPositive ordered).coeFn_toLp
  apply ext_inner_left ℂ
  intro test
  have native := burnolL2Bochner_pairing_raw volume
    (fun h : ℝ => pulse.normed volume h • burnolMultiplicativeDilation (-h) source)
    (burnolReciprocalStepSmoothOrbit_integrable pulse source)
    (rawOrbit pulse (burnolReciprocalStepSourceRaw lower upper))
    (rawOrbit_measurable pulse _ (burnolReciprocalStepSource_measurable lower upper))
    (ae_of_all volume fun h => rawOrbit_read pulse source _ rawRead h) test
  rw [burnolReciprocalStepSmoothedValue_integral, native.2, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(burnolReciprocalStepSmoothedSource pulse lower upper).coeFn_toLp 2 volume] with x smoothAt
  rw [smoothAt]
  change inner ℂ (test x) (burnolReciprocalStepSmoothSourceRaw pulse lower upper x) = _
  rw [burnolReciprocalStepSmoothSource_rawOrbit pulse lower upper x lowerPositive (lowerPositive.trans_le ordered)]
  rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
