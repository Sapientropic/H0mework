import H0mework.Versions.Y.Arithmetic.RieszColumns.Support
import H0mework.Versions.Y.Arithmetic.RieszFiniteSource.Bochner

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteColumns

open Complex MeasureTheory Set
open OriginalPaPhysicalGreen OriginalRieszFiniteSource
noncomputable section

local notation "q" => (1 / 4 : ℝ)

theorem intervalDilation_cutoff_self (value : BurnolQuarterIntervalL2) (shift radius : ℝ)
    (covers : q * Real.exp (-shift) ≤ radius) :
    originalPhysicalCutoff radius
      (burnolMultiplicativeDilation shift (burnolQuarterZeroExtension value)) =
      burnolMultiplicativeDilation shift (burnolQuarterZeroExtension value) := by
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp shift) (Real.exp_ne_zero shift))
  apply cutoff_eq_self_of_ae_zero
  filter_upwards [burnolMultiplicativeDilation_coeFn shift (burnolQuarterZeroExtension value),
    qmp.ae (burnolRadiusZeroExtension_coe value)] with x dilation extension
  intro outside
  have sourceOutside : Real.exp shift * x ∉ symmetricInterval q := by
    intro inside
    have sourceBound : |Real.exp shift * x| ≤ q :=
      abs_le.mpr (by simpa only [symmetricInterval, mem_Icc] using inside)
    have targetBound : |x| ≤ radius := by
      calc
        |x| = Real.exp (-shift) * |Real.exp shift * x| := by
          rw [abs_mul, abs_of_pos (Real.exp_pos shift), ← mul_assoc, ← Real.exp_add,
            neg_add_cancel, Real.exp_zero, one_mul]
        _ ≤ Real.exp (-shift) * q :=
          mul_le_mul_of_nonneg_left sourceBound (Real.exp_pos (-shift)).le
        _ ≤ radius := by simpa only [mul_comm] using covers
    exact outside (by simpa only [symmetricInterval, mem_Icc] using abs_le.mp targetBound)
  rw [dilation]
  unfold burnolL2RawNormalizedDilation
  change _ * burnolRadiusZeroExtension q value (Real.exp shift * x) = 0
  rw [extension, Set.indicator_of_notMem sourceOutside, mul_zero]

private theorem time_bounds {endpoint time : ℝ} (inside : time ∈ Set.uIcc 0 endpoint) :
    -|endpoint| ≤ time ∧ time ≤ |endpoint| := by
  exact ⟨(le_min (neg_nonpos.mpr (abs_nonneg endpoint)) (neg_abs_le endpoint)).trans inside.1,
    inside.2.trans (max_le (abs_nonneg endpoint) (le_abs_self endpoint))⟩

theorem nativeIntegral_interval_cutoff_self (lambda : ℂ) (value : BurnolQuarterIntervalL2)
    (endpoint : ℝ) :
    originalPhysicalCutoff (q * Real.exp |endpoint|)
      (nativeIntegral lambda (burnolQuarterZeroExtension value) endpoint) =
      nativeIntegral lambda (burnolQuarterZeroExtension value) endpoint := by
  apply intervalIntegral_cutoff_self _ _ _ _ (nativeIntegrand_integrable _ _ _)
  intro time inside
  apply cutoff_smul_self
  apply intervalDilation_cutoff_self
  have lower := (time_bounds inside).1
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

def backwardIntegrand (lambda : ℂ) (value : BurnolL2) (endpoint time : ℝ) : BurnolL2 :=
  Complex.exp (-lambda * ((endpoint : ℂ) - (time : ℂ))) • burnolMultiplicativeDilation (-time) value

theorem backwardIntegrand_continuous (lambda : ℂ) (value : BurnolL2) (endpoint : ℝ) :
    Continuous (backwardIntegrand lambda value endpoint) := by
  have weight : Continuous (fun time : ℝ =>
      Complex.exp (-lambda * ((endpoint : ℂ) - (time : ℂ)))) :=
    (continuous_const.mul (continuous_const.sub Complex.continuous_ofReal)).cexp
  exact weight.smul ((burnolMultiplicativeDilation_stronglyContinuous value).comp continuous_neg)

def backwardIntegral (lambda : ℂ) (value : BurnolL2) (endpoint : ℝ) : BurnolL2 :=
  ∫ time : ℝ in (0 : ℝ)..endpoint, backwardIntegrand lambda value endpoint time

theorem backwardIntegral_interval_cutoff_self (lambda : ℂ) (value : BurnolQuarterIntervalL2)
    (endpoint : ℝ) :
    originalPhysicalCutoff (q * Real.exp |endpoint|)
      (backwardIntegral lambda (burnolQuarterZeroExtension value) endpoint) =
      backwardIntegral lambda (burnolQuarterZeroExtension value) endpoint := by
  apply intervalIntegral_cutoff_self _ _ _ _
    ((backwardIntegrand_continuous _ _ _).intervalIntegrable (μ := volume) 0 endpoint)
  intro time inside
  apply cutoff_smul_self
  apply intervalDilation_cutoff_self
  simp only [neg_neg]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (time_bounds inside).2) (by norm_num)

theorem fourier_backwardIntegral (lambda : ℂ) (value : BurnolL2) (endpoint : ℝ) :
    fourierL2 (backwardIntegral lambda value endpoint) =
      nativeIntegral lambda (fourierL2 value) endpoint := by
  have mapped := fourierL2.toLinearIsometry.intervalIntegral_comp_comm
    (μ := volume) (a := (0 : ℝ)) (b := endpoint) (backwardIntegrand lambda value endpoint)
  change (∫ time : ℝ in (0 : ℝ)..endpoint,
    fourierL2 (backwardIntegrand lambda value endpoint time)) =
    fourierL2 (∫ time : ℝ in (0 : ℝ)..endpoint, backwardIntegrand lambda value endpoint time) at mapped
  unfold backwardIntegral nativeIntegral
  rw [← mapped]
  apply intervalIntegral.integral_congr
  intro time _
  dsimp only [backwardIntegrand, nativeIntegrand]
  rw [map_smul, fourierL2_burnolMultiplicativeDilation, neg_neg]

end
end OriginalRieszFiniteColumns
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
