import H0mework.Arithmetic.TruncatedFourier.ConjugatedKernel
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace Pointwise

noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

local instance burnolUnitVariationFiniteMeasure :
    IsFiniteMeasure ((volume : Measure ℝ).restrict (symmetricInterval 1)) where
  measure_univ_lt_top := by
    exact lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top 1)

def burnolUnitFourierRaw
    (state : BurnolUnitIntervalL2) (frequency : ℝ) : ℂ :=
  VectorFourier.fourierIntegral 𝐞
    ((volume : Measure ℝ).restrict (symmetricInterval 1))
    (innerSL ℝ).toLinearMap₁₂ (state : ℝ → ℂ) frequency

def burnolUnitFourierMomentRaw
    (state : BurnolUnitIntervalL2) (frequency : ℝ) : ℂ :=
  (VectorFourier.fourierIntegral 𝐞
    ((volume : Measure ℝ).restrict (symmetricInterval 1))
    (innerSL ℝ).toLinearMap₁₂
    (VectorFourier.fourierSMulRight (innerSL ℝ) (state : ℝ → ℂ))
    frequency) 1

theorem burnolUnitState_integrable (state : BurnolUnitIntervalL2) :
    Integrable (state : ℝ → ℂ)
      ((volume : Measure ℝ).restrict (symmetricInterval 1)) :=
  (Lp.memLp state).integrable (by norm_num)

theorem burnolUnitInterval_norm_le_one :
    ∀ᵐ y ∂((volume : Measure ℝ).restrict (symmetricInterval 1)), ‖y‖ ≤ 1 := by
  apply (ae_restrict_iff' (measurableSet_symmetricInterval 1)).mpr
  filter_upwards with y hy
  simpa [symmetricInterval, Real.norm_eq_abs, abs_le] using hy

theorem burnolUnitState_normMoment_integrable
    (state : BurnolUnitIntervalL2) :
    Integrable (fun y : ℝ ↦ ‖y‖ * ‖state y‖)
      ((volume : Measure ℝ).restrict (symmetricInterval 1)) := by
  apply (burnolUnitState_integrable state).norm.mono'
  · fun_prop
  · filter_upwards [burnolUnitInterval_norm_le_one] with y hy
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    calc
      ‖y‖ * ‖state y‖ ≤ 1 * ‖state y‖ :=
        mul_le_mul_of_nonneg_right hy (norm_nonneg _)
      _ = ‖state y‖ := one_mul _

theorem burnolUnitFourierSMulRight_integrable
    (state : BurnolUnitIntervalL2) :
    Integrable
      (VectorFourier.fourierSMulRight (innerSL ℝ) (state : ℝ → ℂ))
      ((volume : Measure ℝ).restrict (symmetricInterval 1)) := by
  have majorant := (burnolUnitState_normMoment_integrable state).const_mul
    (2 * Real.pi * ‖innerSL (E := ℝ) ℝ‖)
  apply majorant.mono'
  · exact (Lp.memLp state).aestronglyMeasurable.fourierSMulRight
  · filter_upwards with y
    simpa only [mul_assoc] using
      VectorFourier.norm_fourierSMulRight_le
        (innerSL (E := ℝ) ℝ) (state : ℝ → ℂ) y

theorem burnolUnitFourierMomentRaw_eq_integral
    (state : BurnolUnitIntervalL2) (frequency : ℝ) :
    burnolUnitFourierMomentRaw state frequency =
      VectorFourier.fourierIntegral 𝐞
        ((volume : Measure ℝ).restrict (symmetricInterval 1))
        (innerₗ ℝ)
        (fun y : ℝ ↦ (-2 * (Real.pi : ℂ) * Complex.I * y) • state y)
        frequency := by
  unfold burnolUnitFourierMomentRaw
  rw [Real.fourierIntegral_continuousLinearMap_apply'
    (burnolUnitFourierSMulRight_integrable state)]
  unfold VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards with y
  simp only [VectorFourier.fourierSMulRight_apply,
    ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
    innerₗ_apply_apply, neg_smul]
  have innerRead : (innerSL ℝ) y 1 = y := by
    rw [innerSL_apply_apply, Real.inner_apply, mul_one]
  rw [innerRead]
  simp only [real_smul]
  congr 2
  ring

theorem burnolUnitFourierRaw_hasDerivAt
    (state : BurnolUnitIntervalL2) (frequency : ℝ) :
    HasDerivAt (burnolUnitFourierRaw state)
      (burnolUnitFourierMomentRaw state frequency) frequency := by
  have source := VectorFourier.hasFDerivAt_fourierIntegral
    (innerSL ℝ) (burnolUnitState_integrable state)
    (burnolUnitState_normMoment_integrable state) frequency
  unfold burnolUnitFourierRaw burnolUnitFourierMomentRaw
  convert source.hasDerivAt using 1

theorem burnolRadiusRechartedTruncatedFourierRaw_eq_frequencyChart
    (radius : ℝ) (state : BurnolUnitIntervalL2) (x : ℝ) :
    burnolRadiusRechartedTruncatedFourierRaw radius state x =
      radius • burnolUnitFourierRaw state (radius ^ 2 * x) := by
  unfold burnolRadiusRechartedTruncatedFourierRaw burnolUnitFourierRaw
  simp only [real_smul]
  congr 1
  unfold VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards with y
  congr 2
  simp only [LinearMap.smul_apply, smul_eq_mul, innerₗ_apply_apply,
    ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
    innerSL_apply_apply]
  conv_rhs => rw [← smul_eq_mul, real_inner_smul_right]

def burnolRadiusRechartedFirstVariationRaw
    (radius : ℝ) (state : BurnolUnitIntervalL2) (x : ℝ) : ℂ :=
  radius • ((2 * radius * x) •
      burnolUnitFourierMomentRaw state (radius ^ 2 * x)) +
    burnolUnitFourierRaw state (radius ^ 2 * x)

theorem burnolRadiusRechartedTruncatedFourierRaw_hasDerivAt
    (radius : ℝ) (state : BurnolUnitIntervalL2) (x : ℝ) :
    HasDerivAt
      (fun r : ℝ ↦ burnolRadiusRechartedTruncatedFourierRaw r state x)
      (burnolRadiusRechartedFirstVariationRaw radius state x) radius := by
  have frequencyDerivative :
      HasDerivAt (fun r : ℝ ↦ r ^ 2 * x) (2 * radius * x) radius := by
    simpa [mul_assoc] using (hasDerivAt_pow 2 radius).mul_const x
  have baseDerivative :
      HasDerivAt (burnolUnitFourierRaw state)
        (burnolUnitFourierMomentRaw state (radius ^ 2 * x))
        (radius ^ 2 * x) :=
    burnolUnitFourierRaw_hasDerivAt state (radius ^ 2 * x)
  have transformedDerivative :
      HasDerivAt
        (fun r : ℝ ↦ burnolUnitFourierRaw state (r ^ 2 * x))
        ((2 * radius * x) •
          burnolUnitFourierMomentRaw state (radius ^ 2 * x)) radius :=
    by
      simpa only [Function.comp_apply] using!
        baseDerivative.scomp radius frequencyDerivative
  have source := (hasDerivAt_id radius).smul transformedDerivative
  have functionEq :
      (fun r : ℝ ↦ burnolRadiusRechartedTruncatedFourierRaw r state x) =
        fun r : ℝ ↦ r • burnolUnitFourierRaw state (r ^ 2 * x) := by
    funext r
    exact burnolRadiusRechartedTruncatedFourierRaw_eq_frequencyChart r state x
  rw [functionEq]
  simpa only [burnolRadiusRechartedFirstVariationRaw, Pi.smul_apply,
    id_eq, one_smul] using! source

theorem burnolRadiusRechartedTruncatedFourierRaw_differentiable
    (state : BurnolUnitIntervalL2) (x : ℝ) :
    Differentiable ℝ
      (fun radius : ℝ ↦
        burnolRadiusRechartedTruncatedFourierRaw radius state x) :=
  fun radius ↦
    (burnolRadiusRechartedTruncatedFourierRaw_hasDerivAt radius state x).differentiableAt

theorem burnolRadiusRechartedTruncatedFourierRaw_continuous
    (state : BurnolUnitIntervalL2) (x : ℝ) :
    Continuous
      (fun radius : ℝ ↦
        burnolRadiusRechartedTruncatedFourierRaw radius state x) :=
  (burnolRadiusRechartedTruncatedFourierRaw_differentiable state x).continuous

theorem burnolRadiusRechartedTruncatedFourier_sourceFirstVariation
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolUnitIntervalL2) :
    (burnolRadiusRechartedTruncatedFourier positive state : ℝ → ℂ) =ᵐ[
        (volume : Measure ℝ).restrict (symmetricInterval 1)]
      burnolRadiusRechartedTruncatedFourierRaw radius state ∧
    ∀ x : ℝ,
      HasDerivAt
        (fun r : ℝ ↦ burnolRadiusRechartedTruncatedFourierRaw r state x)
        (burnolRadiusRechartedFirstVariationRaw radius state x) radius :=
  ⟨burnolRadiusRechartedTruncatedFourier_coe positive state,
    fun x ↦ burnolRadiusRechartedTruncatedFourierRaw_hasDerivAt radius state x⟩

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
