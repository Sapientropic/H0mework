import H0mework.Arithmetic.TruncatedFourier.RechartEquiv
import Mathlib.Algebra.Order.Field.Pointwise

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace Pointwise

noncomputable section

/-- The actual truncated Fourier operator, conjugated to the fixed unit interval. -/
def burnolRadiusRechartedTruncatedFourier
    {radius : ℝ} (positive : 0 < radius) :
    BurnolUnitIntervalL2 →L[ℂ] BurnolUnitIntervalL2 :=
  (burnolRadiusRechartEquiv positive).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((burnolRadiusTruncatedFourier radius).comp
      (burnolRadiusRechartEquiv positive).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The explicit fixed-chart kernel. Radius now occurs only in the scalar and phase. -/
def burnolRadiusRechartedTruncatedFourierRaw
    (radius : ℝ) (state : BurnolUnitIntervalL2) (x : ℝ) : ℂ :=
  (radius : ℂ) • VectorFourier.fourierIntegral 𝐞
    ((volume : Measure ℝ).restrict (symmetricInterval 1))
    ((radius ^ 2) • innerₗ ℝ) (state : ℝ → ℂ) x

theorem burnolRadius_smul_symmetricInterval
    {radius : ℝ} (positive : 0 < radius) :
    radius • symmetricInterval 1 = symmetricInterval radius := by
  unfold symmetricInterval
  rw [LinearOrderedField.smul_Icc positive]
  congr <;> ring

theorem burnolRadius_setIntegral_change
    {radius : ℝ} (positive : 0 < radius) (integrand : ℝ → ℂ) :
    (∫ y in symmetricInterval radius, integrand y) =
      (radius : ℂ) •
        ∫ z in symmetricInterval 1, integrand (radius * z) := by
  have changed := Measure.setIntegral_comp_smul_of_pos
    (μ := (volume : Measure ℝ)) integrand (symmetricInterval 1) positive
  have scaled := congrArg ((radius : ℂ) • ·) changed
  simp only [Module.finrank_self, pow_one, real_smul, smul_eq_mul,
    ← mul_assoc] at scaled
  have radiusComplexNe : (radius : ℂ) ≠ 0 := by
    exact_mod_cast positive.ne'
  rw [show ((radius⁻¹ : ℝ) : ℂ) = (radius : ℂ)⁻¹ by norm_cast] at scaled
  rw [mul_inv_cancel₀ radiusComplexNe, one_mul] at scaled
  have scaled' :
      (radius : ℂ) *
          (∫ z in symmetricInterval 1, integrand (radius * z)) =
        ∫ y in radius • symmetricInterval 1, integrand y := by
    exact scaled
  rw [burnolRadius_smul_symmetricInterval positive] at scaled'
  exact scaled'.symm

theorem burnolRadiusRechartedTruncatedFourier_coe_eq_scaled_raw
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolUnitIntervalL2) :
    (burnolRadiusRechartedTruncatedFourier positive state : ℝ → ℂ) =ᵐ[
        (volume : Measure ℝ).restrict (symmetricInterval 1)]
      fun x ↦ (Real.sqrt radius : ℂ) •
        burnolRadiusTruncatedFourierRaw radius
          ((burnolRadiusRechartEquiv positive).symm state) (radius * x) := by
  change (burnolRadiusRechart positive
      (burnolRadiusTruncatedFourier radius
        ((burnolRadiusRechartEquiv positive).symm state)) : ℝ → ℂ) =ᵐ[_] _
  have rechartRead := burnolRadiusRechart_coe positive
    (burnolRadiusTruncatedFourier radius
      ((burnolRadiusRechartEquiv positive).symm state))
  have actualEq := burnolRadiusTruncatedFourier_apply_eq_integral positive
    ((burnolRadiusRechartEquiv positive).symm state)
  have integralRead := MemLp.coeFn_toLp
    (burnolRadiusTruncatedFourierRaw_memLp positive
      ((burnolRadiusRechartEquiv positive).symm state))
  have actualRead :
      (burnolRadiusTruncatedFourier radius
          ((burnolRadiusRechartEquiv positive).symm state) : ℝ → ℂ) =ᵐ[
            (volume : Measure ℝ).restrict (symmetricInterval radius)]
        burnolRadiusTruncatedFourierRaw radius
          ((burnolRadiusRechartEquiv positive).symm state) := by
    rw [actualEq]
    exact integralRead
  have scaledActualRead :=
    (burnolRadiusScaleEquiv_measurePreserving positive).quasiMeasurePreserving.ae_eq
      (Measure.ae_smul_measure actualRead (ENNReal.ofReal radius⁻¹))
  filter_upwards [rechartRead, scaledActualRead]
      with x rechartAt actualAt
  rw [rechartAt]
  exact congrArg ((Real.sqrt radius : ℂ) • ·)
    (by simpa only [burnolRadiusScaleMeasurableEquiv_apply,
      Function.comp_apply] using actualAt)

theorem burnolRadius_scaled_raw_eq_recharted_raw
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolUnitIntervalL2) (x : ℝ) :
    (Real.sqrt radius : ℂ) •
        burnolRadiusTruncatedFourierRaw radius
          ((burnolRadiusRechartEquiv positive).symm state) (radius * x) =
      burnolRadiusRechartedTruncatedFourierRaw radius state x := by
  have inverseRead := burnolRadiusRechartEquiv_symm_coe positive state
  have congruent := VectorFourier.fourierIntegral_congr_ae 𝐞
    ((volume : Measure ℝ).restrict (symmetricInterval radius))
    (innerₗ ℝ) inverseRead
  unfold burnolRadiusTruncatedFourierRaw
  rw [congrFun congruent (radius * x)]
  have pullScalar := VectorFourier.fourierIntegral_const_smul 𝐞
    ((volume : Measure ℝ).restrict (symmetricInterval radius))
    (innerₗ ℝ) (fun y : ℝ ↦ state (radius⁻¹ * y))
    (Real.sqrt radius : ℂ)⁻¹
  have pullScalarAt :
      VectorFourier.fourierIntegral 𝐞
          ((volume : Measure ℝ).restrict (symmetricInterval radius))
          (innerₗ ℝ)
          (fun y : ℝ ↦ (Real.sqrt radius : ℂ)⁻¹ •
            state (radius⁻¹ * y)) (radius * x) =
        (Real.sqrt radius : ℂ)⁻¹ •
          VectorFourier.fourierIntegral 𝐞
            ((volume : Measure ℝ).restrict (symmetricInterval radius))
            (innerₗ ℝ) (fun y : ℝ ↦ state (radius⁻¹ * y))
            (radius * x) := by
    change VectorFourier.fourierIntegral 𝐞
        ((volume : Measure ℝ).restrict (symmetricInterval radius))
        (innerₗ ℝ)
        ((Real.sqrt radius : ℂ)⁻¹ •
          fun y : ℝ ↦ state (radius⁻¹ * y)) (radius * x) = _
    exact congrFun pullScalar (radius * x)
  rw [pullScalarAt]
  simp only [smul_smul]
  have rootComplexNe : (Real.sqrt radius : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 positive).ne'
  rw [mul_inv_cancel₀ rootComplexNe, one_smul]
  have changed := burnolRadius_setIntegral_change positive
    (fun y : ℝ ↦ 𝐞 (-((innerₗ ℝ) y (radius * x))) •
      state (radius⁻¹ * y))
  unfold burnolRadiusRechartedTruncatedFourierRaw
  simp only [VectorFourier.fourierIntegral]
  simp [smul_eq_mul, positive.ne'] at changed ⊢
  convert changed using 1
  ring_nf

theorem burnolRadiusRechartedTruncatedFourier_coe
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolUnitIntervalL2) :
    (burnolRadiusRechartedTruncatedFourier positive state : ℝ → ℂ) =ᵐ[
        (volume : Measure ℝ).restrict (symmetricInterval 1)]
      burnolRadiusRechartedTruncatedFourierRaw radius state := by
  filter_upwards [
    burnolRadiusRechartedTruncatedFourier_coe_eq_scaled_raw positive state]
      with x actualAt
  exact actualAt.trans
    (burnolRadius_scaled_raw_eq_recharted_raw positive state x)

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
