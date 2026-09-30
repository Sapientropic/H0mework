import H0mework.Arithmetic.TruncatedFourier.ConjugatedKernel

/-! Actual two-window Fourier restrictions on the existing fixed unit-interval chart. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace Pointwise
noncomputable section

def burnolRectangularFourier (position frequency : ℝ) :
    BurnolRadiusIntervalL2 position →L[ℂ] BurnolRadiusIntervalL2 frequency :=
  (burnolRadiusRestriction frequency).comp
    (fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (burnolRadiusZeroExtension position))

def burnolRectangularRechartedFourier
    {position frequency : ℝ} (hp : 0 < position) (hf : 0 < frequency) :
    BurnolUnitIntervalL2 →L[ℂ] BurnolUnitIntervalL2 :=
  (burnolRadiusRechartEquiv hf).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((burnolRectangularFourier position frequency).comp
      (burnolRadiusRechartEquiv hp).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem burnolRectangularRechartedFourier_coe_scaled_raw
    {position frequency : ℝ} (hp : 0 < position) (hf : 0 < frequency)
    (state : BurnolUnitIntervalL2) :
    (burnolRectangularRechartedFourier hp hf state : ℝ → ℂ) =ᵐ[
      (volume : Measure ℝ).restrict (symmetricInterval 1)]
      fun x => (Real.sqrt frequency : ℂ) •
        burnolRadiusTruncatedFourierRaw position
          ((burnolRadiusRechartEquiv hp).symm state) (frequency * x) := by
  let localState := (burnolRadiusRechartEquiv hp).symm state
  let crossed := burnolRectangularFourier position frequency localState
  have rechart := burnolRadiusRechart_coe hf crossed
  have actual : (crossed : ℝ → ℂ) =ᵐ[
      (volume : Measure ℝ).restrict (symmetricInterval frequency)]
      burnolRadiusTruncatedFourierRaw position localState :=
    (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval frequency)
      (fourierL2 (burnolRadiusZeroExtension position localState))).trans
      (ae_restrict_of_ae (burnolRadiusFourierL2_zeroExtension_ae_eq_raw localState))
  have scaled :=
    (burnolRadiusScaleEquiv_measurePreserving hf).quasiMeasurePreserving.ae_eq
      (Measure.ae_smul_measure actual (ENNReal.ofReal frequency⁻¹))
  filter_upwards [rechart, scaled] with x hr ha
  change (burnolRadiusRechart hf crossed) x = _
  rw [hr]
  exact congrArg ((Real.sqrt frequency : ℂ) • ·)
    (by simpa only [burnolRadiusScaleMeasurableEquiv_apply, Function.comp_apply] using ha)

private theorem rectangular_sqrt_coefficient
    {position frequency : ℝ} (hp : 0 < position) (hf : 0 < frequency) :
    ((Real.sqrt frequency : ℂ) / (Real.sqrt position : ℂ)) * (position : ℂ) =
      (Real.sqrt (position * frequency) : ℂ) := by
  have realRead : Real.sqrt frequency / Real.sqrt position * position =
      Real.sqrt (position * frequency) := by
    rw [Real.sqrt_mul hp.le]
    field_simp
    nlinarith [Real.sq_sqrt hp.le]
  exact_mod_cast realRead

theorem burnolRectangular_scaled_raw_eq_geometric_mean
    {position frequency : ℝ} (hp : 0 < position) (hf : 0 < frequency)
    (state : BurnolUnitIntervalL2) (x : ℝ) :
    (Real.sqrt frequency : ℂ) •
        burnolRadiusTruncatedFourierRaw position
          ((burnolRadiusRechartEquiv hp).symm state) (frequency * x) =
      burnolRadiusRechartedTruncatedFourierRaw
        (Real.sqrt (position * frequency)) state x := by
  have rootNe : (Real.sqrt position : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hp).ne'
  have frequencyEq : position * (frequency / position * x) = frequency * x := by
    field_simp
  calc
    _ = ((Real.sqrt frequency : ℂ) / (Real.sqrt position : ℂ)) •
        ((Real.sqrt position : ℂ) •
          burnolRadiusTruncatedFourierRaw position
            ((burnolRadiusRechartEquiv hp).symm state)
            (position * (frequency / position * x))) := by
      rw [frequencyEq, smul_smul, div_mul_cancel₀ _ rootNe]
    _ = ((Real.sqrt frequency : ℂ) / (Real.sqrt position : ℂ)) •
        burnolRadiusRechartedTruncatedFourierRaw position state
          (frequency / position * x) := by
      rw [burnolRadius_scaled_raw_eq_recharted_raw hp state]
    _ = _ := by
      unfold burnolRadiusRechartedTruncatedFourierRaw
      rw [smul_smul, rectangular_sqrt_coefficient hp hf]
      congr 1
      unfold VectorFourier.fourierIntegral
      apply integral_congr_ae
      filter_upwards with y
      congr 2
      simp only [LinearMap.smul_apply, smul_eq_mul, innerₗ_apply_apply, Real.inner_apply]
      rw [Real.sq_sqrt (mul_pos hp hf).le]
      field_simp

theorem burnolRectangularRechartedFourier_eq_geometric_mean
    {position frequency : ℝ} (hp : 0 < position) (hf : 0 < frequency) :
    burnolRectangularRechartedFourier hp hf =
      burnolRadiusRechartedTruncatedFourier
        (Real.sqrt_pos.mpr (mul_pos hp hf)) := by
  apply ContinuousLinearMap.ext
  intro state
  apply Lp.ext
  filter_upwards [burnolRectangularRechartedFourier_coe_scaled_raw hp hf state,
    burnolRadiusRechartedTruncatedFourier_coe (Real.sqrt_pos.mpr (mul_pos hp hf)) state]
    with x left right
  rw [left, right]
  exact burnolRectangular_scaled_raw_eq_geometric_mean hp hf state x

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
