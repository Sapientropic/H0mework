import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.Operator.ClozelBurnolRechartedCoordinateDerivative
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.Operator.ClozelBurnolRechartedKernelRemainder

/-! The scalar-kernel remainder integrated on the fixed unit L² window. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex Filter FourierTransform MeasureTheory Set Asymptotics
open scoped ENNReal InnerProductSpace Pointwise Topology

noncomputable section

attribute [local instance 1100] Module.complexToReal NormedSpace.complexToReal

local notation "μunit" =>
  (Measure.restrict (volume : Measure ℝ) (symmetricInterval 1))

local instance burnolIntegralUnitFiniteMeasure : IsFiniteMeasure μunit where
  measure_univ_lt_top := by
    exact lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top 1)

local instance burnolIntegralUnitRealNormedSpace :
    NormedSpace ℝ BurnolUnitIntervalL2 :=
  NormedSpace.restrictScalars ℝ ℂ BurnolUnitIntervalL2

private theorem burnolRadiusRechartedTruncatedFourierRaw_eq_kernelIntegral
    (radius : ℝ) (state : BurnolUnitIntervalL2) (x : ℝ) :
    burnolRadiusRechartedTruncatedFourierRaw radius state x =
      ∫ y : ℝ, burnolUnitRechartedKernel radius x y * state y ∂μunit := by
  unfold burnolRadiusRechartedTruncatedFourierRaw
  rw [Real.vector_fourierIntegral_eq_integral_exp_smul]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with y
  unfold burnolUnitRechartedKernel
  simp only [smul_eq_mul, LinearMap.smul_apply, innerₗ_apply_apply,
    Real.inner_apply]
  push_cast
  ring_nf

private theorem burnolRadiusRechartedFirstVariationRaw_eq_kernelIntegral
    (radius : ℝ) (state : BurnolUnitIntervalL2) (x : ℝ) :
    burnolRadiusRechartedFirstVariationRaw radius state x =
      ∫ y : ℝ,
        burnolUnitRechartedKernelDerivative radius x y * state y ∂μunit := by
  let phase : ℝ → ℂ := fun y => Complex.exp
    (-2 * (Real.pi : ℂ) * Complex.I * (radius : ℂ) ^ 2 *
      (x : ℂ) * (y : ℂ))
  let momentIntegrand : ℝ → ℂ := fun y =>
    phase y * ((-2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) * state y)
  have phaseNorm (y : ℝ) : ‖phase y‖ = 1 := by
    exact burnolKernel_base_exp_norm radius x y
  have fourierRead :
      burnolUnitFourierRaw state (radius ^ 2 * x) =
        ∫ y : ℝ, phase y * state y ∂μunit := by
    unfold burnolUnitFourierRaw
    rw [Real.vector_fourierIntegral_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    dsimp only [phase]
    simp only [smul_eq_mul, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
      innerSL_apply_apply, Real.inner_apply]
    push_cast
    ring_nf
  have momentRead :
      burnolUnitFourierMomentRaw state (radius ^ 2 * x) =
        ∫ y : ℝ, momentIntegrand y ∂μunit := by
    rw [burnolUnitFourierMomentRaw_eq_integral]
    rw [Real.vector_fourierIntegral_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    dsimp only [momentIntegrand, phase]
    simp only [smul_eq_mul, innerₗ_apply_apply, Real.inner_apply]
    push_cast
    ring_nf
  have phaseStateIntegrable :
      Integrable (fun y : ℝ => phase y * state y) μunit :=
    (burnolUnitState_integrable state).bdd_mul (c := 1)
      (by fun_prop) (Filter.Eventually.of_forall fun y => by rw [phaseNorm])
  have momentIntegrable : Integrable momentIntegrand μunit := by
    have generated : Integrable
        (fun y : ℝ =>
          (phase y * (-2 * (Real.pi : ℂ) * Complex.I * (y : ℂ))) * state y)
        μunit := by
      apply (burnolUnitState_integrable state).bdd_mul (c := 2 * Real.pi)
        (by fun_prop)
      filter_upwards [burnolUnitInterval_norm_le_one] with y hy
      rw [norm_mul, phaseNorm, one_mul, norm_mul, norm_mul, norm_mul,
        norm_neg, norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      calc
        2 * Real.pi * |y| ≤ 2 * Real.pi * 1 := by
          gcongr
          simpa only [Real.norm_eq_abs] using hy
        _ = 2 * Real.pi := mul_one _
    simpa only [momentIntegrand, mul_assoc] using generated
  have scaledMomentIntegrable : Integrable
      (fun y : ℝ =>
        ((radius : ℂ) * ((2 * radius * x : ℝ) : ℂ)) * momentIntegrand y)
      μunit :=
    momentIntegrable.const_mul
      ((radius : ℂ) * ((2 * radius * x : ℝ) : ℂ))
  rw [burnolRadiusRechartedFirstVariationRaw, fourierRead, momentRead]
  simp only [real_smul]
  rw [← mul_assoc, ← integral_const_mul,
    ← integral_add scaledMomentIntegrable phaseStateIntegrable]
  apply integral_congr_ae
  filter_upwards with y
  unfold burnolUnitRechartedKernelDerivative
  dsimp only [momentIntegrand, phase]
  push_cast
  ring

private theorem burnolUnitRechartedKernel_mul_integrable
    (radius x : ℝ) (state : BurnolUnitIntervalL2) :
    Integrable (fun y : ℝ => burnolUnitRechartedKernel radius x y * state y)
      μunit := by
  apply (burnolUnitState_integrable state).bdd_mul (c := |radius|)
    (by unfold burnolUnitRechartedKernel; fun_prop)
  filter_upwards with y
  unfold burnolUnitRechartedKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    burnolKernel_base_exp_norm, mul_one]

private theorem burnolUnitRechartedKernelDerivative_mul_integrable
    {radius x : ℝ} (hx : |x| ≤ 1) (state : BurnolUnitIntervalL2) :
    Integrable
      (fun y : ℝ => burnolUnitRechartedKernelDerivative radius x y * state y)
      μunit := by
  apply (burnolUnitState_integrable state).bdd_mul
    (c := 1 + 4 * Real.pi * |radius| ^ 2)
    (by unfold burnolUnitRechartedKernelDerivative; fun_prop)
  filter_upwards [burnolUnitInterval_norm_le_one] with y hy
  unfold burnolUnitRechartedKernelDerivative
  rw [norm_mul, burnolKernel_base_exp_norm, one_mul]
  calc
    ‖(1 : ℂ) - 4 * (Real.pi : ℂ) * Complex.I * (radius : ℂ) ^ 2 *
        (x : ℂ) * (y : ℂ)‖ ≤
        1 + ‖4 * (Real.pi : ℂ) * Complex.I * (radius : ℂ) ^ 2 *
          (x : ℂ) * (y : ℂ)‖ := by
      simpa only [norm_one] using norm_sub_le (1 : ℂ)
        (4 * (Real.pi : ℂ) * Complex.I * (radius : ℂ) ^ 2 *
          (x : ℂ) * (y : ℂ))
    _ ≤ 1 + 4 * Real.pi * |radius| ^ 2 := by
      simp only [norm_mul, norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, norm_I, mul_one, norm_pow]
      have core :
        4 * Real.pi * |radius| ^ 2 * |x| * |y| ≤
            4 * Real.pi * |radius| ^ 2 * 1 * 1 := by
        have factorNonnegative : 0 ≤ 4 * Real.pi * |radius| ^ 2 := by positivity
        calc
          4 * Real.pi * |radius| ^ 2 * |x| * |y| ≤
              4 * Real.pi * |radius| ^ 2 * 1 * |y| := by
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg y)
            exact mul_le_mul_of_nonneg_left hx factorNonnegative
          _ ≤ 4 * Real.pi * |radius| ^ 2 * 1 * 1 := by
            apply mul_le_mul_of_nonneg_left _
              (mul_nonneg factorNonnegative zero_le_one)
            simpa only [Real.norm_eq_abs] using hy
      have core' :
          4 * Real.pi * |radius| ^ 2 * |x| * |y| ≤
            4 * Real.pi * |radius| ^ 2 := by
        calc
          _ ≤ 4 * Real.pi * |radius| ^ 2 * 1 * 1 := core
          _ = 4 * Real.pi * |radius| ^ 2 := by ring
      nlinarith

private theorem burnolRadiusRechartedRaw_remainder_eq_integral
    {radius h x : ℝ} (hx : |x| ≤ 1) (state : BurnolUnitIntervalL2) :
    burnolRadiusRechartedTruncatedFourierRaw (radius + h) state x -
        burnolRadiusRechartedTruncatedFourierRaw radius state x -
        (h : ℂ) * burnolRadiusRechartedFirstVariationRaw radius state x =
      ∫ y : ℝ,
        (burnolUnitRechartedKernel (radius + h) x y -
            burnolUnitRechartedKernel radius x y -
            (h : ℂ) * burnolUnitRechartedKernelDerivative radius x y) * state y
        ∂μunit := by
  rw [burnolRadiusRechartedTruncatedFourierRaw_eq_kernelIntegral,
    burnolRadiusRechartedTruncatedFourierRaw_eq_kernelIntegral,
    burnolRadiusRechartedFirstVariationRaw_eq_kernelIntegral]
  have plusIntegrable :=
    burnolUnitRechartedKernel_mul_integrable (radius + h) x state
  have baseIntegrable := burnolUnitRechartedKernel_mul_integrable radius x state
  have derivativeIntegrable :=
    burnolUnitRechartedKernelDerivative_mul_integrable
      (radius := radius) hx state
  rw [← integral_sub plusIntegrable baseIntegrable, ← integral_const_mul]
  have differenceIntegrable : Integrable
      (fun y : ℝ =>
        burnolUnitRechartedKernel (radius + h) x y * state y -
          burnolUnitRechartedKernel radius x y * state y) μunit := by
    exact (plusIntegrable.sub baseIntegrable).congr
      (Filter.Eventually.of_forall fun y => rfl)
  have scaledDerivativeIntegrable : Integrable
      (fun y : ℝ =>
        (h : ℂ) * (burnolUnitRechartedKernelDerivative radius x y * state y))
      μunit := derivativeIntegrable.const_mul (h : ℂ)
  rw [← integral_sub differenceIntegrable scaledDerivativeIntegrable]
  apply integral_congr_ae
  filter_upwards with y
  ring

theorem burnolRadiusRechartedRaw_remainder_norm_le
    {radius h x : ℝ}
    (hh : |h| < burnolKernelVariationRadius radius)
    (hx : |x| ≤ 1) (state : BurnolUnitIntervalL2) :
    ‖burnolRadiusRechartedTruncatedFourierRaw (radius + h) state x -
        burnolRadiusRechartedTruncatedFourierRaw radius state x -
        (h : ℂ) * burnolRadiusRechartedFirstVariationRaw radius state x‖ ≤
      (burnolKernelRemainderBound radius * |h| ^ 2) *
        (Real.sqrt 2 * ‖state‖) := by
  rw [burnolRadiusRechartedRaw_remainder_eq_integral hx state]
  let C : ℝ := burnolKernelRemainderBound radius * |h| ^ 2
  have CNonnegative : 0 ≤ C := mul_nonneg
    (burnolKernelRemainderBound_nonnegative radius) (sq_nonneg |h|)
  have remainderIntegrable : Integrable
      (fun y : ℝ =>
        (burnolUnitRechartedKernel (radius + h) x y -
            burnolUnitRechartedKernel radius x y -
            (h : ℂ) * burnolUnitRechartedKernelDerivative radius x y) * state y)
      μunit := by
    have generated := ((burnolUnitRechartedKernel_mul_integrable
        (radius + h) x state).sub
      (burnolUnitRechartedKernel_mul_integrable radius x state)).sub
      ((burnolUnitRechartedKernelDerivative_mul_integrable
        (radius := radius) hx state).const_mul (h : ℂ))
    exact generated.congr (Filter.Eventually.of_forall fun y => by
      simp only [Pi.sub_apply]
      ring)
  have majorantIntegrable : Integrable (fun y : ℝ => C * ‖state y‖) μunit :=
    (burnolUnitState_integrable state).norm.const_mul C
  calc
    ‖∫ y : ℝ,
        (burnolUnitRechartedKernel (radius + h) x y -
            burnolUnitRechartedKernel radius x y -
            (h : ℂ) * burnolUnitRechartedKernelDerivative radius x y) * state y
        ∂μunit‖ ≤
        ∫ y : ℝ,
          ‖(burnolUnitRechartedKernel (radius + h) x y -
              burnolUnitRechartedKernel radius x y -
              (h : ℂ) * burnolUnitRechartedKernelDerivative radius x y) * state y‖
          ∂μunit := norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, C * ‖state y‖ ∂μunit := by
      apply integral_mono_ae remainderIntegrable.norm majorantIntegrable
      filter_upwards [burnolUnitInterval_norm_le_one] with y hy
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg (state y))
      exact burnolUnitRechartedKernel_remainder_norm_le hh hx
        (by simpa only [Real.norm_eq_abs] using hy)
    _ = C * ∫ y : ℝ, ‖state y‖ ∂μunit := integral_const_mul C _
    _ ≤ C * (Real.sqrt 2 * ‖state‖) := by
      gcongr
      simpa only [one_mul, mul_one] using
        (burnolRadiusInterval_integral_norm_le (radius := 1) zero_lt_one state)
    _ = (burnolKernelRemainderBound radius * |h| ^ 2) *
        (Real.sqrt 2 * ‖state‖) := rfl


end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
