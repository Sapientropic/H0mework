import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.Operator.ClozelBurnolRechartedIntegralRemainder
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Operator-norm differentiability of the fixed-chart truncated Fourier family. -/

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

local instance burnolOperatorUnitFiniteMeasure : IsFiniteMeasure μunit where
  measure_univ_lt_top := by
    exact lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top 1)

local instance burnolOperatorUnitRealNormedSpace :
    NormedSpace ℝ BurnolUnitIntervalL2 :=
  NormedSpace.restrictScalars ℝ ℂ BurnolUnitIntervalL2

/-- The actual positive-radius operator, extended harmlessly outside its physical
domain so that its ordinary real derivative is a well-typed statement. -/
def burnolRechartedTruncatedFourierOperator (radius : ℝ) :
    BurnolUnitIntervalL2 →L[ℂ] BurnolUnitIntervalL2 :=
  if positive : 0 < radius then
    burnolRadiusRechartedTruncatedFourier positive
  else 0

theorem burnolRechartedTruncatedFourierOperator_of_pos
    {radius : ℝ} (positive : 0 < radius) :
    burnolRechartedTruncatedFourierOperator radius =
      burnolRadiusRechartedTruncatedFourier positive := by
  simp only [burnolRechartedTruncatedFourierOperator, dif_pos positive]

private theorem burnolRechartedTruncatedFourierOperator_remainder_coe
    {radius h : ℝ} (positive : 0 < radius) (shiftPositive : 0 < radius + h)
    (state : BurnolUnitIntervalL2) :
    (((burnolRechartedTruncatedFourierOperator (radius + h) -
          burnolRechartedTruncatedFourierOperator radius -
          h • burnolRadiusRechartedTruncatedFourierDerivative positive) state :
        BurnolUnitIntervalL2) : ℝ → ℂ) =ᵐ[μunit]
      fun x : ℝ =>
        burnolRadiusRechartedTruncatedFourierRaw (radius + h) state x -
          burnolRadiusRechartedTruncatedFourierRaw radius state x -
          (h : ℂ) * burnolRadiusRechartedFirstVariationRaw radius state x := by
  rw [burnolRechartedTruncatedFourierOperator_of_pos shiftPositive,
    burnolRechartedTruncatedFourierOperator_of_pos positive]
  change ((((burnolRadiusRechartedTruncatedFourier shiftPositive) state -
      (burnolRadiusRechartedTruncatedFourier positive) state -
      h • burnolRadiusRechartedTruncatedFourierDerivative positive state) :
      BurnolUnitIntervalL2) : ℝ → ℂ) =ᵐ[μunit] _
  filter_upwards [Lp.coeFn_sub
      ((burnolRadiusRechartedTruncatedFourier shiftPositive) state -
        (burnolRadiusRechartedTruncatedFourier positive) state)
      (h • burnolRadiusRechartedTruncatedFourierDerivative positive state),
    Lp.coeFn_sub
      ((burnolRadiusRechartedTruncatedFourier shiftPositive) state)
      ((burnolRadiusRechartedTruncatedFourier positive) state),
    Lp.coeFn_smul (h : ℂ)
      (burnolRadiusRechartedTruncatedFourierDerivative positive state),
    burnolRadiusRechartedTruncatedFourier_coe shiftPositive state,
    burnolRadiusRechartedTruncatedFourier_coe positive state,
    burnolRadiusRechartedTruncatedFourierDerivative_coe positive state]
      with x outerSub innerSub smulRead shiftRead baseRead derivativeRead
  rw [outerSub]
  simp only [Pi.sub_apply]
  rw [innerSub]
  simp only [Pi.sub_apply]
  change (((burnolRadiusRechartedTruncatedFourier shiftPositive) state :
        ℝ → ℂ) x -
      ((burnolRadiusRechartedTruncatedFourier positive) state : ℝ → ℂ) x) -
      (((h : ℂ) • burnolRadiusRechartedTruncatedFourierDerivative positive state :
        BurnolUnitIntervalL2) : ℝ → ℂ) x = _
  rw [smulRead]
  simp only [Pi.smul_apply]
  rw [shiftRead, baseRead, derivativeRead]
  simp only [smul_eq_mul]

private def burnolUnitLpPointwiseFactor : ℝ :=
  ↑(measureUnivNNReal μunit ^ (2 : ℝ≥0∞).toReal⁻¹)

private theorem burnolUnitLpPointwiseFactor_nonnegative :
    0 ≤ burnolUnitLpPointwiseFactor := by
  unfold burnolUnitLpPointwiseFactor
  positivity

private def burnolRechartedOperatorRemainderBound (radius : ℝ) : ℝ :=
  burnolUnitLpPointwiseFactor * burnolKernelRemainderBound radius * Real.sqrt 2

private theorem burnolRechartedOperatorRemainderBound_nonnegative (radius : ℝ) :
    0 ≤ burnolRechartedOperatorRemainderBound radius := by
  unfold burnolRechartedOperatorRemainderBound
  exact mul_nonneg
    (mul_nonneg burnolUnitLpPointwiseFactor_nonnegative
      (burnolKernelRemainderBound_nonnegative radius)) (Real.sqrt_nonneg 2)

private theorem burnolRechartedTruncatedFourierOperator_remainder_norm_le
    {radius h : ℝ} (positive : 0 < radius) (shiftPositive : 0 < radius + h)
    (hh : |h| < burnolKernelVariationRadius radius) :
    ‖burnolRechartedTruncatedFourierOperator (radius + h) -
        burnolRechartedTruncatedFourierOperator radius -
        h • burnolRadiusRechartedTruncatedFourierDerivative positive‖ ≤
      burnolRechartedOperatorRemainderBound radius * |h| ^ 2 := by
  let R := burnolRechartedTruncatedFourierOperator (radius + h) -
    burnolRechartedTruncatedFourierOperator radius -
    h • burnolRadiusRechartedTruncatedFourierDerivative positive
  have boundNonnegative :
      0 ≤ burnolRechartedOperatorRemainderBound radius * |h| ^ 2 :=
    mul_nonneg (burnolRechartedOperatorRemainderBound_nonnegative radius)
      (sq_nonneg |h|)
  apply ContinuousLinearMap.opNorm_le_bound R boundNonnegative
  intro state
  have pointwiseNonnegative :
      0 ≤ (burnolKernelRemainderBound radius * |h| ^ 2) *
        (Real.sqrt 2 * ‖state‖) :=
    mul_nonneg
      (mul_nonneg (burnolKernelRemainderBound_nonnegative radius)
        (sq_nonneg |h|))
      (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg state))
  have lpBound : ‖R state‖ ≤
      burnolUnitLpPointwiseFactor *
        ((burnolKernelRemainderBound radius * |h| ^ 2) *
          (Real.sqrt 2 * ‖state‖)) := by
    apply Lp.norm_le_of_ae_bound pointwiseNonnegative
    filter_upwards [burnolRechartedTruncatedFourierOperator_remainder_coe
        positive shiftPositive state,
      burnolUnitInterval_norm_le_one] with x remainderRead hx
    rw [remainderRead]
    exact burnolRadiusRechartedRaw_remainder_norm_le hh
      (by simpa only [Real.norm_eq_abs] using hx) state
  calc
    ‖R state‖ ≤ burnolUnitLpPointwiseFactor *
        ((burnolKernelRemainderBound radius * |h| ^ 2) *
          (Real.sqrt 2 * ‖state‖)) := lpBound
    _ = (burnolRechartedOperatorRemainderBound radius * |h| ^ 2) *
        ‖state‖ := by
      unfold burnolRechartedOperatorRemainderBound
      ring

/-- On every positive radius, the actual fixed-chart truncated Fourier operator
is differentiable in operator norm.  Its derivative is the source-generated
complex-linear operator `(1/r) T_r - 4π i r X T_r X`. -/
theorem burnolRechartedTruncatedFourierOperator_hasDerivAt
    {radius : ℝ} (positive : 0 < radius) :
    HasDerivAt burnolRechartedTruncatedFourierOperator
      (burnolRadiusRechartedTruncatedFourierDerivative positive) radius := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  apply isLittleO_iff.mpr
  intro c cPositive
  let B := burnolRechartedOperatorRemainderBound radius
  have BNonnegative : 0 ≤ B :=
    burnolRechartedOperatorRemainderBound_nonnegative radius
  have denominatorPositive : 0 < B + 1 := by linarith
  let δ := min (burnolKernelVariationRadius radius)
    (min radius (c / (B + 1)))
  have δPositive : 0 < δ := by
    dsimp only [δ]
    exact lt_min (burnolKernelVariationRadius_pos radius)
      (lt_min positive (div_pos cPositive denominatorPositive))
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) δPositive] with h hδ
  have hδ' : |h| < δ := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hδ
  have hVariation : |h| < burnolKernelVariationRadius radius :=
    hδ'.trans_le (min_le_left _ _)
  have hRadius : |h| < radius :=
    hδ'.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hCoefficient : |h| < c / (B + 1) :=
    hδ'.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have shiftPositive : 0 < radius + h := by
    have lower := (abs_lt.mp hRadius).1
    linarith
  have scaledCoefficient : (B + 1) * |h| < c :=
    by simpa only [mul_comm] using
      (lt_div_iff₀ denominatorPositive).mp hCoefficient
  have linearCoefficient : B * |h| ≤ c := by
    nlinarith [abs_nonneg h]
  calc
    ‖burnolRechartedTruncatedFourierOperator (radius + h) -
        burnolRechartedTruncatedFourierOperator radius -
        h • burnolRadiusRechartedTruncatedFourierDerivative positive‖ ≤
      B * |h| ^ 2 :=
        burnolRechartedTruncatedFourierOperator_remainder_norm_le
          positive shiftPositive hVariation
    _ = (B * |h|) * |h| := by ring
    _ ≤ c * |h| :=
      mul_le_mul_of_nonneg_right linearCoefficient (abs_nonneg h)
    _ = c * ‖h‖ := by rw [Real.norm_eq_abs]

theorem burnolQuarterRechartedTruncatedFourierOperator_hasDerivAt :
    HasDerivAt burnolRechartedTruncatedFourierOperator
      (burnolRadiusRechartedTruncatedFourierDerivative
        (by norm_num : (0 : ℝ) < 1 / 4)) (1 / 4 : ℝ) :=
  burnolRechartedTruncatedFourierOperator_hasDerivAt
    (by norm_num : (0 : ℝ) < 1 / 4)


end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
