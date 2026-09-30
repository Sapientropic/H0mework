import H0mework.Arithmetic.TruncatedFourier.RadiusActualBridge
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFourier

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

theorem burnolRadiusFourierL2_reflectL2_commute (value : BurnolL2) :
    fourierL2 (reflectL2 value) = reflectL2 (fourierL2 value) := by
  rw [← fourierL2_fourierL2 value,
    ← fourierL2_fourierL2 (fourierL2 value)]

theorem burnolRadiusSymmetrizedFourierPair_fixed (value : BurnolL2) :
    fourierL2 ((1 / 2 : ℂ) •
        ((value + fourierL2 value) +
          reflectL2 (value + fourierL2 value))) =
      (1 / 2 : ℂ) •
        ((value + fourierL2 value) +
          reflectL2 (value + fourierL2 value)) := by
  simp only [map_smul, map_add, fourierL2_fourierL2,
    burnolRadiusFourierL2_reflectL2_commute, reflectL2_reflectL2]
  module

theorem burnolRadiusRestriction_zeroExtension
    {radius : ℝ} (state : BurnolRadiusIntervalL2 radius) :
    burnolRadiusRestriction radius (burnolRadiusZeroExtension radius state) = state := by
  apply Lp.ext
  have restrictionRead := LpToLpRestrictCLM_coeFn ℂ
    (symmetricInterval radius) (burnolRadiusZeroExtension radius state)
  have extensionRead := ae_restrict_of_ae (s := symmetricInterval radius)
    (burnolRadiusZeroExtension_coe state)
  have intervalRead := ae_restrict_mem (μ := (volume : Measure ℝ))
    (measurableSet_symmetricInterval radius)
  filter_upwards [restrictionRead, extensionRead, intervalRead]
      with x hxRestriction hxExtension hxInterval
  have hxRestriction' :
      burnolRadiusRestriction radius (burnolRadiusZeroExtension radius state) x =
        burnolRadiusZeroExtension radius state x := hxRestriction
  rw [hxRestriction', hxExtension]
  simp [hxInterval]

def burnolRadiusTruncatedFourierSquare (radius : ℝ) :
    BurnolRadiusIntervalL2 radius →L[ℂ] BurnolRadiusIntervalL2 radius :=
  (burnolRadiusTruncatedFourier radius).comp
    (burnolRadiusTruncatedFourier radius)

theorem burnolRadiusTruncatedFourierSquare_opNorm_lt_one
    {radius : ℝ} (positive : 0 < radius) (short : 2 * radius < 1) :
    ‖burnolRadiusTruncatedFourierSquare radius‖ < 1 := by
  apply lt_of_le_of_lt (ContinuousLinearMap.opNorm_comp_le
    (burnolRadiusTruncatedFourier radius)
    (burnolRadiusTruncatedFourier radius))
  have bound := burnolRadiusTruncatedFourier_opNorm_le positive
  calc
    ‖burnolRadiusTruncatedFourier radius‖ *
        ‖burnolRadiusTruncatedFourier radius‖ ≤
      (2 * radius) * (2 * radius) := by
        exact mul_le_mul bound bound (norm_nonneg _) (by linarith)
    _ < 1 := by nlinarith

def burnolRadiusOneMinusSquare (radius : ℝ) :
    BurnolRadiusIntervalL2 radius →L[ℂ] BurnolRadiusIntervalL2 radius :=
  1 - burnolRadiusTruncatedFourierSquare radius

theorem burnolRadiusOneMinusSquare_isUnit
    {radius : ℝ} (positive : 0 < radius) (short : 2 * radius < 1) :
    IsUnit (burnolRadiusOneMinusSquare radius) :=
  isUnit_one_sub_of_norm_lt_one
    (burnolRadiusTruncatedFourierSquare_opNorm_lt_one positive short)

def burnolRadiusBlockInverse
    (radius : ℝ) (_positive : 0 < radius) (_short : 2 * radius < 1) :
    BurnolRadiusIntervalL2 radius →L[ℂ] BurnolRadiusIntervalL2 radius :=
  Ring.inverse (burnolRadiusOneMinusSquare radius)

theorem burnolRadiusBlockInverse_right
    {radius : ℝ} (positive : 0 < radius) (short : 2 * radius < 1) :
    burnolRadiusOneMinusSquare radius *
        burnolRadiusBlockInverse radius positive short = 1 :=
  Ring.mul_inverse_cancel _ (burnolRadiusOneMinusSquare_isUnit positive short)

def burnolRadiusPlusLocal
    (radius : ℝ) (positive : 0 < radius) (short : 2 * radius < 1) :
    BurnolRadiusIntervalL2 radius :=
  (1 - burnolRadiusTruncatedFourier radius)
    (burnolRadiusBlockInverse radius positive short (intervalConstant radius))

def burnolRadiusMinusLocal
    (radius : ℝ) (positive : 0 < radius) (short : 2 * radius < 1) :
    BurnolRadiusIntervalL2 radius :=
  (1 + burnolRadiusTruncatedFourier radius)
    (burnolRadiusBlockInverse radius positive short (intervalConstant radius))

theorem burnolRadiusPlusLocal_equation
    {radius : ℝ} (positive : 0 < radius) (short : 2 * radius < 1) :
    (1 + burnolRadiusTruncatedFourier radius)
        (burnolRadiusPlusLocal radius positive short) = intervalConstant radius := by
  have factorization :
      (1 + burnolRadiusTruncatedFourier radius) *
          (1 - burnolRadiusTruncatedFourier radius) =
        1 - burnolRadiusTruncatedFourier radius *
          burnolRadiusTruncatedFourier radius := by
    noncomm_ring
  calc
    _ = (((1 + burnolRadiusTruncatedFourier radius) *
          (1 - burnolRadiusTruncatedFourier radius)) *
        burnolRadiusBlockInverse radius positive short) (intervalConstant radius) := by rfl
    _ = (burnolRadiusOneMinusSquare radius *
        burnolRadiusBlockInverse radius positive short) (intervalConstant radius) := by
      rw [factorization]
      rfl
    _ = intervalConstant radius := by
      rw [burnolRadiusBlockInverse_right]
      simp

theorem burnolRadiusMinusLocal_equation
    {radius : ℝ} (positive : 0 < radius) (short : 2 * radius < 1) :
    (1 - burnolRadiusTruncatedFourier radius)
        (burnolRadiusMinusLocal radius positive short) = intervalConstant radius := by
  have factorization :
      (1 - burnolRadiusTruncatedFourier radius) *
          (1 + burnolRadiusTruncatedFourier radius) =
        1 - burnolRadiusTruncatedFourier radius *
          burnolRadiusTruncatedFourier radius := by
    noncomm_ring
  calc
    _ = (((1 - burnolRadiusTruncatedFourier radius) *
          (1 + burnolRadiusTruncatedFourier radius)) *
        burnolRadiusBlockInverse radius positive short) (intervalConstant radius) := by rfl
    _ = (burnolRadiusOneMinusSquare radius *
        burnolRadiusBlockInverse radius positive short) (intervalConstant radius) := by
      rw [factorization]
      rfl
    _ = intervalConstant radius := by
      rw [burnolRadiusBlockInverse_right]
      simp

def burnolRadiusPlusBlockState
    (radius : ℝ) (positive : 0 < radius) (short : 2 * radius < 1) : BurnolL2 :=
  let source := burnolRadiusZeroExtension radius
      (burnolRadiusPlusLocal radius positive short)
  (1 / 2 : ℂ) • ((source + fourierL2 source) +
    reflectL2 (source + fourierL2 source))

def burnolRadiusMinusBlockState
    (radius : ℝ) (positive : 0 < radius) (short : 2 * radius < 1) : BurnolL2 :=
  let source := burnolRadiusZeroExtension radius
      (burnolRadiusMinusLocal radius positive short)
  (1 / 2 : ℂ) • ((source - fourierL2 source) +
    reflectL2 (source - fourierL2 source))

theorem burnolSymmetrizedFourierMinusPair_neg_fixed (value : BurnolL2) :
    fourierL2 ((1 / 2 : ℂ) •
        ((value - fourierL2 value) + reflectL2 (value - fourierL2 value))) =
      -((1 / 2 : ℂ) •
        ((value - fourierL2 value) + reflectL2 (value - fourierL2 value))) := by
  simp only [map_smul, map_sub, map_add, fourierL2_fourierL2,
    burnolRadiusFourierL2_reflectL2_commute, reflectL2_reflectL2]
  rw [← smul_neg]
  congr 1
  abel

theorem burnolRadiusPlusBlockState_fourier
    {radius : ℝ} (positive : 0 < radius) (short : 2 * radius < 1) :
    fourierL2 (burnolRadiusPlusBlockState radius positive short) =
      burnolRadiusPlusBlockState radius positive short := by
  unfold burnolRadiusPlusBlockState
  dsimp only
  exact burnolRadiusSymmetrizedFourierPair_fixed _

theorem burnolRadiusMinusBlockState_fourier
    {radius : ℝ} (positive : 0 < radius) (short : 2 * radius < 1) :
    fourierL2 (burnolRadiusMinusBlockState radius positive short) =
      -burnolRadiusMinusBlockState radius positive short := by
  unfold burnolRadiusMinusBlockState
  dsimp only
  exact burnolSymmetrizedFourierMinusPair_neg_fixed _

theorem burnolRadiusPlusBlockState_even
    {radius : ℝ} (positive : 0 < radius) (short : 2 * radius < 1) :
    reflectL2 (burnolRadiusPlusBlockState radius positive short) =
      burnolRadiusPlusBlockState radius positive short := by
  unfold burnolRadiusPlusBlockState
  dsimp only
  rw [map_smul, map_add, reflectL2_reflectL2]
  congr 1
  exact add_comm _ _

theorem burnolRadiusMinusBlockState_even
    {radius : ℝ} (positive : 0 < radius) (short : 2 * radius < 1) :
    reflectL2 (burnolRadiusMinusBlockState radius positive short) =
      burnolRadiusMinusBlockState radius positive short := by
  unfold burnolRadiusMinusBlockState
  dsimp only
  rw [map_smul, map_add, reflectL2_reflectL2]
  congr 1
  exact add_comm _ _

theorem burnolRadiusPlusBlockState_restriction
    {radius : ℝ} (positive : 0 < radius) (short : 2 * radius < 1) :
    burnolRadiusRestriction radius
        (burnolRadiusPlusBlockState radius positive short) =
      intervalConstant radius := by
  let source := burnolRadiusZeroExtension radius
    (burnolRadiusPlusLocal radius positive short)
  have rawRead :
      burnolRadiusRestriction radius (source + fourierL2 source) =
        intervalConstant radius := by
    dsimp [source]
    rw [map_add, burnolRadiusRestriction_zeroExtension]
    change burnolRadiusPlusLocal radius positive short +
        burnolRadiusTruncatedFourier radius
          (burnolRadiusPlusLocal radius positive short) = intervalConstant radius
    exact burnolRadiusPlusLocal_equation positive short
  unfold burnolRadiusPlusBlockState
  dsimp only
  rw [map_smul, map_add]
  have reflectedRead :
      burnolRadiusRestriction radius
          (reflectL2 (source + fourierL2 source)) = intervalConstant radius := by
    calc
      _ = reflectRestricted radius
          (burnolRadiusRestriction radius (source + fourierL2 source)) :=
        restrictToInterval_reflectL2 radius _
      _ = _ := by rw [rawRead, reflectRestricted_intervalConstant]
  rw [rawRead, reflectedRead]
  module

theorem burnolRadiusMinusBlockState_restriction
    {radius : ℝ} (positive : 0 < radius) (short : 2 * radius < 1) :
    burnolRadiusRestriction radius
        (burnolRadiusMinusBlockState radius positive short) =
      intervalConstant radius := by
  let source := burnolRadiusZeroExtension radius
    (burnolRadiusMinusLocal radius positive short)
  have rawRead :
      burnolRadiusRestriction radius (source - fourierL2 source) =
        intervalConstant radius := by
    dsimp [source]
    rw [map_sub, burnolRadiusRestriction_zeroExtension]
    change burnolRadiusMinusLocal radius positive short -
        burnolRadiusTruncatedFourier radius
          (burnolRadiusMinusLocal radius positive short) = intervalConstant radius
    exact burnolRadiusMinusLocal_equation positive short
  unfold burnolRadiusMinusBlockState
  dsimp only
  rw [map_smul, map_add]
  have reflectedRead :
      burnolRadiusRestriction radius
          (reflectL2 (source - fourierL2 source)) = intervalConstant radius := by
    calc
      _ = reflectRestricted radius
          (burnolRadiusRestriction radius (source - fourierL2 source)) :=
        restrictToInterval_reflectL2 radius _
      _ = _ := by rw [rawRead, reflectRestricted_intervalConstant]
  rw [rawRead, reflectedRead]
  module

theorem burnolRadiusPlusBlockState_fourier_restriction
    {radius : ℝ} (positive : 0 < radius) (short : 2 * radius < 1) :
    burnolRadiusRestriction radius
        (fourierL2 (burnolRadiusPlusBlockState radius positive short)) =
      intervalConstant radius := by
  rw [burnolRadiusPlusBlockState_fourier,
    burnolRadiusPlusBlockState_restriction]

theorem burnolRadiusMinusBlockState_fourier_restriction
    {radius : ℝ} (positive : 0 < radius) (short : 2 * radius < 1) :
    burnolRadiusRestriction radius
        (fourierL2 (burnolRadiusMinusBlockState radius positive short)) =
      -intervalConstant radius := by
  rw [burnolRadiusMinusBlockState_fourier, map_neg,
    burnolRadiusMinusBlockState_restriction]

theorem burnolRadiusPlusBlockState_mem
    {radius : ℝ} (positive : 0 < radius) (short : 2 * radius < 1) :
    burnolRadiusPlusBlockState radius positive short ∈
      evenBurnolClosedFace radius := by
  refine ⟨⟨?_, ?_⟩, mem_evenL2ClosedFace_iff.mpr
    (burnolRadiusPlusBlockState_even positive short)⟩
  · change burnolRadiusRestriction radius
        (burnolRadiusPlusBlockState radius positive short) ∈
      intervalConstantLine radius
    rw [burnolRadiusPlusBlockState_restriction]
    exact Submodule.mem_span_singleton_self _
  · change burnolRadiusRestriction radius
        (fourierL2 (burnolRadiusPlusBlockState radius positive short)) ∈
      intervalConstantLine radius
    rw [burnolRadiusPlusBlockState_fourier_restriction]
    exact Submodule.mem_span_singleton_self _

theorem burnolRadiusMinusBlockState_mem
    {radius : ℝ} (positive : 0 < radius) (short : 2 * radius < 1) :
    burnolRadiusMinusBlockState radius positive short ∈
      evenBurnolClosedFace radius := by
  refine ⟨⟨?_, ?_⟩, mem_evenL2ClosedFace_iff.mpr
    (burnolRadiusMinusBlockState_even positive short)⟩
  · change burnolRadiusRestriction radius
        (burnolRadiusMinusBlockState radius positive short) ∈
      intervalConstantLine radius
    rw [burnolRadiusMinusBlockState_restriction]
    exact Submodule.mem_span_singleton_self _
  · change burnolRadiusRestriction radius
        (fourierL2 (burnolRadiusMinusBlockState radius positive short)) ∈
      intervalConstantLine radius
    rw [burnolRadiusMinusBlockState_fourier_restriction]
    exact Submodule.neg_mem _ (Submodule.mem_span_singleton_self _)

theorem burnolRadiusPlusBlockState_ne_zero
    {radius : ℝ} (positive : 0 < radius) (short : 2 * radius < 1) :
    burnolRadiusPlusBlockState radius positive short ≠ 0 := by
  intro stateZero
  have restrictionZero := congrArg (burnolRadiusRestriction radius) stateZero
  rw [burnolRadiusPlusBlockState_restriction, map_zero] at restrictionZero
  exact (intervalConstant_ne_zero positive) restrictionZero

theorem burnolRadiusMinusBlockState_ne_zero
    {radius : ℝ} (positive : 0 < radius) (short : 2 * radius < 1) :
    burnolRadiusMinusBlockState radius positive short ≠ 0 := by
  intro stateZero
  have restrictionZero := congrArg (burnolRadiusRestriction radius) stateZero
  rw [burnolRadiusMinusBlockState_restriction, map_zero] at restrictionZero
  exact (intervalConstant_ne_zero positive) restrictionZero

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
