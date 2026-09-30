import H0mework.Arithmetic.TruncatedFourier.RadiusIntegralKernel

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

abbrev BurnolQuarterIntervalL2 := BurnolRadiusIntervalL2 (1 / 4 : ℝ)

def burnolQuarterRestriction : BurnolL2 →L[ℂ] BurnolQuarterIntervalL2 :=
  burnolRadiusRestriction (1 / 4 : ℝ)

def burnolQuarterZeroExtension : BurnolQuarterIntervalL2 →L[ℂ] BurnolL2 :=
  burnolRadiusZeroExtension (1 / 4 : ℝ)

def burnolTruncatedFourier :
    BurnolQuarterIntervalL2 →L[ℂ] BurnolQuarterIntervalL2 :=
  burnolRadiusTruncatedFourier (1 / 4 : ℝ)

def burnolTruncatedFourierRaw
    (state : BurnolQuarterIntervalL2) (x : ℝ) : ℂ :=
  burnolRadiusTruncatedFourierRaw (1 / 4 : ℝ) state x

theorem burnolQuarterInterval_measureReal_univ :
    ((volume : Measure ℝ).restrict
      (symmetricInterval (1 / 4 : ℝ))).real Set.univ = 1 / 2 := by
  have generated := burnolRadiusInterval_measureReal_univ
    (by norm_num : (0 : ℝ) < 1 / 4)
  have radiusRead : (2 : ℝ) * (1 / 4) = 1 / 2 := by norm_num
  rw [radiusRead] at generated
  exact generated

theorem burnolQuarterInterval_integral_norm_sq
    (state : BurnolQuarterIntervalL2) :
    (∫ x : ℝ, ‖state x‖ ^ 2
      ∂((volume : Measure ℝ).restrict
        (symmetricInterval (1 / 4 : ℝ)))) = ‖state‖ ^ 2 :=
  burnolRadiusInterval_integral_norm_sq state

theorem burnolQuarterInterval_integral_norm_le
    (state : BurnolQuarterIntervalL2) :
    (∫ x : ℝ, ‖state x‖
      ∂((volume : Measure ℝ).restrict
        (symmetricInterval (1 / 4 : ℝ)))) ≤
      Real.sqrt (1 / 2) * ‖state‖ := by
  have generated := burnolRadiusInterval_integral_norm_le
    (by norm_num : (0 : ℝ) < 1 / 4) state
  have radiusRead : (2 : ℝ) * (1 / 4) = 1 / 2 := by norm_num
  rw [radiusRead] at generated
  exact generated

theorem burnolTruncatedFourierRaw_norm_le
    (state : BurnolQuarterIntervalL2) (x : ℝ) :
    ‖burnolTruncatedFourierRaw state x‖ ≤
      Real.sqrt (1 / 2) * ‖state‖ := by
  have generated := burnolRadiusTruncatedFourierRaw_norm_le
    (by norm_num : (0 : ℝ) < 1 / 4) state x
  have radiusRead : (2 : ℝ) * (1 / 4) = 1 / 2 := by norm_num
  rw [radiusRead] at generated
  exact generated

theorem burnolTruncatedFourierRaw_continuous
    (state : BurnolQuarterIntervalL2) :
    Continuous (burnolTruncatedFourierRaw state) :=
  burnolRadiusTruncatedFourierRaw_continuous state

theorem burnolTruncatedFourierRaw_memLp
    (state : BurnolQuarterIntervalL2) :
    MemLp (burnolTruncatedFourierRaw state) 2
      ((volume : Measure ℝ).restrict
        (symmetricInterval (1 / 4 : ℝ))) :=
  burnolRadiusTruncatedFourierRaw_memLp
    (by norm_num : (0 : ℝ) < 1 / 4) state

def burnolTruncatedFourierIntegralValue
    (state : BurnolQuarterIntervalL2) : BurnolQuarterIntervalL2 :=
  burnolRadiusTruncatedFourierIntegralValue
    (by norm_num : (0 : ℝ) < 1 / 4) state

theorem burnolTruncatedFourierIntegralValue_norm_le
    (state : BurnolQuarterIntervalL2) :
    ‖burnolTruncatedFourierIntegralValue state‖ ≤ (1 / 2 : ℝ) * ‖state‖ := by
  have generated := burnolRadiusTruncatedFourierIntegralValue_norm_le
    (by norm_num : (0 : ℝ) < 1 / 4) state
  have radiusRead : (2 : ℝ) * (1 / 4) = 1 / 2 := by norm_num
  rw [radiusRead] at generated
  exact generated

theorem burnolTruncatedFourierRaw_add
    (left right : BurnolQuarterIntervalL2) :
    burnolTruncatedFourierRaw (left + right) =
      burnolTruncatedFourierRaw left + burnolTruncatedFourierRaw right :=
  burnolRadiusTruncatedFourierRaw_add left right

theorem burnolTruncatedFourierRaw_smul
    (coefficient : ℂ) (state : BurnolQuarterIntervalL2) :
    burnolTruncatedFourierRaw (coefficient • state) =
      coefficient • burnolTruncatedFourierRaw state :=
  burnolRadiusTruncatedFourierRaw_smul coefficient state

theorem burnolTruncatedFourierIntegralValue_add
    (left right : BurnolQuarterIntervalL2) :
    burnolTruncatedFourierIntegralValue (left + right) =
      burnolTruncatedFourierIntegralValue left +
        burnolTruncatedFourierIntegralValue right :=
  burnolRadiusTruncatedFourierIntegralValue_add
    (by norm_num : (0 : ℝ) < 1 / 4) left right

theorem burnolTruncatedFourierIntegralValue_smul
    (coefficient : ℂ) (state : BurnolQuarterIntervalL2) :
    burnolTruncatedFourierIntegralValue (coefficient • state) =
      coefficient • burnolTruncatedFourierIntegralValue state :=
  burnolRadiusTruncatedFourierIntegralValue_smul
    (by norm_num : (0 : ℝ) < 1 / 4) coefficient state

def burnolTruncatedFourierIntegral :
    BurnolQuarterIntervalL2 →L[ℂ] BurnolQuarterIntervalL2 :=
  burnolRadiusTruncatedFourierIntegral (1 / 4 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 4)

theorem burnolTruncatedFourierIntegral_opNorm_le_half :
    ‖burnolTruncatedFourierIntegral‖ ≤ (1 / 2 : ℝ) := by
  have generated := burnolRadiusTruncatedFourierIntegral_opNorm_le
    (by norm_num : (0 : ℝ) < 1 / 4)
  have radiusRead : (2 : ℝ) * (1 / 4) = 1 / 2 := by norm_num
  rw [radiusRead] at generated
  exact generated

theorem burnolTruncatedFourierIntegral_opNorm_lt_one :
    ‖burnolTruncatedFourierIntegral‖ < 1 :=
  lt_of_le_of_lt burnolTruncatedFourierIntegral_opNorm_le_half (by norm_num)

def burnolTruncatedFourierIntegralSquare :
    BurnolQuarterIntervalL2 →L[ℂ] BurnolQuarterIntervalL2 :=
  burnolTruncatedFourierIntegral.comp burnolTruncatedFourierIntegral

theorem burnolTruncatedFourierIntegralSquare_opNorm_le_quarter :
    ‖burnolTruncatedFourierIntegralSquare‖ ≤ (1 / 4 : ℝ) := by
  calc
    _ ≤ ‖burnolTruncatedFourierIntegral‖ *
        ‖burnolTruncatedFourierIntegral‖ := by
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) := by
      exact mul_le_mul burnolTruncatedFourierIntegral_opNorm_le_half
        burnolTruncatedFourierIntegral_opNorm_le_half
        (norm_nonneg _) (by norm_num)
    _ = 1 / 4 := by norm_num

theorem burnolTruncatedFourierIntegralSquare_opNorm_lt_one :
    ‖burnolTruncatedFourierIntegralSquare‖ < 1 :=
  lt_of_le_of_lt burnolTruncatedFourierIntegralSquare_opNorm_le_quarter (by norm_num)

def burnolTruncatedFourierOneMinusSquare :
    BurnolQuarterIntervalL2 →L[ℂ] BurnolQuarterIntervalL2 :=
  1 - burnolTruncatedFourierIntegralSquare

theorem burnolTruncatedFourierOneMinusSquare_isUnit :
    IsUnit burnolTruncatedFourierOneMinusSquare :=
  isUnit_one_sub_of_norm_lt_one
    burnolTruncatedFourierIntegralSquare_opNorm_lt_one

def burnolTruncatedFourierBlockInverse :
    BurnolQuarterIntervalL2 →L[ℂ] BurnolQuarterIntervalL2 :=
  Ring.inverse burnolTruncatedFourierOneMinusSquare

theorem burnolTruncatedFourierBlockInverse_left :
    burnolTruncatedFourierBlockInverse *
        burnolTruncatedFourierOneMinusSquare = 1 :=
  Ring.inverse_mul_cancel _ burnolTruncatedFourierOneMinusSquare_isUnit

theorem burnolTruncatedFourierBlockInverse_right :
    burnolTruncatedFourierOneMinusSquare *
        burnolTruncatedFourierBlockInverse = 1 :=
  Ring.mul_inverse_cancel _ burnolTruncatedFourierOneMinusSquare_isUnit

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
