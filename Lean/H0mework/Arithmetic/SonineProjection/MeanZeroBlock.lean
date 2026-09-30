import H0mework.Arithmetic.TruncatedFourier.SonineSolve

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

/-- The closed constant direction on the quarter interval. -/
def burnolQuarterConstantClosedFace :
    ClosedSubmodule ℂ BurnolQuarterIntervalL2 where
  toSubmodule := intervalConstantLine (1 / 4 : ℝ)
  isClosed' := intervalConstantLine_isClosed (1 / 4 : ℝ)

local instance burnolQuarterConstantLineComplete :
    CompleteSpace (intervalConstantLine (1 / 4 : ℝ)) := by
  apply IsComplete.completeSpace_coe
  exact (intervalConstantLine_isClosed (1 / 4 : ℝ)).isComplete

/-- The interval information retained after quotienting the allowed constant
gap. -/
def burnolQuarterMeanZeroClosedFace :
    ClosedSubmodule ℂ BurnolQuarterIntervalL2 where
  toSubmodule :=
    Submodule.orthogonal (intervalConstantLine (1 / 4 : ℝ))
  isClosed' := Submodule.isClosed_orthogonal
    (intervalConstantLine (1 / 4 : ℝ))

abbrev BurnolQuarterMeanZeroCarrier :=
  burnolQuarterMeanZeroClosedFace.toSubmodule

local instance burnolQuarterMeanZeroCarrierComplete :
    CompleteSpace BurnolQuarterMeanZeroCarrier := by
  apply IsComplete.completeSpace_coe
  exact burnolQuarterMeanZeroClosedFace.isClosed.isComplete

/-- Actual mean-zero projection `R₀`; its kernel is exactly the allowed
constant line. -/
def burnolQuarterMeanZeroProjection :
    BurnolQuarterIntervalL2 →L[ℂ] BurnolQuarterIntervalL2 :=
  burnolQuarterMeanZeroClosedFace.toSubmodule.starProjection

theorem burnolQuarterMeanZeroProjection_mem
    (state : BurnolQuarterIntervalL2) :
    burnolQuarterMeanZeroProjection state ∈
      burnolQuarterMeanZeroClosedFace := by
  exact Submodule.starProjection_apply_mem _ _

theorem burnolQuarterMeanZeroProjection_eq_zero_iff
    (state : BurnolQuarterIntervalL2) :
    burnolQuarterMeanZeroProjection state = 0 ↔
      state ∈ intervalConstantLine (1 / 4 : ℝ) := by
  change burnolQuarterMeanZeroClosedFace.toSubmodule.starProjection state = 0 ↔ _
  change state ∈
      burnolQuarterMeanZeroClosedFace.toSubmodule.starProjection.ker ↔ _
  rw [Submodule.ker_starProjection]
  change state ∈
      (Submodule.orthogonal
        (Submodule.orthogonal (intervalConstantLine (1 / 4 : ℝ)))) ↔ _
  rw [Submodule.orthogonal_orthogonal]

theorem burnolQuarterMeanZeroProjection_idempotent
    (state : BurnolQuarterIntervalL2) :
    burnolQuarterMeanZeroProjection
        (burnolQuarterMeanZeroProjection state) =
      burnolQuarterMeanZeroProjection state := by
  exact Submodule.starProjection_eq_self_iff.mpr
    (burnolQuarterMeanZeroProjection_mem state)

theorem burnolQuarterMeanZeroProjection_opNorm_le_one :
    ‖burnolQuarterMeanZeroProjection‖ ≤ 1 :=
  Submodule.starProjection_norm_le _

/-- `R₀ D R₀`, represented on its actual mean-zero carrier. -/
def burnolMeanZeroTruncatedFourier :
    BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier :=
  burnolQuarterMeanZeroClosedFace.toSubmodule.orthogonalProjectionOnto.comp
    (burnolTruncatedFourier.comp
      (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule))

theorem burnolMeanZeroTruncatedFourier_ambient_read
    (state : BurnolQuarterMeanZeroCarrier) :
    (burnolMeanZeroTruncatedFourier state : BurnolQuarterIntervalL2) =
      burnolQuarterMeanZeroProjection
        (burnolTruncatedFourier
          (burnolQuarterMeanZeroProjection
            (state : BurnolQuarterIntervalL2))) := by
  change burnolQuarterMeanZeroProjection
      (burnolTruncatedFourier (state : BurnolQuarterIntervalL2)) = _
  have stateFixed :
      burnolQuarterMeanZeroProjection (state : BurnolQuarterIntervalL2) =
        (state : BurnolQuarterIntervalL2) := by
    exact Submodule.starProjection_eq_self_iff.mpr state.property
  rw [stateFixed]

theorem burnolMeanZeroTruncatedFourier_norm_le
    (state : BurnolQuarterMeanZeroCarrier) :
    ‖burnolMeanZeroTruncatedFourier state‖ ≤
      (1 / 2 : ℝ) * ‖state‖ := by
  calc
    _ ≤ ‖burnolTruncatedFourier (state : BurnolQuarterIntervalL2)‖ :=
      burnolQuarterMeanZeroClosedFace.toSubmodule
        |>.norm_orthogonalProjectionOnto_apply_le _
    _ ≤ ‖burnolTruncatedFourier‖ * ‖(state : BurnolQuarterIntervalL2)‖ :=
      burnolTruncatedFourier.le_opNorm _
    _ ≤ (1 / 2 : ℝ) * ‖(state : BurnolQuarterIntervalL2)‖ := by
      exact mul_le_mul_of_nonneg_right
        burnolTruncatedFourier_opNorm_le_half (norm_nonneg _)
    _ = (1 / 2 : ℝ) * ‖state‖ := rfl

theorem burnolMeanZeroTruncatedFourier_opNorm_le_half :
    ‖burnolMeanZeroTruncatedFourier‖ ≤ (1 / 2 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  exact burnolMeanZeroTruncatedFourier_norm_le

theorem burnolMeanZeroTruncatedFourier_opNorm_lt_one :
    ‖burnolMeanZeroTruncatedFourier‖ < 1 :=
  lt_of_le_of_lt burnolMeanZeroTruncatedFourier_opNorm_le_half (by norm_num)

def burnolMeanZeroTruncatedFourierSquare :
    BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier :=
  burnolMeanZeroTruncatedFourier.comp burnolMeanZeroTruncatedFourier

theorem burnolMeanZeroTruncatedFourierSquare_opNorm_lt_one :
    ‖burnolMeanZeroTruncatedFourierSquare‖ < 1 := by
  apply lt_of_le_of_lt (ContinuousLinearMap.opNorm_comp_le
    burnolMeanZeroTruncatedFourier burnolMeanZeroTruncatedFourier)
  calc
    ‖burnolMeanZeroTruncatedFourier‖ *
        ‖burnolMeanZeroTruncatedFourier‖ ≤
        (1 / 2 : ℝ) * (1 / 2 : ℝ) := by
      exact mul_le_mul burnolMeanZeroTruncatedFourier_opNorm_le_half
        burnolMeanZeroTruncatedFourier_opNorm_le_half
        (norm_nonneg burnolMeanZeroTruncatedFourier) (by norm_num)
    _ < 1 := by norm_num

def burnolMeanZeroOneMinusSquare :
    BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier :=
  1 - burnolMeanZeroTruncatedFourierSquare

theorem burnolMeanZeroOneMinusSquare_isUnit :
    IsUnit burnolMeanZeroOneMinusSquare := by
  change IsUnit ((1 : BurnolQuarterMeanZeroCarrier →L[ℂ]
    BurnolQuarterMeanZeroCarrier) - burnolMeanZeroTruncatedFourierSquare)
  let unit : IsUnit ((1 : BurnolQuarterMeanZeroCarrier →L[ℂ]
      BurnolQuarterMeanZeroCarrier) - burnolMeanZeroTruncatedFourierSquare) :=
    @isUnit_one_sub_of_norm_lt_one
      (BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier)
      ContinuousLinearMap.toNormedRing inferInstance
      burnolMeanZeroTruncatedFourierSquare
      burnolMeanZeroTruncatedFourierSquare_opNorm_lt_one
  exact unit

def burnolMeanZeroBlockInverse :
    BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier :=
  Ring.inverse burnolMeanZeroOneMinusSquare

theorem burnolMeanZeroBlockInverse_right :
    burnolMeanZeroOneMinusSquare * burnolMeanZeroBlockInverse = 1 :=
  Ring.mul_inverse_cancel _ burnolMeanZeroOneMinusSquare_isUnit

/-- First coordinate of the exact `2×2` mean-zero Burnol block solve. -/
def burnolMeanZeroBlockFirst
    (rightHandSide : BurnolQuarterMeanZeroCarrier ×
      BurnolQuarterMeanZeroCarrier) : BurnolQuarterMeanZeroCarrier :=
  burnolMeanZeroBlockInverse
    (rightHandSide.1 -
      burnolMeanZeroTruncatedFourier rightHandSide.2)

/-- Second coordinate of the exact `2×2` mean-zero Burnol block solve. -/
def burnolMeanZeroBlockSecond
    (rightHandSide : BurnolQuarterMeanZeroCarrier ×
      BurnolQuarterMeanZeroCarrier) : BurnolQuarterMeanZeroCarrier :=
  rightHandSide.2 -
    burnolMeanZeroTruncatedFourier
      (burnolMeanZeroBlockFirst rightHandSide)

theorem burnolMeanZeroBlock_second_equation
    (rightHandSide : BurnolQuarterMeanZeroCarrier ×
      BurnolQuarterMeanZeroCarrier) :
    burnolMeanZeroTruncatedFourier
          (burnolMeanZeroBlockFirst rightHandSide) +
        burnolMeanZeroBlockSecond rightHandSide = rightHandSide.2 := by
  unfold burnolMeanZeroBlockSecond
  module

theorem burnolMeanZeroBlock_first_equation
    (rightHandSide : BurnolQuarterMeanZeroCarrier ×
      BurnolQuarterMeanZeroCarrier) :
    burnolMeanZeroBlockFirst rightHandSide +
        burnolMeanZeroTruncatedFourier
          (burnolMeanZeroBlockSecond rightHandSide) = rightHandSide.1 := by
  have inverseRead := congrArg
    (fun operator : BurnolQuarterMeanZeroCarrier →L[ℂ]
      BurnolQuarterMeanZeroCarrier ↦
        operator (rightHandSide.1 -
          burnolMeanZeroTruncatedFourier rightHandSide.2))
    burnolMeanZeroBlockInverse_right
  have core :
      burnolMeanZeroBlockFirst rightHandSide -
          burnolMeanZeroTruncatedFourier
            (burnolMeanZeroTruncatedFourier
              (burnolMeanZeroBlockFirst rightHandSide)) =
        rightHandSide.1 -
          burnolMeanZeroTruncatedFourier rightHandSide.2 := by
    simpa [burnolMeanZeroOneMinusSquare,
      burnolMeanZeroTruncatedFourierSquare,
      burnolMeanZeroBlockFirst] using inverseRead
  unfold burnolMeanZeroBlockSecond
  rw [map_sub]
  calc
    burnolMeanZeroBlockFirst rightHandSide +
        (burnolMeanZeroTruncatedFourier rightHandSide.2 -
          burnolMeanZeroTruncatedFourier
            (burnolMeanZeroTruncatedFourier
              (burnolMeanZeroBlockFirst rightHandSide))) =
      (burnolMeanZeroBlockFirst rightHandSide -
          burnolMeanZeroTruncatedFourier
            (burnolMeanZeroTruncatedFourier
              (burnolMeanZeroBlockFirst rightHandSide))) +
        burnolMeanZeroTruncatedFourier rightHandSide.2 := by abel
    _ = (rightHandSide.1 -
          burnolMeanZeroTruncatedFourier rightHandSide.2) +
        burnolMeanZeroTruncatedFourier rightHandSide.2 := by rw [core]
    _ = rightHandSide.1 := sub_add_cancel _ _

/-- Exact extended-Sonine membership: the only forbidden interval data are
the two mean-zero residuals. -/
theorem mem_burnolQuarterFace_iff_meanZero_residuals
    (value : BurnolL2) :
    value ∈ burnolFace (1 / 4 : ℝ) ↔
      burnolQuarterMeanZeroProjection
          (burnolQuarterRestriction value) = 0 ∧
        burnolQuarterMeanZeroProjection
          (burnolQuarterRestriction (fourierL2 value)) = 0 := by
  rw [mem_burnolFace_iff]
  change
    burnolQuarterRestriction value ∈
        intervalConstantLine (1 / 4 : ℝ) ∧
      burnolQuarterRestriction (fourierL2 value) ∈
        intervalConstantLine (1 / 4 : ℝ) ↔ _
  rw [← burnolQuarterMeanZeroProjection_eq_zero_iff,
    ← burnolQuarterMeanZeroProjection_eq_zero_iff]

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
