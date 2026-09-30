import H0mework.Arithmetic.TruncatedFourier.ActualBridge
import H0mework.Arithmetic.TruncatedFourier.BlockStates
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFourier

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

theorem burnolQuarterRestriction_zeroExtension
    (state : BurnolQuarterIntervalL2) :
    burnolQuarterRestriction (burnolQuarterZeroExtension state) = state :=
  burnolRadiusRestriction_zeroExtension state

theorem fourierL2_reflectL2_commute (value : BurnolL2) :
    fourierL2 (reflectL2 value) = reflectL2 (fourierL2 value) :=
  burnolRadiusFourierL2_reflectL2_commute value

def burnolQuarterCanonicalPhysicalState : BurnolL2 :=
  burnolRadiusPlusBlockState (1 / 4 : ℝ) (by norm_num) (by norm_num)

theorem burnolQuarterCanonicalPhysicalState_restriction :
    burnolQuarterRestriction burnolQuarterCanonicalPhysicalState =
      intervalConstant (1 / 4 : ℝ) := by
  exact burnolRadiusPlusBlockState_restriction (by norm_num) (by norm_num)

theorem burnolQuarterCanonicalPhysicalState_fourier_restriction :
    burnolQuarterRestriction (fourierL2 burnolQuarterCanonicalPhysicalState) =
      intervalConstant (1 / 4 : ℝ) := by
  exact burnolRadiusPlusBlockState_fourier_restriction
    (by norm_num) (by norm_num)

theorem burnolQuarterCanonicalPhysicalState_even :
    reflectL2 burnolQuarterCanonicalPhysicalState =
      burnolQuarterCanonicalPhysicalState :=
  burnolRadiusPlusBlockState_even (by norm_num) (by norm_num)

theorem burnolQuarterCanonicalPhysicalState_mem :
    burnolQuarterCanonicalPhysicalState ∈
      evenBurnolClosedFace (1 / 4 : ℝ) := by
  exact burnolRadiusPlusBlockState_mem (by norm_num) (by norm_num)

theorem burnolQuarterCanonicalPhysicalState_ne_zero :
    burnolQuarterCanonicalPhysicalState ≠ 0 :=
  burnolRadiusPlusBlockState_ne_zero (by norm_num) (by norm_num)

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
