import H0mework.Versions.V2.Arithmetic.TruncatedFourier.Overlap
import H0mework.Versions.V2.Arithmetic.RieszCanonicalRaw.RieszSingleFourierSource

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set
open scoped InnerProductSpace
noncomputable section

def burnolRieszSourceRawShell (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  fourierL2 (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) -
    burnolQuarterZeroExtension
      (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) :
        BurnolQuarterIntervalL2)

private theorem unitEmbedding_rechart {radius : ℝ} (positive : 0 < radius)
    (state : BurnolRadiusIntervalL2 radius) :
    burnolUnitWindowEmbedding positive (burnolRadiusRechartEquiv positive state) =
      burnolRadiusZeroExtension radius state := by
  change burnolRadiusZeroExtension radius
    ((burnolRadiusRechartEquiv positive).symm
      (burnolRadiusRechartEquiv positive state)) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem burnolRieszSource_positionWindowAction
    (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    burnolRadiusRechartEquiv (by norm_num : (0 : ℝ) < 1 / 4)
        (burnolQuarterRestriction
          (burnolMultiplicativeDilation shift (burnolRieszSourceRawShell coordinate))) =
      burnolRadiusRechartedTruncatedFourier
          (mul_pos (by norm_num : (0 : ℝ) < 1 / 4) (Real.exp_pos (shift / 2)))
        (burnolRadiusRechartEquiv (by norm_num : (0 : ℝ) < 1 / 4)
          (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) -
      burnolFixedWindowDilationOverlap
        (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (0 : ℝ) < 1 / 4) shift
        (burnolRadiusRechartEquiv (by norm_num : (0 : ℝ) < 1 / 4)
          (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) :
            BurnolQuarterIntervalL2)) := by
  let positive : (0 : ℝ) < 1 / 4 := by norm_num
  have radiusEq : Real.sqrt ((1 / 4 : ℝ) * (1 / 4)) = 1 / 4 := by
    rw [show (1 / 4 : ℝ) * (1 / 4) = (1 / 4) ^ 2 by ring,
      Real.sqrt_sq (by norm_num)]
  have native := burnolFixedWindowDilationFourier_eq_radius positive positive shift
  simp only [radiusEq] at native
  rw [← native]
  unfold burnolRieszSourceRawShell
  simp only [map_sub]
  congr 1 <;>
    simp only [burnolFixedWindowDilationFourier, burnolFixedWindowDilationOverlap,
      ContinuousLinearMap.comp_apply, unitEmbedding_rechart] <;> rfl

theorem burnolRieszSource_fourierWindowAction
    (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    burnolRadiusRechartEquiv (by norm_num : (0 : ℝ) < 1 / 4)
        (burnolQuarterRestriction
          (fourierL2
            (burnolMultiplicativeDilation shift (burnolRieszSourceRawShell coordinate)))) =
      burnolFixedWindowDilationOverlap
        (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (0 : ℝ) < 1 / 4) (-shift)
        (burnolRadiusRechartEquiv (by norm_num : (0 : ℝ) < 1 / 4)
          (reflectRestricted (1 / 4 : ℝ)
            (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) -
      burnolRadiusRechartedTruncatedFourier
          (mul_pos (by norm_num : (0 : ℝ) < 1 / 4) (Real.exp_pos (-shift / 2)))
        (burnolRadiusRechartEquiv (by norm_num : (0 : ℝ) < 1 / 4)
          (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) :
            BurnolQuarterIntervalL2)) := by
  let positive : (0 : ℝ) < 1 / 4 := by norm_num
  have radiusEq : Real.sqrt ((1 / 4 : ℝ) * (1 / 4)) = 1 / 4 := by
    rw [show (1 / 4 : ℝ) * (1 / 4) = (1 / 4) ^ 2 by ring,
      Real.sqrt_sq (by norm_num)]
  have native := burnolFixedWindowFourierDilation_eq_radius positive positive shift
  simp only [radiusEq] at native
  rw [← native]
  unfold burnolRieszSourceRawShell
  simp only [map_sub]
  congr 1
  · rw [fourierL2_burnolMultiplicativeDilation, fourierL2_fourierL2]
    change (burnolRadiusRechartEquiv positive)
      (burnolRadiusRestriction (1 / 4)
        (burnolMultiplicativeDilation (-shift)
          (reflectL2 (burnolRadiusZeroExtension (1 / 4)
            (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))))) = _
    rw [burnolRadiusZeroExtension_reflect]
    simp only [burnolFixedWindowDilationOverlap,
      ContinuousLinearMap.comp_apply, unitEmbedding_rechart]
    rfl
  · simp only [burnolFixedWindowFourierDilation,
      ContinuousLinearMap.comp_apply, unitEmbedding_rechart]
    rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
