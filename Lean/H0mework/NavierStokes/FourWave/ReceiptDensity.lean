import H0mework.NavierStokes.FourWave.WholeKernelBudget
import H0mework.NavierStokes.WholeSpace.WholeContinuousMildSerrinUniqueness
import H0mework.NavierStokes.Accumulation.ScaleCriticalWindow

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.HeatQuartetBudget

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNonlinearDuhamelConcentration

noncomputable section

variable {nu : Viscosity} {initial : ComplexVorticityHilbertState} {time : Real}
  (receipt : WholeContinuousMildSerrinReceipt nu initial time)

theorem velocitySquare_integrable :
    Integrable (fun actual => wholeStateVelocityMajorant (receipt.wholePath actual) ^ 2)
      (commonTimeMeasure time) := by
  apply receipt.serrinDensity_integrable.congr
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 (commonTimeMeasure time) Complex receipt.wholePath]
    with actual same
  change wholeStateVelocityMajorant
    ((BoundedContinuousFunction.toLp 2 (commonTimeMeasure time) Complex receipt.wholePath) actual) ^ 2 = _
  rw [same]

/-- This is the original Serrin payment times the same bounded path's mass. -/
def density (actual : Icc (0 : Real) time) : Real :=
  wholeStateVelocityMajorant (receipt.wholePath actual) ^ 2 *
    wholeVorticityEuclideanMass (receipt.wholePath actual)

theorem density_integrable : Integrable (density receipt) (commonTimeMeasure time) := by
  apply ((velocitySquare_integrable receipt).mul_const (3 * ‖receipt.wholePath‖ ^ 2)).mono'
  · exact (velocitySquare_integrable receipt).aestronglyMeasurable.mul
      (continuous_wholeVorticityEuclideanMass.comp receipt.wholePath.continuous).aestronglyMeasurable
  · filter_upwards with actual
    have massNonneg : 0 ≤ wholeVorticityEuclideanMass (receipt.wholePath actual) :=
      tsum_nonneg fun _ => sq_nonneg _
    have massLe : wholeVorticityEuclideanMass (receipt.wholePath actual) ≤ 3 * ‖receipt.wholePath‖ ^ 2 := by
      apply (wholeVorticityEuclideanMass_le_three_mul_norm_sq (receipt.wholePath actual)).trans
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (receipt.wholePath.norm_coe_le_norm actual) 2) (by norm_num)
    rw [Real.norm_eq_abs, density, abs_of_nonneg (mul_nonneg (sq_nonneg _) massNonneg)]
    exact mul_le_mul_of_nonneg_left massLe (sq_nonneg _)

end
end SaturationMonoid.NavierStokes.HeatQuartetBudget
