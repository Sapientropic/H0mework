import H0mework.NavierStokes.CorrectionControl.Rows
import H0mework.Versions.X.NavierStokes.NormControl.Native
import H0mework.Versions.X.NavierStokes.NormControl.Global

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeTurbulenceControl

open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationBoundaryDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

noncomputable section

theorem receipt_correction_norm_le {nu : Viscosity} {initial : ComplexVorticityHilbertState}
    {duration : ℝ} (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (modes : Finset IntegerWavevector) (wave : IntegerWavevector) (time : Icc (0 : ℝ) duration) :
    ‖nativeTurbulenceCorrectionAt modes (receipt.wholePath time) wave‖ ≤
      2 * curlWeight wave ^ 2 * ‖puncturedWholeVelocityEuclideanState initial‖ ^ 2 := by
  have bound := correction_row_norm_le_kinetic modes (receipt.wholePath time)
    (receipt.wholePath_zero_row time) (wholePath_transverse receipt time) wave
  rw [← puncturedWholeVelocityEuclideanState_norm_sq _ (wholePath_transverse receipt time)] at bound
  exact bound.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (NativeNormControl.receipt_velocity_norm_le receipt time)) (by positivity))

/-- The correction in the original native law is controlled on every actual
micro receipt, with one source bound independent of stage and mode inventory. -/
theorem original_correction_norm_le {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat) (modes : Finset IntegerWavevector) (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    ‖nativeTurbulenceCorrectionAt modes ((run initial index).nextContact.prefixReceipt.wholePath time) wave‖ ≤
      2 * curlWeight wave ^ 2 * ‖puncturedWholeVelocityEuclideanState initial.initialState‖ ^ 2 := by
  have bound := receipt_correction_norm_le (run initial index).nextContact.prefixReceipt modes wave time
  have initialBound := (wholeRestartContactVelocityState_norm_le_initial initial index).trans
    (NativeNormControl.contact_velocity_norm_le_initial initial)
  exact bound.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr initialBound) (by positivity))

theorem recovery_correction_norm_le {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry)
    (modes : Finset IntegerWavevector) (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) law.recovery.next.duration) :
    ‖nativeTurbulenceCorrectionAt modes (law.recovery.next.receipt.wholePath time) wave‖ ≤
      2 * curlWeight wave ^ 2 * ‖puncturedWholeVelocityEuclideanState initial.initialState‖ ^ 2 := by
  have bound := receipt_correction_norm_le law.recovery.next.receipt modes wave time
  exact bound.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (NativeNormControl.macro_next_velocity_norm_le law.recovery.step)) (by positivity))

theorem macro_correction_norm_le {nu : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (macroIndex micro : Nat) (modes : Finset IntegerWavevector) (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) (run (lineage.current macroIndex) micro).nextContact.time.1) :
    ‖nativeTurbulenceCorrectionAt modes
      ((run (lineage.current macroIndex) micro).nextContact.prefixReceipt.wholePath time) wave‖ ≤
      2 * curlWeight wave ^ 2 * ‖puncturedWholeVelocityEuclideanState (lineage.current 0).initialState‖ ^ 2 := by
  have bound := original_correction_norm_le (lineage.current macroIndex) micro modes wave time
  exact bound.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (NativeNormControl.macro_initial_velocity_norm_le lineage macroIndex)) (by positivity))

end
end SaturationMonoid.NavierStokes.NativeTurbulenceControl
