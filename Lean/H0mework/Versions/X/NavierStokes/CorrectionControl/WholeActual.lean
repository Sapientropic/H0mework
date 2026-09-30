import H0mework.NavierStokes.CorrectionControl.Whole
import H0mework.Versions.X.NavierStokes.CorrectionControl.Actual

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeTurbulenceControl

open scoped BigOperators
open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalIntegerLatticeCriticalKernel
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationBoundaryDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

noncomputable section

def wholeBudget (velocityRadius : ℝ) : ℝ :=
  (2 * (6 * Real.pi) ^ 2 * velocityRadius ^ 2) ^ 2 * ∑' wave, integerWaveCriticalKernel wave

def receiptWholeCorrection {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (modes : Finset IntegerWavevector) (time : Icc (0 : ℝ) duration) : ComplexVorticityHilbertState :=
  wholeCorrection modes (receipt.wholePath time) (receipt.wholePath_zero_row time) (wholePath_transverse receipt time)

private theorem controlled {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (modes : Finset IntegerWavevector) (time : Icc (0 : ℝ) duration)
    (radius : ℝ) (velocity : ‖puncturedWholeVelocityEuclideanState (receipt.wholePath time)‖ ≤ radius) :
    ‖puncturedEuclideanize (receiptWholeCorrection receipt modes time)‖ ^ 2 ≤ 3 * wholeBudget radius := by
  have energy : puncturedWholeVorticityKineticMass (receipt.wholePath time) ≤ radius ^ 2 := by
    rw [← puncturedWholeVelocityEuclideanState_norm_sq _ (wholePath_transverse receipt time)]
    exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans velocity)).mpr velocity
  have cap := mul_le_mul_of_nonneg_left energy (by positivity : 0 ≤ 2 * (6 * Real.pi) ^ 2)
  have square := (sq_le_sq₀ (correctionCap_nonneg (receipt.wholePath time)) (by positivity)).mpr cap
  have rawBound : ‖receiptWholeCorrection receipt modes time‖ ^ 2 ≤ wholeBudget radius :=
    (wholeCorrection_norm_sq_le modes _ (receipt.wholePath_zero_row time)
    (wholePath_transverse receipt time)).trans
      (mul_le_mul_of_nonneg_right square (tsum_nonneg integerWaveCriticalKernel_nonneg))
  exact (puncturedEuclideanize_norm_sq_le _).trans (mul_le_mul_of_nonneg_left rawBound (by norm_num))

theorem receipt_wholeCorrection_norm_sq_le {nu : Viscosity} {initial : ComplexVorticityHilbertState}
    {duration : ℝ} (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (modes : Finset IntegerWavevector) (time : Icc (0 : ℝ) duration) :
    ‖puncturedEuclideanize (receiptWholeCorrection receipt modes time)‖ ^ 2 ≤
      3 * wholeBudget ‖puncturedWholeVelocityEuclideanState initial‖ :=
  controlled receipt modes time _ (NativeNormControl.receipt_velocity_norm_le receipt time)

private theorem original_velocity_bound {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat) (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    ‖puncturedWholeVelocityEuclideanState ((run initial index).nextContact.prefixReceipt.wholePath time)‖ ≤
      ‖puncturedWholeVelocityEuclideanState initial.initialState‖ :=
  (NativeNormControl.receipt_velocity_norm_le (run initial index).nextContact.prefixReceipt time).trans
    ((wholeRestartContactVelocityState_norm_le_initial initial index).trans
      (NativeNormControl.contact_velocity_norm_le_initial initial))

theorem original_wholeCorrection_norm_sq_le {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat) (modes : Finset IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    ‖puncturedEuclideanize (receiptWholeCorrection (run initial index).nextContact.prefixReceipt modes time)‖ ^ 2 ≤
      3 * wholeBudget ‖puncturedWholeVelocityEuclideanState initial.initialState‖ :=
  controlled _ modes time _ (original_velocity_bound initial index time)

theorem recovery_wholeCorrection_norm_sq_le {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry) (modes : Finset IntegerWavevector)
    (time : Icc (0 : ℝ) law.recovery.next.duration) :
    ‖puncturedEuclideanize (receiptWholeCorrection law.recovery.next.receipt modes time)‖ ^ 2 ≤
      3 * wholeBudget ‖puncturedWholeVelocityEuclideanState initial.initialState‖ :=
  controlled _ modes time _ (NativeNormControl.recovery_receipt_velocity_norm_le law time)

theorem macro_wholeCorrection_norm_sq_le {nu : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu)
    (macroIndex micro : Nat) (modes : Finset IntegerWavevector)
    (time : Icc (0 : ℝ) (run (lineage.current macroIndex) micro).nextContact.time.1) :
    ‖puncturedEuclideanize
      (receiptWholeCorrection (run (lineage.current macroIndex) micro).nextContact.prefixReceipt modes time)‖ ^ 2 ≤
      3 * wholeBudget ‖puncturedWholeVelocityEuclideanState (lineage.current 0).initialState‖ :=
  controlled _ modes time _ ((original_velocity_bound (lineage.current macroIndex) micro time).trans
    (NativeNormControl.macro_initial_velocity_norm_le lineage macroIndex))

end
end SaturationMonoid.NavierStokes.NativeTurbulenceControl
