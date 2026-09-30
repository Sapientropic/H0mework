import H0mework.NavierStokes.SourceReadout.Action
import H0mework.NavierStokes.CorrectionControl.Actual

/-!
# Original occurrence consumes its source stress

The actual root target supplies the contact prefix receipt. Its physical-time
equation consumes the complete source stress and the original kinetic budget.
The source, event, ledger compiler and generated next remain the original ones.
-/

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeStressSource

open scoped BigOperators
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeReceiptKineticTimeModulus
open NativeStressCurlAlgebra
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeActualRoot

noncomputable section

/-- The generated stress enters the original physical-time receipt equation. -/
theorem receipt_vorticity_action {nu : Viscosity} {initial : ComplexVorticityHilbertState}
    {duration : ℝ} (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (modes : Finset IntegerWavevector) (wave : IntegerWavevector) (nonzero : wave ≠ 0) :
    ∀ᵐ time ∂commonTimeMeasure duration,
      (if wave ∈ modes then receipt.rowTangent wave nonzero time else 0) =
        wholeLatticeVorticityFourierTangentAt nu.coeff
          (complexSharpSupportProjection modes (receipt.wholePath time)) wave +
        nativeFluidConstitutiveVorticityAction (correctionStress modes (receipt.wholePath time)) wave := by
  filter_upwards [receipt_projectedRowTangent_eq_classical_add_nativeTurbulence_ae
    receipt modes wave nonzero] with time equation
  rwa [correctionStress_action modes _ (receipt.wholePath_zero_row time)
    (wholePath_transverse receipt time)]

theorem receipt_stress_norm_le {nu : Viscosity} {initial : ComplexVorticityHilbertState}
    {duration : ℝ} (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (modes : Finset IntegerWavevector) (time : Icc (0 : ℝ) duration)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ‖correctionStress modes (receipt.wholePath time) wave output input‖ ≤
      2 * ‖puncturedWholeVelocityEuclideanState initial‖ ^ 2 := by
  have bound := correctionStress_norm_le_kinetic modes (receipt.wholePath time)
    (wholePath_transverse receipt time) wave output input
  rw [← puncturedWholeVelocityEuclideanState_norm_sq _ (wholePath_transverse receipt time)] at bound
  exact bound.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (NativeNormControl.receipt_velocity_norm_le receipt time)) (by norm_num))

/-- Eliminate the original occurrence's target: its receipt is the actual next contact's prefix. -/
def occurrenceReceipt {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu} {index : ℕ}
    (occurrence : GeneratedWholeRestartNativeActualOccurrenceAt initial index) :=
  occurrence.response.1.contact.prefixReceipt

/-- This consumer reads the stress and time equation from the compiler's exact next. -/
theorem occurrence_vorticity_action {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) (modes : Finset IntegerWavevector) (wave : IntegerWavevector) (nonzero : wave ≠ 0) :
    let occurrence := generatedWholeRestartNativeActualOccurrence initial index
    let receipt := occurrenceReceipt occurrence
    ∀ᵐ time ∂commonTimeMeasure occurrence.response.1.contact.time.1,
      (if wave ∈ modes then receipt.rowTangent wave nonzero time else 0) =
        wholeLatticeVorticityFourierTangentAt nu.coeff
          (complexSharpSupportProjection modes (receipt.wholePath time)) wave +
        nativeFluidConstitutiveVorticityAction (correctionStress modes (receipt.wholePath time)) wave :=
  receipt_vorticity_action _ modes wave nonzero

theorem occurrence_stress_norm_le {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) (modes : Finset IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ‖correctionStress modes
        ((occurrenceReceipt (generatedWholeRestartNativeActualOccurrence initial index)).wholePath time)
        wave output input‖ ≤ 2 * ‖puncturedWholeVelocityEuclideanState initial.initialState‖ ^ 2 := by
  have bound := receipt_stress_norm_le (run initial index).nextContact.prefixReceipt
    modes time wave output input
  have initialBound := (wholeRestartContactVelocityState_norm_le_initial initial index).trans
    (NativeNormControl.contact_velocity_norm_le_initial initial)
  exact bound.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr initialBound) (by norm_num))

end
end SaturationMonoid.NavierStokes.NativeStressSource
