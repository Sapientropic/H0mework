import H0mework.NavierStokes.MaterialGauge.Fourier

set_option autoImplicit false
open scoped BigOperators

namespace SaturationMonoid.NavierStokes.NativeGaugeOccurrence

open MeasureTheory Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeActualRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open NativePhysicalFourier NativePhysicalSource NativePhysicalTimeAction NativeGaugeMomentum NativeGaugeFlux NativeStressCurlAlgebra

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def correction (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState) : NativeFluidStressFourierState :=
  (fun wave => if wave ∈ modes then fourier (realField (wholeBiotSavartVelocityState state)) wave else 0) -
    fourier (realField (wholeBiotSavartVelocityState (complexSharpSupportProjection modes state)))

/-- The original native correction is the filter commutator of the source gauge matter current. -/
theorem correction_action (modes : Finset IntegerWavevector)
    (negClosed : ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality state)
    (zero : state 0 = 0) (transverse : WholeStateTransverse state) (wave : IntegerWavevector) :
    nativeFluidConstitutiveVorticityAction (correction modes state) wave = nativeTurbulenceCorrectionAt modes state wave := by
  have projectedZero : complexSharpSupportProjection modes state 0 = 0 := by
    simp [complexSharpSupportProjection_apply, zero]
  rw [correction, ← wholeStressActionCLM_apply, map_sub]
  simp only [Pi.sub_apply, wholeStressActionCLM_apply]
  rw [nativeFluidConstitutiveVorticityAction_projection, source_action state reality zero transverse,
    source_action _ (complexSharpSupportProjection_reality modes state negClosed reality)
      projectedZero (wholeStateTransverse_projection modes state transverse)]
  rfl

def receiptMomentumAction {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (wave : IntegerWavevector) (actual : ℝ) : ComplexCoordinateVector :=
  let state := receipt.wholePath (projIcc (0 : ℝ) T receipt.requestedTimePos.le actual)
  biotSavartVelocityCoefficient wave (nativeFluidConstitutiveVorticityAction
    (fourier (realField (wholeBiotSavartVelocityState state))) wave -
      (nu.coeff * integerWaveViscousMultiplier wave) • state wave)

theorem receiptMomentumAction_eq {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (wave : IntegerWavevector) :
    receiptMomentumAction receipt wave = NativeStressSource.receiptMomentumAction receipt wave := by
  funext actual
  rw [receiptMomentumAction, source_action _ (receipt_reality receipt _)
    (receipt.wholePath_zero_row _) (wholePath_transverse receipt _)]
  rfl

/-- The action read from this same charged current writes the original compiler next. -/
theorem occurrence_velocity_write {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) (wave : IntegerWavevector) (nonzero : wave ≠ 0) :
    let occurrence := generatedWholeRestartNativeActualOccurrence initial index
    (∫ actual in 0..occurrence.response.1.contact.time.1,
      receiptMomentumAction (NativeStressSource.occurrenceReceipt occurrence) wave actual) =
      wholeBiotSavartVelocityState occurrence.response.1.contact.physicalState wave -
        wholeBiotSavartVelocityState (run initial index).contact.physicalState wave := by
  dsimp only
  rw [receiptMomentumAction_eq]
  exact NativeStressSource.occurrence_velocity_write initial index wave nonzero

def temporalCurrent (value : PhysicalField) : PhysicalField := -value

theorem temporalCurrent_apply (value : PhysicalField) :
    ∀ᵐ point : Torus, ∀ color : Fin 3, temporalCurrent value point color =
      current (value point) (momentumVariation (value point) 0 color) := by
  filter_upwards [Lp.coeFn_neg value] with point actual color
  rw [temporalCurrent, actual, Pi.neg_apply, momentum_temporal]
  rfl

theorem occurrence_temporalCurrent_write {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu) (index : ℕ) :
    let occurrence := generatedWholeRestartNativeActualOccurrence initial index
    (∫ actual in 0..occurrence.response.1.contact.time.1,
      -physicalTangent (NativeStressSource.occurrenceReceipt occurrence) actual) =
      temporalCurrent (realField (wholeBiotSavartVelocityState occurrence.response.1.contact.physicalState)) -
        temporalCurrent (realField (wholeBiotSavartVelocityState (run initial index).contact.physicalState)) := by
  dsimp only
  rw [intervalIntegral.integral_neg, occurrence_physical_write]
  simp only [temporalCurrent]
  abel

end
end SaturationMonoid.NavierStokes.NativeGaugeOccurrence
