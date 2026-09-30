import H0mework.NavierStokes.ConstitutiveAction.Fourier

set_option autoImplicit false
open scoped BigOperators

namespace SaturationMonoid.NavierStokes.NativeConstitutiveOccurrence

open MeasureTheory Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeActualRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open NativePhysicalFourier NativePhysicalSource NativeConstitutiveFourier NativeStressCurlAlgebra

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def correction (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState) : NativeFluidStressFourierState :=
  (fun wave => if wave ∈ modes then fourier (realField (wholeBiotSavartVelocityState state)) wave else 0) -
    fourier (realField (wholeBiotSavartVelocityState (complexSharpSupportProjection modes state)))

/-- The filter commutator of the actual mother constitutive stress is the original native correction. -/
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

theorem receipt_vorticity_action {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (modes : Finset IntegerWavevector) (negClosed : ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (wave : IntegerWavevector) (nonzero : wave ≠ 0) :
    ∀ᵐ time ∂commonTimeMeasure duration,
      (if wave ∈ modes then receipt.rowTangent wave nonzero time else 0) =
        wholeLatticeVorticityFourierTangentAt nu.coeff (complexSharpSupportProjection modes (receipt.wholePath time)) wave +
          nativeFluidConstitutiveVorticityAction (correction modes (receipt.wholePath time)) wave := by
  filter_upwards [receipt_projectedRowTangent_eq_classical_add_nativeTurbulence_ae receipt modes wave nonzero] with time equation
  rwa [correction_action modes negClosed _ (receipt_reality receipt time)
    (receipt.wholePath_zero_row time) (wholePath_transverse receipt time)]

def vorticityAction (viscosity : ℝ) (state : ComplexVorticityHilbertState) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  nativeFluidConstitutiveVorticityAction (fourier (realField (wholeBiotSavartVelocityState state))) wave -
    (viscosity * integerWaveViscousMultiplier wave) • state wave

theorem vorticityAction_eq (viscosity : ℝ) (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state) (zero : state 0 = 0) (transverse : WholeStateTransverse state) :
    vorticityAction viscosity state = wholeLatticeVorticityFourierTangentAt viscosity state := by
  funext wave
  rw [vorticityAction, source_action state reality zero transverse]
  rfl

def receiptMomentumAction {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (wave : IntegerWavevector) (actual : ℝ) : ComplexCoordinateVector :=
  biotSavartVelocityCoefficient wave (vorticityAction nu.coeff
    (receipt.wholePath (projIcc (0 : ℝ) duration receipt.requestedTimePos.le actual)) wave)

theorem receiptMomentumAction_eq {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (wave : IntegerWavevector) :
    receiptMomentumAction receipt wave = NativeStressSource.receiptMomentumAction receipt wave := by
  funext actual
  rw [receiptMomentumAction, vorticityAction_eq _ _ (receipt_reality receipt _)
    (receipt.wholePath_zero_row _) (wholePath_transverse receipt _)]
  rfl

/-- The original compiler's literal next consumes the same source-generated mother constitutive impulse. -/
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

end
end SaturationMonoid.NavierStokes.NativeConstitutiveOccurrence
