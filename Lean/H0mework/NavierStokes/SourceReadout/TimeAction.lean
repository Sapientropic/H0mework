import H0mework.NavierStokes.SourceReadout.Receipt

/-!
# Actual receipt action and original velocity write-back

The original heat-Duhamel path differentiates at each physical receipt time.
Velocity, pressure, and flux are the same source readouts. Finite physical
observations consume the complete input action. The integrated action returns
the original current-to-next velocity difference on every nonzero Fourier row.
-/

set_option autoImplicit false
open scoped BigOperators

namespace SaturationMonoid.NavierStokes.NativeStressSource

open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeActualRoot

noncomputable section

theorem receipt_vorticity_hasDerivAt {nu : Viscosity} {initial : ComplexVorticityHilbertState}
    {duration : ℝ} (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (wave : IntegerWavevector) (nonzero : wave ≠ 0) (time : Icc (0 : ℝ) duration) :
    HasDerivAt (actualWholeContinuousHeatDuhamelPath receipt wave)
      (wholeLatticeVorticityFourierTangentAt nu.coeff (receipt.wholePath time) wave) time.1 := by
  have derivative := heatDuhamelComplexCoordinatePath_hasDerivAt_of_continuous
    (initial wave) (actualWholeContinuousNonlinearRow receipt wave)
    (nu.coeff * integerWaveViscousMultiplier wave) 0 time.1
    (actualWholeContinuousNonlinearRow_continuous receipt wave)
  change HasDerivAt (actualWholeContinuousHeatDuhamelPath receipt wave)
    (actualWholeContinuousNonlinearRow receipt wave time.1 -
      (nu.coeff * integerWaveViscousMultiplier wave) •
        actualWholeContinuousHeatDuhamelPath receipt wave time.1) time.1 at derivative
  rw [← wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath receipt wave nonzero time] at derivative
  have stateEq : (actualWholeProjectedTransversePath receipt time.1).1 = receipt.wholePath time := by
    change receipt.wholePath (projIcc (0 : ℝ) duration receipt.requestedTimePos.le time.1) = _
    rw [projIcc_of_mem receipt.requestedTimePos.le time.2]
  simpa only [actualWholeContinuousNonlinearRow, stateEq, wholeLatticeVorticityFourierTangentAt]
    using derivative

/-- The original heat-Duhamel extension reads the same velocity on the entire physical receipt. -/
def receiptVelocityRow {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (wave : IntegerWavevector)
    (time : ℝ) : ComplexCoordinateVector :=
  biotSavartVelocityCoefficient wave (actualWholeContinuousHeatDuhamelPath receipt wave time)

theorem receiptVelocityRow_eq {nu : Viscosity} {initial : ComplexVorticityHilbertState}
    {duration : ℝ} (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (wave : IntegerWavevector) (nonzero : wave ≠ 0) (time : Icc (0 : ℝ) duration) :
    receiptVelocityRow receipt wave time.1 = wholeBiotSavartVelocityState (receipt.wholePath time) wave := by
  rw [receiptVelocityRow,
    ← wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath receipt wave nonzero time]
  rfl

theorem receipt_velocity_hasDerivAt {nu : Viscosity} {initial : ComplexVorticityHilbertState}
    {duration : ℝ} (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (wave : IntegerWavevector) (nonzero : wave ≠ 0) (time : Icc (0 : ℝ) duration) :
    HasDerivAt (receiptVelocityRow receipt wave)
      (nativeFluidStressDivergenceCoefficient
          (quadraticFlux (wholeBiotSavartVelocityState (receipt.wholePath time))) wave -
        ((Complex.I * (((2 * Real.pi : ℝ) : ℂ))) * sourcePressure (receipt.wholePath time) wave) •
          complexWavevector wave -
        (nu.coeff * integerWaveViscousMultiplier wave) •
          wholeBiotSavartVelocityState (receipt.wholePath time) wave) time.1 := by
  have derivative := (biotSavartVelocityCLM wave).hasFDerivAt.comp_hasDerivAt time.1
    (receipt_vorticity_hasDerivAt receipt wave nonzero time)
  rw [biotSavartVelocityCLM_apply, source_momentum_action nu.coeff (receipt.wholePath time)
    (receipt.wholePath_zero_row time) (wholePath_transverse receipt time) wave nonzero] at derivative
  exact derivative

/-- Evaluation of the existing Fourier character is a linear observation, not a new velocity. -/
def realModeCLM (wave : IntegerWavevector) (space : PhysicalSpace) :
    ComplexCoordinateVector →L[ℝ] PhysicalSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := fun value => realComplexFourierMode wave value space
      map_add' := by
        intro left right
        apply PiLp.ext
        intro direction
        simp [realComplexFourierMode, coefficientReal, coefficientImag, mul_add]
        ring
      map_smul' := by
        intro scalar value
        apply PiLp.ext
        intro direction
        simp [realComplexFourierMode, coefficientReal, coefficientImag, smul_eq_mul]
        ring }

/-- An arbitrary finite observation reads the same original complete receipt. -/
def receiptPhysicalVelocity {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (modes : Finset IntegerWavevector) (space : PhysicalSpace) (time : ℝ) : PhysicalSpace :=
  ∑ wave ∈ modes, realModeCLM wave space (receiptVelocityRow receipt wave time)

theorem receiptPhysicalVelocity_eq {nu : Viscosity} {initial : ComplexVorticityHilbertState}
    {duration : ℝ} (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (modes : Finset IntegerWavevector) (nonzero : 0 ∉ modes)
    (space : PhysicalSpace) (time : Icc (0 : ℝ) duration) :
    receiptPhysicalVelocity receipt modes space time.1 =
      finiteRealComplexFourierField modes
        (fun wave => wholeBiotSavartVelocityState (receipt.wholePath time) wave) space := by
  apply Finset.sum_congr rfl
  intro wave inside
  rw [receiptVelocityRow_eq receipt wave (fun zero => nonzero (zero ▸ inside)) time]
  rfl

theorem receiptPhysicalVelocity_hasDerivAt {nu : Viscosity} {initial : ComplexVorticityHilbertState}
    {duration : ℝ} (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (modes : Finset IntegerWavevector) (nonzero : 0 ∉ modes)
    (space : PhysicalSpace) (time : Icc (0 : ℝ) duration) :
    HasDerivAt (receiptPhysicalVelocity receipt modes space)
      (finiteRealComplexFourierField modes (fun wave => biotSavartVelocityCoefficient wave
        (wholeLatticeVorticityFourierTangentAt nu.coeff (receipt.wholePath time) wave)) space) time.1 := by
  apply HasDerivAt.fun_sum
  intro wave inside
  have velocity := (biotSavartVelocityCLM wave).hasFDerivAt.comp_hasDerivAt time.1
    (receipt_vorticity_hasDerivAt receipt wave (fun zero => nonzero (zero ▸ inside)) time)
  exact (realModeCLM wave space).hasFDerivAt.comp_hasDerivAt time.1 velocity

def receiptMomentumAction {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (wave : IntegerWavevector)
    (actual : ℝ) : ComplexCoordinateVector :=
  biotSavartVelocityCoefficient wave (wholeLatticeVorticityFourierTangentAt nu.coeff
    (actualWholeProjectedTransversePath receipt actual).1 wave)

theorem receiptMomentumAction_continuous {nu : Viscosity} {initial : ComplexVorticityHilbertState}
    {duration : ℝ} (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (wave : IntegerWavevector) : Continuous (receiptMomentumAction receipt wave) := by
  have row : Continuous (fun actual => (actualWholeProjectedTransversePath receipt actual).1 wave) :=
    (lp.evalCLM ℝ _ 2 wave).continuous.comp
      (receipt.wholePath.continuous.comp continuous_projIcc)
  exact (biotSavartVelocityCLM wave).continuous.comp
    ((actualWholeContinuousNonlinearRow_continuous receipt wave).sub
      (row.const_smul (nu.coeff * integerWaveViscousMultiplier wave)))

/-- The integrated source action returns the original complete velocity row at the endpoint. -/
theorem receipt_velocity_write {nu : Viscosity} {initial : ComplexVorticityHilbertState}
    {duration : ℝ} (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (wave : IntegerWavevector) (nonzero : wave ≠ 0) :
    (∫ actual in 0..duration, receiptMomentumAction receipt wave actual) =
      wholeBiotSavartVelocityState
        (receipt.wholePath ⟨duration, receipt.requestedTimePos.le, le_rfl⟩) wave -
      wholeBiotSavartVelocityState initial wave := by
  have derivative (actual : ℝ) (inside : actual ∈ uIcc (0 : ℝ) duration) :
      HasDerivAt (receiptVelocityRow receipt wave)
        (receiptMomentumAction receipt wave actual) actual := by
    have member : actual ∈ Icc (0 : ℝ) duration := by
      rwa [uIcc_of_le receipt.requestedTimePos.le] at inside
    have generated := (biotSavartVelocityCLM wave).hasFDerivAt.comp_hasDerivAt actual
      (receipt_vorticity_hasDerivAt receipt wave nonzero ⟨actual, member⟩)
    change HasDerivAt (receiptVelocityRow receipt wave)
      (biotSavartVelocityCoefficient wave
        (wholeLatticeVorticityFourierTangentAt nu.coeff (receipt.wholePath ⟨actual, member⟩) wave)) actual
      at generated
    change HasDerivAt (receiptVelocityRow receipt wave)
      (biotSavartVelocityCoefficient wave (wholeLatticeVorticityFourierTangentAt nu.coeff
        (receipt.wholePath (projIcc (0 : ℝ) duration receipt.requestedTimePos.le actual)) wave)) actual
    rw [projIcc_of_mem receipt.requestedTimePos.le member]
    exact generated
  have write := intervalIntegral.integral_eq_sub_of_hasDerivAt derivative
    ((receiptMomentumAction_continuous receipt wave).intervalIntegrable 0 duration)
  rw [receiptVelocityRow_eq receipt wave nonzero ⟨duration, receipt.requestedTimePos.le, le_rfl⟩,
    receiptVelocityRow_eq receipt wave nonzero ⟨0, le_rfl, receipt.requestedTimePos.le⟩,
    receipt.wholePath_initial] at write
  exact write

/-- Same-source impulse, current and literal next commute on every original nonzero wave. -/
theorem occurrence_velocity_write {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) (wave : IntegerWavevector) (nonzero : wave ≠ 0) :
    let occurrence := generatedWholeRestartNativeActualOccurrence initial index
    (∫ actual in 0..occurrence.response.1.contact.time.1,
      receiptMomentumAction (occurrenceReceipt occurrence) wave actual) =
      wholeBiotSavartVelocityState occurrence.response.1.contact.physicalState wave -
        wholeBiotSavartVelocityState (run initial index).contact.physicalState wave := by
  exact receipt_velocity_write _ wave nonzero

end
end SaturationMonoid.NavierStokes.NativeStressSource
