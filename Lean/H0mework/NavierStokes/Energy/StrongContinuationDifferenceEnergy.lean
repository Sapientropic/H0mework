import H0mework.NavierStokes.LocalEvolution.StrongContinuationDifferenceEquation
import H0mework.NavierStokes.ShellSources.StrongContinuationEnergyLedger

/-!
# Exact energy transport for the strong-continuation difference

The actual coefficient paths of two strong continuations on the same
generated lineage are subtracted before energy is read.  Every nonzero
Fourier difference row is absolutely continuous, has the difference of the
two genuine Navier--Stokes tangents, and starts from zero.  Its exact energy
identity is then assembled over the complete nonzero integer-frequency
carrier at every time in the requested interval.

No equality between the paths, compatibility certificate, finite cutoff,
target endpoint, energy inequality, or uniqueness conclusion is supplied by
a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceEnergy

open scoped BigOperators Topology

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeContinuousMild
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuation
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceEquation

noncomputable section

section SameHorizon

variable
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}

/-- The real-line difference of the two actual nonzero Fourier paths. -/
def actualWaveDifferencePath
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector) :
    ℝ → ComplexCoordinateVector :=
  fun time =>
    WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
        left.toWholeContinuousMildReceipt wave.1 time -
      WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
        right.toWholeContinuousMildReceipt wave.1 time

/--
The exact tangent of the actual coefficient difference path.  Both
nonlinear rows and both viscous rows remain visible before subtraction.
-/
def actualWaveDifferenceTangent
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector) :
    ℝ → ComplexCoordinateVector :=
  fun time =>
    (WholeContinuousMildReceipt.actualWaveNonlinearExtension
          left.toWholeContinuousMildReceipt wave.1 time -
        (ν.coeff * integerWaveViscousMultiplier wave.1) •
          WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
            left.toWholeContinuousMildReceipt wave.1 time) -
      (WholeContinuousMildReceipt.actualWaveNonlinearExtension
          right.toWholeContinuousMildReceipt wave.1 time -
        (ν.coeff * integerWaveViscousMultiplier wave.1) •
          WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
            right.toWholeContinuousMildReceipt wave.1 time)

/-- The actual coefficient difference path is absolutely continuous. -/
theorem actualWaveDifferencePath_absolutelyContinuousOnInterval
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector) :
    AbsolutelyContinuousOnInterval
      (actualWaveDifferencePath left right wave)
      0 requestedTime := by
  exact
    (heatDuhamelComplexCoordinatePath_absolutelyContinuousOnInterval
      (left.initialState wave.1)
      (ν.coeff * integerWaveViscousMultiplier wave.1)
      0
      (WholeContinuousMildReceipt.actualWaveNonlinearExtension_intervalIntegrable
        left.toWholeContinuousMildReceipt wave.1)
      (by simp [requestedTimePos.le])).sub
    (heatDuhamelComplexCoordinatePath_absolutelyContinuousOnInterval
      (right.initialState wave.1)
      (ν.coeff * integerWaveViscousMultiplier wave.1)
      0
      (WholeContinuousMildReceipt.actualWaveNonlinearExtension_intervalIntegrable
        right.toWholeContinuousMildReceipt wave.1)
      (by simp [requestedTimePos.le]))

/--
The derivative of the actual difference path is the difference of the two
complete nonlinear-minus-viscous coefficient tangents almost everywhere.
-/
theorem actualWaveDifferencePath_ae_hasDerivAt
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector) :
    ∀ᵐ time : ℝ,
      time ∈ uIcc (0 : ℝ) requestedTime →
        HasDerivAt
          (actualWaveDifferencePath left right wave)
          (actualWaveDifferenceTangent left right wave time)
          time := by
  filter_upwards [
    heatDuhamelComplexCoordinatePath_ae_hasDerivAt
      (left.initialState wave.1)
      (ν.coeff * integerWaveViscousMultiplier wave.1)
      0
      (WholeContinuousMildReceipt.actualWaveNonlinearExtension_intervalIntegrable
        left.toWholeContinuousMildReceipt wave.1)
      (by simp [requestedTimePos.le]),
    heatDuhamelComplexCoordinatePath_ae_hasDerivAt
      (right.initialState wave.1)
      (ν.coeff * integerWaveViscousMultiplier wave.1)
      0
      (WholeContinuousMildReceipt.actualWaveNonlinearExtension_intervalIntegrable
        right.toWholeContinuousMildReceipt wave.1)
      (by simp [requestedTimePos.le])] with
      time leftDerivative rightDerivative
  intro timeMem
  change
    HasDerivAt
      (fun actual =>
        WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
            left.toWholeContinuousMildReceipt wave.1 actual -
          WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
            right.toWholeContinuousMildReceipt wave.1 actual)
      ((WholeContinuousMildReceipt.actualWaveNonlinearExtension
            left.toWholeContinuousMildReceipt wave.1 time -
          (ν.coeff * integerWaveViscousMultiplier wave.1) •
            WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
              left.toWholeContinuousMildReceipt wave.1 time) -
        (WholeContinuousMildReceipt.actualWaveNonlinearExtension
            right.toWholeContinuousMildReceipt wave.1 time -
          (ν.coeff * integerWaveViscousMultiplier wave.1) •
            WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
              right.toWholeContinuousMildReceipt wave.1 time))
      time
  convert
    (leftDerivative timeMem).sub (rightDerivative timeMem)
      using 1 <;>
    rfl

/--
At every physical time, the real-line difference path is exactly the
corresponding row of the two generated whole continuous paths.
-/
theorem actualWaveDifferencePath_eq_wholePath_sub
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    actualWaveDifferencePath left right wave time.1 =
      left.wholePath time wave.1 -
        right.wholePath time wave.1 := by
  rw [actualWaveDifferencePath,
    ← WholeContinuousMildReceipt.wholePath_wave_eq_actualWaveHeatDuhamelPath
      left.toWholeContinuousMildReceipt wave.1 wave.2 time,
    ← WholeContinuousMildReceipt.wholePath_wave_eq_actualWaveHeatDuhamelPath
      right.toWholeContinuousMildReceipt wave.1 wave.2 time]

/-- The actual coefficient difference has zero source-generated initial row. -/
theorem actualWaveDifferencePath_zero
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector) :
    actualWaveDifferencePath left right wave 0 = 0 := by
  have atZero :=
    actualWaveDifferencePath_eq_wholePath_sub left right wave
      ⟨0, ⟨le_rfl, requestedTimePos.le⟩⟩
  rw [left.wholePath_initial, right.wholePath_initial,
    StrongContinuationReceipt.initialState_eq left right,
    sub_self] at atZero
  exact atZero

/--
Exact rowwise difference-energy transport up to every actual time in the
requested horizon.
-/
theorem actualWaveDifference_endpointEnergy_identity
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector)
    (terminal : Icc (0 : ℝ) requestedTime) :
    (∫ time in (0 : ℝ)..terminal.1,
        2 *
          complexCoordinateRealInner
            (actualWaveDifferencePath left right wave time)
            (actualWaveDifferenceTangent left right wave time)) =
      complexCoordinateAmplitudeSq
        (left.wholePath terminal wave.1 -
          right.wholePath terminal wave.1) := by
  have intervalSubset :
      uIcc (0 : ℝ) terminal.1 ⊆
        uIcc (0 : ℝ) requestedTime := by
    rw [uIcc_of_le terminal.2.1,
      uIcc_of_le requestedTimePos.le]
    exact Icc_subset_Icc le_rfl terminal.2.2
  have pathAC :=
    (actualWaveDifferencePath_absolutelyContinuousOnInterval
      left right wave).mono intervalSubset
  have pathDerivative :
      ∀ᵐ time : ℝ,
        time ∈ uIcc (0 : ℝ) terminal.1 →
          HasDerivAt
            (actualWaveDifferencePath left right wave)
            (actualWaveDifferenceTangent left right wave time)
            time := by
    filter_upwards [
      actualWaveDifferencePath_ae_hasDerivAt
        left right wave] with time derivative
    exact fun timeMem => derivative (intervalSubset timeMem)
  have energyIdentity :=
    AbsolutelyContinuousOnInterval.complexCoordinateAmplitudeSq_energy_identity
      pathAC pathDerivative
  rw [actualWaveDifferencePath_eq_wholePath_sub
      left right wave terminal,
    actualWaveDifferencePath_zero left right wave] at energyIdentity
  simpa [complexCoordinateAmplitudeSq] using energyIdentity

/-- One actual nonzero-wave work entry of the difference energy ledger. -/
def actualWaveDifferenceEnergyWork
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (terminal : Icc (0 : ℝ) requestedTime)
    (wave : NonzeroIntegerWavevector) : ℝ :=
  ∫ time in (0 : ℝ)..terminal.1,
    2 *
      complexCoordinateRealInner
        (actualWaveDifferencePath left right wave time)
        (actualWaveDifferenceTangent left right wave time)

theorem actualWaveDifferenceEnergyWork_eq
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (terminal : Icc (0 : ℝ) requestedTime)
    (wave : NonzeroIntegerWavevector) :
    actualWaveDifferenceEnergyWork left right terminal wave =
      complexCoordinateAmplitudeSq
        (left.wholePath terminal wave.1 -
          right.wholePath terminal wave.1) :=
  actualWaveDifference_endpointEnergy_identity
    left right wave terminal

/-- Exact finite-frequency difference energy at every physical time. -/
theorem finiteWaveDifference_endpointEnergy_identity
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (terminal : Icc (0 : ℝ) requestedTime)
    (waves : Finset NonzeroIntegerWavevector) :
    (∑ wave ∈ waves,
        actualWaveDifferenceEnergyWork left right terminal wave) =
      ∑ wave ∈ waves,
        complexCoordinateAmplitudeSq
          (left.wholePath terminal wave.1 -
            right.wholePath terminal wave.1) := by
  apply Finset.sum_congr rfl
  intro wave waveMem
  exact actualWaveDifferenceEnergyWork_eq
    left right terminal wave

/--
The complete nonzero-wave difference work is summable at every physical
time, generated by the actual endpoint difference state.
-/
theorem summable_actualWaveDifferenceEnergyWork
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (terminal : Icc (0 : ℝ) requestedTime) :
    Summable
      (actualWaveDifferenceEnergyWork left right terminal) := by
  have endpointSummable :=
    summable_puncturedWholeVorticityEuclideanMass
      (left.wholePath terminal - right.wholePath terminal)
  exact endpointSummable.congr fun wave => by
    rw [actualWaveDifferenceEnergyWork_eq]
    rfl

/--
The rowwise actual difference work assembles into the exact complete
punctured Euclidean mass of the whole endpoint difference.
-/
theorem tsum_actualWaveDifferenceEnergyWork_eq
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (terminal : Icc (0 : ℝ) requestedTime) :
    (∑' wave : NonzeroIntegerWavevector,
        actualWaveDifferenceEnergyWork
          left right terminal wave) =
      puncturedWholeVorticityEuclideanMass
        (left.wholePath terminal - right.wholePath terminal) := by
  rw [show
      (fun wave : NonzeroIntegerWavevector =>
        actualWaveDifferenceEnergyWork
          left right terminal wave) =
        fun wave =>
          complexCoordinateAmplitudeSq
            ((left.wholePath terminal -
              right.wholePath terminal) wave.1) by
      funext wave
      rw [actualWaveDifferenceEnergyWork_eq]
      rfl]
  rfl

end SameHorizon

end

end ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceEnergy
end NavierStokes
end SaturationMonoid
