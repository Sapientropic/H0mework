import H0mework.Physics.ADCRuntime.EndpointResidual

/-!
# Uniform successor coordinates for endpoint-seeded ADC runs

The endpoint residual bounds are stable under changing the next binary command.
This layer turns the resulting voltage/current residual bounds into a uniform
inverse-shear coordinate envelope for the next homogeneous trajectory.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Interface
open Netlist.Dissipative.Producer
open Netlist.Dissipative.Dimensioned.Producer
open Netlist.Dissipative.Dimensioned.Driven.Interface
open Physical.Units.Interface

noncomputable section

def finiteADCSuccessorVoltageResidualBoundAt
    (core : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  (1 + 17 * finiteADCSuccessorInductorRatioAt core channel) / 8

def finiteADCSuccessorCurrentResidualBoundAt
    (core : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  (17 : ℝ) / 8 * finiteADCSuccessorPeriodicCurrentRatioBoundAt core channel

theorem finiteADCSuccessorVoltageResidualBound_pos
    (core : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel) :
    0 < finiteADCSuccessorVoltageResidualBoundAt core channel := by
  unfold finiteADCSuccessorVoltageResidualBoundAt
  have ratioPos := finiteADCSuccessorInductorRatio_pos core channel
  nlinarith

theorem finiteADCSuccessorCurrentResidualBound_pos
    (core : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel) :
    0 < finiteADCSuccessorCurrentResidualBoundAt core channel := by
  unfold finiteADCSuccessorCurrentResidualBoundAt
  exact mul_pos (by norm_num)
    (finiteADCSuccessorPeriodicCurrentRatioBound_pos core channel)

/-- Changing the next command adds only the old and new periodic coordinates
to the actual endpoint error. -/
theorem finiteADCResidualAfterCommandChange_abs_lt
    {valueError oldValue nextValue errorBound oldBound nextBound : ℝ}
    (errorLt : |valueError| < errorBound)
    (oldLe : |oldValue| ≤ oldBound)
    (nextLe : |nextValue| ≤ nextBound) :
    |valueError + oldValue - nextValue| <
      errorBound + oldBound + nextBound := by
  have first := abs_add_le valueError oldValue
  have second := abs_sub (valueError + oldValue) nextValue
  linarith

theorem finiteADCGeneratedEndpoint_nextInitialResidual_bounds
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive nextDrive : FiniteBinaryDrive)
    (channel : FiniteEmbodimentChannel) (processingTicks : Nat := 0) :
    let core := source.meteredSource.fixture.coreSource
    let physicalSource := finiteADCCorePhysicalSource core
    let endpoint := finiteADCGeneratedPhysicalEndpointAt
      source drive processingTicks
    |drivenInitialVoltageResidualRatioAt physicalSource
          (sourceOwnedResonantDrivenFrequencyAt core)
          (sourceOwnedResonantDrivenDriveAt core (binaryDriveState nextDrive))
          endpoint channel| <
        finiteADCSuccessorVoltageResidualBoundAt core channel ∧
      |drivenInitialCurrentResidualRatioAt physicalSource
          (sourceOwnedResonantDrivenFrequencyAt core)
          (sourceOwnedResonantDrivenDriveAt core (binaryDriveState nextDrive))
          endpoint channel| <
        finiteADCSuccessorCurrentResidualBoundAt core channel := by
  dsimp only
  let core := source.meteredSource.fixture.coreSource
  let physicalSource := finiteADCCorePhysicalSource core
  let endpoint := finiteADCGeneratedPhysicalEndpointAt
    source drive processingTicks
  let physicalTime := finiteADCClockedSwitchTime source drive processingTicks
  have voltageError :=
    finiteADCGeneratedEndpoint_voltageError_normalized_abs_lt
      source drive channel processingTicks
  have oldVoltage :=
    resonantPeriodicBinaryDriveCapacitor_normalized_abs_le
      core drive channel physicalTime
  have nextVoltage :=
    resonantPeriodicBinaryDriveCapacitor_normalized_abs_le
      core nextDrive channel 0
  have currentError :=
    finiteADCGeneratedEndpoint_currentError_normalized_abs_lt
      source drive channel processingTicks
  have oldCurrent :=
    resonantPeriodicBinaryDriveCurrent_normalized_abs_le
      core drive channel physicalTime
  have nextCurrent :=
    resonantPeriodicBinaryDriveCurrent_normalized_abs_le
      core nextDrive channel 0
  have voltageDecomposition :
      drivenInitialVoltageResidualRatioAt physicalSource
          (sourceOwnedResonantDrivenFrequencyAt core)
          (sourceOwnedResonantDrivenDriveAt core (binaryDriveState nextDrive))
          endpoint channel =
        ((endpoint.voltageAt channel -
            drivenPeriodicVoltageAt physicalSource channel
              (sourceOwnedResonantDrivenFrequencyAt core channel)
              (sourceOwnedResonantDrivenDriveAt core
                (binaryDriveState drive) channel) physicalTime).value /
            core.2.voltageScale.value) +
          (drivenPeriodicVoltageAt physicalSource channel
              (sourceOwnedResonantDrivenFrequencyAt core channel)
              (sourceOwnedResonantDrivenDriveAt core
                (binaryDriveState drive) channel) physicalTime).value /
            core.2.voltageScale.value -
          (drivenPeriodicVoltageAt physicalSource channel
              (sourceOwnedResonantDrivenFrequencyAt core channel)
              (sourceOwnedResonantDrivenDriveAt core
                (binaryDriveState nextDrive) channel) 0).value /
            core.2.voltageScale.value := by
    unfold drivenInitialVoltageResidualRatioAt
    simp only [SIQuantity.sub_value]
    simp only [physicalSource, finiteADCCorePhysicalSource,
      resonantDrivenCoreDimensionedSource]
    ring
  have currentDecomposition :
      drivenInitialCurrentResidualRatioAt physicalSource
          (sourceOwnedResonantDrivenFrequencyAt core)
          (sourceOwnedResonantDrivenDriveAt core (binaryDriveState nextDrive))
          endpoint channel =
        ((endpoint.currentAt channel -
            drivenPeriodicCurrentAt physicalSource channel
              (sourceOwnedResonantDrivenFrequencyAt core channel)
              (sourceOwnedResonantDrivenDriveAt core
                (binaryDriveState drive) channel) physicalTime).value /
            core.2.currentScale.value) +
          (drivenPeriodicCurrentAt physicalSource channel
              (sourceOwnedResonantDrivenFrequencyAt core channel)
              (sourceOwnedResonantDrivenDriveAt core
                (binaryDriveState drive) channel) physicalTime).value /
            core.2.currentScale.value -
          (drivenPeriodicCurrentAt physicalSource channel
              (sourceOwnedResonantDrivenFrequencyAt core channel)
              (sourceOwnedResonantDrivenDriveAt core
                (binaryDriveState nextDrive) channel) 0).value /
            core.2.currentScale.value := by
    unfold drivenInitialCurrentResidualRatioAt
    simp only [SIQuantity.sub_value]
    simp only [physicalSource, finiteADCCorePhysicalSource,
      resonantDrivenCoreDimensionedSource]
    ring
  constructor
  · rw [voltageDecomposition]
    have bound := finiteADCResidualAfterCommandChange_abs_lt
      voltageError oldVoltage nextVoltage
    dsimp only [core] at bound ⊢
    unfold finiteADCSuccessorVoltageResidualBoundAt
    nlinarith
  · rw [currentDecomposition]
    have bound := finiteADCResidualAfterCommandChange_abs_lt
      currentError oldCurrent nextCurrent
    dsimp only [core] at bound ⊢
    unfold finiteADCSuccessorCurrentResidualBoundAt
    nlinarith

def finiteADCSuccessorCoordinateEnvelopeBoundAt
    (core : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  let run := finiteADCCoreNormalizedRun core
  let voltageBound := finiteADCSuccessorVoltageResidualBoundAt core channel
  let currentBound := finiteADCSuccessorCurrentResidualBoundAt core channel
  (currentBound + run.dampingRateAt channel * voltageBound) /
      run.baseRun.frequencyAt channel + voltageBound

theorem finiteADCSuccessorCoordinateEnvelopeBound_nonneg
    (core : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel) :
    0 ≤ finiteADCSuccessorCoordinateEnvelopeBoundAt core channel := by
  unfold finiteADCSuccessorCoordinateEnvelopeBoundAt
  have frequencyPos := compiledFiniteSeriesRLCNetlistRun_frequency_pos
    (finiteADCCorePhysicalSource core).1 channel
  have dampingNonnegative :
      0 ≤ (finiteADCCoreNormalizedRun core).dampingRateAt channel := by
    unfold finiteADCCoreNormalizedRun
    rw [compiledFiniteSeriesRLCNetlistRun_dampingRateAt]
    exact finiteSeriesRLCDampingRate_pos.le
  exact add_nonneg
    (div_nonneg
      (add_nonneg
        (finiteADCSuccessorCurrentResidualBound_pos core channel).le
        (mul_nonneg dampingNonnegative
          (finiteADCSuccessorVoltageResidualBound_pos core channel).le))
      frequencyPos.le)
    (finiteADCSuccessorVoltageResidualBound_pos core channel).le

theorem finiteADCGeneratedEndpoint_nextCoordinateEnvelope_le
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive nextDrive : FiniteBinaryDrive)
    (channel : FiniteEmbodimentChannel) (processingTicks : Nat := 0) :
    let core := source.meteredSource.fixture.coreSource
    drivenHomogeneousCoordinateEnvelopeAt (finiteADCCorePhysicalSource core)
        (sourceOwnedResonantDrivenFrequencyAt core)
        (sourceOwnedResonantDrivenDriveAt core (binaryDriveState nextDrive))
        (finiteADCGeneratedPhysicalEndpointAt
          source drive processingTicks) channel ≤
      finiteADCSuccessorCoordinateEnvelopeBoundAt core channel := by
  dsimp only
  let core := source.meteredSource.fixture.coreSource
  let physicalSource := finiteADCCorePhysicalSource core
  let frequencyAt := sourceOwnedResonantDrivenFrequencyAt core
  let driveAt := sourceOwnedResonantDrivenDriveAt core (binaryDriveState nextDrive)
  let endpoint := finiteADCGeneratedPhysicalEndpointAt
    source drive processingTicks
  let voltageResidual :=
    drivenInitialVoltageResidualRatioAt physicalSource frequencyAt driveAt
      endpoint channel
  let currentResidual :=
    drivenInitialCurrentResidualRatioAt physicalSource frequencyAt driveAt
      endpoint channel
  have residualBounds :=
    finiteADCGeneratedEndpoint_nextInitialResidual_bounds
      source drive nextDrive channel processingTicks
  have voltageLe := le_of_lt residualBounds.left
  have currentLe := le_of_lt residualBounds.right
  have frequencyPos := compiledFiniteSeriesRLCNetlistRun_frequency_pos
    (finiteADCCorePhysicalSource core).1 channel
  have frequencyPos' :
      0 < (finiteADCCoreNormalizedRun core).baseRun.frequencyAt channel :=
    frequencyPos
  have dampingNonnegative :
      0 ≤ (finiteADCCoreNormalizedRun core).dampingRateAt channel := by
    unfold finiteADCCoreNormalizedRun
    rw [compiledFiniteSeriesRLCNetlistRun_dampingRateAt]
    exact finiteSeriesRLCDampingRate_pos.le
  unfold drivenHomogeneousCoordinateEnvelopeAt
    finiteSeriesRLCInitialCoordinateEnvelopeAt
    drivenHomogeneousInitialAt
  dsimp only
  change
    |(currentResidual +
          (finiteADCCoreNormalizedRun core).dampingRateAt channel *
            voltageResidual) /
        (finiteADCCoreNormalizedRun core).baseRun.frequencyAt channel| +
      |voltageResidual| ≤
        finiteADCSuccessorCoordinateEnvelopeBoundAt core channel
  rw [abs_div, abs_of_pos frequencyPos']
  apply le_trans (add_le_add
    (div_le_div_of_nonneg_right
      (abs_add_le currentResidual
        ((finiteADCCoreNormalizedRun core).dampingRateAt channel *
          voltageResidual)) frequencyPos.le) le_rfl)
  rw [abs_mul, abs_of_nonneg dampingNonnegative]
  exact add_le_add
    (div_le_div_of_nonneg_right
      (add_le_add currentLe
        (mul_le_mul_of_nonneg_left voltageLe dampingNonnegative))
      frequencyPos.le)
    voltageLe

end

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
