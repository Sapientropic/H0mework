import H0mework.Physics.ADCRuntime.DelayedCounter

/-! # Core-only absolute bounds at every generated ADC endpoint

The source's actual settling time pays the initial residual, even after arbitrary
receiver processing. Neither the initial state nor the receiver width enters these envelopes.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Units.Interface Physical.Interface
open Netlist.Dissipative.Dimensioned.Producer Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

def finiteADCCoreVoltageEnvelopeAt (core : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel) : SIVolt :=
  ⟨core.2.voltageScale.value * (1 + 9 * finiteADCSuccessorInductorRatioAt core channel) / 8⟩

def finiteADCCoreCurrentEnvelopeAt (core : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel) : SIAmpere :=
  ⟨core.2.currentScale.value * ((9 : ℝ) / 8 *
    finiteADCSuccessorPeriodicCurrentRatioBoundAt core channel)⟩

theorem finiteADCCoreVoltageEnvelopeAt_pos (core : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel) : 0 < (finiteADCCoreVoltageEnvelopeAt core channel).value := by
  have ratio := finiteADCSuccessorInductorRatio_pos core channel
  exact div_pos (mul_pos core.2.voltageScalePositive (by positivity)) (by norm_num)

theorem finiteADCCoreCurrentEnvelopeAt_pos (core : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel) : 0 < (finiteADCCoreCurrentEnvelopeAt core channel).value :=
  mul_pos core.2.currentScalePositive
    (mul_pos (by norm_num) (finiteADCSuccessorPeriodicCurrentRatioBound_pos core channel))

private theorem absolute_of_normalized_residual {value periodic scale error bound : ℝ}
    (scalePositive : 0 < scale) (residual : |(value - periodic) / scale| < error)
    (periodicBound : |periodic / scale| ≤ bound) : |value| < scale * (error + bound) := by
  have normalized : |value / scale| < error + bound := calc
    |value / scale| = |(value - periodic) / scale + periodic / scale| := by congr 1; ring
    _ ≤ |(value - periodic) / scale| + |periodic / scale| := abs_add_le _ _
    _ < error + bound := add_lt_add_of_lt_of_le residual periodicBound
  rw [abs_div, abs_of_pos scalePositive] at normalized
  simpa only [mul_comm] using (div_lt_iff₀ scalePositive).mp normalized

theorem finiteADCGeneratedEndpoint_voltage_abs_lt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) (channel : FiniteEmbodimentChannel)
    (processingTicks : Nat := 0) :
    |((finiteADCGeneratedPhysicalEndpointAt source drive processingTicks).voltageAt channel).value| <
      (finiteADCCoreVoltageEnvelopeAt source.meteredSource.fixture.coreSource channel).value := by
  have error := finiteADCGeneratedEndpoint_voltageError_normalized_abs_lt
    source drive channel processingTicks
  dsimp only at error
  simp only [SIQuantity.sub_value] at error
  have periodic := resonantPeriodicBinaryDriveCapacitor_normalized_abs_le
    source.meteredSource.fixture.coreSource drive channel
    (finiteADCClockedSwitchTime source drive processingTicks)
  have bound := absolute_of_normalized_residual
    source.meteredSource.fixture.coreSource.2.voltageScalePositive error periodic
  convert bound using 1
  unfold finiteADCCoreVoltageEnvelopeAt
  dsimp only
  ring

theorem finiteADCGeneratedEndpoint_current_abs_lt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) (channel : FiniteEmbodimentChannel)
    (processingTicks : Nat := 0) :
    |((finiteADCGeneratedPhysicalEndpointAt source drive processingTicks).currentAt channel).value| <
      (finiteADCCoreCurrentEnvelopeAt source.meteredSource.fixture.coreSource channel).value := by
  have error := finiteADCGeneratedEndpoint_currentError_normalized_abs_lt
    source drive channel processingTicks
  dsimp only at error
  simp only [SIQuantity.sub_value] at error
  have periodic := resonantPeriodicBinaryDriveCurrent_normalized_abs_le
    source.meteredSource.fixture.coreSource drive channel
    (finiteADCClockedSwitchTime source drive processingTicks)
  have bound := absolute_of_normalized_residual
    source.meteredSource.fixture.coreSource.2.currentScalePositive error periodic
  convert bound using 1
  unfold finiteADCCoreCurrentEnvelopeAt
  dsimp only
  ring

theorem finiteADCPhysicalDelayedEndpoint_absolute_bounds
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (current : FiniteADCPhysicalRuntimeCurrent hardware) (processingTicks : Nat)
    (channel : FiniteEmbodimentChannel) :
    |((finiteADCPhysicalDelayedEndpoint current processingTicks).voltageAt channel).value| <
        (finiteADCCoreVoltageEnvelopeAt hardware.meteredSource.fixture.coreSource channel).value ∧
    |((finiteADCPhysicalDelayedEndpoint current processingTicks).currentAt channel).value| <
        (finiteADCCoreCurrentEnvelopeAt hardware.meteredSource.fixture.coreSource channel).value := by
  rw [finiteADCPhysicalDelayedEndpoint_commutes_generated]
  exact ⟨finiteADCGeneratedEndpoint_voltage_abs_lt (finiteADCPhysicalCurrentSource current)
      current.val.drive channel processingTicks,
    finiteADCGeneratedEndpoint_current_abs_lt (finiteADCPhysicalCurrentSource current)
      current.val.drive channel processingTicks⟩

def finiteADCCoreRecipientEnergyEnvelopeAt (core : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel) : SIJoule :=
  let run := finiteADCCoreDimensionedRun core
  ⟨(run.capacitanceAt channel).value / 2 * (finiteADCCoreVoltageEnvelopeAt core channel).value ^ 2 +
    (run.inductanceAt channel).value / 2 * (finiteADCCoreCurrentEnvelopeAt core channel).value ^ 2⟩

theorem finiteADCCoreRecipientEnergyEnvelopeAt_nonneg (core : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel) :
    0 ≤ (finiteADCCoreRecipientEnergyEnvelopeAt core channel).value := by
  exact add_nonneg
    (mul_nonneg (div_nonneg (compiledFiniteDimensionedSeriesRLC_capacitance_pos _ channel).le
      (by norm_num)) (sq_nonneg _))
    (mul_nonneg (div_nonneg (compiledFiniteDimensionedSeriesRLC_inductance_pos _ channel).le
      (by norm_num)) (sq_nonneg _))

end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
