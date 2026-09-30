import H0mework.Computation.LoadedADCPacket.RecoveredConsumer

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet.Interval

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

private theorem normalized_error (code : FiniteADCResolutionCode) (scale voltage : SIVolt)
    (positive : 0 < scale.value) (lower : (-16 : ℝ) ≤ voltage.value / scale.value)
    (upper : voltage.value / scale.value < 16) :
    -(finiteADCNormalizedStep code) <
        (finiteADCDecodeVoltage code scale (finiteADCEncodeVoltage code scale voltage)).value / scale.value -
          voltage.value / scale.value ∧
      (finiteADCDecodeVoltage code scale (finiteADCEncodeVoltage code scale voltage)).value / scale.value -
          voltage.value / scale.value ≤ 0 := by
  have generated := finiteADCDecode_encode_error_of_inRange code (voltage.value / scale.value) lower upper
  simp only [finiteADCDecodeVoltage, finiteADCEncodeVoltage, SIQuantity.smul_value]
  rw [mul_div_cancel_right₀ _ positive.ne']
  constructor <;> linarith [generated.1, generated.2]

private theorem compiled_error (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) (leg : SynchronousSenseLeg) (channel : FiniteEmbodimentChannel) :
    -(finiteADCNormalizedStep source.adcCode / finiteAffineMeterGainAt source.meteredSource.meterCode leg channel) <
      finiteADCClockedDecodedLegAt source (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive) leg channel -
        finiteADCClockedAnalogLegAt source drive leg channel ∧
    finiteADCClockedDecodedLegAt source (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive) leg channel -
        finiteADCClockedAnalogLegAt source drive leg channel ≤ 0 := by
  have range := finiteADCClockedRawVoltage_inRange source drive .operational leg channel
  have signed := normalized_error source.adcCode
    (finiteAffineMeterSenseScaleAt source.meteredSource.fixture.coreSource leg channel)
    (finiteADCClockedRawVoltageAt source drive .operational leg channel)
    (finiteAffineMeterSenseScale_pos source.meteredSource.fixture.coreSource leg channel) range.1 range.2
  rw [compiledFiniteADCClockedDecodedLeg_sub_analog_eq]
  have gain := finiteAffineMeterGain_pos source.meteredSource.meterCode leg channel
  constructor
  · have lower := div_lt_div_of_pos_right signed.1 gain
    rw [neg_div] at lower
    exact lower
  · exact div_nonpos_of_nonpos_of_nonneg signed.2 gain.le

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}

def quantum (leg : SynchronousSenseLeg) (channel : FiniteEmbodimentChannel) : ℝ :=
  finiteADCNormalizedStep hardware.adcCode / finiteAffineMeterGainAt hardware.meteredSource.meterCode leg channel

theorem quantum_pos (leg : SynchronousSenseLeg) (channel : FiniteEmbodimentChannel) :
    0 < quantum (hardware := hardware) leg channel :=
  div_pos (finiteADCNormalizedStep_pos hardware.adcCode)
    (finiteAffineMeterGain_pos hardware.meteredSource.meterCode leg channel)

theorem quantization_interval (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)
    (leg : SynchronousSenseLeg) (channel : FiniteEmbodimentChannel) :
    -quantum (hardware := hardware) leg channel < Recipient.quantizationError current leg channel ∧
      Recipient.quantizationError current leg channel ≤ 0 := by
  rw [Recipient.quantizationError_original]
  have generated := compiled_error (finiteADCPhysicalCurrentSource current.plant)
    current.plant.val.drive leg channel
  have same : current.plant.val = compileFiniteADCClockedNoisyMeteredSynchronousSample
    (finiteADCPhysicalCurrentSource current.plant) current.plant.val.drive := current.plant.property
  rw [← same] at generated
  exact generated

end
end FiniteADCWholeJointCurrent.Information.Packet.Interval
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
