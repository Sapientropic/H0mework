import H0mework.Computation.LoadedADCPacket.Duration

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet.Recipient

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Physical.Interface
open Netlist.Dissipative.Dimensioned.Producer Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}

def decodedDrive
    (packet : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) :
    FiniteBinaryDrive :=
  decodeFiniteADC128EnergySample (unpackADCWirePacket hardware packet)

def decodedLeg
    (packet : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology))
    (leg : SynchronousSenseLeg) (channel : FiniteEmbodimentChannel) : ℝ :=
  (finiteADCDigitalLegRatio (unpackADCWirePacket hardware packet) leg channel : ℚ)

def correctedLeg
    (packet : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology))
    (leg : SynchronousSenseLeg) (channel : FiniteEmbodimentChannel) : ℝ :=
  decodedLeg packet leg channel -
    finiteHalfPowerBandNoiseAt hardware.meteredSource.noiseCode leg
      hardware.meteredSource.fixture.coreSource channel ⟨headerSeconds packet⟩

def decodedRecipient
    (packet : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) :
    FiniteDimensionedSeriesRLCPortState where
  voltageAt channel :=
    let core := hardware.meteredSource.fixture.coreSource
    let source := resonantDrivenCoreDimensionedSource core
    ⟨(voltageWaveformAt (sourceOwnedResonantDrivenFrequencyAt core channel)
        (sourceOwnedResonantDrivenDriveAt core (binaryDriveState (decodedDrive packet)) channel)
        ⟨headerSeconds packet⟩).value -
      core.2.voltageScale.value * correctedLeg packet .resistor channel -
      (resonantInductorOutputScaleAt source channel).value * correctedLeg packet .inductor channel⟩
  currentAt channel :=
    let core := hardware.meteredSource.fixture.coreSource
    let run := compileFiniteDimensionedSeriesRLCNetlistRun (resonantDrivenCoreDimensionedSource core)
    ⟨core.2.voltageScale.value * correctedLeg packet .resistor channel /
      (run.seriesResistanceAt channel).value⟩

variable (current : FiniteADCWholeJointCurrent hardware
  (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

/-- This residual is generated before the recipient decoder: the stored ADC decode/encode error. -/
def quantizationError (leg : SynchronousSenseLeg) (channel : FiniteEmbodimentChannel) : ℝ :=
  (((finiteADCClockedDecodedVoltageAt hardware current.plant.val.adcCode
        current.plant.val.adcWordAt .operational leg channel).value /
      (finiteAffineMeterSenseScaleAt hardware.meteredSource.fixture.coreSource leg channel).value) -
    (current.plant.val.rawVoltageAt .operational leg channel).value /
      (finiteAffineMeterSenseScaleAt hardware.meteredSource.fixture.coreSource leg channel).value) /
    finiteAffineMeterGainAt hardware.meteredSource.meterCode leg channel

def voltageError (channel : FiniteEmbodimentChannel) : SIVolt :=
  let core := hardware.meteredSource.fixture.coreSource
  ⟨core.2.voltageScale.value * quantizationError current .resistor channel +
    (resonantInductorOutputScaleAt (resonantDrivenCoreDimensionedSource core) channel).value *
      quantizationError current .inductor channel⟩

def currentError (channel : FiniteEmbodimentChannel) : SIAmpere :=
  let core := hardware.meteredSource.fixture.coreSource
  let run := compileFiniteDimensionedSeriesRLCNetlistRun (resonantDrivenCoreDimensionedSource core)
  ⟨-(core.2.voltageScale.value / (run.seriesResistanceAt channel).value) *
    quantizationError current .resistor channel⟩

end
end FiniteADCWholeJointCurrent.Information.Packet.Recipient
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
