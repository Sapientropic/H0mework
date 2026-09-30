import H0mework.Computation.LoadedADCPacket.IntervalSource

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet.Interval

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Producer Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}

def voltageWidth (channel : FiniteEmbodimentChannel) : SIVolt :=
  ⟨hardware.meteredSource.fixture.coreSource.2.voltageScale.value * quantum (hardware := hardware) .resistor channel +
    (resonantInductorOutputScaleAt (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel).value *
      quantum (hardware := hardware) .inductor channel⟩

def currentWidth (channel : FiniteEmbodimentChannel) : SIAmpere :=
  ⟨hardware.meteredSource.fixture.coreSource.2.voltageScale.value /
    ((compileFiniteDimensionedSeriesRLCNetlistRun
      (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)).seriesResistanceAt channel).value *
    quantum (hardware := hardware) .resistor channel⟩

def voltageLower (packet : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology))
    (channel : FiniteEmbodimentChannel) : SIVolt :=
  (Recipient.decodedRecipient packet).voltageAt channel - voltageWidth (hardware := hardware) channel

def voltageUpper (packet : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology))
    (channel : FiniteEmbodimentChannel) : SIVolt :=
  (Recipient.decodedRecipient packet).voltageAt channel

def currentLower (packet : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology))
    (channel : FiniteEmbodimentChannel) : SIAmpere :=
  (Recipient.decodedRecipient packet).currentAt channel

def currentUpper (packet : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology))
    (channel : FiniteEmbodimentChannel) : SIAmpere :=
  (Recipient.decodedRecipient packet).currentAt channel + currentWidth (hardware := hardware) channel

theorem voltage_interval (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) (channel : FiniteEmbodimentChannel) :
    (voltageLower current.packet channel).value < ((finiteADCPhysicalEndpoint current.plant).voltageAt channel).value ∧
      ((finiteADCPhysicalEndpoint current.plant).voltageAt channel).value ≤ (voltageUpper current.packet channel).value := by
  have r := quantization_interval current .resistor channel
  have l := quantization_interval current .inductor channel
  have rPos := hardware.meteredSource.fixture.coreSource.2.voltageScalePositive
  have lPos := resonantInductorOutputScale_pos
    (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel
  have rLower := mul_lt_mul_of_pos_left r.1 rPos
  have lLower := mul_lt_mul_of_pos_left l.1 lPos
  have rUpper := mul_nonpos_of_nonneg_of_nonpos rPos.le r.2
  have lUpper := mul_nonpos_of_nonneg_of_nonpos lPos.le l.2
  rw [Recipient.endpoint_voltage]
  simp only [voltageLower, voltageUpper, voltageWidth, Recipient.voltageError,
    SIQuantity.add_value, SIQuantity.sub_value]
  constructor <;> nlinarith

theorem current_interval (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) (channel : FiniteEmbodimentChannel) :
    (currentLower current.packet channel).value ≤ ((finiteADCPhysicalEndpoint current.plant).currentAt channel).value ∧
      ((finiteADCPhysicalEndpoint current.plant).currentAt channel).value < (currentUpper current.packet channel).value := by
  have q := quantization_interval current .resistor channel
  have ratioPos := div_pos hardware.meteredSource.fixture.coreSource.2.voltageScalePositive
    (compiledFiniteDimensionedSeriesRLC_resistance_pos
      (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel)
  have lower := mul_nonpos_of_nonneg_of_nonpos ratioPos.le q.2
  have upper := mul_lt_mul_of_pos_left q.1 ratioPos
  rw [Recipient.endpoint_current]
  simp only [currentLower, currentUpper, currentWidth, Recipient.currentError, SIQuantity.add_value]
  constructor <;> nlinarith

end
end FiniteADCWholeJointCurrent.Information.Packet.Interval
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
