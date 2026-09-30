import H0mework.Physics.ADCSource.InverseInitial
import H0mework.Computation.LoadedADCPacket.RecipientState

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet.Recovered

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open Netlist.Dissipative.Dimensioned.Producer

noncomputable section

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}

abbrev Readout :=
  Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology) ×
    (SynchronousSenseLeg → FiniteEmbodimentChannel → ℝ) ×
      AIGCapacitorMemory technology (aigOutputBank
        (receiverWholeGraph hardware.adcCode (loadedReceiverInstalledClockBits hardware technology actualBoot))).aig

def sourceRead (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :
    Readout (hardware := hardware) (actualBoot := actualBoot) (technology := technology) :=
  (current.packet, Recipient.quantizationError current, current.memory)

def snapshot (value : Readout (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) :
    FiniteDimensionedSeriesRLCPortState :=
  let core := hardware.meteredSource.fixture.coreSource
  let run := compileFiniteDimensionedSeriesRLCNetlistRun (resonantDrivenCoreDimensionedSource core)
  RLCStateError.shift (Recipient.decodedRecipient value.1)
    (fun channel => ⟨core.2.voltageScale.value * value.2.1 .resistor channel +
      (resonantInductorOutputScaleAt (resonantDrivenCoreDimensionedSource core) channel).value * value.2.1 .inductor channel⟩)
    (fun channel => ⟨-(core.2.voltageScale.value / (run.seriesResistanceAt channel).value) * value.2.1 .resistor channel⟩)

theorem snapshot_source (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :
    snapshot (sourceRead current) = finiteADCPhysicalEndpoint current.plant :=
  (Recipient.endpoint_eq_shift current).symm

def initialRead (value : Readout (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) :
    FiniteDimensionedSeriesRLCPortState :=
  let core := hardware.meteredSource.fixture.coreSource
  RLCSourceInverse.recoverInitial (resonantDrivenCoreDimensionedSource core)
    (sourceOwnedResonantDrivenFrequencyAt core)
    (sourceOwnedResonantDrivenDriveAt core (binaryDriveState (Recipient.decodedDrive value.1)))
    (snapshot value) ⟨headerSeconds value.1⟩

theorem initialRead_source (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :
    initialRead (sourceRead current) = current.plant.val.initial := by
  have time : (⟨headerSeconds current.packet⟩ : SISecond) = current.plant.val.executedDuration := by
    apply SIQuantity.ext
    exact (packet_duration current).symm
  unfold initialRead
  rw [snapshot_source]
  change RLCSourceInverse.recoverInitial
    (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
    (sourceOwnedResonantDrivenFrequencyAt hardware.meteredSource.fixture.coreSource)
    (sourceOwnedResonantDrivenDriveAt hardware.meteredSource.fixture.coreSource
      (binaryDriveState (Recipient.decodedDrive current.packet)))
    (finiteADCPhysicalEndpoint current.plant) ⟨headerSeconds current.packet⟩ = _
  rw [Recipient.decodedDrive_original, time, finiteADCPhysicalEndpoint, finiteADCPhysicalStateAt_commutes]
  exact RLCSourceInverse.recover_total _ _ _ _ _

def recoverPlant (value : Readout (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) :
    FiniteADCPhysicalRuntimeCurrent hardware :=
  startFiniteADCPhysicalRuntime hardware (initialRead value) (Recipient.decodedDrive value.1)

theorem recoverPlant_source (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :
    recoverPlant (sourceRead current) = current.plant := by
  unfold recoverPlant
  rw [initialRead_source]
  change startFiniteADCPhysicalRuntime hardware current.plant.val.initial
    (Recipient.decodedDrive current.packet) = current.plant
  rw [Recipient.decodedDrive_original]
  apply Subtype.ext
  exact current.plant.property.symm

/-- Arbitrary data uses the original installed schedule; generated data always reconstructs its original current. -/
def recoverCurrent (value : Readout (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) :
    Option (FiniteADCWholeJointCurrent hardware
      (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :=
  let plant := recoverPlant value
  if scheduled : plant.val.sampleTick ≤ loadedReceiverInstalledMaxTick hardware technology actualBoot then
    some ⟨plant, scheduled, value.2.2⟩
  else none

theorem recoverCurrent_source (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :
    recoverCurrent (sourceRead current) = some current := by
  unfold recoverCurrent
  rw [recoverPlant_source]
  simp only [dif_pos current.inSchedule]
  rfl

theorem sourceRead_injective : Function.Injective
    (sourceRead (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) := by
  intro left right same
  have restored := congrArg recoverCurrent same
  rw [recoverCurrent_source, recoverCurrent_source] at restored
  exact Option.some.inj restored

end
end FiniteADCWholeJointCurrent.Information.Packet.Recovered
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
