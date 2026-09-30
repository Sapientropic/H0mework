import H0mework.Physics.ReceiverActuation.CapacitorRLCEnergy
import H0mework.Physics.ADCRuntime.WholeJointReadout

/-! # A newly connected load starts from the actual receiver and recipient read event -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}

def outputLoadPort (channel : FiniteEmbodimentChannel) : Fin 11 :=
  ⟨(finiteADCChannelEquivFin channel).val + 1, by have := (finiteADCChannelEquivFin channel).isLt; omega⟩

def outputLoadCell (channel : FiniteEmbodimentChannel) : LoadedConductanceCellSource :=
  aigBankCell technology
    (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))
    (outputLoadPort channel)

variable (current : FiniteADCWholeJointCurrent hardware clockMax technology)
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)

def outputLoadInitialVoltage (channel : FiniteEmbodimentChannel) : SIVolt :=
  let entry := receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1))
  let index := outputLoadPort channel
  current.receiverStateAt downstreamTechnology downstreamGraph
    ⟨((aigOutputBank entry).vec.get index.val index.isLt).gate,
      ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩ false
    (readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph).value

def outputLoadInitialRecipient : FiniteDimensionedSeriesRLCPortState :=
  finiteADCPhysicalDelayedEndpoint current.plant
    (receiverWholeHardwareProcessingTicks hardware ((Nat.log 2 clockMax + 1))
      technology downstreamTechnology downstreamGraph)

/-- No voltage source, Boolean verdict or replacement initial value is inserted at connection. -/
def outputLoadStateAt (channel : FiniteEmbodimentChannel) (time : ℝ) : Fin 3 → ℝ :=
  let cell := outputLoadCell (hardware := hardware) (clockMax := clockMax) (technology := technology) channel
  let hold := compileHoldLeaseForGraph cell downstreamTechnology downstreamGraph
    hardware.meteredSource.fixture.coreSource hardware.clockCode
  let recipient := current.outputLoadInitialRecipient downstreamTechnology downstreamGraph
  capacitorRLCStateAt cell hold (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
    channel (current.outputLoadInitialVoltage downstreamTechnology downstreamGraph channel)
    (recipient.voltageAt channel) (recipient.currentAt channel) time

theorem outputLoadStateAt_initial (channel : FiniteEmbodimentChannel) :
    current.outputLoadStateAt downstreamTechnology downstreamGraph channel 0 =
      capacitorRLCInitial (current.outputLoadInitialVoltage downstreamTechnology downstreamGraph channel)
        ((current.outputLoadInitialRecipient downstreamTechnology downstreamGraph).voltageAt channel)
        ((current.outputLoadInitialRecipient downstreamTechnology downstreamGraph).currentAt channel) :=
  capacitorRLCStateAt_initial _ _ _ _ _ _ _

def outputLoadEnergyAt (channel : FiniteEmbodimentChannel) (time : ℝ) : SIJoule :=
  let cell := outputLoadCell (hardware := hardware) (clockMax := clockMax) (technology := technology) channel
  let hold := compileHoldLeaseForGraph cell downstreamTechnology downstreamGraph
    hardware.meteredSource.fixture.coreSource hardware.clockCode
  let recipient := current.outputLoadInitialRecipient downstreamTechnology downstreamGraph
  capacitorRLCEnergyAt cell hold (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
    channel (current.outputLoadInitialVoltage downstreamTechnology downstreamGraph channel)
    (recipient.voltageAt channel) (recipient.currentAt channel) time

theorem outputLoadEnergyAt_power_balance (channel : FiniteEmbodimentChannel) (time : ℝ) :
    let cell := outputLoadCell (hardware := hardware) (clockMax := clockMax) (technology := technology) channel
    let hold := compileHoldLeaseForGraph cell downstreamTechnology downstreamGraph
      hardware.meteredSource.fixture.coreSource hardware.clockCode
    let run := Netlist.Dissipative.Dimensioned.Producer.compileFiniteDimensionedSeriesRLCNetlistRun
      (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
    let state := current.outputLoadStateAt downstreamTechnology downstreamGraph channel time
    HasDerivAt (fun t => (current.outputLoadEnergyAt downstreamTechnology downstreamGraph channel t).value)
      (-state 0 ^ 2 / hold.holdResistance.value - (run.seriesResistanceAt channel).value * state 2 ^ 2) time := by
  dsimp only
  let cell := outputLoadCell (hardware := hardware) (clockMax := clockMax) (technology := technology) channel
  let hold := compileHoldLeaseForGraph cell downstreamTechnology downstreamGraph
    hardware.meteredSource.fixture.coreSource hardware.clockCode
  let recipient := current.outputLoadInitialRecipient downstreamTechnology downstreamGraph
  have balance := capacitorRLCEnergyAt_power_balance cell hold
    (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource) channel
    (current.outputLoadInitialVoltage downstreamTechnology downstreamGraph channel)
    (recipient.voltageAt channel) (recipient.currentAt channel) time
  simpa only [outputLoadEnergyAt, outputLoadStateAt, capacitorRLCLeakPowerAt,
    capacitorRLCResistivePowerAt, neg_div] using balance

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
