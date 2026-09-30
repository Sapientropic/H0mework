import H0mework.Physics.ConductanceCell.AIGMemoryEnergy
import H0mework.Physics.ADCRuntime.LoadedReceiverContinuation

/-! # The actual fixed receiver's complete charge reaches its paid capture snapshot -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section
namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (current : FiniteADCWholeJointCurrent hardware clockMax technology)

def receiverStoredEnergyAt (time : ℝ) : SIJoule :=
  aigMemoryStoredEnergyAt technology
    (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)) current.memory current.assignment
    downstreamTechnology downstreamGraph hardware.meteredSource.fixture.coreSource hardware.clockCode time

theorem receiverStoredEnergyAt_initial :
    receiverStoredEnergyAt downstreamTechnology downstreamGraph current 0 = current.memory.storedEnergy :=
  aigMemoryStoredEnergyAt_initial _ _ _ _ _ _ _ _

/-- The actual source-derived stop is included; no caller-supplied lease or paid-energy ticket enters. -/
theorem receiverStoredEnergyAt_paid_capture :
    let entry := receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)
    let stop := receiverWholeCaptureTime hardware.adcCode (Nat.log 2 clockMax + 1) technology
      (packetLineReadyTime technology (aigOutputBank entry).aig).value
      hardware.meteredSource.fixture.coreSource hardware.clockCode
    (receiverStoredEnergyAt downstreamTechnology downstreamGraph current stop.value).value -
        current.memory.storedEnergy.value =
      (aigDrivenWorkAt technology (aigOutputBank entry).aig current.assignment
        current.memory.inputInitial current.memory.gateInitial stop.value).value -
      (aigDrivenHeatAt technology (aigOutputBank entry).aig current.assignment
        current.memory.inputInitial current.memory.gateInitial stop.value).value :=
  aigMemoryStoredEnergyAt_paid_before_capture _ _ _ _ _ _ _ _ _ le_rfl

/-- The ledger's voltages are the actual complete receiver state, not a fresh evaluation. -/
theorem receiverStoredEnergyAt_is_state_projection (time : ℝ) :
    receiverStoredEnergyAt downstreamTechnology downstreamGraph current time =
      aigActualStoredEnergy technology
        (aigOutputBank (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).aig
        (fun atom => aigMemoryInputWave technology
          (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)) current.memory current.assignment atom time)
        (fun node polarity => current.receiverStateAt downstreamTechnology downstreamGraph node polarity time) := rfl

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical

