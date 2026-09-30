import H0mework.Computation.AIGHold.HeldMemoryWork
import H0mework.Physics.ADCRuntime.LoadedReceiverCaptureEnergy

/-! # Complete source work continues through actual receiver read and fresh-sample waiting -/

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

def receiverSourceWorkAt (time : ℝ) : SIJoule :=
  aigMemoryWorkAt technology (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))
    current.memory current.assignment hardware.meteredSource.fixture.coreSource hardware.clockCode time

def receiverDissipatedHeatAt (time : ℝ) : SIJoule :=
  aigMemoryHeatAt technology (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))
    current.memory current.assignment downstreamTechnology downstreamGraph
    hardware.meteredSource.fixture.coreSource hardware.clockCode time

theorem receiverStoredEnergyAt_integrated_balance (time : ℝ) :
    (receiverStoredEnergyAt downstreamTechnology downstreamGraph current time).value -
        current.memory.storedEnergy.value =
      (receiverSourceWorkAt current time).value -
        (receiverDissipatedHeatAt downstreamTechnology downstreamGraph current time).value :=
  aigMemoryStoredEnergyAt_integrated_balance _ _ _ _ _ _ _ _ time

theorem receiverDissipatedHeatAt_nonneg (time : ℝ) (nonnegative : 0 ≤ time) :
    0 ≤ (receiverDissipatedHeatAt downstreamTechnology downstreamGraph current time).value :=
  aigMemoryHeatAt_nonneg _ _ _ _ _ _ _ _ time nonnegative

/-- This read occurs after capture, so its isolated output rows pay actual leakage. -/
theorem receiverStoredEnergyAt_paid_read :
    let time := readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph
    (receiverStoredEnergyAt downstreamTechnology downstreamGraph current time.value).value -
        current.memory.storedEnergy.value =
      (receiverSourceWorkAt current time.value).value -
        (receiverDissipatedHeatAt downstreamTechnology downstreamGraph current time.value).value :=
  receiverStoredEnergyAt_integrated_balance _ _ _ _

/-- The next ADC's actual duration advances the common target memory under the
old received packet controls; its new stored energy is not substituted by zero. -/
theorem loadedReceiverSnapshotMemory_paid :
    let entry := receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)
    let memory := (commonRecoveryTarget downstreamTechnology downstreamGraph current).1
    let time := (loadedReceiverSnapshotDelay downstreamTechnology downstreamGraph current).value
    (loadedReceiverSnapshotMemory downstreamTechnology downstreamGraph current).storedEnergy.value -
        memory.storedEnergy.value =
      (aigMemoryWorkAt technology entry memory current.assignment
        hardware.meteredSource.fixture.coreSource hardware.clockCode time).value -
      (aigMemoryHeatAt technology entry memory current.assignment downstreamTechnology downstreamGraph
        hardware.meteredSource.fixture.coreSource hardware.clockCode time).value := by
  dsimp only
  change (aigMemoryEndpoint technology (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))
    (commonRecoveryTarget downstreamTechnology downstreamGraph current).1 current.assignment
    downstreamTechnology downstreamGraph hardware.meteredSource.fixture.coreSource hardware.clockCode
    (loadedReceiverSnapshotDelay downstreamTechnology downstreamGraph current).value
    (loadedReceiverSnapshotDelay_pos downstreamTechnology downstreamGraph current).le).storedEnergy.value - _ = _
  rw [aigMemoryEndpoint_storedEnergy]
  exact aigMemoryStoredEnergyAt_integrated_balance _ _ _ _ _ _ _ _ _

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical

