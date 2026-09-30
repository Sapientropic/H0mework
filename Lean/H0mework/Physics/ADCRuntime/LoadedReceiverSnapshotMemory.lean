import H0mework.Physics.ADCRuntime.LoadedReceiverSample

/-! # The new physical sample and every receiver capacitor share the same snapshot time -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Std.Tactic.BVDecide Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section
namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (current : FiniteADCWholeJointCurrent hardware clockMax technology)

/-- Original packet controls remain installed while the accepted feedback generates the next sample. -/
def loadedReceiverAwaitingStateAt
    (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode
      ((Nat.log 2 clockMax + 1)))).aig.decls.size)
    (polarity : Bool) (time : ℝ) : SIVolt :=
  aigMemoryStateAt technology (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))
    (commonRecoveryTarget downstreamTechnology downstreamGraph current).1 current.assignment
    downstreamTechnology downstreamGraph hardware.meteredSource.fixture.coreSource hardware.clockCode node polarity time

theorem loadedReceiverAwaitingStateAt_initial
    (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode
      ((Nat.log 2 clockMax + 1)))).aig.decls.size) (polarity : Bool) :
    loadedReceiverAwaitingStateAt downstreamTechnology downstreamGraph current node polarity 0 =
      commonRecoveryStateAt downstreamTechnology downstreamGraph current node polarity
        (commonRecoverySampleTime downstreamTechnology downstreamGraph current).value := by
  rw [loadedReceiverAwaitingStateAt, aigMemoryStateAt_initial]
  exact commonRecoveryTarget_memory_exact _ _ _ _ _

def loadedReceiverSnapshotDelay : SISecond :=
  (loadedReceiverFreshSample downstreamTechnology downstreamGraph current).val.executedDuration

theorem loadedReceiverSnapshotDelay_pos :
    0 < (loadedReceiverSnapshotDelay downstreamTechnology downstreamGraph current).value :=
  finiteADCPhysicalCurrent_duration_positive _

def loadedReceiverSnapshotMemory : AIGCapacitorMemory technology
    (aigOutputBank (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))).aig :=
  aigMemoryEndpoint technology
    (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))
    (commonRecoveryTarget downstreamTechnology downstreamGraph current).1 current.assignment
    downstreamTechnology downstreamGraph hardware.meteredSource.fixture.coreSource hardware.clockCode
    (loadedReceiverSnapshotDelay downstreamTechnology downstreamGraph current).value
    (loadedReceiverSnapshotDelay_pos downstreamTechnology downstreamGraph current).le

theorem loadedReceiverSnapshotMemory_input_exact
    (port : AIGInputPort (aigOutputBank
      (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))).aig) :
    (loadedReceiverSnapshotMemory downstreamTechnology downstreamGraph current).inputInitial port.val =
      aigMemoryInputWave technology (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))
        (commonRecoveryTarget downstreamTechnology downstreamGraph current).1 current.assignment port.val
        (loadedReceiverSnapshotDelay downstreamTechnology downstreamGraph current).value :=
  aigMemoryEndpoint_input_exact _ _ _ _ _ _ _ _ _ _ _

theorem loadedReceiverSnapshotMemory_restarts_without_reset (newAssignment : BVBit → Bool)
    (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode
      ((Nat.log 2 clockMax + 1)))).aig.decls.size) (polarity : Bool) :
    aigMemoryStateAt technology (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))
      (loadedReceiverSnapshotMemory downstreamTechnology downstreamGraph current) newAssignment downstreamTechnology downstreamGraph
      hardware.meteredSource.fixture.coreSource hardware.clockCode node polarity 0 =
      loadedReceiverAwaitingStateAt downstreamTechnology downstreamGraph current node polarity
        (loadedReceiverSnapshotDelay downstreamTechnology downstreamGraph current).value :=
  aigMemoryStateAt_restart _ _ _ _ _ _ _ _ _ _ _ _ _

def loadedReceiverSampledTarget :
    FiniteADCPhysicalRuntimeCurrent hardware × AIGCapacitorMemory technology (aigOutputBank
      (receiverWholeGraph hardware.adcCode ((Nat.log 2 clockMax + 1)))).aig :=
  (loadedReceiverFreshSample downstreamTechnology downstreamGraph current,
    loadedReceiverSnapshotMemory downstreamTechnology downstreamGraph current)

theorem loadedReceiverSampledTarget_exact :
    (loadedReceiverSampledTarget downstreamTechnology downstreamGraph current).1.val.initial =
        (commonRecoveryTarget downstreamTechnology downstreamGraph current).2 ∧
      (loadedReceiverSampledTarget downstreamTechnology downstreamGraph current).1.val.executedDuration =
        loadedReceiverSnapshotDelay downstreamTechnology downstreamGraph current ∧
      (loadedReceiverSampledTarget downstreamTechnology downstreamGraph current).2 =
        loadedReceiverSnapshotMemory downstreamTechnology downstreamGraph current :=
  ⟨loadedReceiverFreshSample_initial _ _ _, rfl, rfl⟩

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
