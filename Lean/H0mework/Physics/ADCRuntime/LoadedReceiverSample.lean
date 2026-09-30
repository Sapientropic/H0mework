import H0mework.Physics.ReceiverActuation.CommonTarget

/-! # The recovered target's actual read and recipient state generate a fresh sampled physical run -/

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
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (current : FiniteADCWholeJointCurrent hardware clockMax technology)

/-- Only the independently accepted recovered memory emits the next drive. -/
def loadedReceiverFreshSample? : Option (Option (FiniteADCPhysicalRuntimeCurrent hardware)) :=
  (commonRecoveryTargetRead downstreamTechnology downstreamGraph current).map
    (Option.map fun received => startFiniteADCPhysicalRuntime hardware
      (commonRecoveryTarget downstreamTechnology downstreamGraph current).2 (fun channel => !(received channel)))

theorem loadedReceiverFreshSample_generated :
    loadedReceiverFreshSample? downstreamTechnology downstreamGraph current =
      some (some (startFiniteADCPhysicalRuntime hardware
        (commonRecoveryTarget downstreamTechnology downstreamGraph current).2
        (fun channel => !(current.plant.val.drive channel)))) := by
  rw [loadedReceiverFreshSample?, commonRecoveryTarget_reads_actual_command]
  rfl

def loadedReceiverFreshSample : FiniteADCPhysicalRuntimeCurrent hardware :=
  (loadedReceiverFreshSample? downstreamTechnology downstreamGraph current).join.get (by
    rw [loadedReceiverFreshSample_generated]
    rfl)

theorem loadedReceiverFreshSample_eq :
    loadedReceiverFreshSample downstreamTechnology downstreamGraph current =
      startFiniteADCPhysicalRuntime hardware (commonRecoveryTarget downstreamTechnology downstreamGraph current).2
        (fun channel => !(current.plant.val.drive channel)) := by
  simp only [loadedReceiverFreshSample, loadedReceiverFreshSample_generated, Option.join_some, Option.get_some]

theorem loadedReceiverFreshSample_initial :
    (loadedReceiverFreshSample downstreamTechnology downstreamGraph current).val.initial =
      (commonRecoveryTarget downstreamTechnology downstreamGraph current).2 := by
  rw [loadedReceiverFreshSample_eq]
  rfl

theorem loadedReceiverFreshSample_no_reset :
    finiteADCPhysicalStateAt (loadedReceiverFreshSample downstreamTechnology downstreamGraph current) 0 =
      (commonRecoveryTarget downstreamTechnology downstreamGraph current).2 := by
  rw [loadedReceiverFreshSample_eq]
  exact drivenTotalPortState_initial_exact _ _ _ _

theorem loadedReceiverFreshSample_feedback :
    (loadedReceiverFreshSample downstreamTechnology downstreamGraph current).val.drive =
      fun channel => !(current.plant.val.drive channel) := by
  rw [loadedReceiverFreshSample_eq]
  rfl

theorem loadedReceiverFreshSample_generates_receipt :
    SourceGeneratedFiniteADCClockedNoisyMeteredSynchronousSampleAt
      (finiteADCPhysicalCurrentSource (loadedReceiverFreshSample downstreamTechnology downstreamGraph current))
      (loadedReceiverFreshSample downstreamTechnology downstreamGraph current).val.drive :=
  finiteADCPhysicalCurrent_generates_receipt _

theorem loadedReceiverFreshSample_is_not_read_only :
    loadedReceiverFreshSample downstreamTechnology downstreamGraph current ≠ current.plant := by
  intro unchanged
  have bit := congrArg (fun run : FiniteADCPhysicalRuntimeCurrent hardware => run.val.drive .noPowerMinting) unchanged
  rw [loadedReceiverFreshSample_feedback] at bit
  cases actual : current.plant.val.drive .noPowerMinting <;> simp [actual] at bit

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
