import H0mework.Computation.LoadedADCInformation.ConditionalActionConsumer

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}

abbrev Code := FiniteADCWirePacketFor hardware.adcCode
  (loadedReceiverInstalledClockBits hardware technology actualBoot)

theorem unpack_header
    (current : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :
    (unpackADCWirePacket hardware current.packet).sampleTick = current.plant.val.sampleTick := rfl

variable {β : Type} [DecidableEq β] [Hashable β]
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

def nowPacket (bound : Nat) (actor : Fin (bound + 1)) :
    Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology) :=
  (loadedAfter downstreamTechnology downstreamGraph seed actor.val).packet

def nextPacket (bound : Nat) (actor : Fin (bound + 1)) :
    Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology) :=
  (loadedStep downstreamTechnology downstreamGraph
    (loadedAfter downstreamTechnology downstreamGraph seed actor.val)).packet

theorem source_next (bound : Nat) (actor : Fin (bound + 1)) :
    nextPacket downstreamTechnology downstreamGraph seed bound actor =
      loadedReceiverFreshPacket downstreamTechnology downstreamGraph
        (loadedAfter downstreamTechnology downstreamGraph seed actor.val) actualBoot :=
  loadedStep_packet downstreamTechnology downstreamGraph _

theorem next_is_original_history (bound : Nat) (actor : Fin (bound + 1)) :
    nextPacket downstreamTechnology downstreamGraph seed bound actor =
      (loadedAfter downstreamTechnology downstreamGraph seed (actor.val + 1)).packet := by
  rw [loadedAfter_succ]
  rfl

end
end FiniteADCWholeJointCurrent.Information.Packet
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
