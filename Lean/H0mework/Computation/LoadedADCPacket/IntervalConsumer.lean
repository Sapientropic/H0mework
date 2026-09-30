import H0mework.Computation.LoadedADCPacket.IntervalAccount

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet.Interval

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedRuntimeHistoryProbability

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware
  (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

theorem sourceGeneratedLoadedPacketResourceIntervals (bound : Nat) (enough : 2 ≤ bound) :
    (∀ actor : Fin (bound + 1),
      (∀ channel : FiniteEmbodimentChannel,
        (∀ leg, type_of% (quantization_interval (loadedAfter downstreamTechnology downstreamGraph seed actor.val) leg channel)) ∧
        type_of% (voltage_interval (loadedAfter downstreamTechnology downstreamGraph seed actor.val) channel) ∧
        type_of% (current_interval (loadedAfter downstreamTechnology downstreamGraph seed actor.val) channel)) ∧
      type_of% (energy_interval (loadedAfter downstreamTechnology downstreamGraph seed actor.val)) ∧
      type_of% (energy_interval (loadedStep downstreamTechnology downstreamGraph
        (loadedAfter downstreamTechnology downstreamGraph seed actor.val))) ∧
      type_of% (step_work_interval downstreamTechnology downstreamGraph
        (loadedAfter downstreamTechnology downstreamGraph seed actor.val))) ∧
    (∀ value, ∀ supported : value ∈ ((historyPMF bound).map
        (nowPacket downstreamTechnology downstreamGraph seed bound)).support,
      type_of% (conditional_energy_interval downstreamTechnology downstreamGraph seed bound value supported)) ∧
    type_of% (whole_work_interval downstreamTechnology downstreamGraph seed (bound + 1)) ∧
    type_of% (packet_heat_budget downstreamTechnology downstreamGraph seed (bound + 1)) ∧
    type_of% (Recovered.sourceGeneratedLoadedPacketCurrentRecovery
      downstreamTechnology downstreamGraph seed bound enough) :=
  ⟨(fun actor => ⟨(fun channel => ⟨
      (fun leg => quantization_interval (loadedAfter downstreamTechnology downstreamGraph seed actor.val) leg channel),
      voltage_interval (loadedAfter downstreamTechnology downstreamGraph seed actor.val) channel,
      current_interval (loadedAfter downstreamTechnology downstreamGraph seed actor.val) channel⟩),
    energy_interval (loadedAfter downstreamTechnology downstreamGraph seed actor.val),
    energy_interval (loadedStep downstreamTechnology downstreamGraph
      (loadedAfter downstreamTechnology downstreamGraph seed actor.val)),
    step_work_interval downstreamTechnology downstreamGraph
      (loadedAfter downstreamTechnology downstreamGraph seed actor.val)⟩),
    (fun value supported => conditional_energy_interval downstreamTechnology downstreamGraph seed bound value supported),
    whole_work_interval downstreamTechnology downstreamGraph seed (bound + 1),
    packet_heat_budget downstreamTechnology downstreamGraph seed (bound + 1),
    Recovered.sourceGeneratedLoadedPacketCurrentRecovery downstreamTechnology downstreamGraph seed bound enough⟩

end
end FiniteADCWholeJointCurrent.Information.Packet.Interval
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
