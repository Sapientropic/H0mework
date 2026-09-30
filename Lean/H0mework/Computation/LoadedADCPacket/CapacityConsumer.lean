import H0mework.Computation.LoadedADCPacket.CapacityGrowth

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet.Capacity

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware
  (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

theorem sourceGeneratedLoadedPacketHistoryCapacity (bound : Nat) (enough : 2 ≤ bound) :
    type_of% (code_card (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) ∧
    (∀ left right : Fin (bound + 1), type_of% (time_separated downstreamTechnology downstreamGraph seed bound left right)) ∧
    type_of% (history_information_lower downstreamTechnology downstreamGraph seed bound) ∧
    type_of% (residual_information_lower downstreamTechnology downstreamGraph seed bound) ∧
    type_of% (residual_capacity_lower downstreamTechnology downstreamGraph seed bound) ∧
    (∀ decoder : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology) → ℂ,
      type_of% (decoder_capacity_lower downstreamTechnology downstreamGraph seed bound decoder) ∧
      type_of% (time_error_decomposition downstreamTechnology downstreamGraph seed bound decoder)) ∧
    (∀ epsilon : ℝ, type_of% (decoder_eventually_fails downstreamTechnology downstreamGraph seed epsilon)) ∧
    type_of% (Interval.sourceGeneratedLoadedPacketResourceIntervals downstreamTechnology downstreamGraph seed bound enough) :=
  ⟨code_card,
    (fun left right => time_separated downstreamTechnology downstreamGraph seed bound left right),
    history_information_lower downstreamTechnology downstreamGraph seed bound,
    residual_information_lower downstreamTechnology downstreamGraph seed bound,
    residual_capacity_lower downstreamTechnology downstreamGraph seed bound,
    (fun decoder => ⟨decoder_capacity_lower downstreamTechnology downstreamGraph seed bound decoder,
      time_error_decomposition downstreamTechnology downstreamGraph seed bound decoder⟩),
    (fun epsilon => decoder_eventually_fails downstreamTechnology downstreamGraph seed epsilon),
    Interval.sourceGeneratedLoadedPacketResourceIntervals downstreamTechnology downstreamGraph seed bound enough⟩

end
end FiniteADCWholeJointCurrent.Information.Packet.Capacity
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
