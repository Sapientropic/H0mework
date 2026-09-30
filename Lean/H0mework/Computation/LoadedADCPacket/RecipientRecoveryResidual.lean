import H0mework.Computation.LoadedADCPacket.RecipientRecoverySource
import H0mework.Probability.Source.ConditionalNextError

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet.Recipient

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open scoped InnerProductSpace

noncomputable section

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}

variable {β : Type} [DecidableEq β] [Hashable β]
  (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
  (seed : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

theorem voltage_residual_sum (bound : Nat) (channel : FiniteEmbodimentChannel) :
    residual (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (taskValue (historyPMF bound) (voltageTask downstreamTechnology downstreamGraph seed bound channel)) =
      residual (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (taskValue (historyPMF bound) ((voltageDecoder channel) ∘ (nextPacket downstreamTechnology downstreamGraph seed bound))) +
        residual (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (taskValue (historyPMF bound) (voltageSourceError downstreamTechnology downstreamGraph seed bound channel)) := by
  rw [voltage_source_composition]
  exact SourceConditionalNext.residual_error_sum (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (nextPacket downstreamTechnology downstreamGraph seed bound) (voltageDecoder channel) (voltageSourceError downstreamTechnology downstreamGraph seed bound channel)

theorem voltage_residual_square (bound : Nat) (channel : FiniteEmbodimentChannel) :
    ‖residual (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (taskValue (historyPMF bound) (voltageTask downstreamTechnology downstreamGraph seed bound channel))‖ ^ 2 =
      (∑ actor, ((historyPMF bound) actor).toReal *
        SourceConditionalNext.variance (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (nextPacket downstreamTechnology downstreamGraph seed bound) (voltageDecoder channel)
          (nowPacket downstreamTechnology downstreamGraph seed bound actor)
          (observed_supported (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) actor (history_weight_positive bound actor))) +
      ‖residual (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (taskValue (historyPMF bound) (voltageSourceError downstreamTechnology downstreamGraph seed bound channel))‖ ^ 2 +
      2 * (inner ℂ (residual (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (taskValue (historyPMF bound) ((voltageDecoder channel) ∘ (nextPacket downstreamTechnology downstreamGraph seed bound))))
        (residual (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (taskValue (historyPMF bound) (voltageSourceError downstreamTechnology downstreamGraph seed bound channel)))).re := by
  rw [voltage_source_composition]
  exact SourceConditionalNext.residual_error_square (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (nextPacket downstreamTechnology downstreamGraph seed bound) (voltageDecoder channel) (voltageSourceError downstreamTechnology downstreamGraph seed bound channel)
    (fun actor => (PMF.mem_support_iff _ _).mpr (history_weight_positive bound actor))

theorem current_residual_sum (bound : Nat) (channel : FiniteEmbodimentChannel) :
    residual (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (taskValue (historyPMF bound) (currentTask downstreamTechnology downstreamGraph seed bound channel)) =
      residual (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (taskValue (historyPMF bound) ((currentDecoder channel) ∘ (nextPacket downstreamTechnology downstreamGraph seed bound))) +
        residual (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (taskValue (historyPMF bound) (currentSourceError downstreamTechnology downstreamGraph seed bound channel)) := by
  rw [current_source_composition]
  exact SourceConditionalNext.residual_error_sum (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (nextPacket downstreamTechnology downstreamGraph seed bound) (currentDecoder channel) (currentSourceError downstreamTechnology downstreamGraph seed bound channel)

theorem current_residual_square (bound : Nat) (channel : FiniteEmbodimentChannel) :
    ‖residual (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (taskValue (historyPMF bound) (currentTask downstreamTechnology downstreamGraph seed bound channel))‖ ^ 2 =
      (∑ actor, ((historyPMF bound) actor).toReal *
        SourceConditionalNext.variance (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (nextPacket downstreamTechnology downstreamGraph seed bound) (currentDecoder channel)
          (nowPacket downstreamTechnology downstreamGraph seed bound actor)
          (observed_supported (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) actor (history_weight_positive bound actor))) +
      ‖residual (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (taskValue (historyPMF bound) (currentSourceError downstreamTechnology downstreamGraph seed bound channel))‖ ^ 2 +
      2 * (inner ℂ (residual (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (taskValue (historyPMF bound) ((currentDecoder channel) ∘ (nextPacket downstreamTechnology downstreamGraph seed bound))))
        (residual (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (taskValue (historyPMF bound) (currentSourceError downstreamTechnology downstreamGraph seed bound channel)))).re := by
  rw [current_source_composition]
  exact SourceConditionalNext.residual_error_square (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (nextPacket downstreamTechnology downstreamGraph seed bound) (currentDecoder channel) (currentSourceError downstreamTechnology downstreamGraph seed bound channel)
    (fun actor => (PMF.mem_support_iff _ _).mpr (history_weight_positive bound actor))

end
end FiniteADCWholeJointCurrent.Information.Packet.Recipient
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
