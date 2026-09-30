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

theorem voltage_prediction_mean (bound : Nat) (channel : FiniteEmbodimentChannel)
    (value : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology))
    (supported : value ∈ ((historyPMF bound).map (nowPacket downstreamTechnology downstreamGraph seed bound)).support) :
    optimalDecoder (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (voltageTask downstreamTechnology downstreamGraph seed bound channel) value =
      SourceConditionalNext.mean (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (nextPacket downstreamTechnology downstreamGraph seed bound) (voltageDecoder channel) value supported +
        optimalDecoder (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (voltageSourceError downstreamTechnology downstreamGraph seed bound channel) value := by
  rw [voltage_source_composition]
  exact SourceConditionalNext.optimal_with_source_error (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (nextPacket downstreamTechnology downstreamGraph seed bound) (voltageDecoder channel) (voltageSourceError downstreamTechnology downstreamGraph seed bound channel) value supported

theorem voltage_next_decoder_error (bound : Nat) (channel : FiniteEmbodimentChannel) :
    error (historyPMF bound) (nextPacket downstreamTechnology downstreamGraph seed bound) (voltageTask downstreamTechnology downstreamGraph seed bound channel) (voltageDecoder channel) =
      ∑ actor, ((historyPMF bound) actor).toReal * ‖voltageSourceError downstreamTechnology downstreamGraph seed bound channel actor‖ ^ 2 := by
  rw [voltage_source_composition]
  exact SourceConditionalNext.next_decoder_error (historyPMF bound) (nextPacket downstreamTechnology downstreamGraph seed bound) (voltageDecoder channel) (voltageSourceError downstreamTechnology downstreamGraph seed bound channel)

theorem current_prediction_mean (bound : Nat) (channel : FiniteEmbodimentChannel)
    (value : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology))
    (supported : value ∈ ((historyPMF bound).map (nowPacket downstreamTechnology downstreamGraph seed bound)).support) :
    optimalDecoder (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (currentTask downstreamTechnology downstreamGraph seed bound channel) value =
      SourceConditionalNext.mean (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (nextPacket downstreamTechnology downstreamGraph seed bound) (currentDecoder channel) value supported +
        optimalDecoder (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (currentSourceError downstreamTechnology downstreamGraph seed bound channel) value := by
  rw [current_source_composition]
  exact SourceConditionalNext.optimal_with_source_error (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound) (nextPacket downstreamTechnology downstreamGraph seed bound) (currentDecoder channel) (currentSourceError downstreamTechnology downstreamGraph seed bound channel) value supported

theorem current_next_decoder_error (bound : Nat) (channel : FiniteEmbodimentChannel) :
    error (historyPMF bound) (nextPacket downstreamTechnology downstreamGraph seed bound) (currentTask downstreamTechnology downstreamGraph seed bound channel) (currentDecoder channel) =
      ∑ actor, ((historyPMF bound) actor).toReal * ‖currentSourceError downstreamTechnology downstreamGraph seed bound channel actor‖ ^ 2 := by
  rw [current_source_composition]
  exact SourceConditionalNext.next_decoder_error (historyPMF bound) (nextPacket downstreamTechnology downstreamGraph seed bound) (currentDecoder channel) (currentSourceError downstreamTechnology downstreamGraph seed bound channel)

end
end FiniteADCWholeJointCurrent.Information.Packet.Recipient
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
