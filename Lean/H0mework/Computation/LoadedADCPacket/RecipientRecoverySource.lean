import H0mework.Computation.LoadedADCPacket.RecipientState

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

def voltageDecoder (channel : FiniteEmbodimentChannel)
    (packet : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) : ℂ :=
  ((decodedRecipient packet).voltageAt channel).value

def currentDecoder (channel : FiniteEmbodimentChannel)
    (packet : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) : ℂ :=
  ((decodedRecipient packet).currentAt channel).value

variable {β : Type} [DecidableEq β] [Hashable β]
  (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
  (seed : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

def voltageTask (bound : Nat) (channel : FiniteEmbodimentChannel) (actor : Fin (bound + 1)) : ℂ :=
  ((finiteADCPhysicalEndpoint
    (loadedStep downstreamTechnology downstreamGraph
      (loadedAfter downstreamTechnology downstreamGraph seed actor.val)).plant).voltageAt channel).value

def voltageSourceError (bound : Nat) (channel : FiniteEmbodimentChannel) (actor : Fin (bound + 1)) : ℂ :=
  (voltageError (loadedStep downstreamTechnology downstreamGraph
    (loadedAfter downstreamTechnology downstreamGraph seed actor.val)) channel).value

theorem voltage_source_composition (bound : Nat) (channel : FiniteEmbodimentChannel) :
    voltageTask downstreamTechnology downstreamGraph seed bound channel =
      (voltageDecoder channel ∘ nextPacket downstreamTechnology downstreamGraph seed bound) +
        voltageSourceError downstreamTechnology downstreamGraph seed bound channel := by
  funext actor
  have same := congrArg (fun state : FiniteDimensionedSeriesRLCPortState =>
    ((state.voltageAt channel).value : ℂ))
    (endpoint_eq_shift (loadedStep downstreamTechnology downstreamGraph
      (loadedAfter downstreamTechnology downstreamGraph seed actor.val)))
  simp only [RLCStateError.shift, SIQuantity.add_value, Complex.ofReal_add] at same
  exact same

def currentTask (bound : Nat) (channel : FiniteEmbodimentChannel) (actor : Fin (bound + 1)) : ℂ :=
  ((finiteADCPhysicalEndpoint
    (loadedStep downstreamTechnology downstreamGraph
      (loadedAfter downstreamTechnology downstreamGraph seed actor.val)).plant).currentAt channel).value

def currentSourceError (bound : Nat) (channel : FiniteEmbodimentChannel) (actor : Fin (bound + 1)) : ℂ :=
  (currentError (loadedStep downstreamTechnology downstreamGraph
    (loadedAfter downstreamTechnology downstreamGraph seed actor.val)) channel).value

theorem current_source_composition (bound : Nat) (channel : FiniteEmbodimentChannel) :
    currentTask downstreamTechnology downstreamGraph seed bound channel =
      (currentDecoder channel ∘ nextPacket downstreamTechnology downstreamGraph seed bound) +
        currentSourceError downstreamTechnology downstreamGraph seed bound channel := by
  funext actor
  have same := congrArg (fun state : FiniteDimensionedSeriesRLCPortState =>
    ((state.currentAt channel).value : ℂ))
    (endpoint_eq_shift (loadedStep downstreamTechnology downstreamGraph
      (loadedAfter downstreamTechnology downstreamGraph seed actor.val)))
  simp only [RLCStateError.shift, SIQuantity.add_value, Complex.ofReal_add] at same
  exact same

end
end FiniteADCWholeJointCurrent.Information.Packet.Recipient
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
