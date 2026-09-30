import H0mework.Computation.LoadedADCPacket.RecoveredSource
import H0mework.Computation.LoadedADCPacket.Model

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet.Recovered

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedRuntimeHistoryProbability

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)

def predictCurrent (value : Readout (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) :
    Option (FiniteADCWholeJointCurrent hardware
      (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :=
  (recoverCurrent value).map (loadedStep downstreamTechnology downstreamGraph)

def predictPacket (value : Readout (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) :
    Option (Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) :=
  (predictCurrent downstreamTechnology downstreamGraph value).map FiniteADCWholeJointCurrent.packet

def advanceReadout (value : Readout (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) :
    Option (Readout (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) :=
  (predictCurrent downstreamTechnology downstreamGraph value).map sourceRead

theorem predictCurrent_source (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :
    predictCurrent downstreamTechnology downstreamGraph (sourceRead current) =
      some (loadedStep downstreamTechnology downstreamGraph current) := by
  rw [predictCurrent, recoverCurrent_source]
  rfl

theorem predictPacket_source (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :
    predictPacket downstreamTechnology downstreamGraph (sourceRead current) =
      some (loadedStep downstreamTechnology downstreamGraph current).packet := by
  rw [predictPacket, predictCurrent_source]
  rfl

theorem advanceReadout_source (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology) :
    advanceReadout downstreamTechnology downstreamGraph (sourceRead current) =
      some (sourceRead (loadedStep downstreamTechnology downstreamGraph current)) := by
  rw [advanceReadout, predictCurrent_source]
  rfl

variable (seed : FiniteADCWholeJointCurrent hardware
  (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

def observation (bound : Nat) (actor : Fin (bound + 1)) :
    Readout (hardware := hardware) (actualBoot := actualBoot) (technology := technology) :=
  sourceRead (loadedAfter downstreamTechnology downstreamGraph seed actor.val)

theorem conditional_predictor (bound : Nat)
    (value : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology))
    (supported : value ∈ ((historyPMF bound).map (nowPacket downstreamTechnology downstreamGraph seed bound)).support) :
    ((SourceConditionalHistory.conditional (historyPMF bound)
      (nowPacket downstreamTechnology downstreamGraph seed bound) value supported).map
        (observation downstreamTechnology downstreamGraph seed bound)).map
          (predictPacket downstreamTechnology downstreamGraph) =
      (conditionalNext downstreamTechnology downstreamGraph seed bound value supported).map some := by
  rw [conditionalNext, SourceConditionalNext.conditionalNext, PMF.map_comp, PMF.map_comp]
  congr 1
  funext actor
  exact predictPacket_source downstreamTechnology downstreamGraph
    (loadedAfter downstreamTechnology downstreamGraph seed actor.val)

theorem recovered_same_future (left right : Nat)
    (same : sourceRead (loadedAfter downstreamTechnology downstreamGraph seed left) =
      sourceRead (loadedAfter downstreamTechnology downstreamGraph seed right)) :
    ∀ future : Nat, loadedAfter downstreamTechnology downstreamGraph seed (left + future) =
      loadedAfter downstreamTechnology downstreamGraph seed (right + future) := by
  intro future
  induction future with
  | zero => simpa using sourceRead_injective same
  | succ future ih =>
      simpa only [Nat.add_succ, loadedAfter_succ] using congrArg
        (loadedStep downstreamTechnology downstreamGraph) ih

theorem recovered_same_model (left right : Nat)
    (same : sourceRead (loadedAfter downstreamTechnology downstreamGraph seed left) =
      sourceRead (loadedAfter downstreamTechnology downstreamGraph seed right)) :
    modelAt downstreamTechnology downstreamGraph seed left = modelAt downstreamTechnology downstreamGraph seed right :=
  (model_history_fibre downstreamTechnology downstreamGraph seed left right).mpr
    (fun future => congrArg FiniteADCWholeJointCurrent.packet
      (recovered_same_future downstreamTechnology downstreamGraph seed left right same future))

end
end FiniteADCWholeJointCurrent.Information.Packet.Recovered
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
