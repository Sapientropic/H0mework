import H0mework.Computation.LoadedADCPacket.Duration
import H0mework.Probability.Source.ConditionalNext

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Packet

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

private theorem source_supported (bound : Nat) (actor : Fin (bound + 1)) : actor ∈ (historyPMF bound).support :=
  (PMF.mem_support_iff _ _).mpr (history_weight_positive bound actor)

def conditionalNext (bound : Nat)
    (value : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology))
    (supported : value ∈ ((historyPMF bound).map (nowPacket downstreamTechnology downstreamGraph seed bound)).support) :
    PMF (Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) :=
  SourceConditionalNext.conditionalNext (historyPMF bound)
    (nowPacket downstreamTechnology downstreamGraph seed bound)
    (nextPacket downstreamTechnology downstreamGraph seed bound) value supported

theorem conditionalNext_support (bound : Nat)
    (value : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology))
    (supported : value ∈ ((historyPMF bound).map (nowPacket downstreamTechnology downstreamGraph seed bound)).support)
    (next : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology)) :
    next ∈ (conditionalNext downstreamTechnology downstreamGraph seed bound value supported).support ↔
      ∃ actor, nowPacket downstreamTechnology downstreamGraph seed bound actor = value ∧
        nextPacket downstreamTechnology downstreamGraph seed bound actor = next := by
  rw [conditionalNext, SourceConditionalNext.conditionalNext_support]
  constructor
  · rintro ⟨actor, same, _, target⟩
    exact ⟨actor, same, target⟩
  · rintro ⟨actor, same, target⟩
    exact ⟨actor, same, history_weight_positive bound actor, target⟩

theorem conditionalNext_recombines (bound : Nat) :
    ((historyPMF bound).map (nowPacket downstreamTechnology downstreamGraph seed bound)).bindOnSupport
        (conditionalNext downstreamTechnology downstreamGraph seed bound) =
      (historyPMF bound).map (nextPacket downstreamTechnology downstreamGraph seed bound) :=
  SourceConditionalNext.conditionalNext_recombines _ _ _

def sampleMean (bound : Nat) (actor : Fin (bound + 1)) : ℂ :=
  SourceConditionalNext.mean (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound)
    (nextPacket downstreamTechnology downstreamGraph seed bound) headerDecoder
    (nowPacket downstreamTechnology downstreamGraph seed bound actor)
    (observed_supported _ _ actor (source_supported bound actor))

def sampleVariance (bound : Nat) (actor : Fin (bound + 1)) : ℝ :=
  SourceConditionalNext.variance (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound)
    (nextPacket downstreamTechnology downstreamGraph seed bound) headerDecoder
    (nowPacket downstreamTechnology downstreamGraph seed bound actor)
    (observed_supported _ _ actor (source_supported bound actor))

theorem sampleMean_formula (bound : Nat) (actor : Fin (bound + 1)) :
    sampleMean downstreamTechnology downstreamGraph seed bound actor =
      ∑ code, (conditionalNext downstreamTechnology downstreamGraph seed bound
        (nowPacket downstreamTechnology downstreamGraph seed bound actor)
        (observed_supported _ _ actor (source_supported bound actor)) code).toReal • headerDecoder code := rfl

theorem sampleVariance_formula (bound : Nat) (actor : Fin (bound + 1)) :
    sampleVariance downstreamTechnology downstreamGraph seed bound actor =
      ∑ code, (conditionalNext downstreamTechnology downstreamGraph seed bound
        (nowPacket downstreamTechnology downstreamGraph seed bound actor)
        (observed_supported _ _ actor (source_supported bound actor)) code).toReal *
          ‖headerDecoder code - sampleMean downstreamTechnology downstreamGraph seed bound actor‖ ^ 2 := rfl

private theorem sampleTask_composition (bound : Nat) :
    sampleTask downstreamTechnology downstreamGraph seed bound =
      headerDecoder ∘ nextPacket downstreamTechnology downstreamGraph seed bound := by
  funext actor
  exact sampleTask_eq_decode_next downstreamTechnology downstreamGraph seed bound actor

theorem original_transfer_mean (bound : Nat) (actor : Fin (bound + 1)) :
    optimalDecoder (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound)
      (sampleTask downstreamTechnology downstreamGraph seed bound)
      (nowPacket downstreamTechnology downstreamGraph seed bound actor) =
        sampleMean downstreamTechnology downstreamGraph seed bound actor := by
  rw [sampleTask_composition]
  exact SourceConditionalNext.optimal_is_mean _ _ _ _ _ _

theorem sampleVariance_nonnegative (bound : Nat) (actor : Fin (bound + 1)) :
    0 ≤ sampleVariance downstreamTechnology downstreamGraph seed bound actor :=
  SourceConditionalNext.variance_nonnegative _ _ _ _ _ _

theorem original_residual_variance (bound : Nat) :
    ‖residual (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound)
      (taskValue (historyPMF bound) (sampleTask downstreamTechnology downstreamGraph seed bound))‖ ^ 2 =
      ∑ actor, (historyPMF bound actor).toReal * sampleVariance downstreamTechnology downstreamGraph seed bound actor := by
  rw [sampleTask_composition]
  exact SourceConditionalNext.residual_variance _ _ _ _ (source_supported bound)

theorem original_error_decomposition (bound : Nat)
    (decoder : Code (hardware := hardware) (actualBoot := actualBoot) (technology := technology) → ℂ) :
    error (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound)
        (sampleTask downstreamTechnology downstreamGraph seed bound) decoder =
      (∑ actor, (historyPMF bound actor).toReal * sampleVariance downstreamTechnology downstreamGraph seed bound actor) +
      error (historyPMF bound) (nowPacket downstreamTechnology downstreamGraph seed bound)
        (sampleMean downstreamTechnology downstreamGraph seed bound) decoder := by
  rw [sampleTask_composition]
  exact SourceConditionalNext.error_variance _ _ _ _ (source_supported bound) decoder

end
end FiniteADCWholeJointCurrent.Information.Packet
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
