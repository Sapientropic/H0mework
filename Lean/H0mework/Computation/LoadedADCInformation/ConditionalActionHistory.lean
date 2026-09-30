import H0mework.Probability.Source.ConditionalAction
import H0mework.Computation.LoadedADCInformation.ConditionalActionSource

/-! The old source PMF over whole occurrences advances with its actual material and complete conditionals. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.ConditionalAction

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

open SourceOwnedObservationHistory SourceGeneratedRuntimeHistoryProbability

theorem tree_iterate (depth : Nat) :
    ((SourceAccountedAction.occurrenceUpdate (loadedStep downstreamTechnology downstreamGraph))^[depth])
      (RootedAccountedUnfolding.zero seed) = loadedExposure downstreamTechnology downstreamGraph seed depth := by
  induction depth with
  | zero => rfl
  | succ depth induction =>
      rw [Function.iterate_succ_apply', induction]
      rfl

def sourceLaw (bound : Nat) :=
  SourceOwnedObservationHistory.statePMF (SourceAccountedAction.occurrenceUpdate
    (loadedStep downstreamTechnology downstreamGraph)) (RootedAccountedUnfolding.zero seed) bound

theorem sourceLaw_sampled (bound : Nat) :
    sourceLaw downstreamTechnology downstreamGraph seed bound =
      (historyPMF bound).map (materialQuery downstreamTechnology downstreamGraph seed bound) := by
  unfold sourceLaw SourceOwnedObservationHistory.statePMF
  congr 1
  funext point
  exact tree_iterate downstreamTechnology downstreamGraph seed point.val

theorem sourceLaw_next (bound : Nat) :
    (sourceLaw downstreamTechnology downstreamGraph seed bound).map
      (SourceAccountedAction.occurrenceUpdate (loadedStep downstreamTechnology downstreamGraph)) =
    SourceOwnedObservationHistory.statePMF (SourceAccountedAction.occurrenceUpdate
      (loadedStep downstreamTechnology downstreamGraph)) (loadedExposure downstreamTechnology downstreamGraph seed 1) bound :=
  SourceOwnedObservationHistory.statePMF_step _ _ _

theorem next_sampled (bound : Nat) :
    (sourceLaw downstreamTechnology downstreamGraph seed bound).map
      (SourceAccountedAction.occurrenceUpdate (loadedStep downstreamTechnology downstreamGraph)) =
    (historyPMF bound).map (fun point => loadedExposure downstreamTechnology downstreamGraph seed (point.val + 1)) := by
  rw [sourceLaw_sampled, PMF.map_comp]
  rfl

theorem sample_supported (bound : Nat) (point : Fin (bound + 1)) :
    materialQuery downstreamTechnology downstreamGraph seed bound point ∈
      (sourceLaw downstreamTechnology downstreamGraph seed bound).support := by
  rw [sourceLaw_sampled, PMF.mem_support_map_iff]
  exact ⟨point, history_weight_positive bound point, rfl⟩

theorem query_supported (bound : Nat) (point : Fin (bound + 1)) :
    sourcePoint (driveAt downstreamTechnology downstreamGraph seed point.val) ∈
      (SourceConditionalHistory.observed (sourceLaw downstreamTechnology downstreamGraph seed bound) materialRead).support := by
  have supported := SourceWeightedRecovery.observed_supported (sourceLaw downstreamTechnology downstreamGraph seed bound)
    materialRead (materialQuery downstreamTechnology downstreamGraph seed bound point)
    (sample_supported downstreamTechnology downstreamGraph seed bound point)
  simpa only [materialQuery, material_read_history] using supported

theorem conditional_next (bound : Nat) (value : Carrier FiniteBinaryDrive)
    (supported : value ∈ (SourceConditionalHistory.observed
      (sourceLaw downstreamTechnology downstreamGraph seed bound) materialRead).support) :
    ∃ nextSupported : commandAction value ∈ (SourceConditionalHistory.observed
      ((sourceLaw downstreamTechnology downstreamGraph seed bound).map
        (SourceAccountedAction.occurrenceUpdate (loadedStep downstreamTechnology downstreamGraph))) materialRead).support,
      (SourceConditionalHistory.conditional (sourceLaw downstreamTechnology downstreamGraph seed bound)
        materialRead value supported).map (SourceAccountedAction.occurrenceUpdate (loadedStep downstreamTechnology downstreamGraph)) =
      SourceConditionalHistory.conditional
        ((sourceLaw downstreamTechnology downstreamGraph seed bound).map
          (SourceAccountedAction.occurrenceUpdate (loadedStep downstreamTechnology downstreamGraph)))
        materialRead (commandAction value) nextSupported :=
  SourceConditionalHistory.conditional_pushforward _ _ _ _ _
    (material_source_square downstreamTechnology downstreamGraph) command_action_injective value supported

end
end FiniteADCWholeJointCurrent.Information.ConditionalAction
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
