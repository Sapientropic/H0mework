import H0mework.Computation.LoadedADCInformation.Conditional
import H0mework.Computation.LoadedADCInformation.Account

/-! Sampled prefixes and literal loaded next retain the existing whole physical material and energy account. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

theorem material_stage_owned (frame : Nat) :
    let current := loadedAfter downstreamTechnology downstreamGraph seed frame
    (loadedExposure downstreamTechnology downstreamGraph seed frame).frontier = [current] ∧
      (loadedAfter downstreamTechnology downstreamGraph seed (frame + 1)).plant =
        loadedReceiverFreshSample downstreamTechnology downstreamGraph current ∧
      (loadedAfter downstreamTechnology downstreamGraph seed (frame + 1)).memory =
        loadedReceiverSnapshotMemory downstreamTechnology downstreamGraph current ∧
      current.physicalRead downstreamTechnology downstreamGraph = some (some current.plant.val.drive) ∧
      type_of% (current.physicalRead_is_state_projection downstreamTechnology downstreamGraph) ∧
      type_of% (loadedAfter_generates_sample downstreamTechnology downstreamGraph seed frame) ∧
      type_of% (loadedAfter_no_recipient_reset downstreamTechnology downstreamGraph seed frame) ∧
      type_of% (loadedAfter_no_memory_reset downstreamTechnology downstreamGraph seed frame) ∧
      type_of% (loadedStepDuration_four_phases downstreamTechnology downstreamGraph current) ∧
      type_of% (loadedStep_energy_balance downstreamTechnology downstreamGraph current) ∧
      type_of% (loadedAfter_changes_current downstreamTechnology downstreamGraph seed frame) := by
  let current := loadedAfter downstreamTechnology downstreamGraph seed frame
  refine ⟨loadedExposure_frontier downstreamTechnology downstreamGraph seed frame, ?_, ?_,
    current.physicalRead_received downstreamTechnology downstreamGraph,
    current.physicalRead_is_state_projection downstreamTechnology downstreamGraph,
    loadedAfter_generates_sample downstreamTechnology downstreamGraph seed frame,
    loadedAfter_no_recipient_reset downstreamTechnology downstreamGraph seed frame,
    loadedAfter_no_memory_reset downstreamTechnology downstreamGraph seed frame,
    loadedStepDuration_four_phases downstreamTechnology downstreamGraph current,
    loadedStep_energy_balance downstreamTechnology downstreamGraph current,
    loadedAfter_changes_current downstreamTechnology downstreamGraph seed frame⟩
  · rw [loadedAfter_succ]
    rfl
  · rw [loadedAfter_succ]
    rfl

theorem terminal_next (bound : Nat) :
    let current := loadedAfter downstreamTechnology downstreamGraph seed bound
    (loadedExposure downstreamTechnology downstreamGraph seed (bound + 1)).frontier =
        [loadedStep downstreamTechnology downstreamGraph current] ∧
      timeRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed (bound + 1)) =
        timeRead downstreamTechnology downstreamGraph (loadedExposure downstreamTechnology downstreamGraph seed bound) +
          charge downstreamTechnology downstreamGraph current ∧
      (loadedStep downstreamTechnology downstreamGraph current).physicalRead downstreamTechnology downstreamGraph =
        some (some (fun channel => !(current.plant.val.drive channel))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [loadedExposure_frontier, loadedAfter_succ]
  · rw [timeRead_exposure, timeRead_exposure, loadedElapsed_succ]
    rfl
  · rw [loadedStep_receives_own_recorded_sample, loadedStep_feedback]

theorem posterior_retains_material (bound : Nat) (point candidate : Fin (bound + 1))
    (supported : candidate ∈ (SourceConditionalHistory.conditional
      (SourceGeneratedRuntimeHistoryProbability.historyPMF bound)
      (timeQuery downstreamTechnology downstreamGraph seed bound)
      (timeQuery downstreamTechnology downstreamGraph seed bound point)
      (SourceWeightedRecovery.observed_supported _ _ point (history_weight_positive bound point))).support) :
    materialQuery downstreamTechnology downstreamGraph seed bound candidate =
      materialQuery downstreamTechnology downstreamGraph seed bound point := by
  rw [time_conditional, PMF.mem_support_pure_iff] at supported
  subst candidate
  rfl

end
end FiniteADCWholeJointCurrent.Information
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
