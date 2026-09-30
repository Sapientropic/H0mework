import H0mework.Physics.ADCRuntime.LoadedInformationHistoryRegression
import H0mework.Computation.LoadedADCInformation.Material

/-! The original loaded physical consumer receives the information law, whole bill, complete material and literal next. -/

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

open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

theorem information_consumed (bound : Nat) (enough : 2 ≤ bound)
    (task : Fin (bound + 1) → ℂ) (decoder : FiniteBinaryDrive → ℂ) :
    type_of% (drive_future_iff downstreamTechnology downstreamGraph seed) ∧
      type_of% (drive_repetition_retains_distinct_material downstreamTechnology downstreamGraph seed) ∧
      type_of% (drive_error_equation downstreamTechnology downstreamGraph seed bound task decoder) ∧
      type_of% (IsometricRetainedTransfer.pullback_transfer_add_residual
        (pullback (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound))
        (taskValue (historyPMF bound) task)) ∧
      type_of% (compressed_time_lower_bound downstreamTechnology downstreamGraph seed bound enough decoder) ∧
      type_of% (compressed_time_positive downstreamTechnology downstreamGraph seed bound enough decoder) ∧
      type_of% (compressed_residual_lower_bound downstreamTechnology downstreamGraph seed bound enough) ∧
      type_of% (time_conditional downstreamTechnology downstreamGraph seed bound) ∧
      type_of% (time_error_zero downstreamTechnology downstreamGraph seed bound task) ∧
      type_of% (posterior_retains_material downstreamTechnology downstreamGraph seed bound) ∧
      type_of% (drive_task_recovery downstreamTechnology downstreamGraph seed bound) ∧
      type_of% (two_actor_recovery downstreamTechnology downstreamGraph seed) ∧
      type_of% (no_drive_material_decoder downstreamTechnology downstreamGraph seed) ∧
      (∀ frame, frame ≤ bound → type_of% (material_stage_owned downstreamTechnology downstreamGraph seed frame)) ∧
      type_of% (whole_material_account downstreamTechnology downstreamGraph seed (bound + 1)) ∧
      type_of% (material_heat_budget downstreamTechnology downstreamGraph seed (bound + 1)) ∧
      type_of% (terminal_next downstreamTechnology downstreamGraph seed bound) ∧
      type_of% (loaded_arbitrary_finite_horizon downstreamTechnology downstreamGraph seed bound) ∧
      type_of% (loadedContinuation_no_zeno downstreamTechnology downstreamGraph seed) := by
  exact ⟨drive_future_iff downstreamTechnology downstreamGraph seed,
    drive_repetition_retains_distinct_material downstreamTechnology downstreamGraph seed,
    drive_error_equation downstreamTechnology downstreamGraph seed bound task decoder,
    IsometricRetainedTransfer.pullback_transfer_add_residual _ _,
    compressed_time_lower_bound downstreamTechnology downstreamGraph seed bound enough decoder,
    compressed_time_positive downstreamTechnology downstreamGraph seed bound enough decoder,
    compressed_residual_lower_bound downstreamTechnology downstreamGraph seed bound enough,
    time_conditional downstreamTechnology downstreamGraph seed bound,
    time_error_zero downstreamTechnology downstreamGraph seed bound task,
    posterior_retains_material downstreamTechnology downstreamGraph seed bound,
    drive_task_recovery downstreamTechnology downstreamGraph seed bound,
    two_actor_recovery downstreamTechnology downstreamGraph seed,
    no_drive_material_decoder downstreamTechnology downstreamGraph seed,
    fun frame _ => material_stage_owned downstreamTechnology downstreamGraph seed frame,
    whole_material_account downstreamTechnology downstreamGraph seed (bound + 1),
    material_heat_budget downstreamTechnology downstreamGraph seed (bound + 1),
    terminal_next downstreamTechnology downstreamGraph seed bound,
    loaded_arbitrary_finite_horizon downstreamTechnology downstreamGraph seed bound,
    loadedContinuation_no_zeno downstreamTechnology downstreamGraph seed⟩

end
end FiniteADCWholeJointCurrent.Information
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
