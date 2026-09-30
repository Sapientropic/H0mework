import H0mework.Computation.LoadedADCInformation.AccountRecovery
import H0mework.Checks.Realization.OccurrenceChargeHistory

/-! The old loaded information consumer executes the source-generated account update and its dynamic Model. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.AccountAction

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

open SourceOwnedObservationHistory SourceGeneratedActionObservationHistory

theorem incremental_information_consumed (bound : Nat) (enough : 2 ≤ bound)
    (task : Fin (bound + 1) → ℂ) (decoder : FiniteBinaryDrive → ℂ) :
    type_of% (incremental_next downstreamTechnology downstreamGraph seed bound) ∧
      type_of% (incremental_reads_actual downstreamTechnology downstreamGraph seed (bound + 1)) ∧
      type_of% (SourceAccountedAction.source_square (loadedStep downstreamTechnology downstreamGraph)
        (phaseCharge (hardware := hardware) (actualBoot := actualBoot) (technology := technology)
          downstreamTechnology downstreamGraph)) ∧
      type_of% (SourceAccountedAction.kernel_exact (loadedStep downstreamTechnology downstreamGraph)
        (phaseCharge (hardware := hardware) (actualBoot := actualBoot) (technology := technology)
          downstreamTechnology downstreamGraph)) ∧
      type_of% (generated_quotient_action_matches
        (sourceAction (SourceAccountedAction.occurrenceUpdate (loadedStep downstreamTechnology downstreamGraph)))
        (observation (SourceAccountedAction.retained (phaseCharge (hardware := hardware)
          (actualBoot := actualBoot) (technology := technology) downstreamTechnology downstreamGraph)))) ∧
      type_of% (next_model_is_calculation downstreamTechnology downstreamGraph seed bound) ∧
      type_of% (next_time_from_model downstreamTechnology downstreamGraph seed bound) ∧
      type_of% (model_conditional_is_original downstreamTechnology downstreamGraph seed bound) ∧
      type_of% (model_recovery_zero downstreamTechnology downstreamGraph seed bound task) ∧
      type_of% (model_posterior_material downstreamTechnology downstreamGraph seed bound) ∧
      type_of% (forecast_whole_account downstreamTechnology downstreamGraph seed bound) ∧
      type_of% SourceAccountedAction.Regression.same_generated_model ∧
      type_of% SourceAccountedAction.Regression.different_original_histories ∧
      type_of% SourceAccountedAction.Regression.nonzero_charge_separates ∧
      type_of% (information_consumed downstreamTechnology downstreamGraph seed bound enough task decoder) := by
  exact ⟨incremental_next downstreamTechnology downstreamGraph seed bound,
    incremental_reads_actual downstreamTechnology downstreamGraph seed (bound + 1),
    SourceAccountedAction.source_square _ _, SourceAccountedAction.kernel_exact _ _,
    generated_quotient_action_matches _ _,
    next_model_is_calculation downstreamTechnology downstreamGraph seed bound,
    next_time_from_model downstreamTechnology downstreamGraph seed bound,
    model_conditional_is_original downstreamTechnology downstreamGraph seed bound,
    model_recovery_zero downstreamTechnology downstreamGraph seed bound task,
    model_posterior_material downstreamTechnology downstreamGraph seed bound,
    forecast_whole_account downstreamTechnology downstreamGraph seed bound,
    SourceAccountedAction.Regression.same_generated_model,
    SourceAccountedAction.Regression.different_original_histories,
    SourceAccountedAction.Regression.nonzero_charge_separates,
    information_consumed downstreamTechnology downstreamGraph seed bound enough task decoder⟩

end
end FiniteADCWholeJointCurrent.Information.AccountAction
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
