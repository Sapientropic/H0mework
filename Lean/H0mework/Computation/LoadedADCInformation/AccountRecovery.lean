import H0mework.Computation.LoadedADCInformation.AccountModel

/-! The generated dynamic Model consumes the old full conditional and its actual recovery algorithm. -/

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

open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

def modelTime (value : CurrentModel (hardware := hardware) (actualBoot := actualBoot) (technology := technology)
    downstreamTechnology downstreamGraph) : ℝ :=
  (readModel downstreamTechnology downstreamGraph value).2.1

def modelQuery (bound : Nat) (point : Fin (bound + 1)) :=
  modelAt downstreamTechnology downstreamGraph seed point.val

theorem model_query_time (bound : Nat) (point : Fin (bound + 1)) :
    modelTime downstreamTechnology downstreamGraph (modelQuery downstreamTechnology downstreamGraph seed bound point) =
      timeQuery downstreamTechnology downstreamGraph seed bound point := by
  change (readModel downstreamTechnology downstreamGraph
    (modelAt downstreamTechnology downstreamGraph seed point.val)).2.1 = _
  rw [read_model]
  rfl

theorem model_query_injective (bound : Nat) :
    Function.Injective (modelQuery downstreamTechnology downstreamGraph seed bound) := by
  intro left right same
  apply timeQuery_injective downstreamTechnology downstreamGraph seed bound
  have read := congrArg (modelTime downstreamTechnology downstreamGraph) same
  simpa only [model_query_time] using read

theorem model_conditional_is_original (bound : Nat) (point : Fin (bound + 1)) :
    SourceConditionalHistory.conditional (historyPMF bound)
      (modelQuery downstreamTechnology downstreamGraph seed bound)
      (modelQuery downstreamTechnology downstreamGraph seed bound point)
      (observed_supported _ _ point (history_weight_positive bound point)) =
    SourceConditionalHistory.conditional (historyPMF bound)
      (timeQuery downstreamTechnology downstreamGraph seed bound)
      (timeQuery downstreamTechnology downstreamGraph seed bound point)
      (observed_supported _ _ point (history_weight_positive bound point)) := by
  rw [ObservationRefinement.conditional_injective _ _
    (model_query_injective downstreamTechnology downstreamGraph seed bound)
    point (history_weight_positive bound point), time_conditional]

theorem model_error_is_original (bound : Nat) (task : Fin (bound + 1) → ℂ) (decoder : ℝ → ℂ) :
    error (historyPMF bound) (modelQuery downstreamTechnology downstreamGraph seed bound) task
      (decoder ∘ modelTime downstreamTechnology downstreamGraph) =
        error (historyPMF bound) (timeQuery downstreamTechnology downstreamGraph seed bound) task decoder := by
  simp only [error, Function.comp_apply, model_query_time]

theorem model_recovery_zero (bound : Nat) (task : Fin (bound + 1) → ℂ) :
    error (historyPMF bound) (modelQuery downstreamTechnology downstreamGraph seed bound) task
      (optimalDecoder (historyPMF bound) (timeQuery downstreamTechnology downstreamGraph seed bound) task ∘
        modelTime downstreamTechnology downstreamGraph) = 0 := by
  rw [model_error_is_original, time_error_zero]

theorem next_time_from_model (bound : Nat) :
    modelTime downstreamTechnology downstreamGraph
      (advanceModel downstreamTechnology downstreamGraph (modelAt downstreamTechnology downstreamGraph seed bound)) =
        loadedElapsed downstreamTechnology downstreamGraph seed (bound + 1) := by
  rw [next_model]
  change (readModel downstreamTechnology downstreamGraph
    (modelAt downstreamTechnology downstreamGraph seed (bound + 1))).2.1 = _
  rw [read_model, incremental_reads_actual]

theorem model_posterior_material (bound : Nat) (point candidate : Fin (bound + 1))
    (supported : candidate ∈ (SourceConditionalHistory.conditional (historyPMF bound)
      (modelQuery downstreamTechnology downstreamGraph seed bound)
      (modelQuery downstreamTechnology downstreamGraph seed bound point)
      (observed_supported _ _ point (history_weight_positive bound point))).support) :
    materialQuery downstreamTechnology downstreamGraph seed bound candidate =
      materialQuery downstreamTechnology downstreamGraph seed bound point := by
  rw [model_conditional_is_original] at supported
  exact posterior_retains_material downstreamTechnology downstreamGraph seed bound point candidate supported

end
end FiniteADCWholeJointCurrent.Information.AccountAction
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
