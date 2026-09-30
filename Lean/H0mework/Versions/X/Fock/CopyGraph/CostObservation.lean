import H0mework.Versions.X.Fock.CopyGraph.CostField
import H0mework.Versions.X.Fock.CopyGraph.CostEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalCost

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceConditionalCorrection
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceCopyObservation (before after joint twoMaterial)
open SourceCopyProgram (Index sourceDepth)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance observationParentMeasurable : MeasurableSpace ParentCarrier := ⊤

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    let depth := inventoryBound runtime
    (∀ value : FieldSpace depth depth,
      type_of% (original_minimum_cost depth depth index (before depth depth) value) ∧
      type_of% (original_minimum_cost depth depth index (joint depth depth index) value) ∧
      type_of% (original_residual_budget depth depth index (joint depth depth index) value) ∧
      type_of% (zero_surplus_iff depth depth index (joint depth depth index) (Actor.currentPullback depth depth value)) ∧
      ∀ actor : Fin (depth + 1), type_of% (SourceGeneratedConditionalInventory.full_record_read runtime depth
        (Actor.currentPullback depth depth (value - fieldRecovery depth depth index (joint depth depth index) value)) actor)) ∧
      SourceConditionalCorrection.ObservationAt runtime index

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨(fun value => ⟨original_minimum_cost _ _ index _ value, original_minimum_cost _ _ index _ value,
    original_residual_budget _ _ index _ value, zero_surplus_iff _ _ index _ (Actor.currentPullback _ _ value),
    SourceGeneratedConditionalInventory.full_record_read runtime _ _⟩),
    SourceConditionalCorrection.observation_consumed runtime index⟩

def ActualRecovery : Prop :=
    type_of% before_best_cost_strict ∧ type_of% before_complete_budget ∧
      (∀ value : FieldSpace 3 3, type_of% (after_best_cost_zero (Actor.currentPullback 3 3 value))) ∧
      SourceConditionalCorrection.ActualRecovery

theorem actual_recovery_consumed : ActualRecovery :=
  ⟨before_best_cost_strict, before_complete_budget,
    (fun value => after_best_cost_zero (Actor.currentPullback 3 3 value)), SourceConditionalCorrection.actual_recovery_consumed⟩

def RoundAt (round : Nat) : Prop :=
    let depth := sourceDepth round
    SourceConditionalCorrection.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index depth, ObservationAt (roundRuntime round) index ∧
        ∀ value : FieldSpace depth depth,
          SourceCopyGraph.FieldAt round depth depth index (value - fieldRecovery depth depth index (before depth depth) value) ∧
          SourceCopyGraph.FieldAt round depth depth index (value - fieldRecovery depth depth index (joint depth depth index) value)

theorem round_consumed (round : Nat) : RoundAt round := by
  dsimp only [RoundAt]
  exact ⟨SourceConditionalCorrection.round_consumed round, actual_recovery_consumed,
    fun index => ⟨observation_consumed (roundRuntime round) index,
      fun _ => ⟨SourceCopyGraph.original_field_consumed round _ _ index _,
        SourceCopyGraph.original_field_consumed round _ _ index _⟩⟩⟩

end
end SourceConditionalCost
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
