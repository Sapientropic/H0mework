import H0mework.Fock.HistoryConditional.StabilityConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePosteriorStability

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceConditionalModel (NextModel dynamicRead)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  (∀ depth : Nat, ∀ models : Field parity → NextModel runtime, type_of% (profile_error_budget runtime depth models)) ∧
  (∀ depth : Nat, ∀ value : Field parity,
    ∀ supported : value ∈ ((historyPMF (inventoryBound runtime.tick.next)).map (dynamicRead runtime.tick.next depth)).support,
    ∀ model : NextModel runtime.tick.next,
      type_of% (updated_inventory_error runtime depth value supported model) ∧ type_of% (updated_support_restored runtime depth value supported model)) ∧
  (∀ left right : NextModel runtime, type_of% (weights_inventory runtime left right)) ∧
  (∀ enough : 2 ≤ inventoryBound runtime, type_of% (merged_distance runtime enough) ∧ type_of% (merged_fails_support runtime enough)) ∧
  type_of% material.factorizes

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨(fun depth models => profile_error_budget runtime depth models),
    (fun depth value supported model => ⟨updated_inventory_error runtime depth value supported model,
      updated_support_restored runtime depth value supported model⟩),
    (fun left right => weights_inventory runtime left right),
    (fun enough => ⟨merged_distance runtime enough, merged_fails_support runtime enough⟩), material.factorizes⟩

end
end SourcePosteriorStability
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
