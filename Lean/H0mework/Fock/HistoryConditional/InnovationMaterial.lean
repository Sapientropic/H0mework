import H0mework.Fock.HistoryConditional.InnovationOriginal

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInnovation

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  (∀ depth : Nat, type_of% (update_current runtime depth) ∧ type_of% (update_attains_current runtime depth) ∧
    type_of% (minimum_current runtime depth) ∧ type_of% (update_error_current runtime depth) ∧ type_of% (update_information_current runtime depth)) ∧
  (∀ depth : Nat, type_of% (count_append (inventoryBound runtime) depth) ∧
    type_of% (decoder_mean_append (inventoryBound runtime) depth) ∧ type_of% (update_recovers_fresh (inventoryBound runtime) depth)) ∧
  (∀ index : Actors runtime, type_of% (sample_factorizes runtimeSeed (inventoryBound runtime) index) ∧
    type_of% (SourceConditionalInventory.material_retained (inventoryBound runtime) index)) ∧
  type_of% (SourceConditionalInventory.born_current runtime) ∧ type_of% material.factorizes

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨(fun depth => ⟨update_current runtime depth, update_attains_current runtime depth, minimum_current runtime depth,
    update_error_current runtime depth, update_information_current runtime depth⟩),
    (fun depth => ⟨count_append (inventoryBound runtime) depth, decoder_mean_append (inventoryBound runtime) depth,
      update_recovers_fresh (inventoryBound runtime) depth⟩),
    (fun index => ⟨sample_factorizes runtimeSeed (inventoryBound runtime) index, SourceConditionalInventory.material_retained (inventoryBound runtime) index⟩),
    SourceConditionalInventory.born_current runtime, material.factorizes⟩

end
end SourceConditionalInnovation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
