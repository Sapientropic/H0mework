import H0mework.Versions.X.Fock.HistoryConditional.ModelUpdateConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalModelUpdate

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceConditionalModel (Actors dynamicRead)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  (∀ depth : Nat, type_of% (update_is_next runtime depth) ∧ type_of% (update_attains runtime depth) ∧
    type_of% (update_error runtime depth) ∧ type_of% (information_cost runtime depth) ∧ type_of% (fresh_model_recovers runtime depth) ∧
    ∀ value : Field parity, type_of% (retained_decoder runtime (dynamicRead runtime depth) value) ∧ type_of% (update_realization runtime depth value)) ∧
  (∀ index : Actors runtime, type_of% (retained_source runtime index) ∧
    type_of% (SourceActualImageStep.retained_material runtime index) ∧ type_of% (sample_factorizes runtimeSeed (inventoryBound runtime) index)) ∧
  type_of% (birth_realization runtime) ∧ type_of% material.factorizes

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨(fun depth => ⟨update_is_next runtime depth, update_attains runtime depth, update_error runtime depth,
    information_cost runtime depth, fresh_model_recovers runtime depth,
    fun value => ⟨retained_decoder runtime (dynamicRead runtime depth) value, update_realization runtime depth value⟩⟩),
    (fun index => ⟨retained_source runtime index, SourceActualImageStep.retained_material runtime index,
      sample_factorizes runtimeSeed (inventoryBound runtime) index⟩), birth_realization runtime, material.factorizes⟩

end
end SourceConditionalModelUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
