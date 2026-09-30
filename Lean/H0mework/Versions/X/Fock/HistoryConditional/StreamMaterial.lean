import H0mework.Versions.X.Fock.HistoryConditional.StreamConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalStream

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceConditionalModel (Actors NextModel dynamicRead)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  (∀ depth : Nat, type_of% (generated_source (inventoryBound runtime) depth) ∧ type_of% (generated_current_next runtime depth) ∧
    type_of% (generated_model runtime depth) ∧ type_of% (generated_model_next runtime depth) ∧
    type_of% (generated_attains runtime depth) ∧ type_of% (generated_error_next runtime depth) ∧ type_of% (generated_information runtime depth) ∧
    ∀ value : Field parity, type_of% (generated_realization runtime depth value) ∧
      ∀ supported : value ∈ ((historyPMF (inventoryBound runtime)).map (dynamicRead runtime depth)).support,
        type_of% (generated_posterior runtime depth value supported) ∧ type_of% (generated_exact_support runtime depth value supported) ∧
        ∀ model : NextModel runtime, type_of% (generated_support_restored runtime depth value supported model)) ∧
  (∀ index : Actors runtime, type_of% (sample_factorizes runtimeSeed (inventoryBound runtime) index) ∧
    type_of% (SourceConditionalInventory.material_retained (inventoryBound runtime) index)) ∧
  type_of% (SourceConditionalInventory.born_current runtime) ∧ type_of% material.factorizes

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨(fun depth => ⟨generated_source (inventoryBound runtime) depth, generated_current_next runtime depth,
    generated_model runtime depth, generated_model_next runtime depth, generated_attains runtime depth, generated_error_next runtime depth,
    generated_information runtime depth, fun value => ⟨generated_realization runtime depth value,
      fun supported => ⟨generated_posterior runtime depth value supported, generated_exact_support runtime depth value supported,
        fun model => generated_support_restored runtime depth value supported model⟩⟩⟩),
    (fun index => ⟨sample_factorizes runtimeSeed (inventoryBound runtime) index,
      SourceConditionalInventory.material_retained (inventoryBound runtime) index⟩), SourceConditionalInventory.born_current runtime, material.factorizes⟩

end
end SourceConditionalStream
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
