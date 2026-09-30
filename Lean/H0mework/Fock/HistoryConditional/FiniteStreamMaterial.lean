import H0mework.Fock.HistoryConditional.FiniteStreamConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalFiniteStream

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceConditionalModel (Actors NextModel dynamicRead)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  (∀ depth : Nat, type_of% (generated_read (inventoryBound runtime) depth) ∧ type_of% (support_exact (inventoryBound runtime) depth) ∧
    type_of% (support_next (inventoryBound runtime) depth) ∧ type_of% (complete_count (inventoryBound runtime) depth) ∧
    type_of% (table_current_next runtime depth) ∧ type_of% (model_next runtime depth) ∧ type_of% (error_next runtime depth) ∧
    type_of% (information_cost runtime depth) ∧
    ∀ value : Field parity, type_of% (generated_entry (inventoryBound runtime) depth value) ∧
      ∀ supported : value ∈ ((historyPMF (inventoryBound runtime)).map (dynamicRead runtime depth)).support,
        type_of% (posterior runtime depth value supported) ∧
        ∀ candidate : NextModel runtime, type_of% (support_restored runtime depth value supported candidate)) ∧
  (∀ index : Actors runtime, type_of% (sample_factorizes runtimeSeed (inventoryBound runtime) index) ∧
    type_of% (SourceConditionalInventory.material_retained (inventoryBound runtime) index)) ∧
  type_of% (SourceConditionalInventory.born_current runtime) ∧ type_of% material.factorizes

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨(fun depth => ⟨generated_read (inventoryBound runtime) depth, support_exact (inventoryBound runtime) depth,
    support_next (inventoryBound runtime) depth, complete_count (inventoryBound runtime) depth, table_current_next runtime depth,
    model_next runtime depth, error_next runtime depth, information_cost runtime depth,
    fun value => ⟨generated_entry (inventoryBound runtime) depth value, fun supported => ⟨posterior runtime depth value supported,
      fun candidate => support_restored runtime depth value supported candidate⟩⟩⟩),
    (fun index => ⟨sample_factorizes runtimeSeed (inventoryBound runtime) index,
      SourceConditionalInventory.material_retained (inventoryBound runtime) index⟩), SourceConditionalInventory.born_current runtime, material.factorizes⟩

end
end SourceConditionalFiniteStream
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
