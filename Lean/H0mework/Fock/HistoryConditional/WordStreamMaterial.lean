import H0mework.Fock.HistoryConditional.WordStreamConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalWordStream

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceConditionalModel (Actors NextModel dynamicRead)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  (∀ depth : Nat, type_of% (generated_read (inventoryBound runtime) depth) ∧ type_of% (support_exact (inventoryBound runtime) depth) ∧
    type_of% (table_current_next runtime depth) ∧ type_of% (error_next runtime depth) ∧ type_of% (information_cost runtime depth) ∧
    ∀ value : Field parity, type_of% (generated_entry (inventoryBound runtime) depth value) ∧
      ∀ supported : value ∈ ((historyPMF (inventoryBound runtime)).map (SourceConditionalInventory.observation (inventoryBound runtime) depth)).support,
        type_of% (word_conditional (inventoryBound runtime) depth value supported) ∧
        (∀ actor : Actors runtime, type_of% (word_coefficient (inventoryBound runtime) depth value supported actor)) ∧
        type_of% (posterior runtime depth value (by simpa only [SourceConditionalInventory.observation_original] using supported)) ∧
        ∀ candidate : NextModel runtime,
          type_of% (support_restored runtime depth value (by simpa only [SourceConditionalInventory.observation_original] using supported) candidate)) ∧
  (∀ index : Actors runtime, type_of% (source_read (inventoryBound runtime) index) ∧ type_of% (source_single (inventoryBound runtime) index) ∧
    type_of% (sample_factorizes runtimeSeed (inventoryBound runtime) index)) ∧
  type_of% material.factorizes

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨(fun depth => ⟨generated_read (inventoryBound runtime) depth, support_exact (inventoryBound runtime) depth,
    table_current_next runtime depth, error_next runtime depth, information_cost runtime depth,
    fun value => ⟨generated_entry (inventoryBound runtime) depth value, fun supported => ⟨word_conditional (inventoryBound runtime) depth value supported,
      (fun actor => word_coefficient (inventoryBound runtime) depth value supported actor),
      posterior runtime depth value (by simpa only [SourceConditionalInventory.observation_original] using supported),
      fun candidate => support_restored runtime depth value (by simpa only [SourceConditionalInventory.observation_original] using supported) candidate⟩⟩⟩),
    (fun index => ⟨source_read (inventoryBound runtime) index, source_single (inventoryBound runtime) index,
      sample_factorizes runtimeSeed (inventoryBound runtime) index⟩), material.factorizes⟩

end
end SourceConditionalWordStream
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
