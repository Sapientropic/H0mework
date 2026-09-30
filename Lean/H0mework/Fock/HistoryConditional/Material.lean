import H0mework.Fock.HistoryConditional.CopyKeysConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeKeys

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
local instance : MeasurableSpace (Finset Nat.Primes) := ⊤
local instance : MeasurableSingletonClass (Finset Nat.Primes) := ⟨fun _ => trivial⟩

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧ type_of% (key_source_support (inventoryBound runtime)) ∧
  ∀ index : SourceCopyObservation.Index (inventoryBound runtime),
    type_of% (SourceConditionalNativeObservers.generated_next (jointKey index.val) (inventoryBound runtime)) ∧
    (∀ actor : Actors runtime,
      type_of% (native_count runtime (inventoryBound runtime) index actor) ∧
      type_of% (generated_original (inventoryBound runtime) (inventoryBound runtime) index actor) ∧
      (∀ candidate : Actors runtime, type_of% (posterior runtime (inventoryBound runtime) index actor candidate)) ∧
      type_of% (model_original runtime (inventoryBound runtime) index actor) ∧
      type_of% (decoder_original runtime (inventoryBound runtime) index actor)) ∧
    (∀ actor : Actors runtime.tick.next, type_of% (updated_model runtime (inventoryBound runtime) index actor)) ∧
    type_of% (information_original runtime (inventoryBound runtime) index) ∧
    type_of% (joint_error_next runtime index) ∧
    type_of% (SourceConditionalNativeBirth.next_budget runtime (jointKey index.val) Prod.fst)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  refine ⟨material.factorizes, key_source_support (inventoryBound runtime), ?_⟩
  intro index
  exact ⟨SourceConditionalNativeObservers.generated_next (jointKey index.val) (inventoryBound runtime),
    (fun actor => ⟨native_count runtime (inventoryBound runtime) index actor,
      generated_original (inventoryBound runtime) (inventoryBound runtime) index actor,
      posterior runtime (inventoryBound runtime) index actor,
      model_original runtime (inventoryBound runtime) index actor,
      decoder_original runtime (inventoryBound runtime) index actor⟩),
    updated_model runtime (inventoryBound runtime) index,
    information_original runtime (inventoryBound runtime) index,
    joint_error_next runtime index,
    SourceConditionalNativeBirth.next_budget runtime (jointKey index.val) Prod.fst⟩

end
end SourceCopyNativeKeys
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
