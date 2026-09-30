import H0mework.Fock.HistoryConditional.NativeInverseG

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeProgramInverse

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability SourceGeneratedActionWords
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  ∀ word : List (Fock.Letter (inventoryBound runtime)),
    (∀ actor : Actors runtime,
      type_of% (material_original (inventoryBound runtime) (inventoryBound runtime) word actor) ∧
      type_of% (material_next runtime (inventoryBound runtime) word actor) ∧
      type_of% (sample_factorizes runtimeSeed (inventoryBound runtime) actor)) ∧
    ∀ target : Nat,
      type_of% (compiled_none (word.map SourceCopyNativeWord.encode) target) ∧
      type_of% (actor_none_iff (inventoryBound runtime) (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
        (SourceCompiledWordOperator.slope_positive _) target) ∧
      type_of% (raw_recovery (inventoryBound runtime) word target) ∧
      type_of% (raw_residual (inventoryBound runtime) word target) ∧
      type_of% (g_recovery (inventoryBound runtime) word target) ∧
      type_of% (g_residual (inventoryBound runtime) word target)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material :=
  ⟨material.factorizes, fun word => ⟨(fun actor =>
    ⟨material_original (inventoryBound runtime) (inventoryBound runtime) word actor,
      material_next runtime (inventoryBound runtime) word actor, sample_factorizes runtimeSeed (inventoryBound runtime) actor⟩),
    fun target => ⟨compiled_none (word.map SourceCopyNativeWord.encode) target,
      actor_none_iff (inventoryBound runtime) (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
        (SourceCompiledWordOperator.slope_positive _) target,
      raw_recovery (inventoryBound runtime) word target, raw_residual (inventoryBound runtime) word target,
      g_recovery (inventoryBound runtime) word target, g_residual (inventoryBound runtime) word target⟩⟩⟩

end
end SourceNativeProgramInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
