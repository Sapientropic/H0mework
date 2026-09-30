import H0mework.Fock.InverseDistribution.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionBirth

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  ∀ word : List (Fock.Letter (inventoryBound runtime)),
    (type_of% (generated_next (fun index : Nat => (index : ZMod 2)) (inventoryBound runtime) (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))) ∧
      type_of% (SourceInverseDistributionStream.generated_source (fun index : Nat => (index : ZMod 2)) (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) (inventoryBound runtime + 1)) ∧
      type_of% (SourceInverseDistributionStream.source_generated (fun index : Nat => (index : ZMod 2)) (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) (inventoryBound runtime + 1)) ∧
      (type_of% (SourceInverseDistributionAction.generated_source (fun index : Nat => (index : ZMod 2)) (word.map SourceCopyNativeWord.encode) (inventoryBound runtime + 1)) ∧
        type_of% (SourceInverseDistributionAction.source_generated (fun index : Nat => (index : ZMod 2)) (word.map SourceCopyNativeWord.encode) (inventoryBound runtime + 1)) ∧
        ∀ letter : Fock.Letter (inventoryBound runtime), type_of% (SourceInverseDistributionAction.refine_generated (fun index : Nat => (index : ZMod 2)) (SourceCopyNativeWord.encode letter) (word.map SourceCopyNativeWord.encode) (inventoryBound runtime + 1)))) ∧
    (∀ key : ZMod 2,
      type_of% (recovered_advance (fun index : Nat => (index : ZMod 2)) (inventoryBound runtime) (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
        (fun key => (SourceConditionalNativeObservers.generate (fun index : Nat => (index : ZMod 2)) (inventoryBound runtime) key).1)
        (fun key => SourceNativeInverseDistribution.split (inventoryBound runtime) (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
          (SourceConditionalNativeObservers.generate (fun index : Nat => (index : ZMod 2)) (inventoryBound runtime) key).2) key) ∧
      type_of% (residual_advance (fun index : Nat => (index : ZMod 2)) (inventoryBound runtime) (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
        (fun key => (SourceConditionalNativeObservers.generate (fun index : Nat => (index : ZMod 2)) (inventoryBound runtime) key).1)
        (fun key => SourceNativeInverseDistribution.split (inventoryBound runtime) (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
          (SourceConditionalNativeObservers.generate (fun index : Nat => (index : ZMod 2)) (inventoryBound runtime) key).2) key) ∧
      type_of% (decoder_next runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      type_of% (next_moments runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      type_of% (next_residual runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      type_of% (model_update runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      type_of% (model_feedback runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key)) ∧
    type_of% (stale_strict runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)))

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material :=
  ⟨material.factorizes, fun word => ⟨⟨generated_next (fun index : Nat => (index : ZMod 2)) (inventoryBound runtime) (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)),
    SourceInverseDistributionStream.generated_source (fun index : Nat => (index : ZMod 2)) (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) (inventoryBound runtime + 1),
    SourceInverseDistributionStream.source_generated (fun index : Nat => (index : ZMod 2)) (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) (inventoryBound runtime + 1),
    ⟨SourceInverseDistributionAction.generated_source (fun index : Nat => (index : ZMod 2)) (word.map SourceCopyNativeWord.encode) (inventoryBound runtime + 1),
      SourceInverseDistributionAction.source_generated (fun index : Nat => (index : ZMod 2)) (word.map SourceCopyNativeWord.encode) (inventoryBound runtime + 1),
      fun letter => SourceInverseDistributionAction.refine_generated (fun index : Nat => (index : ZMod 2)) (SourceCopyNativeWord.encode letter) (word.map SourceCopyNativeWord.encode) (inventoryBound runtime + 1)⟩⟩,
    (fun key => ⟨recovered_advance (fun index : Nat => (index : ZMod 2)) (inventoryBound runtime) (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
        (fun key => (SourceConditionalNativeObservers.generate (fun index : Nat => (index : ZMod 2)) (inventoryBound runtime) key).1)
        (fun key => SourceNativeInverseDistribution.split (inventoryBound runtime) (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
          (SourceConditionalNativeObservers.generate (fun index : Nat => (index : ZMod 2)) (inventoryBound runtime) key).2) key,
      residual_advance (fun index : Nat => (index : ZMod 2)) (inventoryBound runtime) (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
        (fun key => (SourceConditionalNativeObservers.generate (fun index : Nat => (index : ZMod 2)) (inventoryBound runtime) key).1)
        (fun key => SourceNativeInverseDistribution.split (inventoryBound runtime) (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
          (SourceConditionalNativeObservers.generate (fun index : Nat => (index : ZMod 2)) (inventoryBound runtime) key).2) key,
      decoder_next runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key,
      next_moments runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key,
      next_residual runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key,
      model_update runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key,
      model_feedback runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key⟩),
    stale_strict runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2))⟩⟩

end
end SourceInverseDistributionBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
