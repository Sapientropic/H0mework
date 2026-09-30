import H0mework.Fock.HistoryConditional.Readout

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeWord

open SourceGeneratedAcquisitionContinuation SourceGeneratedActionWords
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  ∀ word : List (Fock.Letter (inventoryBound runtime)), ∀ actor : Actors runtime,
    type_of% (recovered_word (inventoryBound runtime) (inventoryBound runtime) word actor) ∧
    type_of% (recovered_word_model (inventoryBound runtime) (inventoryBound runtime) word actor) ∧
    (∀ index : SourceOwnedObservationHistory.FamilyModel.Fock.Index (inventoryBound runtime),
      type_of% (original_reader (inventoryBound runtime) (inventoryBound runtime) word actor index)) ∧
    ∀ other : List (Fock.Letter (inventoryBound runtime)),
      type_of% (SourceCopyWordAffine.action_kernel (word.map encode) (other.map encode))

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material :=
  ⟨material.factorizes, fun word actor =>
    ⟨recovered_word (inventoryBound runtime) (inventoryBound runtime) word actor,
      recovered_word_model (inventoryBound runtime) (inventoryBound runtime) word actor,
      original_reader (inventoryBound runtime) (inventoryBound runtime) word actor,
      fun other => SourceCopyWordAffine.action_kernel (word.map encode) (other.map encode)⟩⟩

end
end SourceCopyNativeWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
