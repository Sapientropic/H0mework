import H0mework.Fock.HistoryConditional.Conditional

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGWordInverse

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  ∀ word : List (Fock.Letter (inventoryBound runtime)),
    (type_of% (word_recover_eq (inventoryBound runtime) word) ∧ ∀ value : SourceJointClockGraph.Carrier,
      type_of% (recover_effect (inventoryBound runtime) word value) ∧
      type_of% (reconstruction (inventoryBound runtime) word value)) ∧
    (∀ source : SourceOperationNative.Carrier process,
      type_of% (recovery_native_moments (inventoryBound runtime) word source) ∧
      type_of% (correction_effect (inventoryBound runtime) word source) ∧
      type_of% (residual_native_moments (inventoryBound runtime) word source)) ∧
    ∀ key : ZMod 2,
      ∀ supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => (actor.val : ZMod 2))).support,
        type_of% (decoder_moments runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key supported) ∧
        type_of% (decoder_residual runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key supported)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material :=
  ⟨material.factorizes, fun word => ⟨⟨word_recover_eq (inventoryBound runtime) word,
    fun value => ⟨recover_effect (inventoryBound runtime) word value, reconstruction (inventoryBound runtime) word value⟩⟩,
    (fun source => ⟨recovery_native_moments (inventoryBound runtime) word source,
      correction_effect (inventoryBound runtime) word source, residual_native_moments (inventoryBound runtime) word source⟩),
    fun key supported => ⟨decoder_moments runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key supported,
      decoder_residual runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key supported⟩⟩⟩

end
end SourceGWordInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
