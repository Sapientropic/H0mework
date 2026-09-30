import H0mework.Fock.SourceHistory.InverseObservationNative.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationNative

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  ∀ word : List (Fock.Letter (inventoryBound runtime)),
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    (∀ phase : Nat,
      type_of% (generated_source (fun index : Nat => (index : ZMod 2)) (word.map SourceCopyNativeWord.encode) (inventoryBound runtime) phase) ∧
      type_of% (generated_next (fun index : Nat => (index : ZMod 2)) (word.map SourceCopyNativeWord.encode) (inventoryBound runtime) phase)) ∧
    ∀ key : ZMod 2,
      type_of% (packet_source runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      type_of% (recovered runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      type_of% (model_feedback runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      type_of% (model_effect runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      ∀ samples : SourceCopyTimeModel.Packet (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1),
        type_of% (next_budget runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key samples) ∧
        ∀ supported : key ∈ ((historyPMF (inventoryBound runtime)).map
          (fun actor : SourceConditionalModel.Actors runtime => (actor.val : ZMod 2))).support,
          type_of% (field_budget runtime (inventoryBound runtime) word key supported samples)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material :=
  ⟨material.factorizes, fun word => ⟨fun phase =>
    ⟨generated_source (fun index : Nat => (index : ZMod 2)) (word.map SourceCopyNativeWord.encode) (inventoryBound runtime) phase,
      generated_next (fun index : Nat => (index : ZMod 2)) (word.map SourceCopyNativeWord.encode) (inventoryBound runtime) phase⟩,
    fun key => ⟨packet_source runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key,
      recovered runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key,
      model_feedback runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key,
      model_effect runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key,
      fun samples => ⟨next_budget runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key samples,
        fun supported => field_budget runtime (inventoryBound runtime) word key supported samples⟩⟩⟩⟩

end
end SourceInverseObservationNative
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
