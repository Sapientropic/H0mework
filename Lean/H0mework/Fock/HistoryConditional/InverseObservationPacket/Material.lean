import H0mework.Fock.HistoryConditional.Positive

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationPacket

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  ∀ word : List (Fock.Letter (inventoryBound runtime)),
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    (∀ phase : Fin ((copyIndex program.1).val + 1), type_of% (native_sample (inventoryBound runtime) word runtime phase)) ∧
    (∀ value : SourceJointClockGraph.Carrier, type_of% (recovered (inventoryBound runtime) word value) ∧
      type_of% (next_packet (inventoryBound runtime) word value) ∧
      ∀ samples : SourceCopyTimeModel.Packet (program.1 - 1) (copyIndex program.1),
        type_of% (error_budget (inventoryBound runtime) word value samples) ∧
        type_of% (next_error_budget (inventoryBound runtime) word value samples)) ∧
    type_of% (clock_sample_energy (inventoryBound runtime) word) ∧
    (∀ nonunit : 1 < program.1, type_of% (clock_amplification (inventoryBound runtime) word nonunit)) ∧
    ∀ key : ZMod 2,
      type_of% (model_feedback runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      type_of% (model_effect runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      ∀ supported : key ∈ ((historyPMF (inventoryBound runtime)).map
        (fun actor : SourceConditionalModel.Actors runtime => (actor.val : ZMod 2))).support,
      ∀ samples : SourceCopyTimeModel.Packet (program.1 - 1) (copyIndex program.1),
        type_of% (field_budget runtime (inventoryBound runtime) word key supported samples)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material :=
  ⟨material.factorizes, fun word => ⟨fun phase => native_sample (inventoryBound runtime) word runtime phase,
    fun value => ⟨recovered (inventoryBound runtime) word value, next_packet (inventoryBound runtime) word value,
      fun samples => ⟨error_budget (inventoryBound runtime) word value samples, next_error_budget (inventoryBound runtime) word value samples⟩⟩,
    clock_sample_energy (inventoryBound runtime) word, fun nonunit => clock_amplification (inventoryBound runtime) word nonunit,
    fun key => ⟨model_feedback runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key,
      model_effect runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key,
      fun supported samples => field_budget runtime (inventoryBound runtime) word key supported samples⟩⟩⟩

end
end SourceInverseObservationPacket
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
