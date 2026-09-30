import H0mework.Versions.X.Fock.ReceivedStep.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalStep

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyProgram (Index)
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  (∀ (index : Index (inventoryBound runtime)) (count : Nat) (selected : Bool)
      (data : (Fin ((inventoryBound runtime + 1) * (index.val + 1)) → ℚ) × ℚ × ℚ),
    type_of% (next_value_source runtime index count selected data)) ∧
  ∀ (index : Index (inventoryBound runtime)) (nonunit : index.val ≠ 0),
    (∀ (steps : Nat) (data : (Fin ((inventoryBound runtime + steps + 1) * (index.val + 1)) → ℚ) × ℚ × ℚ),
      type_of% (complete_roundtrip runtime index nonunit steps data)) ∧
    (∀ received : ZMod 2 → SourceRationalWindowReadout.Samples (inventoryBound runtime) (index.val + 1),
      (∀ added key : ZMod 2, type_of% (realized_updated_model runtime index nonunit received added key)) ∧
      ∀ key : ZMod 2,
        type_of% (residual_equation runtime index nonunit received (fun n : Nat => (n : ZMod 2)) key) ∧
        type_of% (model_writeback runtime index nonunit received (fun n : Nat => (n : ZMod 2)) key) ∧
        ∀ supported : key ∈ ((historyPMF (inventoryBound runtime.tick.next)).map (fun actor : Actors runtime.tick.next => (actor.val : ZMod 2))).support,
          type_of% (model_error runtime index nonunit received (fun n : Nat => (n : ZMod 2)) key supported)) ∧
    (∀ key : ZMod 2, type_of% (updated_model_source runtime index nonunit (fun n : Nat => (n : ZMod 2)) key)) ∧
    type_of% (complete_feedback_strict runtime index nonunit (fun n : Nat => (n : ZMod 2)))

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨material.factorizes,
    fun index count selected data => next_value_source runtime index count selected data,
    fun index nonunit =>
    ⟨fun steps data => complete_roundtrip runtime index nonunit steps data,
      fun received => ⟨fun added key => realized_updated_model runtime index nonunit received added key,
        fun key => ⟨residual_equation runtime index nonunit received (fun n : Nat => (n : ZMod 2)) key,
          model_writeback runtime index nonunit received (fun n : Nat => (n : ZMod 2)) key,
          fun supported => model_error runtime index nonunit received (fun n : Nat => (n : ZMod 2)) key supported⟩⟩,
      fun key => updated_model_source runtime index nonunit (fun n : Nat => (n : ZMod 2)) key,
      complete_feedback_strict runtime index nonunit (fun n : Nat => (n : ZMod 2))⟩⟩

end
end SourceReceivedConditionalStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
