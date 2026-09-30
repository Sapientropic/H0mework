import H0mework.Fock.HistoryConditional.OperatorRecurrence.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperatorObservationRecurrence

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  ∀ word : List (Fock.Letter (inventoryBound runtime)),
    type_of% (source_law (inventoryBound runtime) word) ∧
    type_of% (least_window (inventoryBound runtime) word) ∧
    (∀ value : SourceJointClockGraph.Carrier, type_of% (next_source (inventoryBound runtime) word value)) ∧
    type_of% (native_next runtime (inventoryBound runtime) word) ∧
    (∀ length : Nat, ∀ shorter : length < SourceInverseObservationHistory.horizon (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)),
      type_of% (hidden_balance (inventoryBound runtime) word length shorter) ∧
      type_of% (hidden_next_visible (inventoryBound runtime) word length shorter) ∧
      type_of% (no_short_update (inventoryBound runtime) word length shorter)) ∧
    ∀ key : ZMod 2,
      type_of% (model_effect runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      ∀ supported : key ∈ ((historyPMF (inventoryBound runtime)).map
        (fun actor : SourceConditionalModel.Actors runtime => (actor.val : ZMod 2))).support,
        type_of% (next_error runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key supported)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨material.factorizes, fun word => ⟨source_law (inventoryBound runtime) word, least_window (inventoryBound runtime) word,
    fun value => next_source (inventoryBound runtime) word value, native_next runtime (inventoryBound runtime) word,
    fun length shorter => ⟨hidden_balance (inventoryBound runtime) word length shorter,
      hidden_next_visible (inventoryBound runtime) word length shorter, no_short_update (inventoryBound runtime) word length shorter⟩,
    fun key => ⟨model_effect runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key,
      fun supported => next_error runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key supported⟩⟩⟩

end
end SourceOperatorObservationRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
