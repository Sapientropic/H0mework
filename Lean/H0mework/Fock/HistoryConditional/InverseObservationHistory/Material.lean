import H0mework.Fock.HistoryConditional.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationHistory

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  ∀ word : List (Fock.Letter (inventoryBound runtime)),
    type_of% (window_injective (inventoryBound runtime) word) ∧
    type_of% (kernel_zero (inventoryBound runtime) word) ∧
    (∀ value : SourceJointClockGraph.Carrier, type_of% (read_window (inventoryBound runtime) word value)) ∧
    (∀ model : SourceGeneratedActionObservationHistory.Model SourceJointClockGraph.action.toLinearMap
      (SourceGWordInverse.recover (inventoryBound runtime) word).toLinearMap,
      type_of% (projection_restore (inventoryBound runtime) word model) ∧
      type_of% (model_action_restore (inventoryBound runtime) word model)) ∧
    ∀ key : ZMod 2,
      type_of% (model_feedback runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      type_of% (model_effect runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key) ∧
      ∀ supported : key ∈ ((historyPMF (inventoryBound runtime)).map
        (fun actor : SourceConditionalModel.Actors runtime => (actor.val : ZMod 2))).support,
        type_of% (field_gain runtime (inventoryBound runtime) word key supported)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material :=
  ⟨material.factorizes, fun word => ⟨window_injective (inventoryBound runtime) word,
    kernel_zero (inventoryBound runtime) word, fun value => read_window (inventoryBound runtime) word value,
    fun model => ⟨projection_restore (inventoryBound runtime) word model, model_action_restore (inventoryBound runtime) word model⟩,
    fun key => ⟨model_feedback runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key,
      model_effect runtime (inventoryBound runtime) word (fun index : Nat => (index : ZMod 2)) key,
      fun supported => field_gain runtime (inventoryBound runtime) word key supported⟩⟩⟩

end
end SourceInverseObservationHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
