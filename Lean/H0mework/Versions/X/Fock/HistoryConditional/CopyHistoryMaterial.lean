import H0mework.Versions.X.Fock.HistoryConditional.CopyHistoryInformation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeHistory

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors)
open SourcePrimeHistoryRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧ type_of% (width_original sourceOwner (inventoryBound runtime)) ∧
  (∀ actor : Actors runtime,
    type_of% (native_row (inventoryBound runtime) actor) ∧
    type_of% (decoded_actor (inventoryBound runtime) actor) ∧
    type_of% (recovered_factorizes (inventoryBound runtime) actor) ∧
    type_of% (model_recovers runtime actor) ∧ type_of% (decoder_recovers runtime actor) ∧
    type_of% (source_step runtime actor) ∧ type_of% (decoded_effect runtime actor) ∧
    (∀ candidate : Actors runtime, type_of% (dynamic_model_fibre (inventoryBound runtime) actor candidate)) ∧
    (∀ task : Actors runtime → ℂ, type_of% (original_transfer (inventoryBound runtime) task actor)) ∧
    ∀ time : Fin (windowBound sourceOwner (inventoryBound runtime) + 1),
      type_of% (history_material (inventoryBound runtime) actor time)) ∧
  (∀ actor : Actors runtime.tick.next, type_of% (next_recovery runtime actor)) ∧
  type_of% (full_information_zero runtime) ∧ type_of% (snapshot_budget runtime) ∧
  ∀ enough : 2 ≤ inventoryBound runtime,
    type_of% (snapshot_gap_positive runtime enough) ∧ type_of% (snapshot_information_positive runtime enough)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  exact ⟨material.factorizes, width_original sourceOwner (inventoryBound runtime),
    (fun actor => ⟨native_row (inventoryBound runtime) actor, decoded_actor (inventoryBound runtime) actor,
      recovered_factorizes (inventoryBound runtime) actor, model_recovers runtime actor, decoder_recovers runtime actor,
      source_step runtime actor, decoded_effect runtime actor,
      dynamic_model_fibre (inventoryBound runtime) actor,
      fun task => original_transfer (inventoryBound runtime) task actor,
      history_material (inventoryBound runtime) actor⟩),
    next_recovery runtime, full_information_zero runtime, snapshot_budget runtime,
    fun enough => ⟨snapshot_gap_positive runtime enough, snapshot_information_positive runtime enough⟩⟩

end
end SourceCopyNativeHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
