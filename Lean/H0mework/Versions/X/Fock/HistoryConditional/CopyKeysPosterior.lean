import H0mework.Versions.X.Fock.HistoryConditional.CopyKeysJoint

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeKeys

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

theorem native_count (runtime : LivingRuntimeState process) (depth : Nat) (index : SourceCopyObservation.Index depth)
    (actor : Actors runtime) :
    (SourceConditionalNativeObservers.generate (jointKey index.val) (inventoryBound runtime) (jointKey index.val actor.val)).1 =
      (SourceUniformFibreVariance.fibre (inventoryBound runtime) (SourceCopyObservation.joint depth (inventoryBound runtime) index)
        (SourceCopyObservation.joint depth (inventoryBound runtime) index actor)).card := by
  rw [SourceConditionalNativePosterior.count_fibre]
  congr 1
  apply Finset.ext
  intro candidate
  simp only [SourceUniformFibreVariance.fibre_mem]
  exact original_fibre depth (inventoryBound runtime) index candidate actor

theorem posterior (runtime : LivingRuntimeState process) (depth : Nat) (index : SourceCopyObservation.Index depth)
    (actor candidate : Actors runtime) :
    ((SourceConditionalNativeObservers.generate (jointKey index.val) (inventoryBound runtime) (jointKey index.val actor.val)).2 candidate : ℝ) =
      (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime))
        (SourceCopyObservation.joint depth (inventoryBound runtime) index)
        (SourceCopyObservation.joint depth (inventoryBound runtime) index actor)
        (SourceWeightedRecovery.observed_supported _ _ actor (SourceConditionalModel.positive runtime actor)) candidate).toReal := by
  let query : Actors runtime → Finset Nat.Primes × Finset Nat.Primes := fun point => jointKey index.val point.val
  have supported := SourceWeightedRecovery.observed_supported (historyPMF (inventoryBound runtime)) query actor
    (SourceConditionalModel.positive runtime actor)
  have same := SourceConditionalHistory.conditional_eq_of_fibre (historyPMF (inventoryBound runtime)) query
    (SourceCopyObservation.joint depth (inventoryBound runtime) index) (query actor)
    (SourceCopyObservation.joint depth (inventoryBound runtime) index actor) supported
    (SourceWeightedRecovery.observed_supported _ _ actor (SourceConditionalModel.positive runtime actor))
    (fun point => original_fibre depth (inventoryBound runtime) index point actor)
  have paid := SourceConditionalNativePosterior.posterior (jointKey index.val) (inventoryBound runtime) (query actor) supported candidate
  rw [same] at paid
  exact paid

theorem model_original (runtime : LivingRuntimeState process) (depth : Nat) (index : SourceCopyObservation.Index depth)
    (actor : Actors runtime) :
    SourceConditionalNativePosterior.model runtime (jointKey index.val) (jointKey index.val actor.val) =
      SourceConditionalModelUpdate.modelDecoder runtime (SourceCopyObservation.joint depth (inventoryBound runtime) index)
        (SourceCopyObservation.joint depth (inventoryBound runtime) index actor) := by
  have supported := SourceWeightedRecovery.observed_supported (historyPMF (inventoryBound runtime))
    (SourceCopyObservation.joint depth (inventoryBound runtime) index) actor (SourceConditionalModel.positive runtime actor)
  rw [SourceConditionalModelUpdate.modelDecoder, dif_pos supported, SourceConditionalVector.estimate,
    SourceConditionalNativePosterior.model]
  apply Finset.sum_congr rfl
  intro candidate _
  have weight := posterior runtime depth index actor candidate
  have casted : ((SourceConditionalNativeObservers.generate (jointKey index.val) (inventoryBound runtime)
      (jointKey index.val actor.val)).2 candidate : ℂ) =
      ((SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime))
        (SourceCopyObservation.joint depth (inventoryBound runtime) index)
        (SourceCopyObservation.joint depth (inventoryBound runtime) index actor) supported candidate).toReal : ℂ) := by
    exact_mod_cast weight
  rw [casted]

theorem decoder_original (runtime : LivingRuntimeState process) (depth : Nat) (index : SourceCopyObservation.Index depth)
    (actor : Actors runtime) :
    SourceConditionalNativePosterior.decoder runtime (jointKey index.val) (jointKey index.val actor.val) =
      SourceConditionalVector.vectorDecoder runtime (SourceCopyObservation.joint depth (inventoryBound runtime) index)
        (SourceCopyObservation.joint depth (inventoryBound runtime) index actor) := by
  rw [SourceConditionalNativePosterior.decoder, model_original, SourceConditionalModelUpdate.model_decoder_realization]

end
end SourceCopyNativeKeys
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
