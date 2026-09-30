import H0mework.Fock.HistoryConditional.NativeBirthConsumer
import H0mework.Fock.HistoryCopy.InformationProjection

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalCopyBirth

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

theorem decoder_original (runtime : LivingRuntimeState process) (depth : Nat)
    (index : SourceCopyObservation.Index depth) :
    SourceConditionalNativePosterior.decoder runtime (SourceCopyInventory.read (NativeCopy.Fock.material depth index)) =
      SourceConditionalVector.vectorDecoder runtime (SourceCopyObservation.joint depth (inventoryBound runtime) index) := by
  rw [SourceConditionalNativePosterior.decoder_original]
  congr 1
  funext actor
  exact (SourceCopyInventory.joint_source depth (inventoryBound runtime) index actor).symm

theorem model_original (runtime : LivingRuntimeState process) (depth : Nat)
    (index : SourceCopyObservation.Index depth) :
    SourceConditionalNativePosterior.model runtime (SourceCopyInventory.read (NativeCopy.Fock.material depth index)) =
      SourceConditionalModelUpdate.modelDecoder runtime (SourceCopyObservation.joint depth (inventoryBound runtime) index) := by
  funext value
  apply SourceActualImageStep.realize_injective runtime
  change SourceConditionalNativePosterior.decoder runtime _ value = _
  rw [decoder_original, SourceConditionalModelUpdate.model_decoder_realization]

theorem updated_model (runtime : LivingRuntimeState process)
    (index : SourceCopyObservation.Index (inventoryBound runtime)) :
    SourceConditionalNativeBirth.update runtime (SourceCopyInventory.read (NativeCopy.Fock.material (inventoryBound runtime) index)) =
      SourceConditionalModelUpdate.modelDecoder runtime.tick.next
        (SourceCopyObservation.joint (inventoryBound runtime) (inventoryBound runtime.tick.next) index) := by
  rw [SourceConditionalNativeBirth.update_is_next, model_original]

theorem original_joint_posterior (runtime : LivingRuntimeState process)
    (index : SourceCopyObservation.Index (inventoryBound runtime)) (value : ParentCarrier × ParentCarrier)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map
      (SourceCopyObservation.joint (inventoryBound runtime) (inventoryBound runtime) index)).support) :
    SourcePosteriorReadback.readWeight runtime
      (SourceConditionalNativePosterior.model runtime (SourceCopyInventory.read (NativeCopy.Fock.material (inventoryBound runtime) index)) value) =
      (fun actor => SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime))
        (SourceCopyObservation.joint (inventoryBound runtime) (inventoryBound runtime) index) value supported actor) := by
  rw [model_original, SourceConditionalModelUpdate.modelDecoder, dif_pos supported]
  exact SourcePosteriorReadback.posterior_recovered _ _ _ _

end
end SourceConditionalCopyBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
