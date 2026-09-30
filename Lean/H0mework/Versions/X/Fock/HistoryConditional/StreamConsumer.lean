import H0mework.Versions.X.Fock.HistoryConditional.StreamModel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalStream

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceConditionalModel (Actors NextModel dynamicRead)
open SourceObservationInvariantControls (parity)
open SourceConditionalInventory (count bornObservation)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
local instance : UniformSpace (Field parity) := fieldUniform parity
local instance : MeasurableSpace (Field parity) := fieldBorel parity
local instance : BorelSpace (Field parity) := ⟨rfl⟩
local instance : T2Space (Field parity) := field_t2 parity

theorem generated_posterior (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (dynamicRead runtime depth)).support) :
    SourcePosteriorReadback.readWeight runtime (generatedModel runtime depth value) =
      (fun actor => SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth) value supported actor) := by
  rw [generated_model, SourceConditionalModelUpdate.modelDecoder, dif_pos supported]
  exact SourcePosteriorReadback.posterior_recovered _ _ _ _

theorem generated_attains (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceConditionalVector.dynamicError runtime depth (generate depth (inventoryBound runtime)).2 =
      SourceConditionalVector.dynamicVariance runtime depth := by
  rw [generated_source, SourceConditionalInnovation.decoder_current]
  exact SourceConditionalVector.dynamic_attains _ _

theorem generated_error_next (runtime : LivingRuntimeState process) (depth : Nat) :
    ((inventoryBound runtime + 2 : Nat) : ℝ) * SourceConditionalVector.dynamicError runtime.tick.next depth
      (generate depth (inventoryBound runtime.tick.next)).2 =
      ((inventoryBound runtime + 1 : Nat) : ℝ) * SourceConditionalVector.dynamicVariance runtime depth +
        count (inventoryBound runtime) depth (bornObservation (inventoryBound runtime) depth) /
          (count (inventoryBound runtime) depth (bornObservation (inventoryBound runtime) depth) + 1) *
          ‖SourceCopyNativeModelStep.sourceValue runtime.tick.next.tick.next -
            (generate depth (inventoryBound runtime)).2 (bornObservation (inventoryBound runtime) depth)‖ ^ 2 := by
  rw [generated_attains, generated_source, SourceConditionalInnovation.decoder_current]
  exact SourceConditionalInnovation.minimum_current runtime depth

theorem generated_information (runtime : LivingRuntimeState process) (depth : Nat) :
    type_of% (SourceInformationReadback.model_decoder_cost runtime depth (generate depth (inventoryBound runtime)).2) :=
  SourceInformationReadback.model_decoder_cost runtime depth _

theorem generated_support_restored (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (dynamicRead runtime depth)).support)
    (model : NextModel runtime)
    (small : ‖SourceConditionalVector.realizeModel runtime model - (generate depth (inventoryBound runtime)).2 value‖ <
      SourcePosteriorStability.threshold runtime) :
    SourcePosteriorStability.restoredSupport runtime model =
      SourceUniformFibreVariance.fibre (inventoryBound runtime) (dynamicRead runtime depth) value := by
  rw [← generated_realization, generated_model, SourceConditionalModelUpdate.modelDecoder, dif_pos supported] at small
  exact SourcePosteriorStability.support_restored _ _ _ _ _ small

theorem generated_exact_support (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (dynamicRead runtime depth)).support) :
    SourcePosteriorStability.restoredSupport runtime (generatedModel runtime depth value) =
      SourceUniformFibreVariance.fibre (inventoryBound runtime) (dynamicRead runtime depth) value := by
  apply generated_support_restored runtime depth value supported
  rw [generated_realization, sub_self, norm_zero]
  exact SourcePosteriorStability.threshold_positive runtime

end
end SourceConditionalStream
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
