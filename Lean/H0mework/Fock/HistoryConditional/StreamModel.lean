import H0mework.Fock.HistoryConditional.StreamSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalStream

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceGeneratedActionObservationHistory (projection)
open SourceConditionalModel (NextModel dynamicRead)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem project_realization (runtime : LivingRuntimeState process) (model : NextModel runtime) :
    projection SourceJointClockGraph.action.toLinearMap (SourceCopyCurrentCoordinates.jointObserver runtime.tick.next)
      (SourceConditionalVector.realizeModel runtime model) = model := by
  apply (SourceCopyCurrentCoordinates.jointModelEquiv runtime.tick.next).injective
  rw [SourceCopyCurrentCoordinates.joint_model_source]
  change SourceCopyCurrentCoordinates.sourceRead runtime.tick.next (SourceCopyCurrentCoordinates.maximumIndex runtime.tick.next) 0
    (SourceCopyCurrentCoordinates.realize runtime.tick.next (SourceCopyCurrentCoordinates.maximumIndex runtime.tick.next) 0
      (SourceCopyCurrentCoordinates.jointModelEquiv runtime.tick.next model)) = _
  exact SourceCopyCurrentCoordinates.realize_source _ _ _ _

def generatedModel (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity) : NextModel runtime :=
  projection SourceJointClockGraph.action.toLinearMap (SourceCopyCurrentCoordinates.jointObserver runtime.tick.next)
    ((generate depth (inventoryBound runtime)).2 value)

theorem generated_model (runtime : LivingRuntimeState process) (depth : Nat) :
    generatedModel runtime depth = SourceConditionalModelUpdate.modelDecoder runtime (dynamicRead runtime depth) := by
  funext value
  rw [generatedModel, generated_source, SourceConditionalInnovation.decoder_current]
  dsimp only [Prod.snd]
  rw [← SourceConditionalModelUpdate.model_decoder_realization runtime (dynamicRead runtime depth) value]
  exact project_realization runtime _

theorem generated_realization (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity) :
    SourceConditionalVector.realizeModel runtime (generatedModel runtime depth value) =
      (generate depth (inventoryBound runtime)).2 value := by
  rw [generated_model, SourceConditionalModelUpdate.model_decoder_realization,
    generated_source, SourceConditionalInnovation.decoder_current]

theorem generated_model_next (runtime : LivingRuntimeState process) (depth : Nat) :
    generatedModel runtime.tick.next depth = SourceConditionalModelUpdate.updateModel runtime depth := by
  rw [generated_model, SourceConditionalModelUpdate.update_is_next]

theorem generated_current_next (runtime : LivingRuntimeState process) (depth : Nat) :
    generate depth (inventoryBound runtime.tick.next) = advance (inventoryBound runtime) depth (generate depth (inventoryBound runtime)) := by
  rw [SourceActualImageStep.next_bound, generated_next]

end
end SourceConditionalStream
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
