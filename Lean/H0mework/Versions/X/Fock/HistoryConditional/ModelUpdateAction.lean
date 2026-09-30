import H0mework.Versions.X.Fock.HistoryConditional.ModelUpdateSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalModelUpdate

open SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceConditionalModel (NextModel dynamicRead)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

def updateModel (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity) : NextModel runtime.tick.next :=
  let previous := SourceActualImageStep.retainModel runtime (modelDecoder runtime (dynamicRead runtime depth) value)
  if SourceConditionalInventory.bornObservation (inventoryBound runtime) depth = value then
    previous + ((SourceConditionalInventory.count (inventoryBound runtime) depth value + 1 : ℝ) : ℂ)⁻¹ •
      ((SourceActualImageStep.birth runtime).val - previous)
  else previous

theorem birth_realization (runtime : LivingRuntimeState process) :
    SourceConditionalVector.realizeModel runtime.tick.next (SourceActualImageStep.birth runtime).val =
      SourceConditionalInventory.born (inventoryBound runtime) := by
  simpa only [SourceActualImageStep.read] using SourceActualImageStep.birth_read runtime

theorem update_realization (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity) :
    SourceConditionalVector.realizeModel runtime.tick.next (updateModel runtime depth value) =
      SourceConditionalInnovation.updateDecoder (inventoryBound runtime) depth value := by
  by_cases atBirth : SourceConditionalInventory.bornObservation (inventoryBound runtime) depth = value
  · simp only [updateModel, SourceConditionalInnovation.updateDecoder, if_pos atBirth, map_add, map_smul, map_sub,
      retained_decoder, birth_realization, SourceConditionalInnovation.decoder_current]
  · simp only [updateModel, SourceConditionalInnovation.updateDecoder, if_neg atBirth,
      retained_decoder, SourceConditionalInnovation.decoder_current]

theorem update_is_next (runtime : LivingRuntimeState process) (depth : Nat) :
    updateModel runtime depth = modelDecoder runtime.tick.next (dynamicRead runtime.tick.next depth) := by
  funext value
  apply SourceActualImageStep.realize_injective runtime.tick.next
  rw [update_realization, model_decoder_realization, SourceConditionalInnovation.update_current]

theorem decoded_update (runtime : LivingRuntimeState process) (depth : Nat) :
    (fun value => SourceConditionalVector.realizeModel runtime.tick.next (updateModel runtime depth value)) =
      SourceConditionalInnovation.updateDecoder (inventoryBound runtime) depth :=
  funext (update_realization runtime depth)

end
end SourceConditionalModelUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
