import H0mework.Fock.HistoryConditional.FiniteStreamSupport

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalFiniteStream

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceGeneratedActionObservationHistory (projection)
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

def model (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity) : NextModel runtime :=
  projection SourceJointClockGraph.action.toLinearMap (SourceCopyCurrentCoordinates.jointObserver runtime.tick.next)
    (generate depth (inventoryBound runtime) value).2

theorem model_original (runtime : LivingRuntimeState process) (depth : Nat) :
    model runtime depth = SourceConditionalStream.generatedModel runtime depth := by
  funext value
  exact congrArg (projection SourceJointClockGraph.action.toLinearMap (SourceCopyCurrentCoordinates.jointObserver runtime.tick.next))
    (congrFun (congrArg Prod.snd (generated_read (inventoryBound runtime) depth)) value)

theorem model_next (runtime : LivingRuntimeState process) (depth : Nat) :
    model runtime.tick.next depth = SourceConditionalModelUpdate.updateModel runtime depth := by
  rw [model_original, SourceConditionalStream.generated_model_next]

theorem posterior (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (dynamicRead runtime depth)).support) :
    SourcePosteriorReadback.readWeight runtime (model runtime depth value) =
      (fun actor => SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth) value supported actor) := by
  rw [model_original]
  exact SourceConditionalStream.generated_posterior _ _ _ _

theorem error_next (runtime : LivingRuntimeState process) (depth : Nat) :
    ((inventoryBound runtime + 2 : Nat) : ℝ) * SourceConditionalVector.dynamicError runtime.tick.next depth
      (read (generate depth (inventoryBound runtime.tick.next))).2 =
      ((inventoryBound runtime + 1 : Nat) : ℝ) * SourceConditionalVector.dynamicVariance runtime depth +
        count (inventoryBound runtime) depth (bornObservation (inventoryBound runtime) depth) /
          (count (inventoryBound runtime) depth (bornObservation (inventoryBound runtime) depth) + 1) *
          ‖SourceCopyNativeModelStep.sourceValue runtime.tick.next.tick.next -
            (read (generate depth (inventoryBound runtime))).2 (bornObservation (inventoryBound runtime) depth)‖ ^ 2 := by
  rw [generated_read, generated_read]
  exact SourceConditionalStream.generated_error_next runtime depth

theorem information_cost (runtime : LivingRuntimeState process) (depth : Nat) :
    type_of% (SourceInformationReadback.model_decoder_cost runtime depth (read (generate depth (inventoryBound runtime))).2) :=
  SourceInformationReadback.model_decoder_cost runtime depth _

theorem support_restored (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (dynamicRead runtime depth)).support)
    (candidate : NextModel runtime)
    (small : ‖SourceConditionalVector.realizeModel runtime candidate - (read (generate depth (inventoryBound runtime))).2 value‖ <
      SourcePosteriorStability.threshold runtime) :
    SourcePosteriorStability.restoredSupport runtime candidate =
      SourceUniformFibreVariance.fibre (inventoryBound runtime) (dynamicRead runtime depth) value := by
  rw [generated_read] at small
  exact SourceConditionalStream.generated_support_restored runtime depth value supported candidate small

end
end SourceConditionalFiniteStream
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
