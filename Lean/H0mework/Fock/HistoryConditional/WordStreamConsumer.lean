import H0mework.Fock.HistoryConditional.WordStreamRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalWordStream

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

def decoder (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity) : SourceJointClockGraph.Carrier :=
  SourceJointClockGraph.read (generate depth (inventoryBound runtime) value).2

def model (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity) : NextModel runtime :=
  projection SourceJointClockGraph.action.toLinearMap (SourceCopyCurrentCoordinates.jointObserver runtime.tick.next)
    (decoder runtime depth value)

theorem decoder_original (runtime : LivingRuntimeState process) (depth : Nat) :
    decoder runtime depth = (SourceConditionalFiniteStream.read (SourceConditionalFiniteStream.generate depth (inventoryBound runtime))).2 := by
  funext value
  exact congrArg Prod.snd (congrArg (fun table : SourceConditionalFiniteStream.Table => table value) (generated_read (inventoryBound runtime) depth))

theorem model_original (runtime : LivingRuntimeState process) (depth : Nat) :
    model runtime depth = SourceConditionalFiniteStream.model runtime depth := by
  funext value
  rw [model, decoder_original]
  rfl

theorem posterior (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (dynamicRead runtime depth)).support) :
    SourcePosteriorReadback.readWeight runtime (model runtime depth value) =
      (fun actor => SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth) value supported actor) := by
  rw [model_original]
  exact SourceConditionalFiniteStream.posterior _ _ _ _

theorem error_next (runtime : LivingRuntimeState process) (depth : Nat) :
    ((inventoryBound runtime + 2 : Nat) : ℝ) * SourceConditionalVector.dynamicError runtime.tick.next depth (decoder runtime.tick.next depth) =
      ((inventoryBound runtime + 1 : Nat) : ℝ) * SourceConditionalVector.dynamicVariance runtime depth +
        count (inventoryBound runtime) depth (bornObservation (inventoryBound runtime) depth) /
          (count (inventoryBound runtime) depth (bornObservation (inventoryBound runtime) depth) + 1) *
          ‖SourceCopyNativeModelStep.sourceValue runtime.tick.next.tick.next - decoder runtime depth (bornObservation (inventoryBound runtime) depth)‖ ^ 2 := by
  rw [decoder_original, decoder_original]
  exact SourceConditionalFiniteStream.error_next runtime depth

theorem information_cost (runtime : LivingRuntimeState process) (depth : Nat) :
    type_of% (SourceInformationReadback.model_decoder_cost runtime depth (decoder runtime depth)) :=
  SourceInformationReadback.model_decoder_cost runtime depth _

theorem support_restored (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (dynamicRead runtime depth)).support)
    (candidate : NextModel runtime)
    (small : ‖SourceConditionalVector.realizeModel runtime candidate - decoder runtime depth value‖ < SourcePosteriorStability.threshold runtime) :
    SourcePosteriorStability.restoredSupport runtime candidate =
      SourceUniformFibreVariance.fibre (inventoryBound runtime) (dynamicRead runtime depth) value := by
  rw [decoder_original] at small
  exact SourceConditionalFiniteStream.support_restored runtime depth value supported candidate small

theorem table_current_next (runtime : LivingRuntimeState process) (depth : Nat) :
    generate depth (inventoryBound runtime.tick.next) = advance (inventoryBound runtime) depth (generate depth (inventoryBound runtime)) := by
  rw [SourceActualImageStep.next_bound, generated_next]

end
end SourceConditionalWordStream
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
