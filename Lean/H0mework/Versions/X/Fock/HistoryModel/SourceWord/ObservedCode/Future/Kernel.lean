import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Action

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFutureBit

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open SourceGeneratedRuntimeHistoryProbability
open scoped Classical
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

/-- Every legal future tail acts on the current observed bit through its original
letter; the material copy remains the .inr branch of Fock.step. -/
def futureRead (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (actor : Actors runtime) :
    List (Fock.Letter (inventoryBound runtime + 1)) → ZMod 2 :=
  fun tail => SourceWordObservedCode.observe
    (Fock.actualWord (inventoryBound runtime + 1) tail
      (SourceWordMinimalCode.executed runtime word actor))

theorem future_read_bit (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (actor : Actors runtime) :
    futureRead runtime word actor =
      fun tail => bitWord (inventoryBound runtime + 1) tail
        (SourceWordObservedCode.sourceQuery runtime word actor) := by
  funext tail
  exact word_observe _ tail _

theorem future_kernel (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (left right : Actors runtime) :
    futureRead runtime word left = futureRead runtime word right ↔
      SourceWordObservedCode.sourceQuery runtime word left =
        SourceWordObservedCode.sourceQuery runtime word right := by
  constructor
  · intro same
    have atNil := congrFun same []
    simpa only [futureRead, Fock.actualWord, List.foldl_nil,
      SourceWordObservedCode.sourceQuery] using atNil
  · intro same
    rw [future_read_bit, future_read_bit, same]

/-- The existing full conditional law may use the future-response function as
its observation without changing any fibre weight. -/
theorem future_conditional (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (actor : Actors runtime) :
    SourceConditionalHistory.conditional
      (historyPMF (inventoryBound runtime)) (futureRead runtime word)
      (futureRead runtime word actor)
      (SourceWeightedRecovery.observed_supported _ _ actor
        (SourceUniformFibreVariance.source_positive _ actor)) =
    SourceConditionalHistory.conditional
      (historyPMF (inventoryBound runtime)) (SourceWordObservedCode.sourceQuery runtime word)
      (SourceWordObservedCode.sourceQuery runtime word actor)
      (SourceWeightedRecovery.observed_supported _ _ actor
        (SourceUniformFibreVariance.source_positive _ actor)) := by
  exact SourceConditionalHistory.conditional_eq_of_fibre _ _ _ _ _ _ _
    (fun other => future_kernel runtime word other actor)

/-- The autonomous next-task information uses exactly the future dynamic kernel,
and is therefore charged to the already generated bit conditional information. -/
theorem future_information (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1))) :
    SourceConditionalNext.conditionalEntropy
      (historyPMF (inventoryBound runtime)) (futureRead runtime word)
      (SourceConditionalNext.Image.actual (SourceConditionalModel.nextRead runtime))
      (SourceConditionalModel.positive runtime) =
    SourceUniformFibreInformation.conditionalEntropy
      (inventoryBound runtime) (SourceWordObservedCode.sourceQuery runtime word) := by
  rw [SourceConditionalNext.conditionalEntropy_eq_of_kernel
    (historyPMF (inventoryBound runtime)) (futureRead runtime word)
    (SourceWordObservedCode.sourceQuery runtime word)
    (SourceConditionalNext.Image.actual (SourceConditionalModel.nextRead runtime))
    (SourceConditionalModel.positive runtime)
    (fun left right => future_kernel runtime word left right)]
  exact SourceInformationReadback.model_information runtime
    (SourceWordObservedCode.sourceQuery runtime word)

theorem counted_future_posterior (runtime : LivingRuntimeState process)
    (nonunit : (SourceCopyCurrentCoordinates.maximumIndex runtime).val ≠ 0)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (actor : Actors runtime) :
    SourcePosteriorReadback.readWeight runtime
      (SourceCountedPosterior.model runtime
        (SourceRetainedReceiver.trajectory_nonunit runtime nonunit 0)
        (SourceWordObservedCode.table runtime nonunit word 0)
        (SourceWordObservedCode.sourceQuery runtime word actor)) =
      SourceConditionalHistory.conditional
        (historyPMF (inventoryBound runtime)) (futureRead runtime word)
        (futureRead runtime word actor)
        (SourceWeightedRecovery.observed_supported _ _ actor
          (SourceUniformFibreVariance.source_positive _ actor)) := by
  have supported := SourceWeightedRecovery.observed_supported
    (historyPMF (inventoryBound runtime))
    (SourceWordObservedCode.sourceQuery runtime word) actor
    (SourceUniformFibreVariance.source_positive _ actor)
  rw [SourceWordObservedCode.counted_complete_posterior runtime nonunit word
    _ supported]
  funext point
  exact congrArg (fun posterior => posterior point)
    (future_conditional runtime word actor).symm


end
end SourceWordFutureBit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
