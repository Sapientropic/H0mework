import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFieldCode

open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceGeneratedActionWords.Fock
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedRuntimeHistoryProbability
open SourceConditionalHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

attribute [local instance] fieldUniformSpace fieldMeasurable fieldBorelSpace fieldT2

theorem counted_mixture (runtime : LivingRuntimeState process)
    (nonunit : (SourceCopyCurrentCoordinates.maximumIndex runtime).val ≠ 0)
    (word : List (Letter (SourceGeneratedAcquisitionContinuation.inventoryBound runtime + 1)))
    (key : ZMod 2)
    (supported : key ∈ (observed
      (observed (historyPMF (SourceGeneratedAcquisitionContinuation.inventoryBound runtime))
        (Actor.nextRead (SourceGeneratedAcquisitionContinuation.inventoryBound runtime + 1)
          (SourceGeneratedAcquisitionContinuation.inventoryBound runtime)))
      (fieldCode (SourceGeneratedAcquisitionContinuation.inventoryBound runtime) word)).support) :
    SourcePosteriorReadback.readWeight runtime
      (SourceCountedPosterior.model runtime
        (SourceRetainedReceiver.trajectory_nonunit runtime nonunit 0)
        (SourceWordObservedCode.table runtime nonunit word 0) key) =
      (fun actor => Coarsening.mixture
        (historyPMF (SourceGeneratedAcquisitionContinuation.inventoryBound runtime))
        (Actor.nextRead (SourceGeneratedAcquisitionContinuation.inventoryBound runtime + 1)
          (SourceGeneratedAcquisitionContinuation.inventoryBound runtime))
        (fieldCode (SourceGeneratedAcquisitionContinuation.inventoryBound runtime) word)
        key supported actor) := by
  obtain ⟨supportRead, mixtureEq⟩ := mixture_full
    (SourceGeneratedAcquisitionContinuation.inventoryBound runtime) word key supported
  have queryEq :
      (fun actor : SourceConditionalModel.Actors runtime =>
        SourceWordObservedCode.readAt (SourceGeneratedAcquisitionContinuation.inventoryBound runtime) word actor.val) =
      SourceWordObservedCode.sourceQuery runtime word := by
    funext actor
    exact (SourceWordObservedCode.source_query_read runtime word actor).symm
  have supportQuery : key ∈ (observed
      (historyPMF (SourceGeneratedAcquisitionContinuation.inventoryBound runtime))
      (SourceWordObservedCode.sourceQuery runtime word)).support := by
    simpa only [queryEq] using supportRead
  have counted := SourceWordObservedCode.counted_complete_posterior runtime
    nonunit word key supportQuery
  rw [mixtureEq]
  simpa only [queryEq] using counted

theorem counted_l2_transfer (runtime : LivingRuntimeState process)
    (nonunit : (SourceCopyCurrentCoordinates.maximumIndex runtime).val ≠ 0)
    (word : List (Letter (SourceGeneratedAcquisitionContinuation.inventoryBound runtime + 1)))
    (task : SourceConditionalModel.Actors runtime → ℂ)
    (key : ZMod 2)
    (supported : key ∈ (observed
      (observed (historyPMF (SourceGeneratedAcquisitionContinuation.inventoryBound runtime))
        (Actor.nextRead (SourceGeneratedAcquisitionContinuation.inventoryBound runtime + 1)
          (SourceGeneratedAcquisitionContinuation.inventoryBound runtime)))
      (fieldCode (SourceGeneratedAcquisitionContinuation.inventoryBound runtime) word)).support) :
    SourceWeightedRecovery.optimalDecoder (historyPMF (SourceGeneratedAcquisitionContinuation.inventoryBound runtime))
      (SourceWordObservedCode.sourceQuery runtime word) task key =
      ∑ actor : SourceConditionalModel.Actors runtime,
        (SourcePosteriorReadback.readWeight runtime
          (SourceCountedPosterior.model runtime
            (SourceRetainedReceiver.trajectory_nonunit runtime nonunit 0)
            (SourceWordObservedCode.table runtime nonunit word 0) key) actor).toReal • task actor := by
  obtain ⟨supportedRead, mixtureEq⟩ := mixture_full
    (SourceGeneratedAcquisitionContinuation.inventoryBound runtime) word key supported
  have queryEq :
      (fun actor : SourceConditionalModel.Actors runtime =>
        SourceWordObservedCode.readAt (SourceGeneratedAcquisitionContinuation.inventoryBound runtime) word actor.val) =
      SourceWordObservedCode.sourceQuery runtime word := by
    funext actor
    exact (SourceWordObservedCode.source_query_read runtime word actor).symm
  have supportedQuery : key ∈ (observed
      (historyPMF (SourceGeneratedAcquisitionContinuation.inventoryBound runtime))
      (SourceWordObservedCode.sourceQuery runtime word)).support := by
    simpa only [queryEq] using supportedRead
  have optimal := SourceWeightedRecovery.optimal_is_conditional
    (historyPMF (SourceGeneratedAcquisitionContinuation.inventoryBound runtime))
    (SourceWordObservedCode.sourceQuery runtime word) task key supportedQuery
  rw [counted_mixture runtime nonunit word key supported, mixtureEq]
  simpa only [SourceWeightedRecovery.conditionalMean, queryEq] using optimal

theorem counted_original_field_transfer (runtime : LivingRuntimeState process)
    (nonunit : (SourceCopyCurrentCoordinates.maximumIndex runtime).val ≠ 0)
    (word : List (Letter (SourceGeneratedAcquisitionContinuation.inventoryBound runtime + 1)))
    (task : SourceConditionalModel.Actors runtime → ℂ)
    (key : ZMod 2)
    (supported : key ∈ (observed
      (observed (historyPMF (SourceGeneratedAcquisitionContinuation.inventoryBound runtime))
        (Actor.nextRead (SourceGeneratedAcquisitionContinuation.inventoryBound runtime + 1)
          (SourceGeneratedAcquisitionContinuation.inventoryBound runtime)))
      (fieldCode (SourceGeneratedAcquisitionContinuation.inventoryBound runtime) word)).support) :
    SourceWeightedRecovery.optimalDecoder
      (historyPMF (SourceGeneratedAcquisitionContinuation.inventoryBound runtime))
      (SourceWordObservedCode.sourceQuery runtime word) task key =
      ∑ actor : SourceConditionalModel.Actors runtime,
        (SourcePosteriorReadback.readWeight runtime
          (SourceCountedPosterior.model runtime
            (SourceRetainedReceiver.trajectory_nonunit runtime nonunit 0)
            (SourceWordObservedCode.table runtime nonunit word 0) key) actor).toReal •
          IsometricRetainedTransfer.transfer
            (SourceOwnedObservationHistory.pullback nativeStep
              (rawWords (SourceGeneratedAcquisitionContinuation.inventoryBound runtime + 1))
              CanonicalUnitArithmeticRoot.initialCurrent
              (SourceGeneratedAcquisitionContinuation.inventoryBound runtime))
            (Actor.currentTransfer
              (SourceGeneratedAcquisitionContinuation.inventoryBound runtime + 1)
              (SourceGeneratedAcquisitionContinuation.inventoryBound runtime)
              (SourceWeightedRecovery.taskValue
                (historyPMF (SourceGeneratedAcquisitionContinuation.inventoryBound runtime)) task))
            (Actor.nextRead (SourceGeneratedAcquisitionContinuation.inventoryBound runtime + 1)
              (SourceGeneratedAcquisitionContinuation.inventoryBound runtime) actor) := by
  rw [counted_l2_transfer runtime nonunit word task key supported]
  apply Finset.sum_congr rfl
  intro actor _
  exact congrArg
    (fun value : ℂ =>
      (SourcePosteriorReadback.readWeight runtime
        (SourceCountedPosterior.model runtime
          (SourceRetainedReceiver.trajectory_nonunit runtime nonunit 0)
          (SourceWordObservedCode.table runtime nonunit word 0) key) actor).toReal • value)
    (OriginalHilbert.original_next_recovery
      (SourceGeneratedAcquisitionContinuation.inventoryBound runtime + 1)
      (SourceGeneratedAcquisitionContinuation.inventoryBound runtime) task actor).symm


end
end SourceWordFieldCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
