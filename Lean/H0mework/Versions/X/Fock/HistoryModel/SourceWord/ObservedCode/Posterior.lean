import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Receiver
import H0mework.Versions.X.Fock.SourceHistory.CountedAdvance.ModelContinuation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordObservedCode

open SourceGeneratedActionWords SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open scoped Classical
noncomputable section

theorem counted_model (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (steps : Nat) (key : ZMod 2) :
    SourceCountedPosterior.model (runtime.advance steps)
      (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps)
      (table runtime nonunit word steps) key =
        SourceConditionalNativePosterior.model (runtime.advance steps)
          (readAt (inventoryBound runtime) word) key := by
  simpa only [table, initial] using
    SourceCountedPosterior.continued_model runtime nonunit
      (readAt (inventoryBound runtime) word) (actualKeys runtime word)
      (actual_inventory runtime word) (exactSamples runtime word)
      (exact_budgets runtime nonunit word) steps key

theorem counted_complete_posterior_at (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (steps : Nat) (key : ZMod 2)
    (supported : key ∈ ((historyPMF (inventoryBound (runtime.advance steps))).map
      (fun actor : Actors (runtime.advance steps) =>
        readAt (inventoryBound runtime) word actor.val)).support) :
    SourcePosteriorReadback.readWeight (runtime.advance steps)
      (SourceCountedPosterior.model (runtime.advance steps)
        (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps)
        (table runtime nonunit word steps) key) =
      (fun actor => SourceConditionalHistory.conditional
        (historyPMF (inventoryBound (runtime.advance steps)))
        (fun index : Actors (runtime.advance steps) =>
          readAt (inventoryBound runtime) word index.val)
        key supported actor) := by
  rw [counted_model runtime nonunit word steps key]
  exact SourceConditionalNativePosterior.complete_posterior
    (runtime.advance steps) (readAt (inventoryBound runtime) word) key supported

theorem counted_complete_posterior (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (key : ZMod 2)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map
      (sourceQuery runtime word)).support) :
    SourcePosteriorReadback.readWeight runtime
      (SourceCountedPosterior.model runtime
        (SourceRetainedReceiver.trajectory_nonunit runtime nonunit 0)
        (table runtime nonunit word 0) key) =
      (fun actor => SourceConditionalHistory.conditional
        (historyPMF (inventoryBound runtime)) (sourceQuery runtime word)
        key supported actor) := by
  have queryEq : (fun actor : Actors runtime => readAt (inventoryBound runtime) word actor.val) =
      sourceQuery runtime word := by
    funext actor
    exact (source_query_read runtime word actor).symm
  have supportedRead : key ∈ ((historyPMF (inventoryBound runtime)).map
      (fun actor : Actors runtime => readAt (inventoryBound runtime) word actor.val)).support := by
    simpa only [queryEq] using supported
  have modelAtZero : SourceCountedPosterior.model runtime
      (SourceRetainedReceiver.trajectory_nonunit runtime nonunit 0)
      (table runtime nonunit word 0) key =
        SourceConditionalNativePosterior.model runtime
          (readAt (inventoryBound runtime) word) key := by
    simpa only [LivingRuntimeState.advance] using
      (counted_model runtime nonunit word 0 key)
  rw [modelAtZero]
  simpa only [queryEq] using
    (SourceConditionalNativePosterior.complete_posterior runtime
      (readAt (inventoryBound runtime) word) key supportedRead)

theorem counted_next_model (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (steps : Nat) (key : ZMod 2) :
    SourceCountedAdvance.nextModel (runtime.advance steps)
      (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps)
      (table runtime nonunit word steps)
      (readAt (inventoryBound runtime) word (runtime.advance steps).tick.next.state) key =
        SourceConditionalNativePosterior.model (runtime.advance steps).tick.next
          (readAt (inventoryBound runtime) word) key := by
  simpa only [table, initial] using
    SourceCountedAdvance.continued_model runtime nonunit
      (readAt (inventoryBound runtime) word) (actualKeys runtime word)
      (actual_inventory runtime word) (exactSamples runtime word)
      (exact_budgets runtime nonunit word) steps key

end
end SourceWordObservedCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
