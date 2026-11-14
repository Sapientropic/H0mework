import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Growth.Transport

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFutureBitGrowth

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

theorem old_new_counted_model (depth : Nat)
    (nonunit : (SourceCopyCurrentCoordinates.maximumIndex (runtimeAt depth)).val ≠ 0)
    (word : List (Fock.Letter (depth + 1))) (key : ZMod 2) :
    SourceCountedPosterior.model ((runtimeAt depth).advance 1)
      (SourceRetainedReceiver.trajectory_nonunit (runtimeAt depth) nonunit 1)
      (SourceWordObservedCode.table (runtimeAt depth) nonunit (oldWordAt depth word) 1) key =
    SourceCountedPosterior.model ((runtimeAt (depth + 1)).advance 0)
      (SourceRetainedReceiver.trajectory_nonunit (runtimeAt (depth + 1))
        (nextNonunit depth) 0)
      (SourceWordObservedCode.table (runtimeAt (depth + 1))
        (nextNonunit depth)
        (nextWordAt depth word) 0) key := by
  rw [SourceWordObservedCode.counted_model (runtimeAt depth) nonunit
    (oldWordAt depth word) 1 key]
  rw [SourceWordObservedCode.counted_model (runtimeAt (depth + 1))
    (nextNonunit depth)
    (nextWordAt depth word) 0 key]
  have queryEq : SourceWordObservedCode.readAt
      (inventoryBound (runtimeAt (depth + 1))) (nextWordAt depth word) =
      SourceWordObservedCode.readAt
        (inventoryBound (runtimeAt depth)) (oldWordAt depth word) := by
    funext index
    exact old_next_read_at depth word index
  rw [queryEq]
  rfl

theorem old_next_model_eq_new_start (depth : Nat)
    (nonunit : (SourceCopyCurrentCoordinates.maximumIndex (runtimeAt depth)).val ≠ 0)
    (word : List (Fock.Letter (depth + 1))) (key : ZMod 2) :
    SourceCountedAdvance.nextModel ((runtimeAt depth).advance 0)
      (SourceRetainedReceiver.trajectory_nonunit (runtimeAt depth) nonunit 0)
      (SourceWordObservedCode.table (runtimeAt depth) nonunit (oldWordAt depth word) 0)
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
        (oldWordAt depth word) ((runtimeAt depth).advance 0).tick.next.state) key =
    SourceCountedPosterior.model ((runtimeAt (depth + 1)).advance 0)
      (SourceRetainedReceiver.trajectory_nonunit (runtimeAt (depth + 1))
        (nextNonunit depth) 0)
      (SourceWordObservedCode.table (runtimeAt (depth + 1))
        (nextNonunit depth) (nextWordAt depth word) 0) key := by
  rw [SourceWordObservedCode.counted_next_model (runtimeAt depth) nonunit
    (oldWordAt depth word) 0 key]
  rw [SourceWordObservedCode.counted_model (runtimeAt (depth + 1))
    (nextNonunit depth) (nextWordAt depth word) 0 key]
  have queryEq : SourceWordObservedCode.readAt
      (inventoryBound (runtimeAt (depth + 1))) (nextWordAt depth word) =
      SourceWordObservedCode.readAt
        (inventoryBound (runtimeAt depth)) (oldWordAt depth word) := by
    funext index
    exact old_next_read_at depth word index
  rw [queryEq]
  rfl


end
end SourceWordFutureBitGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
