import H0mework.Versions.X.Fock.HistoryModel.DynamicMaterial
import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Controls

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

theorem old_bit_action (depth : Nat) (letter : Fock.Letter depth) (bit : ZMod 2) :
    SourceWordFutureBit.bitAction (depth + 1)
        (SourceGeneratedActionWords.Fock.Dynamic.oldLetter depth letter) bit =
      SourceWordFutureBit.bitAction depth letter bit := by
  cases letter <;> rfl

theorem old_bit_word (depth : Nat) (word : List (Fock.Letter depth)) (bit : ZMod 2) :
    SourceWordFutureBit.bitWord (depth + 1)
        (word.map (SourceGeneratedActionWords.Fock.Dynamic.oldLetter depth)) bit =
      SourceWordFutureBit.bitWord depth word bit := by
  induction word generalizing bit with
  | nil => rfl
  | cons letter rest ih =>
      change SourceWordFutureBit.bitWord (depth + 1)
          (rest.map (SourceGeneratedActionWords.Fock.Dynamic.oldLetter depth))
          (SourceWordFutureBit.bitAction (depth + 1)
            (SourceGeneratedActionWords.Fock.Dynamic.oldLetter depth letter) bit) = _
      rw [old_bit_action, ih]
      rfl

theorem old_source_word (depth : Nat) (word : List (Fock.Letter depth)) (state : Current) :
    sourcePoint (Fock.actualWord (depth + 1)
        (word.map (SourceGeneratedActionWords.Fock.Dynamic.oldLetter depth)) state) =
      sourcePoint (Fock.actualWord depth word state) := by
  have sourceRun := congrArg (fun action => action (sourcePoint state))
    (SourceGeneratedActionWords.Fock.Dynamic.old_word_run depth word)
  simpa only [Fock.OriginalHilbert.word_sourcePoint] using sourceRun

theorem old_observed_word (depth : Nat) (word : List (Fock.Letter depth)) (state : Current) :
    SourceWordObservedCode.observe (Fock.actualWord (depth + 1)
        (word.map (SourceGeneratedActionWords.Fock.Dynamic.oldLetter depth)) state) =
      SourceWordObservedCode.observe (Fock.actualWord depth word state) := by
  rw [SourceWordFutureBit.word_observe, SourceWordFutureBit.word_observe,
    old_bit_word]

theorem old_read_at (depth : Nat) (word : List (Fock.Letter (depth + 1)))
    (index : Nat) :
    SourceWordObservedCode.readAt (depth + 1)
        (word.map (SourceGeneratedActionWords.Fock.Dynamic.oldLetter (depth + 1))) index =
      SourceWordObservedCode.readAt depth word index := by
  exact old_observed_word (depth + 1) word
    (nativeStep ((runtimeAt index).current.visit.current : Current))

def transportWord {left right : Nat} (same : left = right)
    (word : List (Fock.Letter (left + 1))) : List (Fock.Letter (right + 1)) :=
  same ▸ word

theorem transport_read_at {left right : Nat} (same : left = right)
    (word : List (Fock.Letter (left + 1))) (index : Nat) :
    SourceWordObservedCode.readAt right (transportWord same word) index =
      SourceWordObservedCode.readAt left word index := by
  cases same
  rfl

def oldWordAt (depth : Nat) (word : List (Fock.Letter (depth + 1))) :
    List (Fock.Letter (inventoryBound (runtimeAt depth) + 1)) :=
  transportWord ((inventory_bound (runtimeAt depth)).trans
    (runtimeAt_state depth)).symm word

def nextWordAt (depth : Nat) (word : List (Fock.Letter (depth + 1))) :
    List (Fock.Letter (inventoryBound (runtimeAt (depth + 1)) + 1)) :=
  transportWord ((inventory_bound (runtimeAt (depth + 1))).trans
    (runtimeAt_state (depth + 1))).symm
    (word.map (SourceGeneratedActionWords.Fock.Dynamic.oldLetter (depth + 1)))

theorem old_next_read_at (depth : Nat) (word : List (Fock.Letter (depth + 1)))
    (index : Nat) :
    SourceWordObservedCode.readAt (inventoryBound (runtimeAt (depth + 1)))
        (nextWordAt depth word) index =
      SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
        (oldWordAt depth word) index := by
  calc
    _ = SourceWordObservedCode.readAt (depth + 1)
        (word.map (SourceGeneratedActionWords.Fock.Dynamic.oldLetter (depth + 1))) index :=
      transport_read_at _ _ _
    _ = SourceWordObservedCode.readAt depth word index := old_read_at depth word index
    _ = _ := (transport_read_at _ _ _).symm

theorem next_runtime (depth : Nat) :
    runtimeAt (depth + 1) = (runtimeAt depth).tick.next := rfl

theorem nextNonunit (depth : Nat) :
    (SourceCopyCurrentCoordinates.maximumIndex (runtimeAt (depth + 1))).val ≠ 0 := by
  rw [next_runtime]
  exact SourceMinimumSharedNext.next_nonunit (runtimeAt depth)


end
end SourceWordFutureBitGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
