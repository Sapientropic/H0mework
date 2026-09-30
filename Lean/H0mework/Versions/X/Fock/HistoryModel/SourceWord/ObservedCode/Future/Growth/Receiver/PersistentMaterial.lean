import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Growth.NoFreeBirth

/-!
# Original source letters survive every lawful inventory expansion

The d2 and d3 letters retain their exact material runtimes while each
subsequent native tick extends the legal inventory. The old letter still
reads zero; the newer letter still distinguishes the original actors.
-/

set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordPersistentMaterial

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime

noncomputable section

def depth (offset : Nat) : Nat := 3 + offset

theorem runtime_from_original (offset : Nat) :
    runtimeAt (depth offset) = (runtimeAt 3).advance offset := by
  induction offset with
  | zero => rfl
  | succ offset ih =>
      change runtimeAt (depth offset + 1) =
        ((runtimeAt 3).advance offset).tick.next
      rw [SourceWordFutureBitGrowth.next_runtime (depth offset), ih]

def slotAt (offset : Nat) (slot : Fin 5) :
    FamilyModel.Fock.Index (depth offset + 1) :=
  ⟨slot.val, by
    rw [runtime_bound]
    have inside := slot.isLt
    dsimp [depth]
    omega⟩

def oldRaw (offset : Nat) : List (Fock.Letter (depth offset + 1)) :=
  [.inr (slotAt offset ⟨3, by decide⟩)]

def freshRaw (offset : Nat) : List (Fock.Letter (depth offset + 1)) :=
  [.inr (slotAt offset ⟨4, by decide⟩)]

def oldWord (offset : Nat) :
    List (Fock.Letter (inventoryBound (runtimeAt (depth offset)) + 1)) :=
  SourceWordFutureBitGrowth.oldWordAt (depth offset) (oldRaw offset)

def freshWord (offset : Nat) :
    List (Fock.Letter (inventoryBound (runtimeAt (depth offset)) + 1)) :=
  SourceWordFutureBitGrowth.oldWordAt (depth offset) (freshRaw offset)

theorem oldWord_zero_is_carriedAtThree :
    oldWord 0 = SourceWordFutureBitGrowth.carriedAtThree := by
  rfl

theorem freshWord_zero_is_original :
    freshWord 0 = SourceWordFreshReceiver.freshWord 3 := by
  rfl

theorem slotAt_next (offset : Nat) (slot : Fin 5) :
    slotAt (offset + 1) slot =
      FamilyModel.Fock.oldIndex (depth offset + 1) (slotAt offset slot) := by
  apply Fin.ext
  rfl

theorem oldRaw_next (offset : Nat) :
    oldRaw (offset + 1) =
      (oldRaw offset).map
        (SourceGeneratedActionWords.Fock.Dynamic.oldLetter (depth offset + 1)) := by
  simp only [oldRaw, List.map_cons, List.map_nil]
  congr 1

theorem freshRaw_next (offset : Nat) :
    freshRaw (offset + 1) =
      (freshRaw offset).map
        (SourceGeneratedActionWords.Fock.Dynamic.oldLetter (depth offset + 1)) := by
  simp only [freshRaw, List.map_cons, List.map_nil]
  congr 1

theorem oldWord_next (offset : Nat) :
    oldWord (offset + 1) =
      SourceWordFutureBitGrowth.nextWordAt (depth offset) (oldRaw offset) := by
  rw [oldWord, SourceWordFutureBitGrowth.nextWordAt, oldRaw_next]
  rfl

theorem freshWord_next (offset : Nat) :
    freshWord (offset + 1) =
      SourceWordFutureBitGrowth.nextWordAt (depth offset) (freshRaw offset) := by
  rw [freshWord, SourceWordFutureBitGrowth.nextWordAt, freshRaw_next]
  rfl

theorem slot_material (offset : Nat) (slot : Fin 5) :
    NativeCopy.Fock.material (depth offset + 1) (slotAt offset slot) =
      ((runtimeAt slot.val).current.visit.current : Current) := by
  exact SourceGeneratedActionWords.Fock.Dynamic.all_material_actual
    (depth offset) (slotAt offset slot)

theorem slot_read (offset : Nat) (slot : Fin 5) (index : Nat) :
    SourceWordObservedCode.readAt (depth offset)
      [(.inr (slotAt offset slot) : Fock.Letter (depth offset + 1))] index =
      SourceWordObservedCode.readAt (depth offset) [] index *
        SourceWordObservedCode.observe
          ((runtimeAt slot.val).current.visit.current : Current) := by
  change SourceWordObservedCode.observe
    (Fock.step (depth offset + 1) (.inr (slotAt offset slot))
      (nativeStep ((runtimeAt index).current.visit.current : Current))) = _
  rw [SourceWordFutureBit.step_observe]
  change SourceWordObservedCode.observe
      (nativeStep ((runtimeAt index).current.visit.current : Current)) *
      SourceWordObservedCode.observe
        (NativeCopy.Fock.material (depth offset + 1) (slotAt offset slot)) = _
  rw [slot_material]
  rfl

theorem old_raw_zero (offset index : Nat) :
    SourceWordObservedCode.readAt (depth offset) (oldRaw offset) index = 0 := by
  rw [oldRaw, slot_read]
  have evenMaterial : SourceWordObservedCode.observe
      ((runtimeAt 3).current.visit.current : Current) = 0 := by
    change ((scanIndex (runtimeAt 3).current.visit.current : Nat) : ZMod 2) = 0
    rw [runtimeAt_scanIndex]
    decide
  rw [evenMaterial, mul_zero]

theorem fresh_raw_retains (offset index : Nat) :
    SourceWordObservedCode.readAt (depth offset) (freshRaw offset) index =
      SourceWordObservedCode.readAt (depth offset) [] index := by
  rw [freshRaw, slot_read]
  have oddMaterial : SourceWordObservedCode.observe
      ((runtimeAt 4).current.visit.current : Current) = 1 := by
    change ((scanIndex (runtimeAt 4).current.visit.current : Nat) : ZMod 2) = 1
    rw [runtimeAt_scanIndex]
    decide
  rw [oddMaterial, mul_one]

theorem old_word_zero (offset : Nat)
    (actor : Actors (runtimeAt (depth offset))) :
    SourceWordObservedCode.sourceQuery (runtimeAt (depth offset))
      (oldWord offset) actor = 0 := by
  calc
    _ = SourceWordObservedCode.readAt
        (inventoryBound (runtimeAt (depth offset)))
          (oldWord offset) actor.val :=
      SourceWordObservedCode.source_query_read _ _ _
    _ = SourceWordObservedCode.readAt (depth offset)
          (oldRaw offset) actor.val :=
      SourceWordFutureBitGrowth.transport_read_at _ _ _
    _ = 0 := old_raw_zero offset actor.val

theorem fresh_word_retains (offset : Nat)
    (actor : Actors (runtimeAt (depth offset))) :
    SourceWordObservedCode.sourceQuery (runtimeAt (depth offset))
      (freshWord offset) actor =
        SourceWordObservedCode.readAt (depth offset) [] actor.val := by
  calc
    _ = SourceWordObservedCode.readAt
        (inventoryBound (runtimeAt (depth offset)))
          (freshWord offset) actor.val :=
      SourceWordObservedCode.source_query_read _ _ _
    _ = SourceWordObservedCode.readAt (depth offset)
          (freshRaw offset) actor.val :=
      SourceWordFutureBitGrowth.transport_read_at _ _ _
    _ = SourceWordObservedCode.readAt (depth offset) [] actor.val :=
      fresh_raw_retains offset actor.val

def actorZero (offset : Nat) : Actors (runtimeAt (depth offset)) :=
  ⟨0, by rw [inventory_bound, runtimeAt_state]; dsimp [depth]; omega⟩

def actorOne (offset : Nat) : Actors (runtimeAt (depth offset)) :=
  ⟨1, by rw [inventory_bound, runtimeAt_state]; dsimp [depth]; omega⟩

theorem fresh_word_separates (offset : Nat) :
    SourceWordObservedCode.sourceQuery (runtimeAt (depth offset))
        (freshWord offset) (actorZero offset) ≠
      SourceWordObservedCode.sourceQuery (runtimeAt (depth offset))
        (freshWord offset) (actorOne offset) := by
  rw [fresh_word_retains, fresh_word_retains]
  change SourceWordObservedCode.observe
      (nativeStep ((runtimeAt 0).current.visit.current : Current)) ≠
    SourceWordObservedCode.observe
      (nativeStep ((runtimeAt 1).current.visit.current : Current))
  decide


end
end SourceWordPersistentMaterial
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
