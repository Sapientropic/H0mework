import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.NativeBirth
import H0mework.Versions.X.Fock.HistoryConditional.GWordConditional

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompiledGWord

open SourceGeneratedActionWords
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem encode_old_letter (depth : Nat) (letter : Fock.Letter depth) :
    SourceCopyNativeWord.encode (Fock.Dynamic.oldLetter depth letter) =
      SourceCopyNativeWord.encode letter := by
  cases letter <;> rfl

theorem encode_old_word (depth : Nat) (word : List (Fock.Letter depth)) :
    (word.map (Fock.Dynamic.oldLetter depth)).map SourceCopyNativeWord.encode =
      word.map SourceCopyNativeWord.encode := by
  induction word with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.map_cons, encode_old_letter, ih]

theorem effect_old_word (depth : Nat) (word : List (Fock.Letter (depth + 1))) :
    effect (depth + 2) (word.map (Fock.Dynamic.oldLetter (depth + 1))) =
      effect (depth + 1) word := by
  unfold effect
  simp only [encode_old_word]

theorem effect_transport_word {left right : Nat} (same : left = right)
    (word : List (Fock.Letter (left + 1))) :
    effect (right + 1) (SourceWordFutureBitGrowth.transportWord same word) =
      effect (left + 1) word := by
  cases same
  rfl

theorem effect_native_birth (depth : Nat) (word : List (Fock.Letter (depth + 1))) :
    effect (inventoryBound (runtimeAt (depth + 1)) + 1)
        (SourceWordFutureBitGrowth.nextWordAt depth word) =
      effect (inventoryBound (runtimeAt depth) + 1)
        (SourceWordFutureBitGrowth.oldWordAt depth word) := by
  calc
    _ = effect (depth + 2) (word.map (Fock.Dynamic.oldLetter (depth + 1))) :=
      effect_transport_word _ _
    _ = effect (depth + 1) word := effect_old_word depth word
    _ = _ := (effect_transport_word _ _).symm

theorem values_transport {left right : Nat} (same : left = right)
    (actor : Fin (left + 1)) :
    SourceConditionalInventory.values right
        (actor.cast (congrArg (· + 1) same)) =
      SourceConditionalInventory.values left actor := by
  cases same
  rfl

theorem values_native_birth_old_actor (depth : Nat) (actor : Fin (depth + 1)) :
    SourceConditionalInventory.values (inventoryBound (runtimeAt (depth + 1)))
        (actor.castSucc.cast (by simp only [SourceConditionalInventory.runtime_bound])) =
      SourceConditionalInventory.values (inventoryBound (runtimeAt depth))
        (actor.cast (by simp only [SourceConditionalInventory.runtime_bound])) := by
  calc
    _ = SourceConditionalInventory.values (depth + 1) actor.castSucc :=
      values_transport (SourceConditionalInventory.runtime_bound (depth + 1)).symm _
    _ = SourceConditionalInventory.values depth actor :=
      SourceConditionalInventory.values_retained depth actor
    _ = _ := (values_transport (SourceConditionalInventory.runtime_bound depth).symm _).symm

theorem image_native_birth_old_actor (depth : Nat)
    (word : List (Fock.Letter (depth + 1))) (actor : Fin (depth + 1)) :
    image (runtimeAt (depth + 1)) (inventoryBound (runtimeAt (depth + 1)) + 1)
        (SourceWordFutureBitGrowth.nextWordAt depth word)
          (actor.castSucc.cast (by simp only [SourceConditionalInventory.runtime_bound])) =
      image (runtimeAt depth) (inventoryBound (runtimeAt depth) + 1)
        (SourceWordFutureBitGrowth.oldWordAt depth word)
          (actor.cast (by simp only [SourceConditionalInventory.runtime_bound])) := by
  calc
    _ = effect (inventoryBound (runtimeAt (depth + 1)) + 1)
          (SourceWordFutureBitGrowth.nextWordAt depth word)
          (SourceConditionalInventory.values (inventoryBound (runtimeAt (depth + 1)))
            (actor.castSucc.cast (by simp only [SourceConditionalInventory.runtime_bound]))) :=
      congrFun (image_original _ _ _) _
    _ = effect (inventoryBound (runtimeAt depth) + 1)
          (SourceWordFutureBitGrowth.oldWordAt depth word)
          (SourceConditionalInventory.values (inventoryBound (runtimeAt (depth + 1)))
            (actor.castSucc.cast (by simp only [SourceConditionalInventory.runtime_bound]))) :=
      congrArg (fun (operation : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier) =>
        operation (SourceConditionalInventory.values (inventoryBound (runtimeAt (depth + 1)))
          (actor.castSucc.cast (by simp only [SourceConditionalInventory.runtime_bound]))))
        (effect_native_birth depth word)
    _ = effect (inventoryBound (runtimeAt depth) + 1)
          (SourceWordFutureBitGrowth.oldWordAt depth word)
          (SourceConditionalInventory.values (inventoryBound (runtimeAt depth))
            (actor.cast (by simp only [SourceConditionalInventory.runtime_bound]))) :=
      congrArg _ (values_native_birth_old_actor depth actor)
    _ = _ := (congrFun (image_original _ _ _) _).symm

theorem query_native_birth_old_actor (depth : Nat)
    (word : List (Fock.Letter (depth + 1))) (actor : Fin (depth + 1)) :
    SourceWordObservedCode.sourceQuery (runtimeAt (depth + 1))
        (SourceWordFutureBitGrowth.nextWordAt depth word)
          (actor.castSucc.cast (by simp only [SourceConditionalInventory.runtime_bound])) =
      SourceWordObservedCode.sourceQuery (runtimeAt depth)
        (SourceWordFutureBitGrowth.oldWordAt depth word)
          (actor.cast (by simp only [SourceConditionalInventory.runtime_bound])) := by
  rw [SourceWordObservedCode.source_query_read,
    SourceWordObservedCode.source_query_read]
  exact SourceWordFutureBitGrowth.old_next_read_at depth word actor.val

theorem old_actor_error_native_birth (depth : Nat)
    (word : List (Fock.Letter (depth + 1)))
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier)
    (actor : Fin (depth + 1)) :
    ‖image (runtimeAt (depth + 1)) (inventoryBound (runtimeAt (depth + 1)) + 1)
        (SourceWordFutureBitGrowth.nextWordAt depth word)
          (actor.castSucc.cast (by simp only [SourceConditionalInventory.runtime_bound])) -
      decoder (SourceWordObservedCode.sourceQuery (runtimeAt (depth + 1))
        (SourceWordFutureBitGrowth.nextWordAt depth word)
          (actor.castSucc.cast (by simp only [SourceConditionalInventory.runtime_bound])))‖ ^ 2 =
    ‖image (runtimeAt depth) (inventoryBound (runtimeAt depth) + 1)
        (SourceWordFutureBitGrowth.oldWordAt depth word)
          (actor.cast (by simp only [SourceConditionalInventory.runtime_bound])) -
      decoder (SourceWordObservedCode.sourceQuery (runtimeAt depth)
        (SourceWordFutureBitGrowth.oldWordAt depth word)
          (actor.cast (by simp only [SourceConditionalInventory.runtime_bound])))‖ ^ 2 := by
  rw [image_native_birth_old_actor, query_native_birth_old_actor]

theorem inventory_bound_native_birth (depth : Nat) :
    inventoryBound (runtimeAt (depth + 1)) = inventoryBound (runtimeAt depth) + 1 := by
  simp only [SourceConditionalInventory.runtime_bound]

theorem old_actor_error_native_birth_from_next (depth : Nat)
    (word : List (Fock.Letter (depth + 1)))
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier)
    (actor : Fin (inventoryBound (runtimeAt (depth + 1)))) :
    ‖image (runtimeAt (depth + 1)) (inventoryBound (runtimeAt (depth + 1)) + 1)
        (SourceWordFutureBitGrowth.nextWordAt depth word) actor.castSucc -
      decoder (SourceWordObservedCode.sourceQuery (runtimeAt (depth + 1))
        (SourceWordFutureBitGrowth.nextWordAt depth word) actor.castSucc)‖ ^ 2 =
    ‖image (runtimeAt depth) (inventoryBound (runtimeAt depth) + 1)
        (SourceWordFutureBitGrowth.oldWordAt depth word)
          (actor.cast (inventory_bound_native_birth depth)) -
      decoder (SourceWordObservedCode.sourceQuery (runtimeAt depth)
        (SourceWordFutureBitGrowth.oldWordAt depth word)
          (actor.cast (inventory_bound_native_birth depth)))‖ ^ 2 := by
  let oldActor : Fin (depth + 1) :=
    actor.cast (SourceConditionalInventory.runtime_bound (depth + 1))
  have nextIndex :
      oldActor.castSucc.cast (by simp only [SourceConditionalInventory.runtime_bound]) =
        actor.castSucc := Fin.ext rfl
  have oldIndex :
      oldActor.cast ((congrArg (· + 1)
        (SourceConditionalInventory.runtime_bound depth)).symm) =
        actor.cast (inventory_bound_native_birth depth) := Fin.ext rfl
  simpa only [nextIndex, oldIndex] using
    (old_actor_error_native_birth depth word decoder oldActor)

theorem old_actor_error_sum_native_birth (depth : Nat)
    (word : List (Fock.Letter (depth + 1)))
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    (∑ actor : Fin (inventoryBound (runtimeAt (depth + 1))),
      ‖image (runtimeAt (depth + 1)) (inventoryBound (runtimeAt (depth + 1)) + 1)
          (SourceWordFutureBitGrowth.nextWordAt depth word) actor.castSucc -
        decoder (SourceWordObservedCode.sourceQuery (runtimeAt (depth + 1))
          (SourceWordFutureBitGrowth.nextWordAt depth word) actor.castSucc)‖ ^ 2) =
      ∑ actor : SourceConditionalModel.Actors (runtimeAt depth),
        ‖image (runtimeAt depth) (inventoryBound (runtimeAt depth) + 1)
            (SourceWordFutureBitGrowth.oldWordAt depth word) actor -
          decoder (SourceWordObservedCode.sourceQuery (runtimeAt depth)
            (SourceWordFutureBitGrowth.oldWordAt depth word) actor)‖ ^ 2 := by
  let oldActors : Fin (inventoryBound (runtimeAt (depth + 1))) ≃
      SourceConditionalModel.Actors (runtimeAt depth) := {
    toFun := fun actor => actor.cast (inventory_bound_native_birth depth)
    invFun := fun actor => actor.cast (inventory_bound_native_birth depth).symm
    left_inv := by intro actor; exact Fin.ext rfl
    right_inv := by intro actor; exact Fin.ext rfl }
  apply Fintype.sum_equiv oldActors
  intro actor
  exact old_actor_error_native_birth_from_next depth word decoder actor

end
end SourceCompiledGWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
