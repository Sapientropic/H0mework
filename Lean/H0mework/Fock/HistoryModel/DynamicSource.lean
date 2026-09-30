import H0mework.Fock.HistoryModel.CompletionConsumer

/-! The already generated old material indices preserve every old source letter and its full operation word. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Dynamic

open SourceGeneratedActionObservationHistory SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock

noncomputable section

def oldLetter (depth : Nat) : Fock.Letter depth → Fock.Letter (depth + 1)
  | .inl token => .inl token
  | .inr index => .inr (FamilyModel.Fock.oldIndex depth index)

theorem old_letter_step (depth : Nat) (letter : Fock.Letter depth) :
    Fock.step (depth + 1) (oldLetter depth letter) = Fock.step depth letter := by
  cases letter <;> rfl

theorem old_letter_action (depth : Nat) (letter : Fock.Letter depth) :
    Fock.actions (depth + 1) (oldLetter depth letter) = Fock.actions depth letter :=
  congrArg sourceAction (old_letter_step depth letter)

theorem old_word_run (depth : Nat) (word : List (Fock.Letter depth)) :
    run (Fock.actions (depth + 1)) (word.map (oldLetter depth)) = run (Fock.actions depth) word := by
  induction word with
  | nil => rfl
  | cons letter rest previous =>
      simp only [List.map_cons, run, previous, old_letter_action]

theorem old_observer (depth : Nat) (source : SourceOwnedObservationHistory.Carrier Current)
    (index : FamilyModel.Fock.Index depth) :
    Fock.observer (depth + 1) source (FamilyModel.Fock.oldIndex depth index) = Fock.observer depth source index := by
  change observation (FamilyModel.familyRead (FamilyModel.Fock.reader (depth + 1))) source
    (FamilyModel.Fock.oldIndex depth index) = observation (FamilyModel.familyRead (FamilyModel.Fock.reader depth)) source index
  rw [FamilyModel.observation_family, FamilyModel.observation_family]
  rfl

theorem old_inventory_read (depth : Nat) (source : SourceOwnedObservationHistory.Carrier Current)
    (word : List (Fock.Letter depth)) (index : FamilyModel.Fock.Index depth) :
    inventory (Fock.actions (depth + 1)) (Fock.observer (depth + 1)) source
        (word.map (oldLetter depth)) (FamilyModel.Fock.oldIndex depth index) =
      inventory (Fock.actions depth) (Fock.observer depth) source word index := by
  rw [inventory_apply, inventory_apply, old_word_run]
  exact old_observer depth _ index

end
end SourceGeneratedActionWords.Fock.Dynamic
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
