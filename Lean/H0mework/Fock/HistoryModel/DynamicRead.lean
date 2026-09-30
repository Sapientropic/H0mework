import H0mework.Fock.HistoryModel.DynamicAction

/-! The complete old word prefix is preserved, and the actual new material index remains present. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Dynamic

open SourceGeneratedActionObservationHistory SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem previous_prefix (depth stage : Nat) (value : Complete.Carrier (depth + 1)) :
    stageRead (Fock.actions depth (.inl ())) (inventory (Fock.actions depth) (Fock.observer depth)) stage (previous depth value) =
      fun index => readPrevious depth
        (stageRead (Fock.actions (depth + 1) (.inl ()))
          (inventory (Fock.actions (depth + 1)) (Fock.observer (depth + 1))) stage value index) := by
  obtain ⟨source, rfl⟩ := full_source_surjective (Fock.actions (depth + 1)) (Fock.observer (depth + 1)) (.inl ()) value
  rw [previous_source, source_reads_prefix, source_reads_prefix]
  funext time word index
  exact (old_inventory_read depth ((Fock.actions depth (.inl ()) ^ time.val) source) word index).symm

theorem previous_word_read (depth : Nat) (word : List (Fock.Letter depth)) (index : FamilyModel.Fock.Index depth)
    (value : Complete.Carrier (depth + 1)) :
    completeRead (Fock.actions depth) (Fock.observer depth) (.inl ()) word (previous depth value) index =
      completeRead (Fock.actions (depth + 1)) (Fock.observer (depth + 1)) (.inl ())
        (word.map (oldLetter depth)) value (FamilyModel.Fock.oldIndex depth index) := by
  rw [complete_read_is_actual, complete_read_is_actual, previous_prefix]
  rfl

theorem newest_not_old (depth : Nat) (index : FamilyModel.Fock.Index depth) :
    FamilyModel.Fock.newestIndex depth ≠ FamilyModel.Fock.oldIndex depth index := by
  intro same
  have values := congrArg Fin.val same
  change NativeWindow.bound (runtimeAt (depth + 1)).current.visit.current = index.val at values
  have old := runtime_bound depth
  have new := runtime_bound (depth + 1)
  have inside := index.isLt
  omega

end
end SourceGeneratedActionWords.Fock.Dynamic
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
