import H0mework.Versions.X.Fock.HistoryModel.DynamicMaterial

/-! The generated full-word restriction is the same original Family forgetLast after the old readout. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Dynamic

open SourceGeneratedActionObservationHistory SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed

noncomputable section

theorem base_restriction_square (depth : Nat) (value : Complete.Carrier (depth + 1)) :
    FamilyModel.Fock.forgetLast depth
      (Fock.restrict (depth + 1) (Complete.originalModel (depth + 1) value)) =
      Fock.restrict depth (Complete.originalModel depth (previous depth value)) := by
  obtain ⟨source, rfl⟩ := full_source_surjective (Fock.actions (depth + 1)) (Fock.observer (depth + 1)) (.inl ()) value
  rw [previous_source]
  have newModel := completion_inverse_source (Fock.actions (depth + 1)) (Fock.observer (depth + 1)) (.inl ()) source
  have oldModel := completion_inverse_source (Fock.actions depth) (Fock.observer depth) (.inl ()) source
  change Complete.originalModel (depth + 1)
    (sourceMap (Fock.actions (depth + 1) (.inl ())) (inventory (Fock.actions (depth + 1)) (Fock.observer (depth + 1))) source) =
      projection (Fock.actions (depth + 1)) (Fock.observer (depth + 1)) (.inl ()) source at newModel
  change Complete.originalModel depth
    (sourceMap (Fock.actions depth (.inl ())) (inventory (Fock.actions depth) (Fock.observer depth)) source) =
      projection (Fock.actions depth) (Fock.observer depth) (.inl ()) source at oldModel
  rw [newModel, oldModel]
  change FamilyModel.Fock.forgetLast depth
    (originalRestriction (Fock.actions (depth + 1)) (Fock.observer (depth + 1)) (.inl ())
      (projection (Fock.actions (depth + 1)) (Fock.observer (depth + 1)) (.inl ()) source)) =
    originalRestriction (Fock.actions depth) (Fock.observer depth) (.inl ())
      (projection (Fock.actions depth) (Fock.observer depth) (.inl ()) source)
  rw [originalRestriction_source, originalRestriction_source]
  exact FamilyModel.restriction_projection nativeStep (FamilyModel.Fock.reader (depth + 1)) (FamilyModel.Fock.oldIndex depth) source

end
end SourceGeneratedActionWords.Fock.Dynamic
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
