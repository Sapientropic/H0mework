import H0mework.Fock.HistoryModel.DynamicBase

/-! Original Family, complete source history and literal next consume dynamic action-word inventory growth. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Dynamic

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalHistory

noncomputable section

theorem dynamic_words_consumed (depth : Nat) :
    (∀ letter : Fock.Letter depth, type_of% (old_letter_action depth letter) ∧
      ∀ value : Complete.Carrier (depth + 1), type_of% (previous_action depth letter value)) ∧
      (∀ word : List (Fock.Letter depth), ∀ value : Complete.Carrier (depth + 1), type_of% (previous_word depth word value) ∧
        ∀ index : FamilyModel.Fock.Index depth, type_of% (previous_word_read depth word index value)) ∧
      (∀ value : Complete.Carrier (depth + 1), type_of% (base_restriction_square depth value) ∧
        ∀ stage, type_of% (previous_prefix depth stage value)) ∧
      type_of% (previous_surjective depth) ∧ type_of% (previous_native_next depth) ∧
      (∀ candidate : Complete.Carrier (depth + 1), type_of% (whole_next_fibre depth candidate)) ∧
      type_of% (Fock.sourceLaw_actual (depth + 1)) ∧ type_of% (full_history_pushforward depth) ∧
      type_of% (actual_next_coarsening depth) ∧
      (∀ supported : previous depth (Complete.nativeNext depth) ∈
        (observed (Fock.sourceLaw (depth + 1)) (Complete.point depth)).support,
        ∀ state : Current, type_of% (conditional_whole_fibre depth supported state)) ∧
      (∀ index : FamilyModel.Fock.Index (depth + 1), type_of% (all_material_actual depth index)) ∧
      (∀ letter : Fock.Letter depth, type_of% (newest_letter_not_old depth letter)) ∧
      type_of% (newest_material_actual depth) ∧ type_of% (fresh_letter_execution depth) ∧
      type_of% (Complete.complete_words_consumed depth) :=
  ⟨(fun letter => ⟨old_letter_action depth letter, previous_action depth letter⟩),
    (fun word value => ⟨previous_word depth word value, fun index => previous_word_read depth word index value⟩),
    (fun value => ⟨base_restriction_square depth value, fun stage => previous_prefix depth stage value⟩),
    previous_surjective depth, previous_native_next depth, whole_next_fibre depth,
    Fock.sourceLaw_actual (depth + 1), full_history_pushforward depth, actual_next_coarsening depth,
    conditional_whole_fibre depth, all_material_actual depth, newest_letter_not_old depth,
    newest_material_actual depth, fresh_letter_execution depth, Complete.complete_words_consumed depth⟩

end
end SourceGeneratedActionWords.Fock.Dynamic
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
