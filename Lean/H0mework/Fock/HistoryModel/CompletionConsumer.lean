import H0mework.Fock.HistoryModel.CompletionMixture

/-! Full completed word operations feed the existing Family mixture, material and literal next. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Complete

open SourceGeneratedActionObservationHistory SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime

noncomputable section

theorem word_original_model (depth : Nat) (word : List (Fock.Letter depth)) (value : Carrier depth) :
    originalModel depth (run (action depth) word value) =
      run (Fock.letterAction depth) word (originalModel depth value) :=
  complete_run_model (Fock.actions depth) (Fock.observer depth) (.inl ()) word value

theorem complete_word_material (depth : Nat) (word : List (Fock.Letter (depth + 1))) (index : FamilyModel.Fock.Index (depth + 1)) :
    FamilyModel.Fock.readout (depth + 1)
      (Fock.restrict (depth + 1) (originalModel (depth + 1) (run (action (depth + 1)) word (nativeNext depth)))) index =
      sourceStateAt (NativeCopy.copy (NativeCopy.Fock.material (depth + 1) index)
        (Fock.actualWord (depth + 1) word (runtimeAt depth).tick.next.current.visit.current)) := by
  rw [word_original_model, next_original_model]
  exact (Fock.native_word_information depth).2.2.1 word index

theorem complete_words_consumed (depth : Nat) :
    type_of% (original_fibre depth) ∧
      (∀ word : List (Fock.Letter (depth + 1)), ∀ index : FamilyModel.Fock.Index (depth + 1),
        type_of% (complete_word_material depth word index)) ∧
      type_of% (next_mixture_original depth) ∧ type_of% (original_mixture_complete_next depth) ∧
      type_of% (next_actual depth) ∧ type_of% (Fock.native_word_information depth) :=
  ⟨original_fibre depth, complete_word_material depth, next_mixture_original depth,
    original_mixture_complete_next depth, next_actual depth, Fock.native_word_information depth⟩

end
end SourceGeneratedActionWords.Fock.Complete

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
