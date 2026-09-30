import H0mework.Versions.X.Fock.HistoryModel.DynamicPrevious

/-! The new complete word inventory preserves every old letter and the literal native next before its fibre is read. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Dynamic

open SourceGeneratedActionObservationHistory SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem previous_action (depth : Nat) (letter : Fock.Letter depth) (value : Complete.Carrier (depth + 1)) :
    previous depth (Complete.action (depth + 1) (oldLetter depth letter) value) =
      Complete.action depth letter (previous depth value) := by
  obtain ⟨source, rfl⟩ := full_source_surjective (Fock.actions (depth + 1)) (Fock.observer (depth + 1)) (.inl ()) value
  change previous depth
    (completeAdvance (Fock.actions (depth + 1)) (Fock.observer (depth + 1)) (.inl ()) (oldLetter depth letter)
      (sourceMap (Fock.actions (depth + 1) (.inl ())) (inventory (Fock.actions (depth + 1)) (Fock.observer (depth + 1))) source)) = _
  rw [complete_advance_source, previous_source, old_letter_action, previous_source, complete_advance_source]

theorem previous_word (depth : Nat) (word : List (Fock.Letter depth)) (value : Complete.Carrier (depth + 1)) :
    previous depth (run (Complete.action (depth + 1)) (word.map (oldLetter depth)) value) =
      run (Complete.action depth) word (previous depth value) := by
  induction word generalizing value with
  | nil => rfl
  | cons letter rest previousLaw =>
      change previous depth (run (Complete.action (depth + 1)) (rest.map (oldLetter depth))
        (Complete.action (depth + 1) (oldLetter depth letter) value)) = _
      rw [previousLaw, previous_action]
      rfl

theorem previous_native_next (depth : Nat) :
    previous depth (Complete.nativeNext depth) =
      Complete.action depth (.inl ()) (Complete.point depth ((runtimeAt depth).current.visit.current : Current)) := by
  let state : Current := (runtimeAt depth).current.visit.current
  exact (previous_action depth (.inl ()) (Complete.point (depth + 1) state)).trans
    (congrArg (Complete.action depth (.inl ())) (previous_point depth state))

theorem whole_next_fibre (depth : Nat) (candidate : Complete.Carrier (depth + 1)) :
    previous depth candidate =
        Complete.action depth (.inl ()) (Complete.point depth ((runtimeAt depth).current.visit.current : Current)) ↔
      candidate - Complete.nativeNext depth ∈ LinearMap.ker (previous depth) := by
  rw [LinearMap.mem_ker, map_sub, previous_native_next, sub_eq_zero]

end
end SourceGeneratedActionWords.Fock.Dynamic
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
