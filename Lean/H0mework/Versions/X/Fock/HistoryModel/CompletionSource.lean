import H0mework.Realization.ObservationActions.WordsCompletionRestriction
import H0mework.Versions.X.Fock.HistoryModel.ConditionalWords

/-! The original Family's actual source letters now generate their unchanged complete word occurrence. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Complete

open SourceGeneratedActionObservationHistory SourceOwnedObservationHistory
open SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

abbrev Carrier (depth : Nat) := completion (Fock.actions depth (.inl ())) (inventory (Fock.actions depth) (Fock.observer depth))

def point (depth : Nat) (state : Current) : Carrier depth :=
  sourceMap (Fock.actions depth (.inl ())) (inventory (Fock.actions depth) (Fock.observer depth)) (sourcePoint state)

abbrev action (depth : Nat) := completeAdvance (Fock.actions depth) (Fock.observer depth) (.inl ())

def originalModel (depth : Nat) : Carrier depth →ₗ[ℤ] Fock.WholeModel depth :=
  (completionEquiv (Fock.actions depth) (Fock.observer depth) (.inl ())).symm.toLinearMap

theorem original_model_point (depth : Nat) (state : Current) : originalModel depth (point depth state) = Fock.point depth state :=
  completion_inverse_source (Fock.actions depth) (Fock.observer depth) (.inl ()) (sourcePoint state)

theorem action_point (depth : Nat) (letter : Fock.Letter depth) (state : Current) :
    action depth letter (point depth state) = point depth (Fock.step depth letter state) := by
  change completeAdvance (Fock.actions depth) (Fock.observer depth) (.inl ()) letter
    (sourceMap (Fock.actions depth (.inl ())) (inventory (Fock.actions depth) (Fock.observer depth)) (sourcePoint state)) = _
  rw [complete_advance_source]
  exact congrArg (sourceMap (Fock.actions depth (.inl ())) (inventory (Fock.actions depth) (Fock.observer depth)))
    (sourceAction_point (Fock.step depth letter) state)

def nativeNext (depth : Nat) : Carrier (depth + 1) :=
  action (depth + 1) (.inl ()) (point (depth + 1) ((runtimeAt depth).current.visit.current : Current))

theorem next_original_model (depth : Nat) : originalModel (depth + 1) (nativeNext depth) = Fock.nextValue depth := by
  let state : Current := (runtimeAt depth).current.visit.current
  exact (congrArg (originalModel (depth + 1)) (action_point (depth + 1) (.inl ()) state)).trans
    ((original_model_point (depth + 1) (Fock.step (depth + 1) (.inl ()) state)).trans
      (Fock.action_point (depth + 1) (.inl ()) state).symm)

theorem next_actual (depth : Nat) :
    nativeNext depth = point (depth + 1) ((runtimeAt depth).tick.next.current.visit.current : Current) := by
  apply (completionEquiv (Fock.actions (depth + 1)) (Fock.observer (depth + 1)) (.inl ())).symm.injective
  exact (next_original_model depth).trans ((Fock.nextValue_is_source depth).trans
    (original_model_point (depth + 1) ((runtimeAt depth).tick.next.current.visit.current : Current)).symm)

theorem original_fibre (depth : Nat) :
    Fock.restrict (depth + 1) (originalModel (depth + 1) (nativeNext depth)) =
      (FamilyModel.Fock.realizedNext depth).val := by
  rw [next_original_model]
  exact Fock.nextValue_is_original_fibre depth

end
end SourceGeneratedActionWords.Fock.Complete
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
