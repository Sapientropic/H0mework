import H0mework.Fock.HistoryModel.RecordedWhole

/-! The recorded native word advances the recovered historical actor to the existing acquisition normal target. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery SourcePrimeCalculation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem actualWord_native (depth start steps : Nat) :
    Fock.actualWord depth (List.replicate steps (.inl ()))
      ((runtimeAt start).current.visit.current : Current) =
        ((runtimeAt (start + steps)).current.visit.current : Current) := by
  induction steps generalizing start with
  | zero => rfl
  | succ steps previous =>
      change Fock.actualWord depth (List.replicate steps (.inl ()))
        ((runtimeAt (start + 1)).current.visit.current : Current) = _
      exact (previous (start + 1)).trans (congrArg (fun position : Nat =>
        ((runtimeAt position).current.visit.current : Current)) (by omega))

theorem complete_word_point (depth : Nat) (word : List (Fock.Letter depth)) (current : Current) :
    run (Complete.action depth) word (Complete.point depth current) =
      Complete.point depth (Fock.actualWord depth word current) :=
  (complete_run_source (Fock.actions depth) (Fock.observer depth) (.inl ()) word (sourcePoint current)).trans
    (congrArg (sourceMap (Fock.actions depth (.inl ())) (inventory (Fock.actions depth) (Fock.observer depth)))
      (word_sourcePoint depth word current))

theorem whole_at_acquisition_normal (depth bound : Nat) :
    run (Complete.action depth) (List.replicate (windowBound sourceOwner bound) (.inl ()))
      ((originalField depth).symm (whole depth bound (recordedQuery bound (Fin.last bound)))) =
        Complete.point depth ((normal bound).targetRuntime.current.visit.current : Current) := by
  let current : Current := (runtimeAt (bound + 1)).current.visit.current
  have restored : (originalField depth).symm (whole depth bound (recordedQuery bound (Fin.last bound))) =
      Complete.point depth current :=
    (congrArg (originalField depth).symm
      ((whole_recorded depth bound (Fin.last bound)).trans (next_read_actual depth bound (Fin.last bound)))).trans
      ((originalField depth).symm_apply_apply _)
  have count : bound + 1 + windowBound sourceOwner bound = completionDepth sourceOwner bound + 1 := by
    unfold completionDepth
    omega
  have target : ((runtimeAt (bound + 1 + windowBound sourceOwner bound)).current.visit.current : Current) =
      ((normal bound).targetRuntime.current.visit.current : Current) :=
    (congrArg (fun position : Nat => ((runtimeAt position).current.visit.current : Current)) count).trans
      (congrArg (fun runtime : LivingRuntimeState process => (runtime.current.visit.current : Current)) (target_is_original bound)).symm
  rw [restored, complete_word_point]
  exact congrArg (Complete.point depth) ((actualWord_native depth (bound + 1) (windowBound sourceOwner bound)).trans target)

theorem original_field_at_acquisition_normal (depth bound : Nat) :
    originalField depth
      (run (Complete.action depth) (List.replicate (windowBound sourceOwner bound) (.inl ()))
        ((originalField depth).symm (whole depth bound (recordedQuery bound (Fin.last bound))))) =
      fieldPoint nativeStep (rawWords depth) ((normal bound).targetRuntime.current.visit.current : Current) :=
  (congrArg (originalField depth) (whole_at_acquisition_normal depth bound)).trans (original_point depth _)

theorem recovered_actor_before_normal (bound : Nat) (actor : Fin (bound + 1)) :
    actor.val + 1 < (normal bound).targetRuntime.state := by
  rw [target_is_original, runtimeAt_state]
  have inside := actor.isLt
  unfold completionDepth windowBound
  omega

theorem acquisition_stage_count (bound : Nat) :
    (frontier bound).stageCount + 1 = bound + windowBound sourceOwner bound + 1 := rfl

theorem canonical_next_after_records (bound : Nat) :
    let position := completionDepth sourceOwner bound + 1
    let depth := position + 1
    Complete.action depth (.inl ())
      (run (Complete.action depth) (List.replicate (windowBound sourceOwner bound) (.inl ()))
        ((originalField depth).symm (whole depth bound (recordedQuery bound (Fin.last bound))))) =
      Complete.nativeNext position := by
  let depth := completionDepth sourceOwner bound + 1 + 1
  have acquired := whole_at_acquisition_normal depth bound
  have current := congrArg (fun runtime : LivingRuntimeState process =>
    Complete.point depth (runtime.current.visit.current : Current)) (target_is_original bound)
  exact (congrArg (Complete.action depth (.inl ())) acquired).trans
    (congrArg (Complete.action depth (.inl ())) current)

end
end SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
