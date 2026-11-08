import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedRecoveryRun

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedRecoveryTrace
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

def isRecovery : UnifiedRecoveryDispatch.Kind → Bool
  | .recovery => true
  | .original _ => false

theorem every_record_is_on_the_same_actual_execution
    (rounds : Nat) (past : JointResponse.Stages model)
    (entry : UnifiedRecoveryRun.RecoveryEvent model start vocabulary encoding law)
    (member : entry ∈ (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).recoveries) :
    past <+: entry.past ∧ NativeRecovery.full model start entry.past vocabulary encoding law entry.answer <+:
      (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages := by
  induction rounds generalizing past with
  | zero => simp only [UnifiedRecoveryRun.run] at member; split_ifs at member <;> contradiction
  | succ rounds ih =>
    cases actual : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | clear complete => simp only [UnifiedRecoveryRun.run, actual] at member; contradiction
    | exhausted empty => simp only [UnifiedRecoveryRun.run, actual] at member; contradiction
    | advance action =>
      simp only [UnifiedRecoveryRun.run, actual] at member ⊢
      rcases List.mem_append.mp member with here | later
      · cases action with
        | original action => simp only [UnifiedRecoveryRun.events, List.not_mem_nil] at here
        | recovery answer =>
          simp only [UnifiedRecoveryRun.events, List.mem_singleton] at here
          subst entry
          exact ⟨List.prefix_refl _, UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history model start vocabulary encoding law rounds _⟩
      · have next := ih (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action) later
        exact ⟨(UnifiedRecoveryDispatch.every_action_keeps_the_whole_actual_history model start vocabulary encoding law past action).trans next.1, next.2⟩

theorem the_original_recovery_records_are_exactly_the_recovery_trace_steps
    (rounds : Nat) (past : JointResponse.Stages model) :
    (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).recoveries.length =
      ((UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).trace.filter isRecovery).length := by
  induction rounds generalizing past with
  | zero => simp only [UnifiedRecoveryRun.run]; split_ifs <;> rfl
  | succ rounds ih =>
    cases actual : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | clear complete => simp only [UnifiedRecoveryRun.run, actual]; rfl
    | exhausted empty => simp only [UnifiedRecoveryRun.run, actual]; rfl
    | advance action =>
      have next := ih (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action)
      cases action <;> simpa only [UnifiedRecoveryRun.run, actual, UnifiedRecoveryRun.events, UnifiedRecoveryDispatch.kind,
        List.nil_append, List.singleton_append, List.length_cons, List.filter_cons, isRecovery, Bool.false_eq_true,
        ↓reduceIte] using (by omega : _)

theorem the_complete_source_bounds_the_actual_recovery_journal
    (rounds : Nat) (past : JointResponse.Stages model) :
    (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).recoveries.length ≤ JointResponse.fuel model start past := by
  rw [the_original_recovery_records_are_exactly_the_recovery_trace_steps]
  exact (List.length_filter_le _ _).trans
    (UnifiedRecoveryRun.every_unified_macro_is_paid_from_the_same_source_fuel model start vocabulary encoding law rounds past)

theorem every_record_is_one_actual_stage_with_two_paid_items
    (entry : UnifiedRecoveryRun.RecoveryEvent model start vocabulary encoding law) :
    (NativeRecovery.full model start entry.past vocabulary encoding law entry.answer).length = entry.past.length + 1 ∧
    (StageTrace.items (NativeRecoveryMaterial.row model start entry.past entry.answer.material)).length = 2 ∧
    (∀ item ∈ StageTrace.items (NativeRecoveryMaterial.row model start entry.past entry.answer.material),
      model.source.code.law.Valid item.before item.request) := by
  exact ⟨by simp only [NativeRecovery.full, NativeRecoveryMaterial.full, List.length_append, List.length_singleton],
    NativeRecoveryMaterial.the_actual_row_has_exactly_two_items model start entry.past entry.answer.material,
    NativeRecovery.the_recovery_word_has_actual_validity_for_every_original_item model start entry.past vocabulary encoding law entry.answer⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedRecoveryTrace
