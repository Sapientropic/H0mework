import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeServiceSource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeServiceTrace
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

structure Entry where
  private mk ::
  past : JointResponse.Stages model
  receipt : NativeServiceSource.Receipt model start vocabulary encoding law past

def here (past : JointResponse.Stages model) : List (Entry model start vocabulary encoding law) :=
  match NativeServiceSource.produce model start vocabulary encoding law past with
  | none => []
  | some receipt => [⟨past, receipt⟩]

def records : Nat → JointResponse.Stages model → List (Entry model start vocabulary encoding law)
  | 0, _ => []
  | rounds + 1, past => match UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | .advance action => here model start vocabulary encoding law past ++
        records rounds (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action)
    | _ => []

abbrev cut (entry : Entry model start vocabulary encoding law) := NativeServiceSource.visit model start entry.past
abbrev full (entry : Entry model start vocabulary encoding law) :=
  UnifiedRecoveryDispatch.after model start vocabulary encoding law entry.past entry.receipt.action

theorem every_service_record_is_on_the_same_actual_mixed_execution
    (rounds : Nat) (past : JointResponse.Stages model) (entry : Entry model start vocabulary encoding law)
    (member : entry ∈ records model start vocabulary encoding law rounds past) :
    past <+: entry.past ∧ full model start vocabulary encoding law entry <+:
      (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages := by
  induction rounds generalizing past with
  | zero => contradiction
  | succ rounds ih =>
    cases selected : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | clear complete => simp only [records, selected, List.not_mem_nil] at member
    | exhausted empty => simp only [records, selected, List.not_mem_nil] at member
    | advance action =>
      simp only [records, selected] at member
      simp only [UnifiedRecoveryRun.run, selected]
      rcases List.mem_append.mp member with first | later
      · unfold here at first
        split at first
        · contradiction
        · have same := List.mem_singleton.mp first
          subst entry
          rename_i receipt generated
          have actionSame : receipt.action = action := UnifiedRecoveryDispatch.Step.advance.inj (receipt.selected.symm.trans selected)
          refine ⟨List.prefix_refl _, ?_⟩
          change UnifiedRecoveryDispatch.after model start vocabulary encoding law past receipt.action <+: _
          rw [actionSame]
          exact UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history model start vocabulary encoding law rounds _
      · have next := ih _ later
        exact ⟨(UnifiedRecoveryDispatch.every_action_keeps_the_whole_actual_history model start vocabulary encoding law past action).trans next.1, next.2⟩

theorem every_record_has_a_distinct_completed_service_visit (rounds : Nat) (past : JointResponse.Stages model) :
    ((records model start vocabulary encoding law rounds past).map (cut model start vocabulary encoding law)).Nodup := by
  induction rounds generalizing past with
  | zero => exact List.nodup_nil
  | succ rounds ih =>
    cases selected : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | clear complete => simp only [records, selected, List.map_nil]; exact List.nodup_nil
    | exhausted empty => simp only [records, selected, List.map_nil]; exact List.nodup_nil
    | advance action =>
      simp only [records, selected]
      unfold here
      split
      · simp only [List.nil_append]; exact ih _
      · rename_i receipt generated
        simp only [List.singleton_append, List.map_cons]
        apply List.nodup_cons.mpr
        refine ⟨?_, ih _⟩
        intro repeated
        obtain ⟨entry, member, same⟩ := List.mem_map.mp repeated
        have ordered := (every_service_record_is_on_the_same_actual_mixed_execution model start vocabulary encoding law rounds
          (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action) entry member).1.length_le
        have length := (NativeServiceSource.every_record_is_one_actual_native_stage model start vocabulary encoding law past receipt).1
        have actionSame : receipt.action = action := UnifiedRecoveryDispatch.Step.advance.inj (receipt.selected.symm.trans selected)
        rw [actionSame] at length
        have before := IncidentChallenge.execution_advances_the_actual_boundary model start past
        have after := IncidentChallenge.execution_advances_the_actual_boundary model start entry.past
        change EventStep.boundary (EventHistory.execute start entry.past) = EventStep.boundary (EventHistory.execute start past) at same
        omega

theorem every_record_is_inside_the_actual_completed_window
    (rounds : Nat) (past : JointResponse.Stages model) (entry : Entry model start vocabulary encoding law)
    (member : entry ∈ records model start vocabulary encoding law rounds past) :
    UnifiedInventoryBudget.first model start past ≤ cut model start vocabulary encoding law entry ∧
      cut model start vocabulary encoding law entry < EventStep.boundary (UnifiedInventorySource.final model start vocabulary encoding law rounds past) := by
  have retained := every_service_record_is_on_the_same_actual_mixed_execution model start vocabulary encoding law rounds past entry member
  have initial := IncidentChallenge.execution_advances_the_actual_boundary model start past
  have middle := IncidentChallenge.execution_advances_the_actual_boundary model start entry.past
  have last := IncidentChallenge.execution_advances_the_actual_boundary model start
    (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages
  have single := (NativeServiceSource.every_record_is_one_actual_native_stage model start vocabulary encoding law entry.past entry.receipt).1
  have lower := retained.1.length_le
  have upper := retained.2.length_le
  change (UnifiedRecoveryDispatch.after model start vocabulary encoding law entry.past entry.receipt.action).length ≤ _ at upper
  dsimp only [UnifiedInventoryBudget.first, cut, NativeServiceSource.visit, UnifiedInventorySource.final]
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeServiceTrace
