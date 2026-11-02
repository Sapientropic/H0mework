import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Cut

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Prepaid.Receipt
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (point : View (code := code)) (rule : Distributed.Recall.Information.Agency.Protocol.Rule code)

private theorem initial_state (external : Opponent code) :
    (point.point.target rule external).feedbackState (point.point.targetInput rule external) point.point.cut = Cut.seed point.point :=
  Future.complete_state_before point.point.source point.point.entry point.point.cut
    (Cursor.controller point.point rule external) (term point.point.source point.point.entry point.point.cut rule).val
    point.point.cut (Nat.le_refl _)

private theorem initial_history_length :
    (Cut.seed point.point).history.length = point.point.source.history.length+1+point.point.cut := by
  have actual := congrArg List.length (point.point.source.feedback_keeps_the_complete_actual_history point.point.entry rfl rfl point.point.cut)
  simpa only [Machine.feedbackWords,List.length_append,List.length_cons,List.length_nil,List.length_map,List.length_range] using actual

theorem before_is_the_same_actual_current (external : Opponent code) :
    Replay.before point external rule = (Cut.seed point.point).current := by
  exact ((point.point.target rule external).feedback_body_reads_the_actual_local_current
    (point.point.targetInput rule external) rfl rfl point.point.cut).symm.trans
    (congrArg State.current (initial_state point rule external))

variable (worker : Fin code.sites)
  (owned : Distributed.Recall.Information.Agency.ownerAt code point.point.ownerStart
    (Cut.seed point.point).history.length = some worker)

include owned in
theorem submitted_is_independent_of_the_current_external_opponent
    (first second : Opponent code) : Replay.submitted point first rule = Replay.submitted point second rule := by
  change ((point.point.target rule first).actualExecution (point.point.source.history.length+1+point.point.cut)).submitted =
    ((point.point.target rule second).actualExecution (point.point.source.history.length+1+point.point.cut)).submitted
  rw [(point.point.target rule first).feedback_word_is_actual (point.point.targetInput rule first) rfl rfl point.point.cut,
    (point.point.target rule second).feedback_word_is_actual (point.point.targetInput rule second) rfl rfl point.point.cut,
    initial_state point rule first,initial_state point rule second]
  have left := Execution.policy_at {point.point.source with feedback? := some (point.point.targetInput rule first)}
    point.point.cut (term point.point.source point.point.entry point.point.cut rule).val 0
  have right := Execution.policy_at {point.point.source with feedback? := some (point.point.targetInput rule second)}
    point.point.cut (term point.point.source point.point.entry point.point.cut rule).val 0
  simp only [Nat.add_zero] at left right
  change Feedback.word code ((point.point.target rule first).feedbackPolicy point.point.cut) _ _ =
    Feedback.word code ((point.point.target rule second).feedbackPolicy point.point.cut) _ _
  have policies : (point.point.target rule first).feedbackPolicy point.point.cut =
      (point.point.target rule second).feedbackPolicy point.point.cut := by rw [left,right];rfl
  rw [policies]
  unfold Feedback.word Feedback.decision
  by_cases empty : (Cut.seed point.point).remaining = 0
  · simp only [if_pos empty]
  · simp only [if_neg empty]
    have threshold := initial_history_length point
    simp only [threshold,lt_self_iff_false,if_false]
    rw [show Cursor.controller point.point rule first (Cut.seed point.point).history (Cut.seed point.point).past (Cut.seed point.point).frame =
        Cursor.controller point.point rule second (Cut.seed point.point).history (Cut.seed point.point).past (Cut.seed point.point).frame from
      (own_action_uses_only_its_actual_local_record code point.point.ownerStart rule first second _ _ _ _ worker owned rfl)]


include owned in
theorem activation_is_independent_of_the_current_external_opponent
    (first second : Opponent code) : Cut.Active worker point rule first ↔ Cut.Active worker point rule second := by
  unfold Cut.Active
  rw [show Cursor.controller point.point rule first (Cut.seed point.point).history (Cut.seed point.point).past (Cut.seed point.point).frame =
    Cursor.controller point.point rule second (Cut.seed point.point).history (Cut.seed point.point).past (Cut.seed point.point).frame from
    (own_action_uses_only_its_actual_local_record code point.point.ownerStart rule first second _ _ _ _ worker owned rfl)]

include owned in
theorem a_local_paid_receipt_survives_every_current_adaptive_opponent
    (fee : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
    (first second : Opponent code) (paid : Cut.Ready worker (Replay.inspect worker fee point first)) :
    Cut.Ready worker (Replay.inspect worker fee point second) := by
  cases looked : Replay.inspect worker fee point first with
  | unsupported outside => simp only [looked,Cut.Ready] at paid
  | withheld supported different => simp only [looked,Cut.Ready] at paid
  | refused supported emitted illegal => simp only [looked,Cut.Ready] at paid
  | paid supported emitted legal =>
      have originalActive : Cut.Active worker point (Replay.protocol worker fee supported) first := by
        simpa only [looked,Cut.Ready] using paid
      have otherEmitted : Replay.submitted point second (Replay.protocol worker fee supported) = fee :=
        (submitted_is_independent_of_the_current_external_opponent point (Replay.protocol worker fee supported) worker owned second first).trans emitted
      have otherLegal : Open.Legal code.law (Replay.before point second (Replay.protocol worker fee supported)) fee := by
        rw [before_is_the_same_actual_current point (Replay.protocol worker fee supported) second]
        rw [before_is_the_same_actual_current point (Replay.protocol worker fee supported) first] at legal
        exact legal
      have otherActive := (activation_is_independent_of_the_current_external_opponent point
        (Replay.protocol worker fee supported) worker owned first second).mp originalActive
      simpa only [Replay.inspect,dif_pos supported,dif_pos otherEmitted,dif_pos otherLegal,Cut.Ready] using otherActive

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Prepaid.Receipt
