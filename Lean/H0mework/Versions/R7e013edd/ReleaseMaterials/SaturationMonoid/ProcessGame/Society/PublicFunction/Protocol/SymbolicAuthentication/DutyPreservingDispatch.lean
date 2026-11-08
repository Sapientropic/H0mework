import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DutyOriginStability

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DutyPreservingDispatch
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

-- Only the actual ready inquiry is used: the ambiguous inquiry may legitimately send.
theorem the_actual_ready_recovery_has_no_outgoing_content
    (past : JointResponse.Stages model) (answer : NativeRecoveryMaterial.Ready model start past) :
    StageTransport.outgoing (NativeRecoveryMaterial.row model start past answer) = none := by
  have prepared := answer.prepared
  change WithdrawalState.produce model start (past.map Prod.fst) answer.worker
    (LocalWithdrawal.reading model (EventHistory.execute start past) answer.worker) = .ready answer.value at prepared
  have admitted := WithdrawalState.ready_admission model start _ _ _ answer.value prepared
  have word : WithdrawalInquiry.work model start (past.map Prod.fst) answer.worker
      (LocalWithdrawal.reading model (EventHistory.execute start past) answer.worker) =
      [WithdrawalInquiry.reaffirm model answer.worker, answer.value] := by
    simp only [WithdrawalInquiry.work, prepared, if_pos (And.intro answer.supported answer.capacity)]
  apply DutyOriginStability.an_actual_activation_has_no_outgoing_content _ answer.worker
  simp [NativeRecoveryMaterial.row, NativeRecoveryMaterial.current, NativeRecoveryMaterial.protocol,
    StageTrace.activation, StageTrace.material, StageTrace.capture, Nat.ne_of_gt answer.live,
    answer.owned, localEvent, WithdrawalInquiry.protocol, WithdrawalInquiry.event, prepared,
    word, admitted.2.2.1, LocalWithdrawal.activation]

theorem every_communication_action_preserves_confirmed_content
    (past : JointResponse.Stages model) (action : UnifiedResponse.Action model start vocabulary encoding law past)
    (empty : UnifiedResponse.duties model start vocabulary encoding law past = []) :
    UnifiedResponse.duties model start vocabulary encoding law
      (UnifiedResponse.after model start vocabulary encoding law past action) = [] := by
  cases action with
  | conflict response actual =>
    apply DutyOriginStability.no_outgoing_stage_preserves_confirmed_content vocabulary model start encoding law past _ _ empty
    exact DutyOriginStability.an_actual_activation_has_no_outgoing_content _ response.incident.receiver
      (IncidentResponse.response_uses_the_actual_receivers_owned_activation model start past vocabulary encoding law response _)
  | rejection response actual =>
    apply DutyOriginStability.no_outgoing_stage_preserves_confirmed_content vocabulary model start encoding law past _ _ empty
    exact DutyOriginStability.an_actual_activation_has_no_outgoing_content _ response.receiver
      (RejectionResponse.response_uses_the_actual_receivers_owned_activation model start past vocabulary encoding law response _)
  | retry answer actual =>
    exact False.elim (answer.overdue.unconfirmed
      (DutyOriginStability.empty_duties_mean_every_original_content_is_confirmed vocabulary model start encoding law
        past empty answer.overdue.emission answer.overdue.actual))
  | wait live =>
    exact DutyOriginStability.no_outgoing_stage_preserves_confirmed_content vocabulary model start encoding law past _ _ empty
      (DutyOriginStability.an_actual_quiet_stage_has_no_outgoing_content _ _)

theorem every_original_action_preserves_confirmed_content
    (past : JointResponse.Stages model) (action : JointResponse.Action model start vocabulary encoding law past)
    (empty : UnifiedResponse.duties model start vocabulary encoding law past = []) :
    UnifiedResponse.duties model start vocabulary encoding law
      (JointResponse.after model start vocabulary encoding law past action) = [] := by
  cases action with
  | communication action => exact every_communication_action_preserves_confirmed_content model start vocabulary encoding law past action empty
  | withdrawal ready accepted selected =>
    apply DutyOriginStability.no_outgoing_stage_preserves_confirmed_content vocabulary model start encoding law past _ _ empty
    exact DutyOriginStability.an_actual_activation_has_no_outgoing_content _ ready.receiver
      (NativeReview.the_actual_owner_submits_the_original_member_request model start past ready _).1
  | refused ready denied selected =>
    apply DutyOriginStability.no_outgoing_stage_preserves_confirmed_content vocabulary model start encoding law past _ _ empty
    exact DutyOriginStability.an_actual_activation_has_no_outgoing_content _ ready.receiver
      (NativeReview.the_actual_owner_submits_the_original_member_request model start past ready _).1
  | wait live =>
    exact DutyOriginStability.no_outgoing_stage_preserves_confirmed_content vocabulary model start encoding law past _ _ empty
      (DutyOriginStability.an_actual_quiet_stage_has_no_outgoing_content _ _)

theorem every_actual_dispatch_preserves_confirmed_content
    (past : JointResponse.Stages model) (action : UnifiedRecoveryDispatch.Action model start vocabulary encoding law past)
    (empty : UnifiedResponse.duties model start vocabulary encoding law past = []) :
    UnifiedResponse.duties model start vocabulary encoding law
      (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action) = [] := by
  cases action with
  | original action => exact every_original_action_preserves_confirmed_content model start vocabulary encoding law past action empty
  | recovery answer =>
    exact DutyOriginStability.no_outgoing_stage_preserves_confirmed_content vocabulary model start encoding law past _ _ empty
      (the_actual_ready_recovery_has_no_outgoing_content model start past answer.material)

theorem the_original_mixed_run_generates_persistent_content_confirmation
    (rounds : Nat) (past : JointResponse.Stages model)
    (empty : UnifiedResponse.duties model start vocabulary encoding law past = []) :
    UnifiedResponse.duties model start vocabulary encoding law
      (UnifiedRunPrefix.atCut model start vocabulary encoding law past rounds) = [] := by
  induction rounds generalizing past with
  | zero => simpa only [UnifiedRunPrefix.zero_has_the_original_stages] using empty
  | succ rounds ih =>
    cases actual : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | clear closed => simpa only [UnifiedRunPrefix.atCut, UnifiedRecoveryRun.run, actual] using empty
    | exhausted stopped => simpa only [UnifiedRunPrefix.atCut, UnifiedRecoveryRun.run, actual] using empty
    | advance action =>
      simpa only [UnifiedRunPrefix.atCut, UnifiedRecoveryRun.run, actual] using
        ih (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action)
          (every_actual_dispatch_preserves_confirmed_content model start vocabulary encoding law past action empty)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DutyPreservingDispatch
