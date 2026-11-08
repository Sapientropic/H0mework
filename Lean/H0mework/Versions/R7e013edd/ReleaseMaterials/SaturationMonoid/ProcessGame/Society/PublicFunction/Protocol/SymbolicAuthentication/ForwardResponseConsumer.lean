import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ForwardResponseWindow

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ForwardResponseConsumer
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

theorem an_already_clear_original_cut_is_unchanged_at_every_observation_budget
    (rounds : Nat) (past : JointResponse.Stages model) (clear : JointResponse.Clear model start vocabulary encoding law past) :
    JointResponseRun.run model start vocabulary encoding law rounds past = ⟨past, .jointComplete, []⟩ := by
  cases rounds with
  | zero => simp only [JointResponseRun.run, if_pos clear]
  | succ rounds =>
    have step : JointResponse.step model start vocabulary encoding law past = .clear clear := by
      simp only [JointResponse.step, dif_pos clear]
    simp only [JointResponseRun.run, step]

theorem a_completed_original_run_is_identical_at_every_larger_observation_budget
    (rounds extra : Nat) (past : JointResponse.Stages model)
    (complete : (JointResponseRun.run model start vocabulary encoding law rounds past).status = .jointComplete) :
    JointResponseRun.run model start vocabulary encoding law (rounds + extra) past =
      JointResponseRun.run model start vocabulary encoding law rounds past := by
  induction rounds generalizing past with
  | zero =>
    have clear : JointResponse.Clear model start vocabulary encoding law past := by
      by_contra pending
      simp only [JointResponseRun.run, if_neg pending] at complete
      split at complete <;> contradiction
    rw [an_already_clear_original_cut_is_unchanged_at_every_observation_budget model start vocabulary encoding law _ past clear,
      an_already_clear_original_cut_is_unchanged_at_every_observation_budget model start vocabulary encoding law _ past clear]
  | succ rounds ih =>
    rw [show rounds + 1 + extra = (rounds + extra) + 1 by omega]
    cases actual : JointResponse.step model start vocabulary encoding law past with
    | clear closed => simp only [JointResponseRun.run, actual]
    | exhausted empty => simp only [JointResponseRun.run, actual] at complete; contradiction
    | advance action =>
      simp only [JointResponseRun.run, actual] at complete ⊢
      rw [ih _ complete]

abbrev full (past : JointResponse.Stages model) := (JointResponseRun.produce model start vocabulary encoding law past).stages

instance (history : JointResponse.Stages model) (birth : Nat) :
    Decidable (RejectionService.BirthsWithin model start vocabulary encoding law history birth) := by
  unfold RejectionService.BirthsWithin
  infer_instance

structure Ready (past : JointResponse.Stages model) (birthAllowance : Nat) where
  private mk ::
  reserve : ForwardResponseBudget.deadline model start vocabulary encoding law past ≤ JointResponse.fuel model start past
  compliant : AdaptiveRejectionHistory.Compliant start birthAllowance (full model start vocabulary encoding law past)
  births : RejectionService.BirthsWithin model start vocabulary encoding law (full model start vocabulary encoding law past) past.length
  available : ForwardResponseWindow.Available model start vocabulary encoding law past (full model start vocabulary encoding law past)

inductive Obstruction where
  | sourceReserve | externalEnvelope | lateBirth | localResources
  deriving DecidableEq

inductive Result (past : JointResponse.Stages model) (birthAllowance : Nat) where
  | served (ready : Ready model start vocabulary encoding law past birthAllowance)
  | blocked (reason : Obstruction)

-- The caller supplies neither a schedule, a service row, nor a completion certificate.
def produce (past : JointResponse.Stages model) (birthAllowance : Nat) : Result model start vocabulary encoding law past birthAllowance :=
  if reserve : ForwardResponseBudget.deadline model start vocabulary encoding law past ≤ JointResponse.fuel model start past then
    if compliant : AdaptiveRejectionHistory.check start birthAllowance (full model start vocabulary encoding law past) = true then
      if births : RejectionService.BirthsWithin model start vocabulary encoding law (full model start vocabulary encoding law past) past.length then
        if available : ForwardResponseWindow.Available model start vocabulary encoding law past (full model start vocabulary encoding law past) then
          .served ⟨reserve, (AdaptiveRejectionHistory.check_iff start birthAllowance _).mp compliant, births, available⟩
        else .blocked .localResources
      else .blocked .lateBirth
    else .blocked .externalEnvelope
  else .blocked .sourceReserve

def isServed {past : JointResponse.Stages model} {birthAllowance : Nat} : Result model start vocabulary encoding law past birthAllowance → Bool
  | .served _ => true
  | .blocked _ => false

theorem all_primitive_source_conditions_select_the_success_branch
    (past : JointResponse.Stages model) (birthAllowance : Nat)
    (reserve : ForwardResponseBudget.deadline model start vocabulary encoding law past ≤ JointResponse.fuel model start past)
    (compliant : AdaptiveRejectionHistory.Compliant start birthAllowance (full model start vocabulary encoding law past))
    (births : RejectionService.BirthsWithin model start vocabulary encoding law (full model start vocabulary encoding law past) past.length)
    (available : ForwardResponseWindow.Available model start vocabulary encoding law past (full model start vocabulary encoding law past)) :
    ∃ ready, produce model start vocabulary encoding law past birthAllowance = .served ready := by
  have checked := (AdaptiveRejectionHistory.check_iff start birthAllowance _).mpr compliant
  unfold produce
  rw [dif_pos reserve, dif_pos checked, dif_pos births, dif_pos available]
  exact ⟨_, rfl⟩

theorem the_source_generated_forward_window_reaches_the_original_root_and_own_next
    (past : JointResponse.Stages model) (birthAllowance : Nat)
    (ready : Ready model start vocabulary encoding law past birthAllowance) :
    let history := full model start vocabulary encoding law past
    let final := EventHistory.execute start history
    let runtime := WithdrawalInquiryRuntime.runtime model final
    past <+: history ∧
    UnifiedResponse.rejections model start vocabulary encoding law
      (history.take (past.length + ForwardResponseBudget.deadline model start vocabulary encoding law past)) = [] ∧
    UnifiedResponse.rejections model start vocabulary encoding law history = [] ∧
    StageAccountability.ledger start vocabulary encoding law past <+:
      StageAccountability.ledger start vocabulary encoding law history ∧
    (∀ receiver, (StageReception.run vocabulary encoding law start past receiver past.length).receipts <+:
      (StageReception.run vocabulary encoding law start history receiver history.length).receipts) ∧
    (∀ original : Native.Authority.Challenge (WithdrawalInquiryRuntime.native model final),
      let carried := Mandate.Challenge.through (WithdrawalInquiryRuntime.family model final)
        (WithdrawalInquiryRuntime.sourceIndex model final) original (WithdrawalInquiryRuntime.depth model final + 2)
      carried.state.current.history = carried.state.generated.events) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model final).process.stateAt
      ((WithdrawalInquiryRuntime.facade model final).process.successor runtime.state) := by
  dsimp only
  have deadline := ForwardResponseWindow.primitive_source_conditions_generate_a_forward_rejection_deadline
    model start vocabulary encoding law past birthAllowance ready.reserve ready.compliant ready.births ready.available
  have retained := JointResponseRun.original_incidents_and_confirmations_survive model start vocabulary encoding law past
  have rooted := WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next
    model (EventHistory.execute start (full model start vocabulary encoding law past))
  exact ⟨JointResponseRun.every_run_keeps_the_whole_source_history model start vocabulary encoding law
    (JointResponse.fuel model start past) past, deadline.1, deadline.2, retained.1, retained.2,
    rooted.2.1, rooted.2.2.2.1, rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ForwardResponseConsumer
