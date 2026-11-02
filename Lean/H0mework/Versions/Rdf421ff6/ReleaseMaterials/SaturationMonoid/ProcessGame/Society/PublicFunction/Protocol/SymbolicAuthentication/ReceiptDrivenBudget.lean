import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenRun
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EagerDelivery

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenBudget
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
  (allowance : Nat)

theorem the_actual_executor_has_a_compliant_callback
    (programme : List (Rule model.source.code)) (past : ReceiptDrivenRun.Stages model) (pending : ReceiptDrivenRun.Mailbox model) :
    ((ReceiptDrivenRun.run model start vocabulary encoding law allowance programme past pending (EagerDelivery.callback start)).inputs.all
      fun input => input.within) = true := by
  induction programme generalizing past pending with
  | nil => rfl
  | cons base tail ih =>
    simp only [ReceiptDrivenRun.run]
    split
    · rfl
    · simp only [EagerDelivery.every_actual_reply_is_within_the_source_communication_domain, List.all_cons, Bool.true_and]
      exact ih _ _

theorem every_compliant_continuation_uses_the_same_source_deviation_budget
    (programme : List (Rule model.source.code)) (past : ReceiptDrivenRun.Stages model) (pending : ReceiptDrivenRun.Mailbox model)
    (rival : Opponent model.source.code)
    (compliant : ((ReceiptDrivenRun.run model start vocabulary encoding law allowance programme past pending rival).inputs.all
      fun input => input.within) = true) :
    InterferenceEnvelope.spent start (ReceiptDrivenRun.run model start vocabulary encoding law allowance programme past pending rival).state.past ≤
      max model.source.code.eventLimit (InterferenceEnvelope.spent start past) := by
  induction programme generalizing past pending with
  | nil => exact Nat.le_max_right _ _
  | cons base tail ih =>
    simp only [ReceiptDrivenRun.run]
    split
    · exact Nat.le_max_right _ _
    · rename_i live
      simp only [ReceiptDrivenRun.run, if_neg live, List.all_cons, Bool.and_eq_true] at compliant
      let queued := FreshReception.queue pending (FreshReception.poll vocabulary encoding law start past)
      let rule := ReceiptDrivenRule.protocol base queued
      have edge := InterferenceEnvelope.a_supported_actual_step_preserves_the_source_interface_bound start past allowance rule
        (InterferenceEnvelope.observe start past allowance rival).admitted
        (InterferenceEnvelope.external_intake_is_idempotent _) (of_decide_eq_true compliant.1)
      have rest := ih _ _ compliant.2
      exact rest.trans (Nat.max_le.mpr ⟨Nat.le_max_left _ _, edge⟩)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenBudget
