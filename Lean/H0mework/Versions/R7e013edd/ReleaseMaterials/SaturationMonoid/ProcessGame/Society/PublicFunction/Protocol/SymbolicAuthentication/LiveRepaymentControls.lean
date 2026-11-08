import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveRepaymentConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveSupplySynthesisControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 240000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveRepaymentControls
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open LiveSupplySynthesisSource (Emitter Word current)
open LiveRepaymentSource
noncomputable section
abbrev old := AtomicWorkControls.old
abbrev oldDelivery : Opponent old := fun _ _ _ => some ⟨.deliver 0,by decide +kernel⟩
abbrev paidPast := AtomicWorkControls.past ++ [(SilentWindow.quiet,oldDelivery)]
abbrev saved := EventHistory.execute AtomicWorkControls.start paidPast
theorem original : saved.side = .original := rfl
abbrev active := code old saved
abbrev silent : Opponent active := EventStep.fixed none
abbrev production := row old saved true silent
abbrev repaid := next old saved true silent
abbrev priorLaw : StageReception.Law old := ⟨fun _ _ => ActualRoundNetworkSource.scope AtomicWorkControls.net,3⟩
abbrev priorReceipt := StageReception.run AtomicWorkControls.vocabulary AtomicWorkControls.encoding priorLaw
  AtomicWorkControls.start paidPast 0 paidPast.length

theorem actual_supply_and_original_repayment_share_one_live_occurrence :
    offer old saved = some LiveSupplySynthesisSource.donorCycle ∧ assess old saved true silent = .executed ∧
      production.submitted.length = 12 ∧
      production.after.current.claims () 1 2 < production.before.current.claims () 1 2 ∧
      production.after.current.stock 1 .service = 0 ∧
      production.after.current.stock 0 .energy = production.before.current.stock 0 .energy - 1 ∧
      production.after.current.stock 0 .labor = production.before.current.stock 0 .labor - 1 ∧
      production.after.current.stock 1 .waste = production.before.current.stock 1 .waste - 1 ∧
      production.after.current.clock = production.before.current.clock + 1 ∧
      production.after.frame.sent = production.before.frame.sent ∧
      (production.after.frame.inbox 0).val = 1 ∧
      priorReceipt.receipts.length = 1 ∧ (production.before.frame.inbox 0).val = 2 := by
  and_intros <;> decide +kernel

theorem prior_nonempty : priorReceipt.receipts ≠ [] := by
  intro empty
  have size := actual_supply_and_original_repayment_share_one_live_occurrence.2.2.2.2.2.2.2.2.2.2.2.1
  rw [empty] at size
  contradiction
abbrev deliveredReceipt := priorReceipt.receipts.head prior_nonempty
abbrev priorNativeDelivery := StageReception.receipt_has_actual_send_delivery_and_owned_ballot_origin
  AtomicWorkControls.vocabulary AtomicWorkControls.encoding priorLaw AtomicWorkControls.start paidPast
  0 paidPast.length deliveredReceipt (List.head_mem prior_nonempty)

abbrev paymentStatement := Settlement.issuedAt active.law production.before.current production.submitted 11
theorem the_original_payment_classifier_reads_the_actual_new_word : paymentStatement.isSome = true := by decide +kernel
abbrev statement := paymentStatement.get the_original_payment_classifier_reads_the_actual_new_word
abbrev paymentEffects := Settlement.issued_payment_has_actual_material_and_claim_effects active.law
  production.before.current production.submitted 11 statement (Option.some_get _).symm
abbrev actualDebt := LiveRepaymentConsumer.executed_repayment_strictly_reduces_the_same_original_debt
  old saved true silent original actual_supply_and_original_repayment_share_one_live_occurrence.2.1
abbrev actualLedger := LiveRepaymentConsumer.the_final_native_ledger_consumes_the_actual_repayment old saved true silent
abbrev withheld := row old saved false silent
abbrev followingCode := code active repaid
abbrev followingSilent : Opponent followingCode := EventStep.fixed none
theorem withholding_and_later_material_shortage_keep_the_original_debt :
    assess old saved false silent = .withheld ∧ withheld.submitted = [] ∧
      withheld.after.current.claims () 1 2 = withheld.before.current.claims () 1 2 ∧
      0 < (current active repaid).claims () 1 2 ∧ offer active repaid = none ∧
      assess active repaid true followingSilent = .withheld := by
  and_intros <;> decide +kernel

-- The opposite ordering is also executed: repayment consumes the liquidity
-- needed by the later delivery, so a paid principal is not a receipt.
abbrev pending := AtomicWorkControls.oldWaited
abbrev pendingCode := code old pending
abbrev pendingSilent : Opponent pendingCode := EventStep.fixed none
abbrev pendingExtra := AtomicWorkSource.catalogue old (batch old pending)
abbrev pendingWork := AtomicWorkSource.protocol old (batch old pending) (submit old pending true)
abbrev laterDelivery : Opponent pendingCode := fun _ _ _ => some ⟨.deliver 0,by
  exact List.mem_append_left _ (by decide +kernel)⟩
abbrev pendingStages := [(pendingWork,pendingSilent),(SilentWindow.quiet,laterDelivery)]
abbrev pendingLaw : StageReception.Law pendingCode := ⟨fun _ _ => ActualRoundNetworkSource.scope AtomicWorkControls.net,3⟩
abbrev unpaidDelivery := CatalogueHandoffConsumer.run AtomicWorkControls.start AtomicWorkControls.fullPast
  pendingExtra AtomicWorkControls.handoffOriginal AtomicWorkControls.vocabulary AtomicWorkControls.encoding
  pendingLaw pendingStages 0 AtomicWorkControls.origin 2
theorem actual_repayment_does_not_manufacture_the_missing_delivery_fee :
    assess old pending true pendingSilent = .executed ∧ unpaidDelivery.receipts = [] ∧
      (row old pending true pendingSilent).after.current.claims () 1 2 <
        (row old pending true pendingSilent).before.current.claims () 1 2 := by
  and_intros <;> decide +kernel

abbrev extra := AtomicWorkSource.catalogue old (batch old saved)
abbrev stages := [(AtomicWorkSource.protocol old (batch old saved) (submit old saved true),silent)]
abbrev financialPrefix := CatalogueHandoffSource.completeFinancialPrefix old extra saved original stages
def bound : Native.Authority.Bound (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
    (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit) :=
  ⟨AtomicWorkControls.net.entry.bound.base,AtomicWorkControls.net.entry.bound.scope,
    (start old saved).source,AtomicWorkControls.net.entry.bound.law_exact,AtomicWorkControls.net.entry.bound.task_exact⟩
abbrev native := StageRuntime.the_final_root_consumes_actual_budget_native_responsibility_ledger_and_next
  bound (start old saved) stages AtomicWorkControls.vocabulary
def pendingBound : Native.Authority.Bound (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
    (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit) :=
  ⟨AtomicWorkControls.net.entry.bound.base,AtomicWorkControls.net.entry.bound.scope,
    (start old pending).source,AtomicWorkControls.net.entry.bound.law_exact,AtomicWorkControls.net.entry.bound.task_exact⟩
abbrev failedDeliveryNative := StageRuntime.the_final_root_consumes_actual_budget_native_responsibility_ledger_and_next
  pendingBound (start old pending) pendingStages AtomicWorkControls.vocabulary
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveRepaymentControls
