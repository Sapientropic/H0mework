import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveJointRepaymentConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveRepaymentControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 240000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveJointRepaymentControls
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open LiveSupplySynthesisSource (Emitter Word current)
open LiveJointRepaymentSource
noncomputable section
abbrev old := AtomicWorkControls.old
abbrev saved := AtomicWorkControls.oldWaited
abbrev active := code old saved
abbrev silent : Opponent active := EventStep.fixed none
abbrev production := row old saved true silent
abbrev generated := next old saved true silent

theorem the_same_live_source_now_pays_principal_and_preserves_transport_liquidity :
    addresses old saved = [0] ∧ offer old saved = some LiveSupplySynthesisSource.donorCycle ∧
      assess old saved true silent = .executed ∧ production.submitted.length = 12 ∧
      reserve old saved LiveSupplySynthesisSource.donorCycle = 1 ∧
      0 < quantity old saved LiveSupplySynthesisSource.donorCycle ∧
      quantity old saved LiveSupplySynthesisSource.donorCycle <
        Repayment.quantity old.law LiveRepaymentSource.position
          (LiveRepaymentSource.intermediate old saved LiveSupplySynthesisSource.donorCycle) ∧
      production.after.current.claims () 1 2 < production.before.current.claims () 1 2 ∧
      1 ≤ production.after.current.stock 1 .service ∧
      production.after.current.clock = production.before.current.clock + 1 ∧
      production.after.frame.sent = production.before.frame.sent := by
  and_intros <;> decide +kernel

abbrev extra := AtomicWorkSource.catalogue old (batch old saved)
abbrev work := AtomicWorkSource.protocol old (batch old saved) (submit old saved true)
abbrev delivery : Opponent active := fun _ _ _ => some ⟨.deliver 0,by
  exact List.mem_append_left _ (by decide +kernel)⟩
abbrev stages := [(work,silent),(SilentWindow.quiet,delivery)]
abbrev law : StageReception.Law active := ⟨fun _ _ => ActualRoundNetworkSource.scope AtomicWorkControls.net,3⟩
abbrev received := CatalogueHandoffConsumer.run AtomicWorkControls.start AtomicWorkControls.fullPast extra
  AtomicWorkControls.handoffOriginal AtomicWorkControls.vocabulary AtomicWorkControls.encoding law stages 0 AtomicWorkControls.origin 2
abbrev final := EventHistory.execute (start old saved) stages
theorem actual_repayment_then_old_delivery_share_the_original_debt_and_receipt :
    received.receipts = [AtomicWorkControls.receipt] ∧
      received.audit.length = 2 ∧
      (EventStep.seed final).current.claims () 1 2 = production.after.current.claims () 1 2 ∧
      (EventStep.seed final).current.stock 1 .service = 0 ∧
      LiveRepaymentControls.unpaidDelivery.receipts = [] := by
  and_intros <;> decide +kernel

abbrev actualDebtAndFees := LiveJointRepaymentConsumer.actual_repayment_and_fee_capacity_share_the_same_next
  old saved true silent AtomicWorkControls.waitedOriginal
  the_same_live_source_now_pays_principal_and_preserves_transport_liquidity.2.2.1
abbrev actualLedger := LiveJointRepaymentConsumer.all_future_stages_retain_the_actual_financial_visit
  old saved true silent
abbrev actualDelivery := CatalogueHandoffConsumer.receipt_consumes_the_new_native_delivery
  AtomicWorkControls.start AtomicWorkControls.fullPast extra AtomicWorkControls.handoffOriginal
  AtomicWorkControls.vocabulary AtomicWorkControls.encoding law stages 0 AtomicWorkControls.origin 2
  AtomicWorkControls.receipt (by
    rw [actual_repayment_then_old_delivery_share_the_original_debt_and_receipt.1]
    exact List.mem_singleton_self _)
abbrev paymentStatement := Settlement.issuedAt active.law production.before.current production.submitted 11
theorem actual_settlement_is_classified_by_the_original_payment_source : paymentStatement.isSome = true := by decide +kernel
abbrev statement := paymentStatement.get actual_settlement_is_classified_by_the_original_payment_source
abbrev paymentEffects := Settlement.issued_payment_has_actual_material_and_claim_effects active.law
  production.before.current production.submitted 11 statement (Option.some_get _).symm

abbrev withheld := row old saved false silent
abbrev absent := CatalogueHandoffConsumer.run AtomicWorkControls.start AtomicWorkControls.fullPast extra
  AtomicWorkControls.handoffOriginal AtomicWorkControls.vocabulary AtomicWorkControls.encoding law
  [(work,silent),(SilentWindow.quiet,silent)] 0 AtomicWorkControls.origin 2
abbrev deliveryRow := StageTrace.material generated SilentWindow.quiet delivery
abbrev check := CatalogueHandoffConsumer.check AtomicWorkControls.start AtomicWorkControls.fullPast extra AtomicWorkControls.vocabulary
abbrev late : StageReception.Law active := ⟨law.scope,0⟩
abbrev stale : StageReception.Law active := ⟨fun _ _ => {ActualRoundNetworkSource.scope AtomicWorkControls.net with epoch := 0},3⟩
abbrev wrongSigner : StageTransport.Wire (code := old) :=
  {AtomicWorkControls.wire with ballot := {AtomicWorkControls.wire.ballot with actor := 0}}
theorem reservation_does_not_manufacture_delivery_or_authentication :
    assess old saved false silent = .withheld ∧ withheld.submitted = [] ∧
      withheld.after.current.claims () 1 2 = withheld.before.current.claims () 1 2 ∧
      absent.receipts = [] ∧
      check AtomicWorkControls.encoding law 0 deliveryRow [] wrongSigner = .rejected .unauthenticated ∧
      check AtomicWorkControls.encoding late 0 deliveryRow [] AtomicWorkControls.wire = .rejected .late ∧
      check AtomicWorkControls.encoding stale 0 deliveryRow [] AtomicWorkControls.wire = .rejected .staleScope ∧
      check AtomicWorkControls.encoding law 0 deliveryRow
        [(AtomicWorkControls.wire.ballot.cut,AtomicWorkControls.wire.ballot.position)] AtomicWorkControls.wire = .rejected .duplicate := by
  and_intros <;> decide +kernel

abbrev financialPrefix := CatalogueHandoffSource.completeFinancialPrefix old extra saved AtomicWorkControls.waitedOriginal stages
def bound : Native.Authority.Bound (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
    (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit) :=
  ⟨AtomicWorkControls.net.entry.bound.base,AtomicWorkControls.net.entry.bound.scope,
    (start old saved).source,AtomicWorkControls.net.entry.bound.law_exact,AtomicWorkControls.net.entry.bound.task_exact⟩
abbrev native := StageRuntime.the_final_root_consumes_actual_budget_native_responsibility_ledger_and_next
  bound (start old saved) stages AtomicWorkControls.vocabulary
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveJointRepaymentControls
