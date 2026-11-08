import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveSupplySynthesisConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AtomicWorkControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 240000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveSupplySynthesisControls
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open LiveSupplySynthesisSource
noncomputable section
abbrev old := AtomicWorkControls.old
abbrev saved := AtomicWorkControls.oldWaited
abbrev active := code old saved
abbrev silent : Opponent active := EventStep.fixed none
abbrev production := row old saved true silent
abbrev supplied := next old saved true silent

theorem the_live_source_synthesizes_and_executes_the_complete_upstream_cycle :
    offer old saved = some donorCycle ∧ assess old saved true silent = .executed ∧
      production.submitted = donorCycle ∧
      production.after.current.stock 1 .service = production.before.current.stock 1 .service + 3 ∧
      production.after.current.stock 0 .energy = production.before.current.stock 0 .energy - 1 ∧
      production.after.current.stock 0 .labor = production.before.current.stock 0 .labor - 1 ∧
      production.after.current.stock 1 .waste = production.before.current.stock 1 .waste - 1 ∧
      production.after.current.claims = production.before.current.claims ∧
      production.after.current.clock = production.before.current.clock + 1 ∧
      production.after.frame.sent = production.before.frame.sent ∧
      production.before.frame.sent.length = 1 := by
  and_intros <;> decide +kernel

abbrev withheld := row old saved false silent
abbrev afterCode := code active supplied
abbrev afterSilent : Opponent afterCode := EventStep.fixed none
theorem depletion_and_withholding_are_recomputed_from_the_actual_endpoint :
    assess old saved false silent = .withheld ∧ withheld.submitted = [] ∧
      offer active supplied = none ∧ demand (current active supplied) ∧
      assess active supplied true afterSilent = .withheld ∧
      (row active supplied true afterSilent).submitted = [] := by
  and_intros <;> decide +kernel

abbrev actualSupply := LiveSupplySynthesisConsumer.actual_supply_is_a_paid_original_word_and_increases_service
  old saved true silent AtomicWorkControls.waitedOriginal
  the_live_source_synthesizes_and_executes_the_complete_upstream_cycle.2.1
abbrev actualLedger := LiveSupplySynthesisConsumer.the_native_ledger_consumes_the_same_actual_supply old saved true silent
abbrev exhausted := LiveSupplySynthesisConsumer.no_offer_is_an_exhausted_source_menu active supplied
  depletion_and_withholding_are_recomputed_from_the_actual_endpoint.2.2.2.1
  depletion_and_withholding_are_recomputed_from_the_actual_endpoint.2.2.1
def initial : Snapshot := ⟨old,saved⟩
def controller (state : Snapshot) : Command state := ⟨true,EventStep.fixed none⟩
abbrev second := LiveSupplySynthesisSource.run initial controller 2
theorem recursive_synthesis_uses_its_own_generated_current :
    (EventStep.seed second.cursor).current.stock 1 .service = production.after.current.stock 1 .service ∧
      (EventStep.seed second.cursor).frame.sent.length = 1 := by
  and_intros <;> decide +kernel

abbrev externalCode := code old AtomicWorkControls.saved
abbrev externalSilent : Opponent externalCode := EventStep.fixed none
theorem a_source_offer_does_not_replace_the_actual_activation :
    (offer old AtomicWorkControls.saved).isSome = true ∧
      assess old AtomicWorkControls.saved true externalSilent = .external := by
  and_intros <;> decide +kernel

abbrev extra := AtomicWorkSource.catalogue old (batch old saved)
abbrev work := AtomicWorkSource.protocol old (batch old saved) (submit old saved true)
abbrev delivery : Opponent active := fun _ _ _ => some ⟨.deliver 0,by
  exact List.mem_append_left _ (by decide +kernel)⟩
abbrev stages := [(work,silent),(SilentWindow.quiet,delivery)]
abbrev law : StageReception.Law active := ⟨fun _ _ => ActualRoundNetworkSource.scope AtomicWorkControls.net,3⟩
abbrev received := CatalogueHandoffConsumer.run AtomicWorkControls.start AtomicWorkControls.fullPast extra
  AtomicWorkControls.handoffOriginal AtomicWorkControls.vocabulary AtomicWorkControls.encoding law stages 0 AtomicWorkControls.origin 2
theorem synthesized_supply_and_the_old_authenticated_receipt_coexist :
    received.receipts = [AtomicWorkControls.receipt] ∧ received.audit.length = 2 := by
  and_intros <;> decide +kernel
abbrev actualDelivery := CatalogueHandoffConsumer.receipt_consumes_the_new_native_delivery
  AtomicWorkControls.start AtomicWorkControls.fullPast extra AtomicWorkControls.handoffOriginal
  AtomicWorkControls.vocabulary AtomicWorkControls.encoding law stages 0 AtomicWorkControls.origin 2
  AtomicWorkControls.receipt (by rw [synthesized_supply_and_the_old_authenticated_receipt_coexist.1];exact List.mem_singleton_self _)
def bound : Native.Authority.Bound (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
    (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit) :=
  ⟨AtomicWorkControls.net.entry.bound.base,AtomicWorkControls.net.entry.bound.scope,
    (start old saved).source,AtomicWorkControls.net.entry.bound.law_exact,AtomicWorkControls.net.entry.bound.task_exact⟩
abbrev native := StageRuntime.the_final_root_consumes_actual_budget_native_responsibility_ledger_and_next
  bound (start old saved) stages AtomicWorkControls.vocabulary
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveSupplySynthesisControls
