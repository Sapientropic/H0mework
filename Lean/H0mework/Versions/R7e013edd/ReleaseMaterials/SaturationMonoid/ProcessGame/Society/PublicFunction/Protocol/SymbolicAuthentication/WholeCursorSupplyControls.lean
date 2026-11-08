import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholeCursorSupplyConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholeCursorSupplyControls
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open WholeCursorLaw
open WholeCursorSupplySource
abbrev saved := pending
abbrev activeCode := active saved
abbrev workRule := work saved true
abbrev noEvent : Opponent activeCode := EventStep.fixed none
abbrev productionRow := row saved true noEvent
abbrev generated := after saved true noEvent
abbrev delivery : Opponent activeCode := fun _ _ _ => some ⟨.deliver 0,by decide +kernel⟩
abbrev future : List (EventHistory.Stage (code := activeCode)) := [(SilentWindow.quiet,delivery)]
abbrev stages : List (EventHistory.Stage (code := activeCode)) := (workRule,noEvent)::future
abbrev final := EventHistory.execute (start saved) stages
abbrev extra := AtomicWorkSource.catalogue code (batch saved)
theorem original : saved.side = .original := rfl
abbrev reception : StageReception.Law activeCode := ⟨fun _ _ => slot,3⟩
abbrev received := CatalogueHandoffConsumer.run initialCursor past extra original vocabulary encoding reception
  stages ⟨0,by decide⟩ origin 2
abbrev wire : StageTransport.Wire (code := code) :=
  ((CatalogueHandoffConsumer.candidates initialCursor past vocabulary encoding).head?).get (by decide +kernel)
abbrev receipt : StageReception.Receipt (code := code) := ⟨wire,1,5⟩

theorem the_old_debt_is_an_actual_original_financing_occurrence :
    code.initial.claims () producer creditor = 0 ∧
      (emitter.actualExecution 0).submitted = [issue] ∧
      (emitter.actualExecution 0).before.claims () producer creditor = 0 ∧
      (EventStep.seed initialCursor).current.claims () producer creditor = 7 := by
  and_intros <;> decide +kernel

theorem the_pending_message_and_original_debt_precede_the_new_supply :
    (EventStep.seed saved).frame.sent.length = 1 ∧
      (EventStep.seed saved).current.stock producer .service = 0 ∧
      (EventStep.seed saved).current.claims () producer creditor = 7 ∧
      WholeCursorSupplySource.reserve saved = 1 ∧ cycles saved = 3 ∧ (batch saved).length = 10 ∧
      (EventStep.seed saved).current.stock supplier .feedstock = 0 := by
  and_intros <;> decide +kernel

theorem one_native_word_reproduces_pays_the_original_debt_and_keeps_the_old_packet :
    assess saved true noEvent = .executed ∧
      productionRow.submitted = batch saved ∧
      productionRow.after.current.stock supplier .waste = 0 ∧
      productionRow.after.current.stock supplier .energy = 0 ∧
      productionRow.after.current.stock supplier .labor = 0 ∧
      productionRow.after.current.stock producer .energy = 0 ∧
      productionRow.after.current.stock producer .labor = 0 ∧
      productionRow.after.current.stock producer .service = 2 ∧
      productionRow.after.current.stock creditor .service = 7 ∧
      productionRow.after.current.claims () producer creditor = 0 ∧
      productionRow.after.frame.sent = productionRow.before.frame.sent ∧
      productionRow.after.current.clock = productionRow.before.current.clock + 1 := by
  and_intros <;> decide +kernel

theorem the_same_old_authenticated_packet_is_delivered_after_actual_upstream_payment :
    received.receipts = [receipt] ∧ received.audit.length = 2 ∧
      (EventStep.seed final).current.stock producer .service = 1 ∧
      (EventStep.seed final).current.claims () producer creditor = 0 ∧
      (EventStep.seed final).frame.inbox ⟨0,by decide⟩ = ⟨1,by decide⟩ := by
  and_intros <;> decide +kernel

abbrev withheldStages : List (EventHistory.Stage (code := activeCode)) :=
  [(work saved false,noEvent),(SilentWindow.quiet,delivery)]
abbrev withheld := row saved false noEvent
abbrev unpaid := CatalogueHandoffConsumer.run initialCursor past extra original vocabulary encoding reception
  withheldStages ⟨0,by decide⟩ origin 2
abbrev absent := CatalogueHandoffConsumer.run initialCursor past extra original vocabulary encoding reception
  [(workRule,noEvent),(SilentWindow.quiet,noEvent)] ⟨0,by decide⟩ origin 2
abbrev deliveryRow := StageTrace.material generated SilentWindow.quiet delivery
abbrev check := CatalogueHandoffConsumer.check initialCursor past extra vocabulary encoding
abbrev wrongSigner : StageTransport.Wire (code := code) := {wire with ballot := {wire.ballot with actor := supplier}}
abbrev stale : StageReception.Law activeCode := ⟨fun _ _ => {slot with epoch := 1},3⟩
abbrev late : StageReception.Law activeCode := ⟨reception.scope,0⟩

theorem real_withholding_and_independent_authentication_rejections_survive_material_success :
    assess saved false noEvent = .withheld ∧ withheld.submitted = [] ∧
      withheld.after.current.stock supplier .energy = 3 ∧
      withheld.after.current.claims () producer creditor = 7 ∧
      unpaid.receipts = [] ∧ absent.receipts = [] ∧
      check reception ⟨0,by decide⟩ deliveryRow [] wrongSigner = .rejected .unauthenticated ∧
      check stale ⟨0,by decide⟩ deliveryRow [] wire = .rejected .staleScope ∧
      check late ⟨0,by decide⟩ deliveryRow [] wire = .rejected .late ∧
      check reception ⟨0,by decide⟩ deliveryRow [(0,0)] wire = .rejected .duplicate := by
  and_intros <;> decide +kernel

def forgedBatch : List Action := {WholeCursorLaw.production with signer := producer} :: (batch saved).drop 1
abbrev forgedCode := AtomicWorkSource.code code forgedBatch
abbrev forgedNone : Opponent forgedCode := EventStep.fixed none
abbrev forgedDelivery : Opponent forgedCode := fun _ _ _ => some ⟨.deliver 0,by decide +kernel⟩
abbrev forgedStart := AtomicWorkSource.cursor code forgedBatch saved
abbrev forgedWork := AtomicWorkSource.protocol code forgedBatch true
abbrev forgedRow := AtomicWorkSource.row code forgedBatch saved true forgedNone
abbrev forgedStages : List (EventHistory.Stage (code := forgedCode)) :=
  [(forgedWork,forgedNone),(SilentWindow.quiet,forgedDelivery)]
abbrev forgedExtra := AtomicWorkSource.catalogue code forgedBatch
abbrev forgedReception : StageReception.Law forgedCode := ⟨fun _ _ => slot,3⟩
abbrev receivedForged := CatalogueHandoffConsumer.run initialCursor past forgedExtra original vocabulary encoding
  forgedReception forgedStages ⟨0,by decide⟩ origin 2

theorem actual_wrong_signer_refusal_can_coexist_with_later_paid_delivery_without_clearing_the_old_debt :
    AtomicWorkSource.assess code forgedBatch saved true forgedNone = .refused ∧
      ¬ WholeCursorLaw.law.Valid forgedRow.before.current {WholeCursorLaw.production with signer := producer} ∧
      forgedRow.submitted = forgedBatch ∧
      forgedRow.after.current.stock supplier .energy = 1 ∧
      forgedRow.after.current.stock producer .service = 6 ∧
      forgedRow.after.current.claims () producer creditor = 7 ∧
      receivedForged.receipts = [receipt] := by
  and_intros <;> decide +kernel

abbrev rawOccurrence := WholeCursorSupplyConsumer.the_actual_source_batch_has_its_one_original_raw_occurrence
  saved true noEvent one_native_word_reproduces_pays_the_original_debt_and_keeps_the_old_packet.1
abbrev forgedLedger := AtomicWorkConsumer.the_final_ledger_consumes_the_original_batch code forgedBatch saved true forgedNone
  [(SilentWindow.quiet,forgedDelivery)]
abbrev ledger := WholeCursorSupplyConsumer.every_future_keeps_the_original_financial_items saved true noEvent future
abbrev native := WholeCursorSupplyConsumer.native saved true noEvent future
abbrev financialPrefix := WholeCursorSupplyConsumer.priorFinancialPrefix saved original stages
abbrev receiptConsumer := CatalogueHandoffConsumer.receipt_consumes_the_new_native_delivery
  initialCursor past extra original vocabulary encoding reception stages ⟨0,by decide⟩ origin 2 receipt
  (by rw [the_same_old_authenticated_packet_is_delivered_after_actual_upstream_payment.1];exact List.mem_singleton_self _)
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholeCursorSupplyControls
