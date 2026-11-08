import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeDeliveryJournal

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeDeliveryConsumer
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open NativeDeliveryJournal
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

-- Potential cost of one delivery for each unconfirmed packet, not a bound on future replay costs.
def reserve (saved : Cursor code) (payer : Party) (good : Good) : ℚ :=
  max 0 (((feeWord saved).map fun request =>
    flowAt (code.law.debit (EventStep.seed saved).current request) payer good).sum)

theorem no_pending_delivery_needs_no_future_reserve (saved : Cursor code) (payer : Party) (good : Good)
    (complete : pending saved = []) : reserve saved payer good = 0 := by
  simp [reserve,feeWord,complete]

-- Feedback executes only the fresh fee word; the accumulated frame.word must not be charged twice.
theorem the_generated_entry_is_paid_in_the_actual_root (saved : Cursor code) (index serial : Nat)
    (packet : code.Packet) (found : paidDelivery? saved index = some (serial,packet)) :
    (saved.source.actualExecution (saved.source.history.length+1+index)).submitted = code.deliveryCost packet.recipient ∧
      (saved.source.actualExecution (saved.source.history.length+1+index)).before = (before saved index).current ∧
      (∀ item ∈ code.law.rawItems
        (saved.source.actualExecution (saved.source.history.length+1+index)).before
        (saved.source.actualExecution (saved.source.history.length+1+index)).submitted,
        code.law.Valid item.before item.request) ∧
      (before saved (index+1)).frame.inbox packet.recipient =
        code.afterDelivery packet.recipient packet.sender ((before saved index).frame.inbox packet.recipient) packet.signal := by
  obtain ⟨policy,chosen,active,decision,event,present,paid⟩ := paidDelivery_sound saved index serial packet found
  have word : Feedback.word code (saved.source.feedbackPolicy index) saved.entry (before saved index) =
      code.deliveryCost packet.recipient := by
    simp only [Feedback.word,active,decision,Feedback.stepLocal,event,Code.step,present,List.nil_append]
  have actualWord := (saved.source.feedback_word_is_actual saved.entry rfl rfl index).trans word
  have actualBefore := (saved.source.feedback_body_reads_the_actual_local_current saved.entry rfl rfl index).symm
  refine ⟨actualWord,actualBefore,?_,?_⟩
  · rw [actualWord,actualBefore]
    exact paid
  · change (Feedback.advance code (saved.source.feedbackPolicy index) saved.entry (before saved index)).frame.inbox packet.recipient = _
    simp only [Feedback.advance,active,decision,Feedback.stepLocal,event]
    exact code.delivery_reads_only_an_already_sent_packet policy (before saved index).current
      {(before saved index).frame with word := []} serial packet present paid

abbrev native (saved : Cursor code) (index : Nat) :=
  ProgrammeHistory.execution_face_shares_whole_ledger_and_next saved.source.input
    (saved.source.history.length+2+index)

theorem every_published_entry_consumes_its_native_fee_and_memory (saved : Cursor code) (index serial : Nat)
    (member : (index,serial) ∈ entries saved) :
    index < saved.cut ∧ ∃ packet,
      (before saved index).frame.sent[serial]? = some packet ∧
      (saved.source.actualExecution (saved.source.history.length+1+index)).submitted = code.deliveryCost packet.recipient ∧
      (before saved (index+1)).frame.inbox packet.recipient =
        code.afterDelivery packet.recipient packet.sender ((before saved index).frame.inbox packet.recipient) packet.signal := by
  obtain ⟨completed,packet,found⟩ := every_entry_has_its_actual_paid_source saved index serial member
  have exactSource := paidDelivery_sound saved index serial packet found
  have actual := the_generated_entry_is_paid_in_the_actual_root saved index serial packet found
  exact ⟨completed,packet,exactSource.choose_spec.choose_spec.2.2.2.1,actual.1,actual.2.2.2⟩
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeDeliveryConsumer
