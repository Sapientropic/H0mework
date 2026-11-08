import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeDeliveryConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 96000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeDeliveryControls
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open WholeCursorLaw
open Repayment.Recovery (Good)
open NativeDeliveryJournal
abbrev paid := LiveExternalSupplyControls.final

theorem an_actual_paid_delivery_releases_the_address_but_keeps_the_debt :
    entries paid = [(5,0)] ∧ settled paid = [0] ∧ pending paid = [] ∧
      NativeDeliveryConsumer.reserve paid producer .service = 0 ∧
      LiveExternalSupplySource.reserve LiveExternalSupplyControls.active paid [] = 1 ∧
      (EventStep.seed paid).current.claims () producer creditor = 3 ∧
      (EventStep.seed paid).remaining = 0 := by
  and_intros <;> decide +kernel

abbrev unpaid := EventHistory.execute (WholeCursorSupplySource.start WholeCursorSupplyControls.saved)
  WholeCursorSupplyControls.withheldStages
abbrev unpaidRow := StageTrace.material
  (WholeCursorSupplySource.after WholeCursorSupplyControls.saved false WholeCursorSupplyControls.noEvent)
  SilentWindow.quiet WholeCursorSupplyControls.delivery

theorem an_event_tag_without_actual_payment_does_not_settle_the_address :
    StageReception.delivered unpaidRow 0 = true ∧ entries unpaid = [] ∧ settled unpaid = [] ∧
      pending unpaid = [0] ∧ NativeDeliveryConsumer.reserve unpaid producer .service = 1 ∧
      (EventStep.seed unpaid).current.stock producer .service = 0 := by
  and_intros <;> decide +kernel

-- The larger opportunity budget is fixed at genesis, before the original send and all payments.
def replayInitial : Cursor WholeCursorSupplySource.code :=
  {WholeCursorSupplySource.initialCursor with
    entry := {WholeCursorSupplySource.initialCursor.entry with budget := 10}}
abbrev replaySaved := EventHistory.execute replayInitial WholeCursorSupplySource.past
abbrev replayCode := WholeCursorSupplySource.active replaySaved
abbrev noEvent : Opponent replayCode := EventStep.fixed none
abbrev delivery : Opponent replayCode := fun _ _ _ => some ⟨.deliver 0,by decide +kernel⟩
abbrev replayStages : List (EventHistory.Stage (code := replayCode)) :=
  [(WholeCursorSupplySource.work replaySaved true,noEvent),(SilentWindow.quiet,delivery),
    (SilentWindow.quiet,noEvent),(SilentWindow.quiet,delivery)]
abbrev replay := EventHistory.execute (WholeCursorSupplySource.start replaySaved) replayStages

theorem repeated_paid_deliveries_keep_two_occurrences_and_one_settled_address :
    entries replay = [(5,0),(7,0)] ∧ settled replay = [0] ∧ pending replay = [] ∧
      NativeDeliveryConsumer.reserve replay producer .service = 0 ∧
      (EventStep.seed replay).current.stock producer .service = 0 ∧
      (EventStep.seed replay).current.claims () producer creditor = 0 ∧
      (EventStep.seed replay).remaining = 2 := by
  and_intros <;> decide +kernel

abbrev thirdStages : List (EventHistory.Stage (code := replayCode)) :=
  [(SilentWindow.quiet,noEvent),(SilentWindow.quiet,delivery)]
abbrev third := EventHistory.execute replay thirdStages
abbrev thirdRow := StageTrace.material (EventHistory.execute replay [(SilentWindow.quiet,noEvent)])
  SilentWindow.quiet delivery

theorem a_settled_address_does_not_prepay_another_replay :
    StageReception.delivered thirdRow 0 = true ∧ entries third = [(5,0),(7,0)] ∧
      (EventStep.seed third).current.stock producer .service = 0 ∧
      (EventStep.seed third).remaining = 0 := by
  and_intros <;> decide +kernel

abbrev actualPayment := NativeDeliveryConsumer.every_published_entry_consumes_its_native_fee_and_memory
  paid 5 0 (by rw [an_actual_paid_delivery_releases_the_address_but_keeps_the_debt.1];simp)
abbrev firstReplayPayment := NativeDeliveryConsumer.every_published_entry_consumes_its_native_fee_and_memory
  replay 5 0 (by rw [repeated_paid_deliveries_keep_two_occurrences_and_one_settled_address.1];simp)
abbrev secondReplayPayment := NativeDeliveryConsumer.every_published_entry_consumes_its_native_fee_and_memory
  replay 7 0 (by rw [repeated_paid_deliveries_keep_two_occurrences_and_one_settled_address.1];simp)
abbrev native := NativeDeliveryConsumer.native paid 5
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeDeliveryControls
