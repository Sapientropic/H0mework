import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveProductionInletConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 96000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveProductionInletControls
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open WholeCursorLaw
open Repayment.Recovery (Good)
open LiveProductionInletSource
abbrev old := WholeCursorSupplySource.code
-- This is an opportunity budget fixed before the original history, not a restart of a spent Cursor.
def initial : Cursor old := {WholeCursorSupplySource.initialCursor with
  entry := {WholeCursorSupplySource.initialCursor.entry with budget := 14}}
abbrev saved := EventHistory.execute initial WholeCursorSupplySource.past

def forged : Action := {WholeCursorLaw.production with signer := producer}
def vocabulary : List Action := [WholeCursorLaw.production,WholeCursorLaw.transfer,forged]
abbrev active := code old vocabulary
abbrev opening := start old vocabulary saved
abbrev quiet : Rule active := SilentWindow.quiet
abbrev working : State old vocabulary := ⟨opening,[WholeCursorLaw.production,WholeCursorLaw.transfer]⟩
def controller : Controller old vocabulary := fun _ => ⟨quiet,true,[]⟩
abbrev supplied := LiveProductionInletSource.run old vocabulary working controller 4
abbrev stages := LiveProductionInletSource.trace old vocabulary working controller 4
abbrev productionStart := EventHistory.execute opening (stages.take 1)
abbrev productionRow := row old vocabulary productionStart quiet true WholeCursorLaw.production

theorem live_external_turns_generate_the_new_feedstock :
    supplied.cursor = EventHistory.execute opening stages ∧ supplied.pending = [] ∧
      (EventStep.seed saved).frame.sent.length = 1 ∧
      (EventStep.seed saved).current.stock supplier .feedstock = 0 ∧
      assess old vocabulary opening quiet true WholeCursorLaw.production = .owned ∧
      assess old vocabulary productionStart quiet true WholeCursorLaw.production = .executed ∧
      productionRow.submitted = [WholeCursorLaw.production] ∧
      productionRow.after.current.stock supplier .feedstock = 1 ∧
      (EventStep.seed supplied.cursor).current.stock supplier .waste = 2 ∧
      (EventStep.seed supplied.cursor).current.stock supplier .energy = 2 ∧
      (EventStep.seed supplied.cursor).current.stock supplier .labor = 2 ∧
      (EventStep.seed supplied.cursor).current.stock producer .feedstock = 1 ∧
      (EventStep.seed supplied.cursor).current.claims () producer creditor = 7 ∧
      (EventStep.seed supplied.cursor).frame.sent.length = 1 ∧
      (EventStep.seed supplied.cursor).remaining = 6 := by
  constructor
  · exact LiveProductionInletConsumer.the_run_is_its_source_generated_trace old vocabulary working controller 4
  · and_intros <;> decide +kernel

-- The old debt and packet determine the payment; the incoming feed is consumed at this actual next.
abbrev front : List Action := [WholeCursorLaw.useFeed]
abbrev batch := LiveExternalSupplySource.assembled active supplied.cursor front
abbrev paymentCode := AtomicWorkSource.code active batch
abbrev paymentStart := AtomicWorkSource.cursor active batch supplied.cursor
abbrev paymentRule := AtomicWorkSource.protocol active batch true
abbrev noEvent : Opponent paymentCode := EventStep.fixed none
abbrev delivery : Opponent paymentCode := fun _ _ _ => some ⟨.deliver 0,by
  exact List.mem_append_left _ (List.mem_append_left _ (by decide +kernel))⟩
abbrev paymentStages : List (EventHistory.Stage (code := paymentCode)) :=
  [(paymentRule,noEvent),(SilentWindow.quiet,delivery)]
abbrev final := EventHistory.execute paymentStart paymentStages

theorem the_actual_external_feed_pays_the_old_debt_and_delivers_the_old_packet :
    batch.length = 2 ∧ AtomicWorkSource.assess active batch supplied.cursor true noEvent = .executed ∧
      (EventStep.seed final).current.stock producer .feedstock = 0 ∧
      (EventStep.seed final).current.stock producer .service = 0 ∧
      (EventStep.seed final).current.claims () producer creditor = 5 ∧
      (EventStep.seed final).current.stock creditor .service = 2 ∧
      (EventStep.seed final).frame.sent.length = 1 ∧
      (EventStep.seed final).frame.inbox ⟨0,by decide⟩ = ⟨1,by decide⟩ ∧
      NativeDeliveryJournal.entries final = [(9,0)] ∧
      (EventStep.seed final).remaining = 4 := by
  and_intros <;> decide +kernel

abbrev withheld := row old vocabulary productionStart quiet false WholeCursorLaw.production
abbrev refused := row old vocabulary productionStart quiet true forged
abbrev missing := row old vocabulary productionStart quiet true WholeCursorLaw.charge
abbrev shortState : State old vocabulary := ⟨productionStart,[forged]⟩
abbrev shortNext := LiveProductionInletSource.step old vocabulary shortState ⟨quiet,true,[]⟩

theorem withholding_missing_admission_and_wrong_signer_are_distinct_actual_branches :
    assess old vocabulary productionStart quiet false WholeCursorLaw.production = .withheld ∧
      withheld.submitted = [] ∧ withheld.after.current.stock supplier .energy = 3 ∧
      assess old vocabulary productionStart quiet true WholeCursorLaw.charge = .unadmitted ∧
      missing.submitted = [] ∧
      assess old vocabulary productionStart quiet true forged = .refused ∧
      refused.submitted = [forged] ∧ refused.after.current.stock supplier .energy = 3 ∧
      shortNext.pending = [forged] := by
  and_intros <;> decide +kernel

abbrev added := LiveProductionInletSource.step old vocabulary supplied ⟨quiet,true,[WholeCursorLaw.production,WholeCursorLaw.transfer]⟩
abbrev resupplied := LiveProductionInletSource.run old vocabulary added controller 3

theorem a_new_actual_input_is_consumed_after_the_first_queue_finishes :
    added.pending = [WholeCursorLaw.production,WholeCursorLaw.transfer] ∧
      (EventStep.seed added.cursor).current.stock producer .feedstock = 1 ∧
      resupplied.pending = [] ∧
      (EventStep.seed resupplied.cursor).current.stock supplier .energy = 1 ∧
      (EventStep.seed resupplied.cursor).current.stock supplier .labor = 1 ∧
      (EventStep.seed resupplied.cursor).current.stock producer .feedstock = 2 ∧
      (EventStep.seed resupplied.cursor).current.claims () producer creditor = 7 ∧
      (EventStep.seed resupplied.cursor).frame.sent.length = 1 ∧
      (EventStep.seed resupplied.cursor).remaining = 2 := by
  and_intros <;> decide +kernel

abbrev repeatProduction : List (EventHistory.Stage (code := active)) :=
  List.replicate 7 (quiet,rival old vocabulary true WholeCursorLaw.production)
abbrev exhausted := EventHistory.execute opening repeatProduction
abbrev exhaustedRow := row old vocabulary exhausted quiet true WholeCursorLaw.production

theorem exhausted_primitive_inputs_keep_the_actual_refused_attempt :
    (EventStep.seed exhausted).current.stock supplier .energy = 0 ∧
      (EventStep.seed exhausted).current.stock supplier .feedstock = 3 ∧
      assess old vocabulary exhausted quiet true WholeCursorLaw.production = .refused ∧
      exhaustedRow.submitted = [WholeCursorLaw.production] ∧
      exhaustedRow.after.current.stock supplier .feedstock = 3 := by
  and_intros <;> decide +kernel

abbrev originalLive : State old vocabulary :=
  ⟨start old vocabulary WholeCursorSupplySource.pending,[WholeCursorLaw.production,WholeCursorLaw.transfer]⟩
abbrev stopped := LiveProductionInletSource.run old vocabulary originalLive controller 2

theorem the_original_small_opportunity_budget_is_never_restarted :
    stopped.pending = [WholeCursorLaw.transfer] ∧
      (EventStep.seed stopped.cursor).remaining = 0 ∧
      (EventStep.seed stopped.cursor).current.stock supplier .feedstock = 1 ∧
      (EventStep.seed stopped.cursor).current.stock producer .feedstock = 0 ∧
      assess old vocabulary stopped.cursor quiet true WholeCursorLaw.transfer = .stopped := by
  and_intros <;> decide +kernel

abbrev actualInput := LiveProductionInletConsumer.executed_keeps_the_actual_input_and_next old vocabulary
  productionStart quiet true WholeCursorLaw.production
  live_external_turns_generate_the_new_feedstock.2.2.2.2.2.1
abbrev inletFinance := LiveProductionInletConsumer.financial old vocabulary productionStart quiet true
  WholeCursorLaw.production (stages.drop 2)
abbrev priorFinance := LiveProductionInletConsumer.priorFinancial old vocabulary saved rfl stages
abbrev oldInputOccurrence := LiveProductionInletConsumer.occurrence old vocabulary productionStart quiet true
  WholeCursorLaw.production (stages.drop 2)
abbrev repaymentFinance := AtomicWorkConsumer.the_final_ledger_consumes_the_original_batch active batch supplied.cursor
  true noEvent [(SilentWindow.quiet,delivery)]
abbrev native := ProgrammeHistory.execution_face_shares_whole_ledger_and_next final.source.input (EventStep.boundary final)
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveProductionInletControls
