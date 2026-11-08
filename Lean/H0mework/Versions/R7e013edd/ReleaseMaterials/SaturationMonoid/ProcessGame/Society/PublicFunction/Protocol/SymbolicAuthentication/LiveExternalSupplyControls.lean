import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveExternalSupplyConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 96000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveExternalSupplyControls
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open WholeCursorLaw
open Repayment.Recovery (Good)
open LiveExternalSupplySource
abbrev legacy := LiveJointRepaymentControls.active
abbrev legacySaved := WholePartyControls.start
-- A fixed source opening supplies the finite exterior reserve; no later state is overwritten.
def opening : Good → ℚ := WholeCursorLaw.initial.stock supplier
abbrev old := PartyCode.code legacy opening
abbrev saved := PartyCursor.cursor legacy opening WholePartyControls.lawExact legacySaved
abbrev active := code old saved
abbrev quietRival : Opponent active := EventStep.fixed none
abbrev productionRow := row old saved true quietRival
abbrev generated := next old saved true quietRival
abbrev delivery : Opponent active := fun _ _ _ => some ⟨.deliver 0,by
  exact List.mem_append_left _ (by decide +kernel)⟩
abbrev future : List (EventHistory.Stage (code := active)) := [(SilentWindow.quiet,delivery)]
abbrev stages : List (EventHistory.Stage (code := active)) := (work old saved true,quietRival)::future
abbrev final := EventHistory.execute (start old saved) stages

theorem the_same_saved_source_precedes_the_new_supplier :
    (EventStep.seed saved).frame.sent.length = 1 ∧
      (EventStep.seed saved).remaining = 2 ∧
      (EventStep.seed saved).current.claims () producer creditor = 6 ∧
      (EventStep.seed saved).current.stock producer .service = 1 ∧
      (EventStep.seed saved).current.stock supplier .energy = 3 ∧
      reserve old saved [] = 1 := by
  and_intros <;> decide +kernel

theorem the_source_selects_and_pays_its_new_supplier_in_one_original_visit :
    offer old saved = some ((preparation.map WholePartyLift.request) ++ cycle) ∧
      assess old saved true quietRival = .executed ∧ productionRow.submitted.length = 11 ∧
      productionRow.after.current.stock supplier .waste = 2 ∧
      productionRow.after.current.stock supplier .energy = 2 ∧
      productionRow.after.current.stock supplier .labor = 2 ∧
      productionRow.after.current.stock producer .service = 1 ∧
      productionRow.after.current.claims () producer creditor = 3 ∧
      productionRow.after.frame.sent = productionRow.before.frame.sent := by
  and_intros <;> decide +kernel

theorem the_old_packet_still_uses_its_actual_fee_and_memory :
    (EventStep.seed final).current.stock producer .service = 0 ∧
      (EventStep.seed final).current.claims () producer creditor = 3 ∧
      StageReception.delivered (StageTrace.material generated SilentWindow.quiet delivery) 0 = true ∧
      (EventStep.seed final).frame.sent.length = 1 ∧
      (EventStep.seed final).remaining = 0 := by
  and_intros <;> decide +kernel

abbrev emptyOld := PartyCode.code legacy PartyCursorControls.outside
abbrev emptySaved := PartyCursor.cursor legacy PartyCursorControls.outside WholePartyControls.lawExact legacySaved
abbrev emptyRival : Opponent (code emptyOld emptySaved) := EventStep.fixed none
abbrev emptyRow := row emptyOld emptySaved true emptyRival
abbrev withheld := row old saved false quietRival

theorem absent_resources_and_withheld_work_are_real_branches :
    offer emptyOld emptySaved = none ∧
      selection emptyOld emptySaved true = .unavailable ∧
      assess emptyOld emptySaved true emptyRival = .withheld ∧ emptyRow.submitted = [] ∧
      emptyRow.after.current.stock supplier .energy = 0 ∧
      selection old saved false = .withheld ∧
      assess old saved false quietRival = .withheld ∧ withheld.submitted = [] ∧
      withheld.after.current.stock supplier .energy = 3 ∧
      withheld.after.current.claims () producer creditor = 6 := by
  and_intros <;> decide +kernel

def forgedBatch : Word := (batch old saved).take 7 ++
  [{WholeCursorLaw.production with signer := producer}] ++ (batch old saved).drop 8
abbrev forgedCode := AtomicWorkSource.code old forgedBatch
abbrev forgedRival : Opponent forgedCode := EventStep.fixed none
abbrev forgedRow := AtomicWorkSource.row old forgedBatch saved true forgedRival

theorem a_forged_supplier_does_not_erase_its_actual_attempt :
    AtomicWorkSource.assess old forgedBatch saved true forgedRival = .refused ∧
      forgedRow.submitted = forgedBatch ∧ forgedRow.submitted.length = 11 ∧
      forgedRow.after.current.stock supplier .energy = 3 ∧
      forgedRow.after.current.claims () producer creditor = 6 := by
  and_intros <;> decide +kernel

abbrev sourceIdentity := LiveExternalSupplyConsumer.same_actual_live_state old saved rfl
abbrev selected := LiveExternalSupplyConsumer.actual_execution_keeps_the_source_and_payment old saved true quietRival
  the_source_selects_and_pays_its_new_supplier_in_one_original_visit.2.1
abbrev originalOccurrence := LiveExternalSupplyConsumer.rawOccurrence old saved true quietRival
  the_source_selects_and_pays_its_new_supplier_in_one_original_visit.2.1
abbrev originalFinance := LiveExternalSupplyConsumer.financialItems old saved true quietRival future
abbrev forgedFinance := AtomicWorkConsumer.the_final_ledger_consumes_the_original_batch old forgedBatch saved true forgedRival []
abbrev priorFinance := LiveExternalSupplyConsumer.financialPrefix old saved rfl stages
abbrev native := LiveExternalSupplyConsumer.native old saved true quietRival future (EventStep.boundary (start old saved))
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveExternalSupplyControls
