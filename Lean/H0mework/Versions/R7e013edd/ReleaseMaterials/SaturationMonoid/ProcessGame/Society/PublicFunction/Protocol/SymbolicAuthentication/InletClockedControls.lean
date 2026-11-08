import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletClockedProgress

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 96000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletClockedControls
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open InletClockedSource InletClockedProgress
open LiveProductionInletControls
open WholeCursorLaw
open Repayment.Recovery (Good)

theorem supplier_instructions_are_clock_free : ClockFree old vocabulary := by
  intro current request admitted
  simp only [vocabulary,List.mem_cons,List.not_mem_nil,or_false] at admitted
  rcases admitted with same | same | same <;> subst request <;> rfl

theorem the_actual_start_passes_resource_admission_and_budget_checks : ready old vocabulary working = true := by
  decide +kernel

theorem every_adaptive_arrival_preserves_original_prefix_progress (incoming : Incoming old vocabulary) :
    Completes old vocabulary working incoming working.pending [] :=
  checked_queue_completes old vocabulary supplier_instructions_are_clock_free incoming working
    the_actual_start_passes_resource_admission_and_budget_checks

def adaptive : Incoming old vocabulary := fun state =>
  if (EventStep.seed state.cursor).current.stock supplier .feedstock = 0 then [forged] else [WholeCursorLaw.charge]
abbrev completed := InletClockedSource.run old vocabulary adaptive 2 working

theorem adaptive_proposals_stay_behind_the_paid_original_instructions :
    completed.submitted = [WholeCursorLaw.production,WholeCursorLaw.transfer] ∧
      completed.state.pending = [forged,WholeCursorLaw.charge] ∧
      completed.stages.length = 4 ∧ completed.state.cursor.cut = opening.cut + 4 ∧
      (EventStep.seed completed.state.cursor).current.stock supplier .energy = 2 ∧
      (EventStep.seed completed.state.cursor).current.stock supplier .labor = 2 ∧
      (EventStep.seed completed.state.cursor).current.stock producer .feedstock = 1 ∧
      (EventStep.seed completed.state.cursor).current.claims () producer creditor = 7 ∧
      (EventStep.seed completed.state.cursor).frame.sent.length = 1 ∧
      (EventStep.seed completed.state.cursor).remaining = 6 := by
  and_intros <;> decide +kernel

abbrev firstRow := LiveProductionInletSource.row old vocabulary (prepared old vocabulary working)
  SilentWindow.quiet true WholeCursorLaw.production
theorem first_production_is_in_the_generated_execution :
    firstRow ∈ StageTrace.records opening completed.stages := by
  change firstRow ∈ _ :: firstRow :: _
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
abbrev productionFinance := every_generated_record_is_native_financial old vocabulary adaptive 2 working
  firstRow first_production_is_in_the_generated_execution
abbrev priorFinance := LiveProductionInletConsumer.priorFinancial old vocabulary saved rfl completed.stages
abbrev actualOccurrence := StageTrace.every_record_is_a_completed_occurrence_of_the_final_source
  opening completed.stages firstRow first_production_is_in_the_generated_execution

abbrev paymentBatch := LiveExternalSupplySource.assembled active completed.state.cursor [WholeCursorLaw.useFeed]
abbrev paidCode := AtomicWorkSource.code active paymentBatch
abbrev paidStart := AtomicWorkSource.cursor active paymentBatch completed.state.cursor
abbrev paidRule := AtomicWorkSource.protocol active paymentBatch true
abbrev delivery : Opponent paidCode := fun _ _ _ => some ⟨.deliver 0,by
  exact List.mem_append_left _ (List.mem_append_left _ (by decide +kernel))⟩
abbrev paidStages : List (EventHistory.Stage (code := paidCode)) :=
  [(paidRule,EventStep.fixed none),(SilentWindow.quiet,delivery)]
abbrev settled := EventHistory.execute paidStart paidStages

theorem generated_material_is_consumed_by_original_debt_and_packet :
    paymentBatch.length = 2 ∧
      AtomicWorkSource.assess active paymentBatch completed.state.cursor true (EventStep.fixed none) = .executed ∧
      (EventStep.seed settled).current.stock producer .feedstock = 0 ∧
      (EventStep.seed settled).current.claims () producer creditor = 5 ∧
      (EventStep.seed settled).current.stock creditor .service = 2 ∧
      (EventStep.seed settled).current.stock producer .service = 0 ∧
      (EventStep.seed settled).frame.sent.length = 1 ∧
      (EventStep.seed settled).frame.inbox ⟨0,by decide⟩ = ⟨1,by decide⟩ ∧
      NativeDeliveryJournal.entries settled = [(9,0)] ∧
      (EventStep.seed settled).remaining = 4 := by
  and_intros <;> decide +kernel
abbrev repaymentFinance := AtomicWorkConsumer.the_final_ledger_consumes_the_original_batch
  active paymentBatch completed.state.cursor true (EventStep.fixed none) [(SilentWindow.quiet,delivery)]
abbrev native := ProgrammeHistory.execution_face_shares_whole_ledger_and_next settled.source.input (EventStep.boundary settled)

abbrev depleted : InletClockedSource.State old vocabulary := ⟨LiveProductionInletControls.exhausted,[WholeCursorLaw.production]⟩
abbrev deprived := InletClockedSource.run old vocabulary (fun _ => []) 1 depleted
abbrev unlisted : InletClockedSource.State old vocabulary := ⟨opening,[WholeCursorLaw.charge]⟩
abbrev unlistedNext := InletClockedSource.run old vocabulary (fun _ => []) 1 unlisted
abbrev short := InletClockedSource.run old vocabulary (fun _ => []) 2 originalLive

theorem depleted_inputs_are_refused_without_deleting_the_proposal :
    ready old vocabulary depleted = false ∧
      deprived.submitted = [WholeCursorLaw.production] ∧ deprived.state.pending = [WholeCursorLaw.production] ∧
      (EventStep.seed deprived.state.cursor).current.stock supplier .energy = 0 ∧
      (EventStep.seed deprived.state.cursor).current.stock supplier .feedstock = 3 := by
  and_intros <;> decide +kernel

theorem admission_and_opportunity_shortfalls_keep_the_unfinished_queue :
    ready old vocabulary unlisted = false ∧ unlistedNext.submitted = [] ∧
      unlistedNext.state.pending = [WholeCursorLaw.charge] ∧
      ready old vocabulary originalLive = false ∧
      short.state.pending = [WholeCursorLaw.transfer] ∧
      (EventStep.seed short.state.cursor).remaining = 0 ∧
      (EventStep.seed short.state.cursor).current.stock producer .feedstock = 0 := by
  and_intros <;> decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletClockedControls
