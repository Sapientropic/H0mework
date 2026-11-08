import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletOmissionProgress

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 96000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletOmissionControls
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open InletClockedSource (State prepared)
open InletOmissionSource InletOmissionProgress
open LiveProductionInletControls WholeCursorLaw
open Repayment.Recovery (Good)

def adaptive : Controller old vocabulary := fun state =>
  ⟨decide (state.cursor.cut ≠ opening.cut),
    if (EventStep.seed state.cursor).current.stock supplier .feedstock = 0 then [forged] else [WholeCursorLaw.charge]⟩
abbrev completed := InletOmissionSource.produce old vocabulary working adaptive 3
abbrev omissionRow := row old vocabulary working (adaptive working)
abbrev afterHold := after old vocabulary working (adaptive working)
abbrev productionRow := row old vocabulary afterHold (adaptive afterHold)

theorem an_actual_omission_precedes_the_two_paid_original_instructions :
    funded old vocabulary working 1 = true ∧ completed.withheld = 1 ∧ completed.unserved = 0 ∧
      completed.submitted = [WholeCursorLaw.production,WholeCursorLaw.transfer] ∧
      completed.state.pending = [forged,forged,WholeCursorLaw.charge] ∧
      completed.stages.length = 6 ∧ completed.state.cursor.cut = opening.cut + 6 ∧
      observe old vocabulary working (adaptive working) = some .withheld ∧
      omissionRow.call = .external none ∧ omissionRow.submitted = [] ∧
      (EventStep.seed afterHold.cursor).current.stock supplier .energy = 3 ∧
      (EventStep.seed completed.state.cursor).current.stock supplier .energy = 2 ∧
      (EventStep.seed completed.state.cursor).current.stock producer .feedstock = 1 ∧
      (EventStep.seed completed.state.cursor).current.claims () producer creditor = 7 ∧
      (EventStep.seed completed.state.cursor).frame.sent.length = 1 ∧
      (EventStep.seed completed.state.cursor).remaining = 4 := by
  and_intros <;> first | decide +kernel | rfl

theorem actual_omission_is_in_the_generated_history :
    omissionRow ∈ StageTrace.records opening completed.stages := by
  change omissionRow ∈ _ :: omissionRow :: _
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem actual_production_is_in_the_generated_history :
    productionRow ∈ StageTrace.records opening completed.stages := by
  change productionRow ∈ _ :: _ :: _ :: productionRow :: _
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
abbrev omissionFinance := every_generated_record_is_native_financial old vocabulary adaptive 3 2 working
  omissionRow actual_omission_is_in_the_generated_history
abbrev productionFinance := every_generated_record_is_native_financial old vocabulary adaptive 3 2 working
  productionRow actual_production_is_in_the_generated_history
abbrev priorFinance := LiveProductionInletConsumer.priorFinancial old vocabulary saved rfl completed.stages

abbrev batch := LiveExternalSupplySource.assembled active completed.state.cursor [WholeCursorLaw.useFeed]
abbrev paidCode := AtomicWorkSource.code active batch
abbrev paidStart := AtomicWorkSource.cursor active batch completed.state.cursor
abbrev paidRule := AtomicWorkSource.protocol active batch true
abbrev delivery : Opponent paidCode := fun _ _ _ => some ⟨.deliver 0,by
  exact List.mem_append_left _ (List.mem_append_left _ (by decide +kernel))⟩
abbrev paymentStages : List (EventHistory.Stage (code := paidCode)) :=
  [(paidRule,EventStep.fixed none),(SilentWindow.quiet,delivery)]
abbrev settled := EventHistory.execute paidStart paymentStages

theorem the_delayed_real_material_pays_original_debt_and_old_packet :
    batch.length = 2 ∧ AtomicWorkSource.assess active batch completed.state.cursor true (EventStep.fixed none) = .executed ∧
      (EventStep.seed settled).current.stock producer .feedstock = 0 ∧
      (EventStep.seed settled).current.claims () producer creditor = 5 ∧
      (EventStep.seed settled).current.stock creditor .service = 2 ∧
      (EventStep.seed settled).current.stock producer .service = 0 ∧
      NativeDeliveryJournal.entries settled = [(11,0)] ∧
      (EventStep.seed settled).frame.inbox ⟨0,by decide⟩ = ⟨1,by decide⟩ ∧
      (EventStep.seed settled).remaining = 2 := by
  and_intros <;> decide +kernel
abbrev repaymentFinance := AtomicWorkConsumer.the_final_ledger_consumes_the_original_batch active batch
  completed.state.cursor true (EventStep.fixed none) [(SilentWindow.quiet,delivery)]
abbrev native := ProgrammeHistory.execution_face_shares_whole_ledger_and_next settled.source.input (EventStep.boundary settled)

def withholding : Controller old vocabulary := fun _ => ⟨false,[]⟩
def following : Controller old vocabulary := fun _ => ⟨true,[]⟩
abbrev overrun := InletOmissionSource.produce old vocabulary working withholding 3
abbrev bad : State old vocabulary := ⟨opening,[forged]⟩
abbrev rejected := InletOmissionSource.produce old vocabulary bad following 1
abbrev missing : State old vocabulary := ⟨opening,[WholeCursorLaw.charge]⟩
abbrev unadmitted := InletOmissionSource.produce old vocabulary missing following 1
abbrev spent := InletOmissionSource.produce old vocabulary originalLive following 3

theorem excess_withholding_really_occurs_without_forced_follow :
    funded old vocabulary working 1 = true ∧ overrun.withheld = 3 ∧ overrun.unserved = 2 ∧
      overrun.submitted = [] ∧ overrun.state.pending = working.pending ∧
      (EventStep.seed overrun.state.cursor).current.stock supplier .energy = 3 ∧
      (EventStep.seed overrun.state.cursor).current.stock producer .feedstock = 0 ∧
      (EventStep.seed overrun.state.cursor).remaining = 4 := by
  and_intros <;> decide +kernel

theorem refused_and_unadmitted_heads_are_not_omissions_or_completion :
    funded old vocabulary bad 0 = false ∧ observe old vocabulary bad (following bad) = some .refused ∧
      rejected.unserved = 1 ∧ rejected.withheld = 0 ∧ rejected.submitted = [forged] ∧ rejected.state.pending = [forged] ∧
      observe old vocabulary missing (following missing) = some .unadmitted ∧
      unadmitted.unserved = 1 ∧ unadmitted.withheld = 0 ∧ unadmitted.submitted = [] ∧
      unadmitted.state.pending = [WholeCursorLaw.charge] := by
  and_intros <;> decide +kernel

theorem the_original_spent_opportunity_is_not_restarted :
    funded old vocabulary originalLive 1 = false ∧ spent.unserved = 1 ∧ spent.withheld = 0 ∧
      spent.state.pending = [WholeCursorLaw.transfer] ∧
      (EventStep.seed spent.state.cursor).remaining = 0 ∧
      (EventStep.seed spent.state.cursor).current.stock producer .feedstock = 0 := by
  and_intros <;> decide +kernel

theorem every_control_with_one_actual_omission_completes (control : Controller old vocabulary)
    (within : (InletOmissionSource.produce old vocabulary working control 3).withheld ≤ 1) :
    Completes old vocabulary control 3 working working.pending [] :=
  checked_production_completes old vocabulary InletClockedControls.supplier_instructions_are_clock_free
    control working 1 an_actual_omission_precedes_the_two_paid_original_instructions.1 within

inductive Classification where
  | completed | checksFailed | overrun
  deriving DecidableEq

def classify (control : Controller old vocabulary) (state : State old vocabulary) (allowance : Nat) : Classification :=
  match inspect old vocabulary InletClockedControls.supplier_instructions_are_clock_free control state allowance with
  | .completed _ => .completed
  | .checksFailed _ => .checksFailed
  | .overrun _ _ => .overrun

theorem the_producer_classifies_its_own_source_and_control_checks :
    classify adaptive working 1 = .completed ∧ classify withholding working 1 = .overrun ∧
      classify following bad 0 = .checksFailed ∧ classify following missing 0 = .checksFailed ∧
      classify following originalLive 1 = .checksFailed := by
  and_intros <;> decide +kernel

theorem the_attempt_ledger_retains_the_held_head_and_actual_cuts :
    completed.attempts.map (fun entry => entry.observation) = [some .withheld,some .executed,some .executed] ∧
      completed.attempts.map (fun entry => entry.row.cursor.cut) = [5,7,9] ∧
      completed.attempts.map (fun entry => entry.state.pending) =
        [[WholeCursorLaw.production,WholeCursorLaw.transfer],
         [WholeCursorLaw.production,WholeCursorLaw.transfer,forged],
         [WholeCursorLaw.transfer,forged,forged]] ∧
      completed.withheld = countWithheld old vocabulary completed.attempts := by
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,?_⟩
  exact the_omission_count_is_its_actual_attempt_ledger old vocabulary adaptive 3 2 working

abbrev attemptFinance (entry : Attempt old vocabulary) (inside : entry ∈ completed.attempts) :=
  every_attempt_is_consumed_in_the_final_native_inventory old vocabulary adaptive 3 2 working entry inside

theorem the_independent_ledger_replay_preserves_the_complete_state :
    replay old vocabulary working completed.attempts = completed.state :=
  the_actual_attempt_ledger_replays_to_the_complete_original_endpoint old vocabulary adaptive 3 2 working

theorem deleting_the_omission_loses_its_input_and_original_opportunity_debit :
    (EventStep.seed (replay old vocabulary working (completed.attempts.drop 1)).cursor).remaining = 6 ∧
      (replay old vocabulary working (completed.attempts.drop 1)).pending = [forged,WholeCursorLaw.charge] := by
  and_intros <;> decide +kernel
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletOmissionControls
