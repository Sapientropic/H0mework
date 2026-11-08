import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandScheduleExecution

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandScheduleConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedQuorumConsumer (code start protocols rivals)
open DemandScheduleExecution

abbrev original := AdaptiveDeliveryTrace.cursorAt start protocols rivals 16
def requests : List Bool := [false,true,false,true,false,true]
def quiet : Nat → Opponent code := fun _ => EventStep.fixed none
def supplied : Nat → Bool := fun _ => true
def delayed : Nat → Bool := fun cut => decide (22 ≤ cut)
def withheld : Nat → Bool := fun _ => false
def attempted : Nat → Opponent code := fun cut =>
  if cut = 17 then EventStep.fixed (some ⟨.activate 2,by simp [code,RenewedQuorumSource.code]⟩)
  else EventStep.fixed none

abbrev report (available : Nat → Bool) (callbacks : Nat → Opponent code) (demands : List Bool) :=
  DemandScheduleExecution.run original available callbacks demands
abbrev final (available : Nat → Bool) (callbacks : Nat → Opponent code) (demands : List Bool) :=
  EventHistory.execute original (report available callbacks demands).stages
abbrev facade (available : Nat → Bool) (callbacks : Nat → Opponent code) (demands : List Bool) :=
  Feedback.Runtime.facade (final available callbacks demands).source
    (final available callbacks demands).entry rfl rfl

theorem the_original_mixed_schedule_completes_the_paid_requests :
    (report supplied quiet requests).status = .finished ∧
      (report supplied quiet requests).served = requests ∧
      (report supplied quiet requests).pending = [] ∧
      (final supplied quiet requests).cut = 37 ∧
      (report supplied quiet requests).state.current.stock 0 .feedstock = 0 ∧
      (report supplied quiet requests).state.current.stock 1 .service = 0 := by
  repeat' constructor
  all_goals decide +kernel

theorem a_real_supply_delay_still_completes_before_the_original_deadline :
    (report delayed quiet requests).status = .finished ∧
      (report delayed quiet requests).served = requests ∧
      (final delayed quiet requests).cut = 43 := by
  repeat' constructor
  all_goals decide +kernel

theorem exhaustively_spent_fuel_generates_a_real_refused_fee :
    let actual := report supplied quiet (requests ++ [false])
    actual.status = .resourceRefusal ∧ actual.served = requests ∧ actual.pending = [false] ∧
      ∃ row ∈ StageTrace.records original actual.stages,
        row.cursor.cut = 38 ∧ row.submitted = [RenewedQuorumSource.fee false] ∧
          ¬ code.law.Valid row.before.current (RenewedQuorumSource.fee false) := by
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,?_
    ⟩
  exact ⟨(StageTrace.records original (report supplied quiet (requests ++ [false])).stages)[22]'(by decide +kernel),
    by simp only [List.getElem_mem],by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem withholding_preserves_real_resources_and_unfinished_demand :
    (report withheld quiet requests).status = .windowExhausted ∧
      (report withheld quiet requests).served = [] ∧
      (report withheld quiet requests).pending = requests ∧
      (final withheld quiet requests).cut = 48 ∧
      (report withheld quiet requests).state.remaining = 0 ∧
      (report withheld quiet requests).state.current.stock 0 .feedstock = 2 := by
  repeat' constructor
  all_goals decide +kernel

theorem a_retained_wrong_interface_attempt_coexists_with_success :
    (report supplied attempted requests).status = .finished ∧
      (report supplied attempted requests).served = requests ∧
      ∃ row ∈ StageTrace.records original (report supplied attempted requests).stages,
        row.cursor.cut = 17 ∧ ControlExecution.suppressed code row.call = true ∧ row.submitted = [] := by
  refine ⟨by decide +kernel,by decide +kernel,?_
    ⟩
  exact ⟨(StageTrace.records original (report supplied attempted requests).stages)[1]'(by decide +kernel),
    by simp only [List.getElem_mem],by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem every_completed_payment_consumes_its_own_source_inventory
    (available : Nat → Bool) (callbacks : Nat → Opponent code) (demands : List Bool)
    (charge : Charge) (member : charge ∈ (report available callbacks demands).charges) :
    charge.row.submitted = [RenewedQuorumSource.fee charge.second] ∧
      code.law.Valid charge.row.before.current (RenewedQuorumSource.fee charge.second) ∧
      (Financial.inventoryAt (final available callbacks demands).source.input
        (ProgrammeHistory.visitAt (final available callbacks demands).source.input
          (EventStep.boundary charge.row.cursor))).filterMap
        (Financial.InstructionOrigin.instruction? (final available callbacks demands).source.input) =
          StageTrace.items charge.row := by
  obtain ⟨inside,submitted,paid⟩ := every_generated_charge_is_an_actual_paid_original_request
    original available callbacks demands charge member
  exact ⟨submitted,paid,StageTrace.final_financial_inventory_is_the_original_record_items
    original _ charge.row inside⟩

theorem the_same_original_history_preserves_its_past_and_generates_whole_ledger_and_next
    (available : Nat → Bool) (callbacks : Nat → Opponent code) (demands : List Bool) :
    let runtime := (facade available callbacks demands).seed.advance (EventStep.boundary (final available callbacks demands))
    (∀ ordinal, ordinal ≤ EventStep.boundary original →
      (final available callbacks demands).source.currentAt ordinal = original.source.currentAt ordinal) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (facade available callbacks demands).process.stateAt
        ((facade available callbacks demands).process.successor runtime.state) := by
  have rooted := (facade available callbacks demands).readoutAt_factorizes
    ((facade available callbacks demands).seed.advance (EventStep.boundary (final available callbacks demands))) .feedback
  exact ⟨(StageTrace.final_preserves_the_complete_past original _).1,rooted.2.2.1,rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandScheduleConsumer
