import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandBallotSource
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandScheduleConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InterfaceQuorum

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandBallotConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedQuorumConsumer (code)
open DemandScheduleConsumer (original quiet requests attempted)
open DemandBallotSource (vocabulary ballots)

abbrev report (rivals : Nat → Opponent code) (demands : List Bool) := DemandBallotSource.run original rivals demands
abbrev final (rivals : Nat → Opponent code) (demands : List Bool) := EventHistory.execute original (report rivals demands).stages

theorem the_actual_gap_regenerates_supply_and_six_paid_signatures :
    (report quiet requests).status = .finished ∧ (report quiet requests).served = requests ∧
      (ballots (report quiet requests)).length = 6 ∧
      (report quiet requests).state.current.stock 0 .feedstock = 0 ∧
      (report quiet requests).state.current.stock 1 .service = 0 ∧
      (final quiet requests).cut = 37 := by
  obtain ⟨finished,served,_,cut,fuel,cash⟩ := DemandScheduleConsumer.the_original_mixed_schedule_completes_the_paid_requests
  refine ⟨finished,served,?_,fuel,cash,cut⟩
  rw [DemandBallotSource.no_served_request_is_lost_at_the_authentication_boundary]
  rw [show (report quiet requests).served = requests from served]
  rfl

theorem the_two_actual_supply_rows_are_regenerated_from_their_own_exhausted_stocks :
    ∃ first ∈ StageTrace.records original (report quiet requests).stages,
      ∃ second ∈ StageTrace.records original (report quiet requests).stages,
        first.cursor.cut = 16 ∧ second.cursor.cut = 28 ∧
        first.submitted = RenewedQuorumMaterial.word ∧ second.submitted = RenewedQuorumMaterial.word ∧
        DemandRenewalStep.refill first.before.current = true ∧ DemandRenewalStep.refill second.before.current = true ∧
        ((StageTrace.audit first).all Prod.snd) = true ∧ ((StageTrace.audit second).all Prod.snd) = true := by
  exact ⟨(StageTrace.records original (report quiet requests).stages)[0]'(by decide +kernel),List.getElem_mem _,
    (StageTrace.records original (report quiet requests).stages)[12]'(by decide +kernel),List.getElem_mem _,
    by decide +kernel⟩

theorem all_six_actual_signatures_are_independently_verified_in_the_original_ledger :
    (ballots (report quiet requests)).all
      (StageBudget.verify vocabulary original (report quiet requests).stages) = true := by
  apply List.all_eq_true.mpr
  intro body inside
  obtain ⟨charge,member,issued⟩ := List.mem_filterMap.mp inside
  have original := (DemandScheduleExecution.generated_steps_are_actual_ordered_paid_occurrences
    (fun _ => true) quiet _ original _ rfl requests).2.2.1 charge member
  apply decide_eq_true
  apply List.mem_flatMap.mpr
  refine ⟨charge.row,original,List.mem_filterMap.mpr ⟨0,?_,issued⟩⟩
  apply List.mem_range.mpr
  rw [charge.submitted]
  simp only [List.length_singleton];omega

theorem the_seventh_attempt_is_retained_but_cannot_generate_an_authenticated_ballot :
    let actual := report quiet (requests ++ [false])
    actual.status = .resourceRefusal ∧ actual.served = requests ∧ actual.pending = [false] ∧
      (ballots actual).length = 6 ∧
      ∃ row ∈ StageTrace.records original actual.stages,
        row.cursor.cut = 38 ∧ row.submitted = [RenewedQuorumSource.fee false] ∧
          StageBudget.outcome vocabulary row 0 = .rejected .invalid ∧
          StageBudget.issued vocabulary row 0 = none := by
  dsimp only
  obtain ⟨refused,served,pending,_⟩ := DemandScheduleConsumer.exhaustively_spent_fuel_generates_a_real_refused_fee
  refine ⟨refused,served,pending,?_,?_
    ⟩
  · rw [DemandBallotSource.no_served_request_is_lost_at_the_authentication_boundary]
    rw [show (report quiet (requests ++ [false])).served = requests from served]
    rfl
  · exact ⟨(StageTrace.records original (report quiet (requests ++ [false])).stages)[22]'(by decide +kernel),
      List.getElem_mem _,by decide +kernel⟩

theorem resource_regeneration_and_signing_do_not_fabricate_delivery_or_a_quorum :
    (StageReception.run vocabulary RenewedQuorumConsumer.encoding RenewedQuorumConsumer.reception
      original (report quiet requests).stages 2 37).receipts = [] ∧
      InterfaceQuorum.produce original vocabulary RenewedQuorumConsumer.encoding RenewedQuorumConsumer.reception
        (report quiet requests).stages 2 (RenewedQuorumSource.slot false) 2 = .blocked .missingQuorum ∧
      StageBudget.evidence vocabulary original (report quiet requests).stages = [] := by
  decide +kernel

theorem an_actual_interface_deviation_and_successful_authenticated_service_coexist :
    (report attempted requests).status = .finished ∧ (ballots (report attempted requests)).length = 6 ∧
      ∃ row ∈ StageTrace.records original (report attempted requests).stages,
        row.cursor.cut = 17 ∧ ControlExecution.suppressed code row.call = true ∧
          row.submitted = [] ∧ StageBudget.issued vocabulary row 0 = none := by
  obtain ⟨finished,served,_⟩ := DemandScheduleConsumer.a_retained_wrong_interface_attempt_coexists_with_success
  refine ⟨finished,?_,?_
    ⟩
  · rw [DemandBallotSource.no_served_request_is_lost_at_the_authentication_boundary]
    rw [show (report attempted requests).served = requests from served]
    rfl
  · exact ⟨(StageTrace.records original (report attempted requests).stages)[1]'(by decide +kernel),
      List.getElem_mem _,by decide +kernel⟩

theorem every_authentication_item_has_its_original_financial_inventory
    (rivals : Nat → Opponent code) (demands : List Bool)
    (charge : DemandScheduleExecution.Charge) (member : charge ∈ (report rivals demands).charges) :
    (Financial.inventoryAt (final rivals demands).source.input
      (ProgrammeHistory.visitAt (final rivals demands).source.input (EventStep.boundary charge.row.cursor))).filterMap
      (Financial.InstructionOrigin.instruction? (final rivals demands).source.input) = StageTrace.items charge.row := by
  exact StageTrace.final_financial_inventory_is_the_original_record_items original _ charge.row
    ((DemandScheduleExecution.generated_steps_are_actual_ordered_paid_occurrences (fun _ => true) rivals _ original _ rfl demands).2.2.1 charge member)

theorem every_generated_history_retains_all_material_rows_whole_ledger_and_own_next
    (rivals : Nat → Opponent code) (demands : List Bool) :
    let facade := Feedback.Runtime.facade (final rivals demands).source (final rivals demands).entry rfl rfl
    let runtime := facade.seed.advance (EventStep.boundary (final rivals demands))
    (∀ row ∈ StageTrace.records original (report rivals demands).stages,
      (Financial.inventoryAt (final rivals demands).source.input
        (ProgrammeHistory.visitAt (final rivals demands).source.input (EventStep.boundary row.cursor))).filterMap
        (Financial.InstructionOrigin.instruction? (final rivals demands).source.input) = StageTrace.items row) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = facade.process.stateAt (facade.process.successor runtime.state) := by
  let facade := Feedback.Runtime.facade (final rivals demands).source (final rivals demands).entry rfl rfl
  have rooted := facade.readoutAt_factorizes (facade.seed.advance (EventStep.boundary (final rivals demands))) .feedback
  exact ⟨fun row member => StageTrace.final_financial_inventory_is_the_original_record_items original _ row member,
    rooted.2.2.1,rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandBallotConsumer
