import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandTransitSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandTransitConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedQuorumConsumer (code)
open DemandScheduleConsumer (original quiet attempted)
open DemandBallotSource (vocabulary ballots)
open DemandTransitSource

abbrev actual := full quiet true
abbrev received (delay : Nat) := StageReception.run vocabulary (encoding quiet) (reception delay) original actual 2 actual.length
def idle : Rule code := ⟨⟨DemandSchedulePolicy.work true,DemandSchedulePolicy.work_generated true⟩,
  fun _ _ => ⟨none,List.mem_cons_self⟩⟩
def withoutOrigin := actual.set 2 (idle,EventStep.fixed none)
def withoutSupply := actual.set 12 (idle,EventStep.fixed none)
def withoutDelivery := actual.set 13 (idle,EventStep.fixed none)
def forgedEncoding : StageTransport.Encoding (code := code) :=
  fun signal => (encoding quiet signal).map fun body => {body with actor := 0}

theorem the_original_resource_gap_pays_signing_send_and_delivery_before_its_clock :
    (signed quiet).status = .finished ∧ (ballots (signed quiet)).length = 2 ∧
      window quiet = 13 ∧ (final quiet true).cut = 34 ∧
      (tail quiet true).state.current.stock 0 .feedstock = 0 ∧
      (tail quiet true).state.current.stock 1 .service = 0 ∧
      (StageTransport.wires vocabulary (encoding quiet) original actual).map
        (fun wire => (wire.sendCut,wire.serial,wire.ballot.cut,wire.ballot.key.val)) =
          [(24,2,18,0),(32,3,20,1)] ∧
      (received 5).receipts.map (fun receipt => (receipt.delivery,receipt.wire.serial,receipt.wire.ballot.key.val)) =
        [(29,2,0),(33,3,1)] ∧
      produce quiet true 5 = .decided true := by
  decide +kernel

theorem the_second_supply_is_an_actual_paid_material_row_in_the_same_history :
    ∃ row ∈ StageTrace.records original actual,
      row.cursor.cut = 28 ∧ row.submitted = RenewedQuorumMaterial.word ∧
        DemandRenewalStep.refill row.before.current = true ∧
        (StageTrace.audit row).all Prod.snd = true := by
  exact ⟨(StageTrace.records original actual)[12]'(by decide +kernel),List.getElem_mem _,by decide +kernel⟩

theorem withholding_and_insufficient_timing_are_distinct_actual_failures :
    produce quiet false 5 = .blocked .missingQuorum ∧
      (StageReception.run vocabulary (encoding quiet) (reception 5) original (full quiet false) 2
        (full quiet false).length).receipts = [] ∧
      (tail quiet false).state.current.stock 1 .service = 2 ∧
      produce quiet true 4 = .blocked .missingQuorum ∧
      (received 4).receipts.length = 1 := by
  decide +kernel

theorem removing_actual_source_supply_or_delivery_cannot_be_repaired_by_a_readout :
    StageBudget.verify vocabulary original withoutOrigin
      ⟨18,0,0,1,RenewedQuorumSource.slot true,true,1⟩ = false ∧
      InterfaceQuorum.produce original vocabulary (encoding quiet) (reception 5) withoutSupply 2
        (RenewedQuorumSource.slot true) 2 = .blocked .missingQuorum ∧
      InterfaceQuorum.produce original vocabulary (encoding quiet) (reception 5) withoutDelivery 2
        (RenewedQuorumSource.slot true) 2 = .blocked .missingQuorum ∧
      InterfaceQuorum.produce original vocabulary forgedEncoding (reception 5) actual 2
        (RenewedQuorumSource.slot true) 2 = .blocked .missingQuorum := by
  decide +kernel

theorem an_actual_interface_deviation_coexists_with_the_paid_quorum :
    produce attempted true 5 = .decided true ∧
      ∃ row ∈ StageTrace.records original (full attempted true),
        row.cursor.cut = 17 ∧ ControlExecution.suppressed code row.call = true ∧ row.submitted = [] := by
  exact ⟨by decide +kernel,
    (StageTrace.records original (full attempted true))[1]'(by decide +kernel),List.getElem_mem _,by decide +kernel⟩

theorem every_actual_received_vote_retains_its_owned_paid_source
    (receipt : StageReception.Receipt (code := code)) (inside : receipt ∈ (received 5).receipts) :
    receipt.wire.ballot ∈ StageBudget.ledger vocabulary original actual := by
  exact StageQuorum.supporting_receipt_has_actual_owned_paid_origin vocabulary (encoding quiet) (reception 5)
    original actual 2 actual.length receipt inside

theorem every_other_generated_decision_agrees_with_the_actual_completed_source
    (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) (value : Bool)
    (decided : InterfaceQuorum.produce original vocabulary (encoding quiet) (reception 5) stages receiver
      (RenewedQuorumSource.slot true) 2 = .decided value) : value = true := by
  exact InterfaceQuorum.produced_decisions_agree_across_all_generated_protocols_and_networks original vocabulary
    (encoding quiet) (reception 5) stages actual receiver 2 (RenewedQuorumSource.slot true) 2 value true decided
    the_original_resource_gap_pays_signing_send_and_delivery_before_its_clock.2.2.2.2.2.2.2.2

theorem every_generated_transit_retains_all_financial_rows_whole_ledger_and_own_next
    (callbacks : Nat → Opponent code) (enabled : Bool) :
    let facade := Feedback.Runtime.facade (final callbacks enabled).source (final callbacks enabled).entry rfl rfl
    let runtime := facade.seed.advance (EventStep.boundary (final callbacks enabled))
    (∀ row ∈ StageTrace.records original (full callbacks enabled),
      (Financial.inventoryAt (final callbacks enabled).source.input
        (ProgrammeHistory.visitAt (final callbacks enabled).source.input (EventStep.boundary row.cursor))).filterMap
        (Financial.InstructionOrigin.instruction? (final callbacks enabled).source.input) = StageTrace.items row) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = facade.process.stateAt (facade.process.successor runtime.state) := by
  let facade := Feedback.Runtime.facade (final callbacks enabled).source (final callbacks enabled).entry rfl rfl
  have rooted := facade.readoutAt_factorizes (facade.seed.advance (EventStep.boundary (final callbacks enabled))) .feedback
  exact ⟨fun row member => StageTrace.final_financial_inventory_is_the_original_record_items original _ row member,
    rooted.2.2.1,rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandTransitConsumer
