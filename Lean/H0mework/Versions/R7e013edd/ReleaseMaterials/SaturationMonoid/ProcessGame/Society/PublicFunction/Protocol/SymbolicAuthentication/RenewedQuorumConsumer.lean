import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewedQuorumSource
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Runtime

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewedQuorumConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open RenewedQuorumSource (vocabulary slot)

abbrev resources : Repayment.Recovery.Resources := ⟨1,1,true⟩
abbrev code := RenewedQuorumSource.code resources 2 true
abbrev start := RenewedQuorumSource.start resources 2 true
abbrev protocols := RenewedQuorumSource.protocols resources 2 true
abbrev rivals := RenewedQuorumSource.rivals resources 2 true .normal
abbrev full := RenewedQuorumSource.full resources 2 true .normal
abbrev encoding := RenewedQuorumSource.encoding resources 2 true
abbrev reception := RenewedQuorumSource.reception resources 2 true 1
abbrev current (cut : Nat) := (AdaptiveDeliveryTrace.state start protocols rivals cut).current
abbrev row (cut : Nat) := StageTrace.material (AdaptiveDeliveryTrace.cursorAt start protocols rivals cut) (protocols cut) (rivals cut)

theorem exhaustion_generates_two_original_paid_renewal_rows (cycle : Fin 2) :
    (row (16 + 6 * cycle.val)).submitted = RenewedQuorumMaterial.word ∧
      RenewedQuorumMaterial.Inputs (row (16 + 6 * cycle.val)).before.current := by
  fin_cases cycle <;> constructor <;> decide +kernel

theorem every_actual_renewal_and_recycling_item_consumes_its_own_permission (cycle : Fin 2) :
    ∀ item ∈ StageTrace.items (row (16 + 6 * cycle.val)), code.law.Valid item.before item.request := by
  have actual := exhaustion_generates_two_original_paid_renewal_rows cycle
  change ∀ item ∈ RenewedQuorumMaterial.law.rawItems (row (16 + 6 * cycle.val)).before.current
    (row (16 + 6 * cycle.val)).submitted, _
  rw [actual.1]
  exact RenewedQuorumMaterial.actual_items _ actual.2

theorem the_exhausted_actual_current_generates_its_full_renewal_budget :
    (current 16).stock 1 .energy = 0 ∧ (current 16).stock 2 .energy = 0 ∧
      RenewedQuorumMaterial.capacity (current 16) = 2 ∧
      RenewedQuorumMaterial.run (current 16) (RenewedQuorumMaterial.capacity (current 16)) =
        RenewedQuorumMaterial.expected (current 16) (RenewedQuorumMaterial.capacity (current 16)) := by
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,?_⟩
  apply (RenewedQuorumMaterial.actual_fuel_generates_the_complete_renewed_service_budget (current 16) _).1
  have inputs := (exhaustion_generates_two_original_paid_renewal_rows ⟨0,by decide⟩).2
  exact ⟨inputs.material,by decide +kernel,inputs.labor,inputs.energy⟩

theorem original_material_and_finance_are_retained_after_both_phases :
    (current 41).stock 1 .feedstock = 2 ∧ (current 41).stock 1 .waste = 1 ∧
      (current 41).stock 1 .energy = 0 ∧ (current 41).stock 1 .labor = 0 ∧
      (current 41).stock 2 .energy = 0 ∧ (current 41).stock 2 .labor = 0 ∧
      (current 41).stock 1 .service = 0 ∧ (current 41).stock 0 .feedstock = 0 ∧
      (current 41).stock 0 .labor = 1 ∧ (current 41).claims () 1 2 = 7 ∧
      InterferenceEnvelope.spent start full = 0 := by
  repeat' constructor
  all_goals decide +kernel

theorem two_actual_phases_generate_four_paid_ballots_and_content_receipts :
    StageBudget.ledger vocabulary start full =
        [⟨6,0,0,1,slot false,true,1⟩,⟨8,0,1,1,slot false,true,1⟩,
         ⟨24,0,0,1,slot true,true,1⟩,⟨26,0,1,1,slot true,true,1⟩] ∧
      (StageTransport.wires vocabulary encoding start full).length = 4 ∧
      (StageReception.run vocabulary encoding reception start full 2 41).receipts.length = 4 := by
  repeat' constructor
  all_goals decide +kernel

theorem both_scope_decisions_are_generated_by_the_same_paid_recycling_history :
    RenewedQuorumSource.produce resources 2 true .normal 1 2 false = .ready true ∧
      RenewedQuorumSource.produce resources 2 true .normal 1 2 true = .ready true := by
  constructor <;> decide +kernel

theorem both_ready_phases_have_actual_quorum_decisions (second : Bool) :
    AdmittedStageQuorum.produce start vocabulary encoding reception full 2 (slot second) 2 = .decided true := by
  have ready : RenewedQuorumSource.produce resources 2 true .normal 1 2 second = .ready true := by
    cases second
    · exact both_scope_decisions_are_generated_by_the_same_paid_recycling_history.1
    · exact both_scope_decisions_are_generated_by_the_same_paid_recycling_history.2
  exact (AdmittedAdaptiveWindow.generated_ready_window_decides_at_its_actual_source_deadline
    start vocabulary encoding reception protocols rivals 0 33 2 (slot second) 2 true ready).2.2.2

abbrev final := EventHistory.execute start full
abbrev facade := Feedback.Runtime.facade final.source final.entry rfl rfl
theorem all_material_and_communication_rows_share_the_final_financial_ledger_and_own_next :
    let runtime := facade.seed.advance (EventStep.boundary final)
    (∀ record ∈ StageTrace.records start full,
      (Financial.inventoryAt final.source.input (ProgrammeHistory.visitAt final.source.input (EventStep.boundary record.cursor))).filterMap
        (Financial.InstructionOrigin.instruction? final.source.input) = StageTrace.items record) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = facade.process.stateAt (facade.process.successor runtime.state) := by
  have rooted := facade.readoutAt_factorizes (facade.seed.advance (EventStep.boundary final)) .feedback
  exact ⟨fun record member => StageTrace.final_financial_inventory_is_the_original_record_items start full record member,
    rooted.2.2.1,rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewedQuorumConsumer
