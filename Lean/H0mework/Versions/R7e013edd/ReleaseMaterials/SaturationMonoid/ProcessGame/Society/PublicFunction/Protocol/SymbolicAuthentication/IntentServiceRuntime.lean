import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IntentServiceRun

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IntentServiceRuntime

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

private theorem row_lookup {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
    (cursor : Cursor code) (rule : Rule code) (rival : Opponent code) (count index : Nat) (bounded : index < count) :
    (StageTrace.records cursor (List.replicate count (rule, rival)))[index]? =
      some (StageTrace.material (ServiceClock.cursorAt cursor rule rival index) rule rival) := by
  induction count with
  | zero => omega
  | succ count ih =>
    rw [List.replicate_succ', StageQueue.records_append, ServiceClock.installed_stages_are_the_actual_service_cursor]
    rw [List.getElem?_append, StageTrace.record_count, List.length_replicate]
    split
    · exact ih (by omega)
    · have same : index = count := by omega
      subst index
      simp [StageTrace.records]

variable
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (past : List (EventHistory.Stage (code := model.source.code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
  (rival : Opponent model.source.code) (scope : Scope) (threshold : Nat)

abbrev service := IntentServiceRun.produce vocabulary encoding law start past rival
abbrev full := JointReceivedRuntime.full model start (service model start past vocabulary encoding law rival).stages vocabulary encoding law
abbrev facade := JointReceivedRuntime.facade model start (service model start past vocabulary encoding law rival).stages vocabulary encoding law scope threshold
abbrev runtime := JointReceivedRuntime.runtime model start (service model start past vocabulary encoding law rival).stages vocabulary encoding law scope threshold
abbrev rooted := JointReceivedRuntime.rooted model start (service model start past vocabulary encoding law rival).stages vocabulary encoding law scope threshold

theorem the_same_original_root_keeps_every_actual_service_submission
    (serviced : (service model start past vocabulary encoding law rival).status = .serviced)
    (site : Fin model.source.code.sites) (needed : RetainedIntent.intent vocabulary encoding law start past site ≠ []) :
    ∃ index < IntentServiceRun.used vocabulary encoding law start past rival,
      ∃ row ∈ StageTrace.records start (full model start past vocabulary encoding law rival),
        row = IntentServiceProgress.row vocabulary encoding law start past rival index ∧
        StageTrace.activation row = some site ∧ row.submitted = RetainedIntent.intent vocabulary encoding law start past site ∧
        (row.cursor.cut, RequestAttestation.audit vocabulary row) ∈ (rooted model start past vocabulary encoding law rival scope threshold).audit := by
  obtain ⟨index, bounded, owned, submitted, _, _⟩ :=
    IntentServiceRun.every_entry_intent_has_an_actual_nonempty_submission_before_the_deadline vocabulary encoding law start past rival serviced site needed
  let row := IntentServiceProgress.row vocabulary encoding law start past rival index
  have inSuffix : row ∈ StageTrace.records (RetainedIntent.origin start past) (IntentServiceRun.suffix vocabulary encoding law start past rival) :=
    List.mem_of_getElem? (row_lookup _ _ _ _ index bounded)
  have inService : row ∈ StageTrace.records start (service model start past vocabulary encoding law rival).stages := by
    rw [(IntentServiceRun.service_facts vocabulary encoding law start past rival serviced).2.2, StageQueue.records_append]
    exact List.mem_append_right _ inSuffix
  have inFull : row ∈ StageTrace.records start (full model start past vocabulary encoding law rival) := by
    obtain ⟨more, generated⟩ := JointReceivedRun.every_run_keeps_the_whole_source_history model start vocabulary encoding law
      (service model start past vocabulary encoding law rival).stages.length
      (JointReceivedResponse.fuel model start (service model start past vocabulary encoding law rival).stages)
      (service model start past vocabulary encoding law rival).stages
    change (service model start past vocabulary encoding law rival).stages ++ more = full model start past vocabulary encoding law rival at generated
    rw [← generated, StageQueue.records_append]
    exact List.mem_append_left _ inService
  refine ⟨index, bounded, row, inFull, rfl, owned, submitted, ?_⟩
  rw [(rooted model start past vocabulary encoding law rival scope threshold).audit_exact]
  exact List.mem_map.mpr ⟨row, inFull, rfl⟩

theorem bounded_service_consumes_its_entry_receipt_actual_rejection_ledger_and_next
    (serviced : (service model start past vocabulary encoding law rival).status = .serviced)
    (site : Fin model.source.code.sites) (needed : RetainedIntent.intent vocabulary encoding law start past site ≠ []) :
    let state := runtime model start past vocabulary encoding law rival scope threshold
    (∃ body ∈ (ReceivedStatementAuthentication.generate vocabulary encoding law start (past.map Prod.fst) past.length
        (RetainedIntent.memory start past site) site (RetainedIntent.memory start past site)).statements,
      ∃ receipt ∈ (RequestReadback.produce vocabulary encoding law start past site past.length).receipts,
        receipt.statement = body) ∧
    (∃ index < IntentServiceRun.used vocabulary encoding law start past rival,
      ∃ row ∈ StageTrace.records start (full model start past vocabulary encoding law rival),
        row = IntentServiceProgress.row vocabulary encoding law start past rival index ∧
        StageTrace.activation row = some site ∧ row.submitted = RetainedIntent.intent vocabulary encoding law start past site ∧
        (row.cursor.cut, RequestAttestation.audit vocabulary row) ∈ (rooted model start past vocabulary encoding law rival scope threshold).audit) ∧
    HEq state.tick.generated.wholeLedgerWriteBack
      (state.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt state.current.visit.current) ∧
    state.tick.nextCurrent = (facade model start past vocabulary encoding law rival scope threshold).process.stateAt
      ((facade model start past vocabulary encoding law rival scope threshold).process.successor state.state) := by
  have factor := (facade model start past vocabulary encoding law rival scope threshold).readoutAt_factorizes
    (runtime model start past vocabulary encoding law rival scope threshold) .joint
  exact ⟨RetainedIntent.retained_intent_has_its_original_paid_receipt vocabulary encoding law start past site needed,
    the_same_original_root_keeps_every_actual_service_submission model start past vocabulary encoding law rival scope threshold serviced site needed,
    factor.2.2.1, factor.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IntentServiceRuntime
