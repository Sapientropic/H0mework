import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenRuntime

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenConsumer

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol Continuation
open ReceiptDrivenRuntime

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (programme : List (Rule model.source.code))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
  (allowance : Nat) (rival : Opponent model.source.code) (scope : Scope) (threshold : Nat)

abbrev answer := ReceiptDrivenRun.produce model start vocabulary encoding law allowance programme rival

theorem installed_completion_keeps_every_old_new_and_native_gate
    (accepted : (rooted model start programme vocabulary encoding law allowance rival scope threshold).answer.status = .jointComplete) :
    InterferenceValidity.Goal model start vocabulary encoding law
      (rooted model start programme vocabulary encoding law allowance rival scope threshold).answer.state := by
  rw [(rooted model start programme vocabulary encoding law allowance rival scope threshold).answer_exact] at accepted ⊢
  exact (ReceiptDrivenRun.success_keeps_the_entire_original_goal model start vocabulary encoding law allowance (ReceiptDrivenRun.template model start programme) [] (fun _ => []) rival accepted).2

private theorem preserve_rows (first second : BatchReentry.Stages model) (kept : first <+: second)
    (row : StageTrace.Record (code := model.source.code)) (inside : row ∈ StageTrace.records start first) :
    row ∈ StageTrace.records start second := by
  obtain ⟨suffix, rfl⟩ := kept
  rw [StageQueue.records_append]
  exact List.mem_append_left _ inside

theorem every_recovered_entry_keeps_its_original_receipt_valid_word_and_root_audit
    (accepted : (rooted model start programme vocabulary encoding law allowance rival scope threshold).answer.status = .jointComplete)
    (entry : BatchReentry.Stages model)
    (registered : entry ∈ (rooted model start programme vocabulary encoding law allowance rival scope threshold).answer.state.batches)
    (site : Fin model.source.code.sites) (needed : RetainedIntent.intent vocabulary encoding law start entry site ≠ []) :
    (∃ body ∈ (ReceivedStatementAuthentication.generate vocabulary encoding law start (entry.map Prod.fst) entry.length
        (RetainedIntent.memory start entry site) site (RetainedIntent.memory start entry site)).statements,
      ∃ receipt ∈ (RequestReadback.produce vocabulary encoding law start entry site entry.length).receipts, receipt.statement = body) ∧
    ∃ row ∈ StageTrace.records start (full model start programme vocabulary encoding law allowance rival),
      StageTrace.activation row = some site ∧ row.submitted = RetainedIntent.intent vocabulary encoding law start entry site ∧
      (∀ item ∈ StageTrace.items row, model.source.code.law.Valid item.before item.request) ∧
      (row.cursor.cut, RequestAttestation.audit vocabulary row) ∈
        (rooted model start programme vocabulary encoding law allowance rival scope threshold).parent.joint.audit := by
  have ready := installed_completion_keeps_every_old_new_and_native_gate model start programme vocabulary encoding law allowance rival scope threshold accepted
  obtain ⟨index, _, _, row, found, owned, submitted, valid, _⟩ := ready.2 entry registered site needed
  have member := List.mem_of_getElem? found
  rw [(rooted model start programme vocabulary encoding law allowance rival scope threshold).answer_exact] at member
  have literal : actual model start programme vocabulary encoding law allowance rival =
      (answer model start programme vocabulary encoding law allowance rival).state.past := by unfold actual; rfl
  rw [← literal] at member
  have kept := (BatchReentryRuntime.the_original_root_consumes_reentered_history_ledger_and_literal_next
    model start (actual model start programme vocabulary encoding law allowance rival) vocabulary encoding law scope threshold).1
  have inRoot := preserve_rows model start _ _ kept row member
  refine ⟨RetainedIntent.retained_intent_has_its_original_paid_receipt vocabulary encoding law start entry site needed,
    row, inRoot, owned, submitted, valid, ?_⟩
  rw [(rooted model start programme vocabulary encoding law allowance rival scope threshold).parent.joint.audit_exact]
  exact List.mem_map.mpr ⟨row, inRoot, rfl⟩

private theorem native_completion_keeps_its_input_literal (ended : BatchReentry.Stages model)
    (clear : BatchReentry.Clear model start vocabulary encoding law ended) :
    (BatchReentryRuntime.result model start ended vocabulary encoding law).status = .jointComplete ∧
    (BatchReentryRuntime.result model start ended vocabulary encoding law).stages = ended := by
  unfold BatchReentryRuntime.result BatchReentry.produce
  cases count : BatchReentry.fuel model start ended with
  | zero => simp only [BatchReentry.run, if_pos clear, and_self]
  | succ count => simp only [BatchReentry.run, BatchReentry.step, dif_pos clear.2, dif_pos clear.1, and_self]

theorem completed_history_is_consumed_by_the_root_without_further_stages
    (accepted : (rooted model start programme vocabulary encoding law allowance rival scope threshold).answer.status = .jointComplete) :
    full model start programme vocabulary encoding law allowance rival = actual model start programme vocabulary encoding law allowance rival := by
  have clear := (installed_completion_keeps_every_old_new_and_native_gate model start programme vocabulary encoding law allowance rival scope threshold accepted).1.1
  rw [(rooted model start programme vocabulary encoding law allowance rival scope threshold).answer_exact] at clear
  have literal : actual model start programme vocabulary encoding law allowance rival =
      (answer model start programme vocabulary encoding law allowance rival).state.past := by unfold actual; rfl
  rw [← literal] at clear
  have stopped := native_completion_keeps_its_input_literal model start vocabulary encoding law _ clear
  exact (BatchReentryRuntime.the_original_root_adds_no_stage_after_reentered_completion model start _ vocabulary encoding law stopped.1).trans stopped.2

theorem the_same_root_consumes_history_entire_ledger_and_literal_next :
    let state := runtime model start programme vocabulary encoding law allowance rival scope threshold
    actual model start programme vocabulary encoding law allowance rival <+: full model start programme vocabulary encoding law allowance rival ∧
    HEq ((facade model start programme vocabulary encoding law allowance rival scope threshold).readoutAt state .recovery)
      (state.tick.generated.projectionOutcome (.component ())) ∧
    HEq state.tick.generated.wholeLedgerWriteBack
      (state.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt state.current.visit.current) ∧
    state.tick.nextCurrent = (facade model start programme vocabulary encoding law allowance rival scope threshold).process.stateAt
      ((facade model start programme vocabulary encoding law allowance rival scope threshold).process.successor state.state) := by
  have original := BatchReentryRuntime.the_original_root_consumes_reentered_history_ledger_and_literal_next
    model start (actual model start programme vocabulary encoding law allowance rival) vocabulary encoding law scope threshold
  have factor := (facade model start programme vocabulary encoding law allowance rival scope threshold).readoutAt_factorizes
    (runtime model start programme vocabulary encoding law allowance rival scope threshold) .recovery
  exact ⟨original.1, factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenConsumer
