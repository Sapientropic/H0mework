import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalCommandRun

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalCommandConsumer
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open LocalCommandSource LocalCommandRun

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (state : LocalCommandRun.State model start)

theorem every_generated_ballot_has_an_actual_input_row
    (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (body : StageBudget.Ballot (code := model.source.code))
    (inside : body ∈ StageBudget.ledger vocabulary start state.stages) :
    ∃ entry ∈ state.entries, ∃ position, StageBudget.issued vocabulary (entry.row model) position = some body := by
  obtain ⟨row,member,position,issued⟩ := StageBudget.ledger_origin vocabulary start state.stages body inside
  rw [← state.row_exact] at member
  obtain ⟨entry,included,same⟩ := List.mem_map.mp member
  exact ⟨entry,included,position,same ▸ issued⟩

theorem actual_native_audit_retains_all_submitted_requests_including_rejections
    (entry : LocalCommandSource.Entry model) (inside : entry ∈ state.entries) :
    entry.row model ∈ StageTrace.records start state.stages ∧
    (StageTrace.audit (entry.row model)).map (fun item => item.1.request) = (entry.row model).submitted ∧
    ∀ item ∈ StageTrace.audit (entry.row model), item.2 = true ↔ model.source.code.law.Valid item.1.before item.1.request :=
  ⟨each_attempt_row_is_an_original_execution_record model start state entry inside,
    StageTrace.audit_retains_every_request_and_its_actual_validity (entry.row model)⟩

theorem a_submitted_native_refusal_keeps_its_actual_state_and_zero_financial_flow
    (entry : LocalCommandSource.Entry model)
    (item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument × Bool)
    (inside : item ∈ StageTrace.audit (entry.row model)) (refused : item.2 = false) :
    model.source.code.law.step item.1.before item.1.request = item.1.before ∧
      model.source.code.law.actualDebit item.1.before item.1.request = [] ∧
      model.source.code.law.actualCredit item.1.before item.1.request = [] :=
  StageTrace.rejected_request_has_no_material_or_financial_debit (entry.row model) item inside refused

theorem native_permission_is_derived_from_the_actual_audited_command
    (entry : LocalCommandSource.Entry model)
    (item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument × Bool)
    (inside : item ∈ StageTrace.audit (entry.row model))
    (signer : Party) (command : Mandate.Command Party)
    (requested : item.1.request = Mandate.request model.scope item.1.before signer command)
    (accepted : item.2 = true) : Mandate.CanRun model.scope item.1.before signer command := by
  have valid := ((StageTrace.audit_retains_every_request_and_its_actual_validity (entry.row model)).2 item inside).mp accepted
  rw [requested,model.law_exact] at valid
  exact (Mandate.command_policy model.base model.scope _ _ _).mp valid.1.2

theorem all_source_attempt_rows_reach_original_finance_whole_ledger_and_next :
    let final := state.current model start
    let facade := Feedback.Runtime.facade final.source final.entry rfl rfl
    let runtime := facade.seed.advance (EventStep.boundary final)
    (∀ entry ∈ state.entries,
      (Financial.inventoryAt final.source.input
        (ProgrammeHistory.visitAt final.source.input (EventStep.boundary (entry.row model).cursor))).filterMap
        (Financial.InstructionOrigin.instruction? final.source.input) = StageTrace.items (entry.row model)) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = facade.process.stateAt (facade.process.successor runtime.state) := by
  have original := ActorStageConsumer.the_actual_source_keeps_all_financial_rows_whole_ledger_and_literal_next start state.stages
  exact ⟨fun entry inside => original.1 (entry.row model)
    (each_attempt_row_is_an_original_execution_record model start state entry inside),original.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalCommandConsumer
