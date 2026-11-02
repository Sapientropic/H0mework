import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.BatchReentry

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.BatchReentryRuntime

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
  (scope : Scope) (threshold : Nat)

abbrev result := BatchReentry.produce model start vocabulary encoding law past
abbrev full := JointReceivedRuntime.full model start (result model start past vocabulary encoding law).stages vocabulary encoding law
abbrev actualBound := JointReceivedRuntime.actualBound model start (result model start past vocabulary encoding law).stages vocabulary encoding law
abbrev ordinal := JointReceivedRuntime.ordinal model start (result model start past vocabulary encoding law).stages vocabulary encoding law

structure Census where
  private mk ::
  batch : BatchReentry.Result model
  batch_exact : batch = result model start past vocabulary encoding law
  joint : JointReceivedRuntime.Census model start (result model start past vocabulary encoding law).stages vocabulary encoding law

def generate : Census model start past vocabulary encoding law :=
  ⟨result model start past vocabulary encoding law, rfl,
    JointReceivedRuntime.generate model start (result model start past vocabulary encoding law).stages vocabulary encoding law⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (actualBound model start past vocabulary encoding law).source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (actualBound model start past vocabulary encoding law).source.input
      (ordinal model start past vocabulary encoding law)).current → Census model start past vocabulary encoding law
  project := fun _ {_} _ _ _own => generate model start past vocabulary encoding law

def parentRoot := JointReceivedRuntime.root model start (result model start past vocabulary encoding law).stages vocabulary encoding law scope threshold
def root := (parentRoot model start past vocabulary encoding law scope threshold).withProjectionCoface
  (projectionLaw model start past vocabulary encoding law)

theorem original_emitter_root_is_preserved :
    (root model start past vocabulary encoding law scope threshold).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (actualBound model start past vocabulary encoding law).source.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (index : Nat) : SourceNativeLivingRootCurrentAt
    (ProgrammeSource.N (actualBound model start past vocabulary encoding law).source.input) :=
  ⟨ProgrammeSource.V (actualBound model start past vocabulary encoding law).source.input,
    root model start past vocabulary encoding law scope threshold,
    ProgrammeHistory.temporalVisit (actualBound model start past vocabulary encoding law).source.input index⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (actualBound model start past vocabulary encoding law).source.input) where
  State := Nat
  stateAt := stateAt model start past vocabulary encoding law scope threshold
  stateAt_injective := by
    intro first second same
    have labels := congrArg (fun state : SourceNativeLivingRootCurrentAt
        (ProgrammeSource.N (actualBound model start past vocabulary encoding law).source.input) =>
      (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (actualBound model start past vocabulary encoding law).source.input first).current =
        (ProgrammeHistory.visitAt (actualBound model start past vocabulary encoding law).source.input second).current :=
      eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun index => ⟨index + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : JointReceivedRuntime.Face)
  | batch

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (actualBound model start past vocabulary encoding law).source.input) where
  process := process model start past vocabulary encoding law scope threshold
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous =>
      (JointReceivedRuntime.facade model start (result model start past vocabulary encoding law).stages vocabulary encoding law scope threshold).componentAt
        (JointReceivedRuntime.facade model start (result model start past vocabulary encoding law).stages vocabulary encoding law scope threshold).seed previous
    | .batch => projectionLaw model start past vocabulary encoding law
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((JointReceivedRuntime.facade model start (result model start past vocabulary encoding law).stages vocabulary encoding law scope threshold).installationAt
        (JointReceivedRuntime.facade model start (result model start past vocabulary encoding law).stages vocabulary encoding law scope threshold).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (parentRoot model start past vocabulary encoding law scope threshold).toAuthoritativeRoot.source
          (projectionLaw model start past vocabulary encoding law))
    | batch =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (parentRoot model start past vocabulary encoding law scope threshold).toAuthoritativeRoot.source
        (projectionLaw model start past vocabulary encoding law)
  projectionAt := fun _ face => match face with
    | .previous previous =>
      (JointReceivedRuntime.facade model start (result model start past vocabulary encoding law).stages vocabulary encoding law scope threshold).projectionAt
        (JointReceivedRuntime.facade model start (result model start past vocabulary encoding law).stages vocabulary encoding law scope threshold).seed previous
    | .batch => ()

def activated (index : Nat) : LivingRuntimeState (process model start past vocabulary encoding law scope threshold) :=
  (facade model start past vocabulary encoding law scope threshold).seed.advance index

theorem activated_state_is_the_generated_ordinal (index : Nat) :
    (activated model start past vocabulary encoding law scope threshold index).state = index := by
  induction index with
  | zero => rfl
  | succ index ih =>
    change Nat.succ (activated model start past vocabulary encoding law scope threshold index).state = Nat.succ index
    exact congrArg Nat.succ ih

abbrev runtime := activated model start past vocabulary encoding law scope threshold (ordinal model start past vocabulary encoding law)

def rooted : Census model start past vocabulary encoding law :=
  match (facade model start past vocabulary encoding law scope threshold).readoutAt
      (runtime model start past vocabulary encoding law scope threshold) .batch with
  | .inl value => value.2 (by
      change (ProgrammeHistory.visitAt (actualBound model start past vocabulary encoding law).source.input
        (activated model start past vocabulary encoding law scope threshold (ordinal model start past vocabulary encoding law)).state).current = _
      rw [activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

theorem completion_is_the_original_joint_gate
    (complete : (result model start past vocabulary encoding law).status = .jointComplete) :
    JointReceivedResponse.Clear model start vocabulary encoding law (result model start past vocabulary encoding law).stages.length
      (result model start past vocabulary encoding law).stages := by
  have clear := BatchReentry.completion_consumes_the_newest_same_cut_gates model start vocabulary encoding law _ past complete
  refine ⟨clear.1, List.all_eq_true.mpr ?_⟩
  intro site _
  apply decide_eq_true
  have snapshot := ReceivedStatementAuthentication.the_entering_snapshot_is_an_actual_local_record start
    (result model start past vocabulary encoding law).stages [] site
  rw [List.append_nil] at snapshot
  change ReceivedStatementAuthentication.work vocabulary encoding law start _ _ _ _ _ = []
  rw [snapshot]
  exact clear.2 site

theorem the_original_root_adds_no_stage_after_reentered_completion
    (complete : (result model start past vocabulary encoding law).status = .jointComplete) :
    full model start past vocabulary encoding law = (result model start past vocabulary encoding law).stages := by
  have clear := completion_is_the_original_joint_gate model start past vocabulary encoding law complete
  unfold full JointReceivedRuntime.full JointReceivedRuntime.result JointReceivedRun.produce
  cases fuel : JointReceivedResponse.fuel model start (result model start past vocabulary encoding law).stages with
  | zero => simp only [JointReceivedRun.run, if_pos clear]
  | succ count => simp only [JointReceivedRun.run, JointReceivedResponse.step, dif_pos clear]

theorem every_recorded_batch_retains_its_own_receipt_submission_and_full_outcome
    (entry : BatchReentry.Stages model)
    (recorded : entry ∈ (result model start past vocabulary encoding law).batches)
    (serviced : (BatchReentry.service model start vocabulary encoding law entry).status = .serviced)
    (site : Fin model.source.code.sites) (needed : RetainedIntent.intent vocabulary encoding law start entry site ≠ []) :
    (∃ body ∈ (ReceivedStatementAuthentication.generate vocabulary encoding law start (entry.map Prod.fst) entry.length
        (RetainedIntent.memory start entry site) site (RetainedIntent.memory start entry site)).statements,
      ∃ receipt ∈ (RequestReadback.produce vocabulary encoding law start entry site entry.length).receipts,
        receipt.statement = body) ∧
    ∃ row ∈ StageTrace.records start (full model start past vocabulary encoding law),
      StageTrace.activation row = some site ∧ row.submitted = RetainedIntent.intent vocabulary encoding law start entry site ∧
      (row.cursor.cut, RequestAttestation.audit vocabulary row) ∈ (rooted model start past vocabulary encoding law scope threshold).joint.audit := by
  refine ⟨RetainedIntent.retained_intent_has_its_original_paid_receipt vocabulary encoding law start entry site needed, ?_⟩
  obtain ⟨index, bounded, owned, submitted, _, _⟩ :=
    IntentServiceRun.every_entry_intent_has_an_actual_nonempty_submission_before_the_deadline vocabulary encoding law start entry
      (OriginQueue.environment start) serviced site needed
  let row := IntentServiceProgress.row vocabulary encoding law start entry (OriginQueue.environment start) index
  have inSuffix : row ∈ StageTrace.records (RetainedIntent.origin start entry)
      (IntentServiceRun.suffix vocabulary encoding law start entry (OriginQueue.environment start)) :=
    List.mem_of_getElem? (row_lookup _ _ _ _ index bounded)
  have inService : row ∈ StageTrace.records start (BatchReentry.service model start vocabulary encoding law entry).stages := by
    rw [(IntentServiceRun.service_facts vocabulary encoding law start entry (OriginQueue.environment start) serviced).2.2,
      StageQueue.records_append]
    exact List.mem_append_right _ inSuffix
  obtain ⟨later, next⟩ := (BatchReentry.every_recorded_batch_is_executed_in_the_final_history model start vocabulary encoding law
    _ past entry recorded).2
  have inResult : row ∈ StageTrace.records start (result model start past vocabulary encoding law).stages := by
    change (BatchReentry.service model start vocabulary encoding law entry).stages ++ later =
      (result model start past vocabulary encoding law).stages at next
    rw [← next, StageQueue.records_append]
    exact List.mem_append_left _ inService
  obtain ⟨more, generated⟩ := JointReceivedRun.every_run_keeps_the_whole_source_history model start vocabulary encoding law
    (result model start past vocabulary encoding law).stages.length _ (result model start past vocabulary encoding law).stages
  have inFull : row ∈ StageTrace.records start (full model start past vocabulary encoding law) := by
    change (result model start past vocabulary encoding law).stages ++ more = full model start past vocabulary encoding law at generated
    rw [← generated, StageQueue.records_append]
    exact List.mem_append_left _ inResult
  refine ⟨row, inFull, owned, submitted, ?_⟩
  rw [(rooted model start past vocabulary encoding law scope threshold).joint.audit_exact]
  exact List.mem_map.mpr ⟨row, inFull, rfl⟩

theorem all_cross_batch_actual_attempts_share_the_original_source_capacity
    (accepted : SourceResponseCapacity.inspect model.source.code = true) :
    ResponseCapacity.count start (result model start past vocabulary encoding law).stages +
      ResponseCapacity.rank (EventHistory.execute start (result model start past vocabulary encoding law).stages) ≤
        ResponseCapacity.rank start :=
  ResponseCapacity.the_actual_source_pays_for_every_productive_response
    (SourceResponseCapacity.checked_source_generates_its_absorption_law model.source.code accepted) start _

theorem a_source_funded_new_batch_generates_its_own_receipt_and_actual_response
    (entry : BatchReentry.Stages model)
    (recorded : entry ∈ (result model start past vocabulary encoding law).batches)
    (accepted : RetainedIntent.inspect vocabulary encoding law start entry = true)
    (budget : IntentServiceRun.horizon start entry ≤ BatchReentry.fuel model start entry)
    (site : Fin model.source.code.sites) (needed : RetainedIntent.intent vocabulary encoding law start entry site ≠ []) :
    (∃ receipt ∈ (RequestReadback.produce vocabulary encoding law start entry site entry.length).receipts,
      receipt.statement ∈ (ReceivedStatementAuthentication.generate vocabulary encoding law start (entry.map Prod.fst) entry.length
        (RetainedIntent.memory start entry site) site (RetainedIntent.memory start entry site)).statements) ∧
    ∃ row ∈ StageTrace.records start (full model start past vocabulary encoding law),
      StageTrace.activation row = some site ∧ row.submitted = RetainedIntent.intent vocabulary encoding law start entry site ∧
      (row.cursor.cut, RequestAttestation.audit vocabulary row) ∈ (rooted model start past vocabulary encoding law scope threshold).joint.audit := by
  have serviced := IntentServiceRun.the_source_budget_guarantees_service vocabulary encoding law start entry
    (OriginQueue.environment start) accepted budget
  obtain ⟨⟨body, known, receipt, received, same⟩, actual⟩ :=
    every_recorded_batch_retains_its_own_receipt_submission_and_full_outcome model start past vocabulary encoding law scope threshold
      entry recorded serviced site needed
  exact ⟨⟨receipt, received, by rw [same]; exact known⟩, actual⟩

theorem completion_disposes_every_responsibility_born_in_any_batch
    (complete : (result model start past vocabulary encoding law).status = .jointComplete) :
    LocalJointResponse.Clear model start vocabulary encoding law (full model start past vocabulary encoding law) ∧
      ∀ site, RetainedIntent.intent vocabulary encoding law start (full model start past vocabulary encoding law) site = [] := by
  rw [the_original_root_adds_no_stage_after_reentered_completion model start past vocabulary encoding law complete]
  exact BatchReentry.completion_consumes_the_newest_same_cut_gates model start vocabulary encoding law _ past complete

theorem the_original_root_consumes_reentered_history_ledger_and_literal_next :
    let state := runtime model start past vocabulary encoding law scope threshold
    past <+: full model start past vocabulary encoding law ∧
    HEq state.tick.generated.wholeLedgerWriteBack
      (state.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt state.current.visit.current) ∧
    state.tick.nextCurrent = (facade model start past vocabulary encoding law scope threshold).process.stateAt
      ((facade model start past vocabulary encoding law scope threshold).process.successor state.state) := by
  have kept := BatchReentry.every_run_keeps_the_whole_history model start vocabulary encoding law
    (BatchReentry.fuel model start past) past
  have next := JointReceivedRun.every_run_keeps_the_whole_source_history model start vocabulary encoding law
    (result model start past vocabulary encoding law).stages.length
    (JointReceivedResponse.fuel model start (result model start past vocabulary encoding law).stages)
    (result model start past vocabulary encoding law).stages
  have factor := (facade model start past vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime model start past vocabulary encoding law scope threshold) .batch
  exact ⟨kept.trans next, factor.2.2.1, factor.2.2.2.2⟩

theorem the_installed_disposition_keeps_completion_refusal_and_exhaustion_distinct :
    let state := runtime model start past vocabulary encoding law scope threshold
    let batch := (rooted model start past vocabulary encoding law scope threshold).batch
    batch = result model start past vocabulary encoding law ∧
    (batch.status = .jointComplete →
      LocalJointResponse.Clear model start vocabulary encoding law (full model start past vocabulary encoding law) ∧
        ∀ site, RetainedIntent.intent vocabulary encoding law start (full model start past vocabulary encoding law) site = []) ∧
    (batch.status = .exhausted → BatchReentry.fuel model start batch.stages = 0 ∧
      ¬ BatchReentry.Clear model start vocabulary encoding law batch.stages) ∧
    HEq ((facade model start past vocabulary encoding law scope threshold).readoutAt state .batch)
      (state.tick.generated.projectionOutcome (.component ())) ∧
    HEq state.tick.generated.wholeLedgerWriteBack
      (state.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt state.current.visit.current) ∧
    state.tick.nextCurrent = (facade model start past vocabulary encoding law scope threshold).process.stateAt
      ((facade model start past vocabulary encoding law scope threshold).process.successor state.state) := by
  have exactBatch := (rooted model start past vocabulary encoding law scope threshold).batch_exact
  have factor := (facade model start past vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime model start past vocabulary encoding law scope threshold) .batch
  refine ⟨exactBatch, ?_, ?_, factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩
  · rw [exactBatch]
    exact completion_disposes_every_responsibility_born_in_any_batch model start past vocabulary encoding law
  · rw [exactBatch]
    exact BatchReentry.exhaustion_keeps_zero_fuel_and_an_unclosed_current_gate model start vocabulary encoding law _ past

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.BatchReentryRuntime
