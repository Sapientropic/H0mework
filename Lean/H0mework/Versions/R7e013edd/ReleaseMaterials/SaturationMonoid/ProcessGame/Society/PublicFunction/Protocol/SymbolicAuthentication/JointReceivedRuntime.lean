import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceivedRun

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceivedRuntime

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (past : List (EventHistory.Stage (code := model.source.code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code))
  (law : StageReception.Law model.source.code) (scope : Scope) (threshold : Nat)

abbrev result := JointReceivedRun.produce model start vocabulary encoding law past.length past
abbrev full := (result model start past vocabulary encoding law).stages
abbrev final := RequestReadbackRuntime.final model start (full model start past vocabulary encoding law) vocabulary encoding law
abbrev actualBound := RequestReadbackRuntime.actualBound model start (full model start past vocabulary encoding law) vocabulary encoding law
abbrev ordinal := RequestReadbackRuntime.ordinal model start (full model start past vocabulary encoding law) vocabulary encoding law
abbrev requests := RequestReadbackRuntime.inheritedRequests model start (full model start past vocabulary encoding law) vocabulary encoding law scope threshold
abbrev authority := RequestReadbackRuntime.authority model start (full model start past vocabulary encoding law) vocabulary encoding law scope threshold

abbrev Audit := List (Nat × List (ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument ×
  RequestAttestation.Outcome (code := model.source.code)))

structure Census where
  private mk ::
  response : JointReceivedRun.Result model
  response_exact : response = result model start past vocabulary encoding law
  audit : Audit model
  audit_exact : audit = (StageTrace.records start (full model start past vocabulary encoding law)).map
    (fun row => (row.cursor.cut, RequestAttestation.audit vocabulary row))

def generate : Census model start past vocabulary encoding law :=
  ⟨result model start past vocabulary encoding law, rfl,
    (StageTrace.records start (full model start past vocabulary encoding law)).map
      (fun row => (row.cursor.cut, RequestAttestation.audit vocabulary row)), rfl⟩

theorem the_actual_root_ends_at_the_generated_joint_history :
    RequestReadbackRuntime.full model start (full model start past vocabulary encoding law) vocabulary encoding law =
      full model start past vocabulary encoding law :=
  JointReceivedRun.the_original_joint_continuation_adds_no_stage model start vocabulary encoding law past.length past

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

-- The new projection extends the same completed source; the prior faces remain installed.
def parentRoot := RequestReadbackRuntime.root model start (full model start past vocabulary encoding law) vocabulary encoding law scope threshold

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
  | previous (face : RequestReadbackRuntime.Face)
  | joint

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (actualBound model start past vocabulary encoding law).source.input) where
  process := process model start past vocabulary encoding law scope threshold
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous =>
      (RequestReadbackRuntime.facade model start (full model start past vocabulary encoding law) vocabulary encoding law scope threshold).componentAt
        (RequestReadbackRuntime.facade model start (full model start past vocabulary encoding law) vocabulary encoding law scope threshold).seed previous
    | .joint => projectionLaw model start past vocabulary encoding law
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((RequestReadbackRuntime.facade model start (full model start past vocabulary encoding law) vocabulary encoding law scope threshold).installationAt
        (RequestReadbackRuntime.facade model start (full model start past vocabulary encoding law) vocabulary encoding law scope threshold).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (parentRoot model start past vocabulary encoding law scope threshold).toAuthoritativeRoot.source
          (projectionLaw model start past vocabulary encoding law))
    | joint =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (parentRoot model start past vocabulary encoding law scope threshold).toAuthoritativeRoot.source
        (projectionLaw model start past vocabulary encoding law)
  projectionAt := fun _ face => match face with
    | .previous previous => (RequestReadbackRuntime.facade model start (full model start past vocabulary encoding law) vocabulary encoding law scope threshold).projectionAt
        (RequestReadbackRuntime.facade model start (full model start past vocabulary encoding law) vocabulary encoding law scope threshold).seed previous
    | .joint => ()

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
      (runtime model start past vocabulary encoding law scope threshold) .joint with
  | .inl value => value.2 (by
      change (ProgrammeHistory.visitAt (actualBound model start past vocabulary encoding law).source.input
        (activated model start past vocabulary encoding law scope threshold (ordinal model start past vocabulary encoding law)).state).current = _
      rw [activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

theorem the_same_root_keeps_every_actual_request_and_its_rejection :
    ((rooted model start past vocabulary encoding law scope threshold).audit).map
      (fun entry => (entry.1, entry.2.map (fun item => item.1.request))) =
      (StageTrace.records start (full model start past vocabulary encoding law)).map
        (fun row => (row.cursor.cut, row.submitted)) := by
  change ((StageTrace.records start (full model start past vocabulary encoding law)).map
    (fun row => (row.cursor.cut, RequestAttestation.audit vocabulary row))).map _ = _
  rw [List.map_map]
  apply List.map_congr_left
  intro row _
  dsimp only [Function.comp_def]
  rw [RequestAttestation.the_audit_keeps_every_original_request]

theorem the_same_root_consumes_joint_response_completion_or_actual_exhaustion_ledger_and_next :
    let state := runtime model start past vocabulary encoding law scope threshold
    let response := (rooted model start past vocabulary encoding law scope threshold).response
    (response.status = .jointComplete →
      LocalJointResponse.Clear model start vocabulary encoding law response.stages ∧
      ∀ site, ReceivedStatementAuthentication.work vocabulary encoding law start (response.stages.map Prod.fst) past.length
        (ReceivedStatementAuthentication.remembered start response.stages past.length site) site
        ((EventStep.seed (EventHistory.execute start response.stages)).frame.inbox site) = []) ∧
    (response.status = .jointComplete ∨
      (response.status = .exhausted ∧ JointReceivedResponse.fuel model start response.stages = 0)) ∧
    RequestReadbackRuntime.full model start response.stages vocabulary encoding law = response.stages ∧
    (authority model start past vocabulary encoding law scope threshold).current = Native.Authority.fullGenerate
      (actualBound model start past vocabulary encoding law)
      ((final model start past vocabulary encoding law).source.history.length + 1 + (final model start past vocabulary encoding law).cut) ∧
    HEq ((facade model start past vocabulary encoding law scope threshold).readoutAt state .joint)
      (state.tick.generated.projectionOutcome (.component ())) ∧
    HEq state.tick.generated.wholeLedgerWriteBack
      (state.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt state.current.visit.current) ∧
    state.tick.nextCurrent = (facade model start past vocabulary encoding law scope threshold).process.stateAt
      ((facade model start past vocabulary encoding law scope threshold).process.successor state.state) := by
  have factor := (facade model start past vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime model start past vocabulary encoding law scope threshold) .joint
  refine ⟨?_, JointReceivedRun.source_budget_generates_complete_or_actual_exhaustion model start vocabulary encoding law past.length past,
    the_actual_root_ends_at_the_generated_joint_history model start past vocabulary encoding law,
    (authority model start past vocabulary encoding law scope threshold).current_exact,
    factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩
  intro complete
  have clear := JointReceivedRun.completion_has_all_same_cut_gates model start vocabulary encoding law past.length _ past complete
  exact ⟨clear.1, JointReceivedResponse.completion_has_no_unprocessed_locally_supported_response
    model start vocabulary encoding law past.length _ clear.2⟩

theorem locally_supported_statements_reach_their_own_receipt_original_request_face_and_next
    (site : Fin model.source.code.sites) (body : RequestAttestation.Statement (code := model.source.code))
    (known : body ∈ (ReceivedStatementAuthentication.generate vocabulary encoding law start (past.map Prod.fst) past.length
      (ReceivedStatementAuthentication.remembered start past past.length site) site
      ((EventStep.seed (EventHistory.execute start past)).frame.inbox site)).statements) :
    (∃ receipt ∈ (RequestReadback.produce vocabulary encoding law start past site past.length).receipts,
      receipt.statement = body) ∧
    RequestAttestation.verify vocabulary start past body = true ∧
    body ∈ requests model start past vocabulary encoding law scope threshold ∧
    HEq (runtime model start past vocabulary encoding law scope threshold).tick.generated.wholeLedgerWriteBack
      ((runtime model start past vocabulary encoding law scope threshold).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (runtime model start past vocabulary encoding law scope threshold).current.visit.current) ∧
    (runtime model start past vocabulary encoding law scope threshold).tick.nextCurrent =
      (facade model start past vocabulary encoding law scope threshold).process.stateAt
        ((facade model start past vocabulary encoding law scope threshold).process.successor
          (runtime model start past vocabulary encoding law scope threshold).state) := by
  obtain ⟨receipt, received, same, _, _⟩ :=
    ReceivedStatementAuthentication.locally_known_statements_generate_an_actual_receipt_without_shared_delivery_metadata
      vocabulary encoding law start past past.length site body known
  have source := (RequestReadback.recovered_requests_have_paid_communication_complete_source_and_local_readback
    vocabulary encoding law start past site past.length receipt received).2.1
  rw [same] at source
  have member : body ∈ requests model start past vocabulary encoding law scope threshold := by
    change body ∈ RequestAttestation.ledger vocabulary start
      (RequestReadbackRuntime.full model start (full model start past vocabulary encoding law) vocabulary encoding law)
    rw [the_actual_root_ends_at_the_generated_joint_history]
    obtain ⟨more, extended⟩ := JointReceivedRun.every_run_keeps_the_whole_source_history model start vocabulary encoding law past.length _ past
    change past ++ more = full model start past vocabulary encoding law at extended
    rw [← extended]
    unfold RequestAttestation.ledger at *
    rw [StageQueue.records_append, List.flatMap_append]
    exact List.mem_append_left _ source
  have factor := (facade model start past vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime model start past vocabulary encoding law scope threshold) .joint
  exact ⟨⟨receipt, received, same⟩, (RequestAttestation.independently_verified_iff vocabulary start past body).mpr source,
    member, factor.2.2.1, factor.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceivedRuntime
