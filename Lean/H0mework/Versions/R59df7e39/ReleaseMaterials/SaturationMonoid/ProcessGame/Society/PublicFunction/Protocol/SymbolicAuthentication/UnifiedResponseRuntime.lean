import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedResponseRun

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedResponseRuntime

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (foundation : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor (AdmissionRuntime.profile foundation).source.code)
  (past : List (EventHistory.Stage (code := (AdmissionRuntime.profile foundation).source.code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := (AdmissionRuntime.profile foundation).source.code))
  (law : StageReception.Law (AdmissionRuntime.profile foundation).source.code) (scope : Scope) (threshold : Nat)

abbrev result := UnifiedResponseRun.produce (AdmissionRuntime.profile foundation) start vocabulary encoding law past
abbrev full := (result foundation start past vocabulary encoding law).stages
abbrev final := EventHistory.execute start (full foundation start past vocabulary encoding law)
abbrev actualBound := LocalContentRuntime.native (AdmissionRuntime.profile foundation) (final foundation start past vocabulary encoding law)
abbrev ordinal := EventStep.boundary (final foundation start past vocabulary encoding law)

structure Census where
  private mk ::
  source : AdmissionRuntime.Census foundation start (full foundation start past vocabulary encoding law) vocabulary encoding law scope threshold
  source_exact : source = AdmissionRuntime.generate foundation start (full foundation start past vocabulary encoding law) vocabulary encoding law scope threshold
  response : UnifiedResponseRun.Result (AdmissionRuntime.profile foundation)
  response_exact : response = result foundation start past vocabulary encoding law
  duties : List (Sigma (StageDuty.History start vocabulary encoding law))
  duties_exact : duties = StageDuty.histories start vocabulary encoding law (full foundation start past vocabulary encoding law)
  conflicts : List (IncidentResponse.Answer (AdmissionRuntime.profile foundation) start vocabulary encoding law)
  conflicts_exact : conflicts = IncidentResponse.journal (AdmissionRuntime.profile foundation) start (full foundation start past vocabulary encoding law) vocabulary encoding law
  rejections : List (RejectionResponse.Answer (AdmissionRuntime.profile foundation) start vocabulary encoding law)
  rejections_exact : rejections = RejectionResponse.journal (AdmissionRuntime.profile foundation) start (full foundation start past vocabulary encoding law) vocabulary encoding law

def generate : Census foundation start past vocabulary encoding law scope threshold :=
  ⟨AdmissionRuntime.generate foundation start (full foundation start past vocabulary encoding law) vocabulary encoding law scope threshold, rfl,
    result foundation start past vocabulary encoding law, rfl,
    StageDuty.histories start vocabulary encoding law (full foundation start past vocabulary encoding law), rfl,
    IncidentResponse.journal (AdmissionRuntime.profile foundation) start (full foundation start past vocabulary encoding law) vocabulary encoding law, rfl,
    RejectionResponse.journal (AdmissionRuntime.profile foundation) start (full foundation start past vocabulary encoding law) vocabulary encoding law, rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (actualBound foundation start past vocabulary encoding law).source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (actualBound foundation start past vocabulary encoding law).source.input
      (ordinal foundation start past vocabulary encoding law)).current → Census foundation start past vocabulary encoding law scope threshold
  project := fun _ {_} _ _ _own => generate foundation start past vocabulary encoding law scope threshold

-- Install on the exact completed history; no extra queue suffix is appended after the gate.
def root := (AdmissionRuntime.root foundation start (full foundation start past vocabulary encoding law) vocabulary encoding law scope threshold).withProjectionCoface
  (projectionLaw foundation start past vocabulary encoding law scope threshold)

theorem original_emitter_root_is_preserved :
    (root foundation start past vocabulary encoding law scope threshold).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (actualBound foundation start past vocabulary encoding law).source.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (index : Nat) : SourceNativeLivingRootCurrentAt
    (ProgrammeSource.N (actualBound foundation start past vocabulary encoding law).source.input) :=
  ⟨ProgrammeSource.V (actualBound foundation start past vocabulary encoding law).source.input,
    root foundation start past vocabulary encoding law scope threshold,
    ProgrammeHistory.temporalVisit (actualBound foundation start past vocabulary encoding law).source.input index⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (actualBound foundation start past vocabulary encoding law).source.input) where
  State := Nat
  stateAt := stateAt foundation start past vocabulary encoding law scope threshold
  stateAt_injective := by
    intro first second same
    have labels := congrArg (fun state : SourceNativeLivingRootCurrentAt
        (ProgrammeSource.N (actualBound foundation start past vocabulary encoding law).source.input) =>
      (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (actualBound foundation start past vocabulary encoding law).source.input first).current =
        (ProgrammeHistory.visitAt (actualBound foundation start past vocabulary encoding law).source.input second).current :=
      eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun index => ⟨index + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : AdmissionRuntime.Face)
  | responses

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (actualBound foundation start past vocabulary encoding law).source.input) where
  process := process foundation start past vocabulary encoding law scope threshold
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous =>
      (AdmissionRuntime.facade foundation start (full foundation start past vocabulary encoding law) vocabulary encoding law scope threshold).componentAt
        (AdmissionRuntime.facade foundation start (full foundation start past vocabulary encoding law) vocabulary encoding law scope threshold).seed previous
    | .responses => projectionLaw foundation start past vocabulary encoding law scope threshold
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((AdmissionRuntime.facade foundation start (full foundation start past vocabulary encoding law) vocabulary encoding law scope threshold).installationAt
        (AdmissionRuntime.facade foundation start (full foundation start past vocabulary encoding law) vocabulary encoding law scope threshold).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (AdmissionRuntime.root foundation start (full foundation start past vocabulary encoding law) vocabulary encoding law scope threshold).toAuthoritativeRoot.source
          (projectionLaw foundation start past vocabulary encoding law scope threshold))
    | responses =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (AdmissionRuntime.root foundation start (full foundation start past vocabulary encoding law) vocabulary encoding law scope threshold).toAuthoritativeRoot.source
        (projectionLaw foundation start past vocabulary encoding law scope threshold)
  projectionAt := fun _ face => match face with
    | .previous previous => (AdmissionRuntime.facade foundation start (full foundation start past vocabulary encoding law) vocabulary encoding law scope threshold).projectionAt
        (AdmissionRuntime.facade foundation start (full foundation start past vocabulary encoding law) vocabulary encoding law scope threshold).seed previous
    | .responses => ()

def activated (index : Nat) : LivingRuntimeState (process foundation start past vocabulary encoding law scope threshold) :=
  (facade foundation start past vocabulary encoding law scope threshold).seed.advance index

theorem activated_state_is_the_generated_ordinal (index : Nat) :
    (activated foundation start past vocabulary encoding law scope threshold index).state = index := by
  induction index with
  | zero => rfl
  | succ index ih =>
    change Nat.succ (activated foundation start past vocabulary encoding law scope threshold index).state = Nat.succ index
    exact congrArg Nat.succ ih

abbrev runtime := activated foundation start past vocabulary encoding law scope threshold (ordinal foundation start past vocabulary encoding law)

def rooted : Census foundation start past vocabulary encoding law scope threshold :=
  match (facade foundation start past vocabulary encoding law scope threshold).readoutAt
      (runtime foundation start past vocabulary encoding law scope threshold) .responses with
  | .inl value => value.2 (by
      change (ProgrammeHistory.visitAt (actualBound foundation start past vocabulary encoding law).source.input
        (activated foundation start past vocabulary encoding law scope threshold (ordinal foundation start past vocabulary encoding law)).state).current = _
      rw [activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

def authority : Feedback.Authority.Disposition (actualBound foundation start past vocabulary encoding law)
    (final foundation start past vocabulary encoding law).entry (final foundation start past vocabulary encoding law).cut rfl rfl :=
  match (facade foundation start past vocabulary encoding law scope threshold).readoutAt
      (runtime foundation start past vocabulary encoding law scope threshold) (.previous (.previous (.previous .responsibilities))) with
  | .inl value => value.2 (final foundation start past vocabulary encoding law).cut (by
      change (ProgrammeHistory.visitAt (actualBound foundation start past vocabulary encoding law).source.input
        (activated foundation start past vocabulary encoding law scope threshold (ordinal foundation start past vocabulary encoding law)).state).current = _
      rw [activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

abbrev NativeResponseAt (cut : Nat) : Prop :=
  ∃ claim : Native.Authority.Challenge (actualBound foundation start past vocabulary encoding law),
    claim.position.ordinal = cut ∧
      (⟨claim, Mandate.Challenge.through
        (Native.Authority.programme (actualBound foundation start past vocabulary encoding law))
        (Native.Authority.sourceIndex (actualBound foundation start past vocabulary encoding law)) claim
        ((final foundation start past vocabulary encoding law).source.history.length + 1 +
          (final foundation start past vocabulary encoding law).cut + 2)⟩ :
        Sigma fun original => Native.Authority.ChallengeHistory (actualBound foundation start past vocabulary encoding law) original) ∈
          (authority foundation start past vocabulary encoding law scope threshold).current.challenges

private theorem actual_signature_reaches_native_authority
    (prior : List (EventHistory.Stage (code := (AdmissionRuntime.profile foundation).source.code)))
    (protocol : Rule (AdmissionRuntime.profile foundation).source.code)
    (rival : Opponent (AdmissionRuntime.profile foundation).source.code)
    (receiver : Fin (AdmissionRuntime.profile foundation).source.code.sites)
    (inside : StageTrace.material (EventHistory.execute start prior) protocol rival ∈
      StageTrace.records start (full foundation start past vocabulary encoding law))
    (submitted : (StageTrace.material (EventHistory.execute start prior) protocol rival).submitted =
      [IncidentResponse.signature (AdmissionRuntime.profile foundation) receiver])
    (standing : Mandate.Challenge.Submission (scope := foundation.scope)
      (IncidentResponse.signature (AdmissionRuntime.profile foundation) receiver))
    (valid : (AdmissionRuntime.profile foundation).source.code.law.Valid
      (EventStep.seed (EventHistory.execute start prior)).current
      (IncidentResponse.signature (AdmissionRuntime.profile foundation) receiver))
    (active : IncidentResponse.Active (AdmissionRuntime.profile foundation) start prior) :
    NativeResponseAt foundation start past vocabulary encoding law scope threshold
      (EventStep.boundary (EventHistory.execute start prior)) := by
  let row := StageTrace.material (EventHistory.execute start prior) protocol rival
  let item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument :=
    ⟨0, (EventStep.seed (EventHistory.execute start prior)).current, IncidentResponse.signature (AdmissionRuntime.profile foundation) receiver⟩
  have items : StageTrace.items row = [item] := by
    unfold StageTrace.items
    rw [submitted]
    rfl
  let index : Fin (StageTrace.items row).length := ⟨0, by rw [items]; exact Nat.zero_lt_succ 0⟩
  have original : (StageTrace.items row).get index = item := by
    simp only [index, List.get_eq_getElem, items, List.getElem_cons_zero]
  obtain ⟨claim, _, position, admitted⟩ := IncidentChallenge.actual_signed_active_item_generates_a_native_claim
    (AdmissionRuntime.profile foundation) start (full foundation start past vocabulary encoding law) row inside index
    (by rw [original]; exact standing) (by rw [original]; exact valid) (by rw [original]; exact active)
  refine ⟨claim, ?_, ?_⟩
  · rw [position]; rfl
  · rw [(authority foundation start past vocabulary encoding law scope threshold).current_exact]
    exact admitted

theorem every_registered_conflict_has_its_actual_native_claim :
    ∀ answer ∈ (rooted foundation start past vocabulary encoding law scope threshold).conflicts,
      NativeResponseAt foundation start past vocabulary encoding law scope threshold
        (EventStep.boundary (EventHistory.execute start answer.pastStages)) := by
  intro answer inside
  have actual := IncidentResponse.every_registered_response_is_an_actual_history_row (AdmissionRuntime.profile foundation) start
    (full foundation start past vocabulary encoding law) vocabulary encoding law answer inside
  exact actual_signature_reaches_native_authority foundation start past vocabulary encoding law scope threshold
    answer.pastStages answer.actualRule answer.rival answer.response.incident.receiver actual
    (IncidentResponse.every_answer_has_the_actual_owned_signature (AdmissionRuntime.profile foundation) start vocabulary encoding law answer).2
    answer.response.standing answer.response.valid answer.response.active

theorem every_registered_rejection_has_its_actual_native_claim :
    ∀ answer ∈ (rooted foundation start past vocabulary encoding law scope threshold).rejections,
      NativeResponseAt foundation start past vocabulary encoding law scope threshold
        (EventStep.boundary (EventHistory.execute start answer.pastStages)) := by
  intro answer inside
  have actual := RejectionResponse.every_registered_response_is_an_actual_history_row (AdmissionRuntime.profile foundation) start
    (full foundation start past vocabulary encoding law) vocabulary encoding law answer inside
  exact actual_signature_reaches_native_authority foundation start past vocabulary encoding law scope threshold
    answer.pastStages answer.actualRule answer.rival answer.response.receiver actual
    (RejectionResponse.every_answer_has_the_actual_owned_signature (AdmissionRuntime.profile foundation) start vocabulary encoding law answer).2
    answer.response.standing answer.response.valid answer.response.active

theorem the_original_root_consumes_unified_completion_agreement_responsibilities_ledger_and_next :
    let state := runtime foundation start past vocabulary encoding law scope threshold
    let census := rooted foundation start past vocabulary encoding law scope threshold
    (census.response.status = .responsesComplete →
      UnifiedResponse.Clear (AdmissionRuntime.profile foundation) start vocabulary encoding law census.response.stages ∧
        ∀ row ∈ census.duties, row.2.2.state.TerminalAt 0) ∧
      (census.response.status = .responsesComplete ∨
        (census.response.status = .exhausted ∧ UnifiedResponse.fuel (AdmissionRuntime.profile foundation) start census.response.stages = 0)) ∧
      (∀ left right a b, census.source.decisions left = .decided a → census.source.decisions right = .decided b → a = b) ∧
      (authority foundation start past vocabulary encoding law scope threshold).current = Native.Authority.fullGenerate
        (actualBound foundation start past vocabulary encoding law)
        ((final foundation start past vocabulary encoding law).source.history.length + 1 + (final foundation start past vocabulary encoding law).cut) ∧
      HEq ((facade foundation start past vocabulary encoding law scope threshold).readoutAt state .responses)
        (state.tick.generated.projectionOutcome (.component ())) ∧
      HEq ((facade foundation start past vocabulary encoding law scope threshold).readoutAt state (.previous .communication))
        (state.tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq ((facade foundation start past vocabulary encoding law scope threshold).readoutAt state (.previous (.previous (.previous .responsibilities))))
        (state.tick.generated.projectionOutcome (.inherited (.inherited (.inherited (.component ()))))) ∧
      HEq state.tick.generated.wholeLedgerWriteBack
        (state.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt state.current.visit.current) ∧
      state.tick.nextCurrent = (facade foundation start past vocabulary encoding law scope threshold).process.stateAt
        ((facade foundation start past vocabulary encoding law scope threshold).process.successor state.state) := by
  have installed := (facade foundation start past vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime foundation start past vocabulary encoding law scope threshold) .responses
  have communication := (facade foundation start past vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime foundation start past vocabulary encoding law scope threshold) (.previous .communication)
  have responsibilities := (facade foundation start past vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime foundation start past vocabulary encoding law scope threshold) (.previous (.previous (.previous .responsibilities)))
  refine ⟨?_, UnifiedResponseRun.source_budget_generates_complete_or_actual_exhaustion (AdmissionRuntime.profile foundation) start vocabulary encoding law past,
    ?_, (authority foundation start past vocabulary encoding law scope threshold).current_exact,
    installed.2.2.2.1, communication.2.2.2.1, responsibilities.2.2.2.1, installed.2.2.1, installed.2.2.2.2⟩
  · intro complete
    have clear := UnifiedResponseRun.completion_has_all_three_source_generated_gates (AdmissionRuntime.profile foundation) start vocabulary encoding law
      (UnifiedResponse.fuel (AdmissionRuntime.profile foundation) start past) past complete
    exact ⟨clear, UnifiedResponse.clear_covers_every_original_duty (AdmissionRuntime.profile foundation) start vocabulary encoding law _ clear⟩
  · intro left right a b one two
    exact AdmissionQuorum.produced_decisions_agree foundation.source.code vocabulary encoding law start
      (full foundation start past vocabulary encoding law) left right scope threshold a b one two

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedResponseRuntime
