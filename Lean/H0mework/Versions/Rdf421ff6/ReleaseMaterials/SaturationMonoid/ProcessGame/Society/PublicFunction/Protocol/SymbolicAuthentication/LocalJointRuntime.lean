import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalJointRun

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalJointRuntime

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

abbrev result := LocalJointRun.produce model start vocabulary encoding law past
abbrev full := (result model start past vocabulary encoding law).stages
abbrev final := EventHistory.execute start (full model start past vocabulary encoding law)
abbrev actualBound := LocalContentRuntime.native model (final model start past vocabulary encoding law)
abbrev ordinal := EventStep.boundary (final model start past vocabulary encoding law)

structure Census where
  private mk ::
  response : LocalJointRun.Result model
  response_exact : response = result model start past vocabulary encoding law
  duties : List (Sigma (StageDuty.History start vocabulary encoding law))
  duties_exact : duties = StageDuty.histories start vocabulary encoding law (full model start past vocabulary encoding law)
  conflicts : List (IncidentResponse.Answer model start vocabulary encoding law)
  conflicts_exact : conflicts = IncidentResponse.journal model start (full model start past vocabulary encoding law) vocabulary encoding law
  rejections : List (RejectionResponse.Answer model start vocabulary encoding law)
  rejections_exact : rejections = RejectionResponse.journal model start (full model start past vocabulary encoding law) vocabulary encoding law
  decisions : Fin model.source.code.sites → Quorum.ReadoutData Bool
  decisions_exact : decisions = fun receiver => StageQuorum.produce vocabulary encoding law start
    (full model start past vocabulary encoding law) receiver (full model start past vocabulary encoding law).length scope threshold

def generate : Census model start past vocabulary encoding law scope threshold :=
  ⟨result model start past vocabulary encoding law, rfl,
    StageDuty.histories start vocabulary encoding law (full model start past vocabulary encoding law), rfl,
    IncidentResponse.journal model start (full model start past vocabulary encoding law) vocabulary encoding law, rfl,
    RejectionResponse.journal model start (full model start past vocabulary encoding law) vocabulary encoding law, rfl,
    (fun receiver => StageQuorum.produce vocabulary encoding law start (full model start past vocabulary encoding law)
      receiver (full model start past vocabulary encoding law).length scope threshold), rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (actualBound model start past vocabulary encoding law).source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (actualBound model start past vocabulary encoding law).source.input
      (ordinal model start past vocabulary encoding law)).current → Census model start past vocabulary encoding law scope threshold
  project := fun _ {_} _ _ _own => generate model start past vocabulary encoding law scope threshold

-- Install on the exact completed history; no extra queue suffix is appended after the gate.
def root := (Feedback.Authority.Runtime.root (actualBound model start past vocabulary encoding law)
    (final model start past vocabulary encoding law).entry rfl rfl).withProjectionCoface
  (projectionLaw model start past vocabulary encoding law scope threshold)

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
  | previous (face : Feedback.Authority.Runtime.Face)
  | joint

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (actualBound model start past vocabulary encoding law).source.input) where
  process := process model start past vocabulary encoding law scope threshold
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous =>
      (Feedback.Authority.Runtime.facade (actualBound model start past vocabulary encoding law)
        (final model start past vocabulary encoding law).entry rfl rfl).componentAt
        (Feedback.Authority.Runtime.facade (actualBound model start past vocabulary encoding law)
        (final model start past vocabulary encoding law).entry rfl rfl).seed previous
    | .joint => projectionLaw model start past vocabulary encoding law scope threshold
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Feedback.Authority.Runtime.facade (actualBound model start past vocabulary encoding law)
        (final model start past vocabulary encoding law).entry rfl rfl).installationAt
        (Feedback.Authority.Runtime.facade (actualBound model start past vocabulary encoding law)
        (final model start past vocabulary encoding law).entry rfl rfl).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (Feedback.Authority.Runtime.root (actualBound model start past vocabulary encoding law)
    (final model start past vocabulary encoding law).entry rfl rfl).toAuthoritativeRoot.source
          (projectionLaw model start past vocabulary encoding law scope threshold))
    | joint =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Feedback.Authority.Runtime.root (actualBound model start past vocabulary encoding law)
    (final model start past vocabulary encoding law).entry rfl rfl).toAuthoritativeRoot.source
        (projectionLaw model start past vocabulary encoding law scope threshold)
  projectionAt := fun _ face => match face with
    | .previous previous => (Feedback.Authority.Runtime.facade (actualBound model start past vocabulary encoding law)
        (final model start past vocabulary encoding law).entry rfl rfl).projectionAt
        (Feedback.Authority.Runtime.facade (actualBound model start past vocabulary encoding law)
        (final model start past vocabulary encoding law).entry rfl rfl).seed previous
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

def rooted : Census model start past vocabulary encoding law scope threshold :=
  match (facade model start past vocabulary encoding law scope threshold).readoutAt
      (runtime model start past vocabulary encoding law scope threshold) .joint with
  | .inl value => value.2 (by
      change (ProgrammeHistory.visitAt (actualBound model start past vocabulary encoding law).source.input
        (activated model start past vocabulary encoding law scope threshold (ordinal model start past vocabulary encoding law)).state).current = _
      rw [activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

def authority : Feedback.Authority.Disposition (actualBound model start past vocabulary encoding law)
    (final model start past vocabulary encoding law).entry (final model start past vocabulary encoding law).cut rfl rfl :=
  match (facade model start past vocabulary encoding law scope threshold).readoutAt
      (runtime model start past vocabulary encoding law scope threshold) (.previous .responsibilities) with
  | .inl value => value.2 (final model start past vocabulary encoding law).cut (by
      change (ProgrammeHistory.visitAt (actualBound model start past vocabulary encoding law).source.input
        (activated model start past vocabulary encoding law scope threshold (ordinal model start past vocabulary encoding law)).state).current = _
      rw [activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

theorem the_original_root_consumes_joint_local_completion_full_histories_ledger_and_next :
    let state := runtime model start past vocabulary encoding law scope threshold
    let census := rooted model start past vocabulary encoding law scope threshold
    (census.response.status = .jointComplete →
      LocalJointResponse.Clear model start vocabulary encoding law census.response.stages ∧
        (∀ row ∈ census.duties, row.2.2.state.TerminalAt 0) ∧
        ∀ original ∈ LocalJointResponse.completedClaims model start census.response.stages,
          original.2.isPending (Native.Authority.programme model)
            (LocalClaimGate.sourceIndex model (EventHistory.execute start census.response.stages)) = false) ∧
      (census.response.status = .jointComplete ∨
        (census.response.status = .exhausted ∧ LocalJointResponse.fuel model start census.response.stages = 0)) ∧
      (∀ left right a b, census.decisions left = .decided a → census.decisions right = .decided b → a = b) ∧
      (∀ original : Native.Authority.Challenge (actualBound model start past vocabulary encoding law),
        let history := Mandate.Challenge.through (Native.Authority.programme (actualBound model start past vocabulary encoding law))
          (Native.Authority.sourceIndex (actualBound model start past vocabulary encoding law)) original
          ((final model start past vocabulary encoding law).source.history.length + 1 + (final model start past vocabulary encoding law).cut + 2)
        history.state.current.history = history.state.generated.events) ∧
      (authority model start past vocabulary encoding law scope threshold).current = Native.Authority.fullGenerate
        (actualBound model start past vocabulary encoding law)
        ((final model start past vocabulary encoding law).source.history.length + 1 + (final model start past vocabulary encoding law).cut) ∧
      HEq ((facade model start past vocabulary encoding law scope threshold).readoutAt state .joint)
        (state.tick.generated.projectionOutcome (.component ())) ∧
      HEq ((facade model start past vocabulary encoding law scope threshold).readoutAt state (.previous .responsibilities))
        (state.tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq state.tick.generated.wholeLedgerWriteBack
        (state.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt state.current.visit.current) ∧
      state.tick.nextCurrent = (facade model start past vocabulary encoding law scope threshold).process.stateAt
        ((facade model start past vocabulary encoding law scope threshold).process.successor state.state) := by
  have localFace := (facade model start past vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime model start past vocabulary encoding law scope threshold) .joint
  have inherited := (facade model start past vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime model start past vocabulary encoding law scope threshold) (.previous .responsibilities)
  refine ⟨?_, LocalJointRun.source_budget_generates_complete_or_actual_exhaustion model start vocabulary encoding law past,
    ?_,
    fun original => Native.Authority.every_challenge_history_is_its_own_actual_native_run
      (actualBound model start past vocabulary encoding law) original _,
    (authority model start past vocabulary encoding law scope threshold).current_exact,
    localFace.2.2.2.1, inherited.2.2.2.1, localFace.2.2.1, localFace.2.2.2.2⟩
  · intro complete
    have clear := LocalJointRun.completion_has_all_three_same_cut_gates model start vocabulary encoding law
      (LocalJointResponse.fuel model start past) past complete
    exact ⟨clear,
      UnifiedResponse.clear_covers_every_original_duty model start vocabulary encoding law _ clear.1,
      (LocalJointResponse.completed_claims_are_closed_iff model start _).mp clear.2.1⟩

  · intro left right a b one two
    exact StageQuorum.produced_decisions_agree vocabulary encoding law start
      (full model start past vocabulary encoding law) left right _ _ scope threshold a b one two

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalJointRuntime
