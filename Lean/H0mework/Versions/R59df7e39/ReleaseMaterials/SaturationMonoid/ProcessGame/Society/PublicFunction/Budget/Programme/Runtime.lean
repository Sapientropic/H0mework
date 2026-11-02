import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.CrossCap
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.AuthorityRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Runtime

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (fallback : Rule model.source.code)
  (reference : Program model.source.code) (party : Party) (good : Good)
  (floor : Gross.Floor model.source.code.law party good model.source.code.actions)

abbrev Pool := CrossCap.pool model domain fallback reference party good floor

structure Prepared where
  outcome : CrossCap.Outcome model domain fallback reference party good floor
  compiled : outcome = CrossCap.compile model domain fallback reference party good floor

def prepare : Prepared model domain fallback reference party good floor :=
  ⟨CrossCap.compile model domain fallback reference party good floor,rfl⟩

def Contract : CrossCap.Outcome model domain fallback reference party good floor → Prop
  | .selected choice =>
      (∀ other : Program model.source.code, CrossCap.Supported model domain fallback other →
        CrossCap.Accepted model domain fallback choice.policy.protocol other →
          ¬ CrossCap.Improves model domain fallback reference party good floor choice.policy.protocol other) ∧
      ((∃ other : Program model.source.code, CrossCap.Supported model domain fallback other ∧
        CrossCap.Accepted model domain fallback reference other ∧
        CrossCap.Improves model domain fallback reference party good floor reference other) →
          CrossCap.Improves model domain fallback reference party good floor reference choice.policy.protocol)
  | .blocked _ => ∀ other : Program model.source.code, CrossCap.Supported model domain fallback other →
      ¬ CrossCap.Accepted model domain fallback reference other

theorem every_outcome_contract (outcome : CrossCap.Outcome model domain fallback reference party good floor) :
    Contract model domain fallback reference party good floor outcome := by
  cases outcome with
  | selected choice => exact ⟨CrossCap.selected_has_no_supported_raw_dominator model domain fallback reference party good floor choice,
      CrossCap.every_supported_raw_improvement_is_actually_selected model domain fallback reference party good floor choice⟩
  | blocked rejected => exact CrossCap.a_blocked_outcome_excludes_every_supported_raw_program model domain fallback reference party good floor rejected

def Failures : CrossCap.Outcome model domain fallback reference party good floor → Type
  | .selected _ => Unit
  | .blocked _ => ∀ program : Program model.source.code, CrossCap.Supported model domain fallback program →
      CrossCap.RawRejection model domain fallback reference program

def failures (outcome : CrossCap.Outcome model domain fallback reference party good floor) :
    Failures model domain fallback reference party good floor outcome := by
  cases outcome with
  | selected => exact ()
  | blocked rejected => exact CrossCap.rawRejection model domain fallback reference party good floor rejected

variable (point : Replanning.Point model domain) (environment : Opponent model.source.code)
  (prepared : Prepared model domain fallback reference party good floor)

def completed (program : Program model.source.code) : Cursor model.source.code :=
  let actual := source point.val fallback program environment
  ⟨actual.reference,actual.reference_generated,actual.history,actual.original,actual.opponent,actual.side,
    entry point.val fallback program environment,actual.feedbackOverrides,
    point.val.cut+remaining point.val,point.val.ownerStart⟩

theorem original_migrations_target_the_selected_actual_source (program : Program model.source.code) :
    Normalization.RawAuthority.candidate (Replanning.native model point.val) point.val.entry point.val.cut
      (controller point.val fallback program environment) (schedule point.val fallback program) =
      Replanning.native model (completed model domain fallback point environment program) := rfl

def finalPoint : Cursor model.source.code := match prepared.outcome with
  | .selected choice => completed model domain fallback point environment choice.policy.protocol
  | .blocked _ => point.val

abbrev bound := Replanning.native model (finalPoint model domain fallback reference party good floor point environment prepared)
abbrev depth (n : Nat) := (bound model domain fallback reference party good floor point environment prepared).source.history.length+1+
  ((finalPoint model domain fallback reference party good floor point environment prepared).cut+n)

structure Migration (program : Program model.source.code) where
  grants : List (Normalization.RawAuthority.GrantContinuation (Replanning.native model point.val) point.val.entry point.val.cut
    (controller point.val fallback program environment) (schedule point.val fallback program) rfl)
  grants_exact : grants = Normalization.RawAuthority.grantContinuations (Replanning.native model point.val) point.val.entry point.val.cut
    (controller point.val fallback program environment) (schedule point.val fallback program) rfl
  challenges : List (Normalization.RawAuthority.ChallengeContinuation (Replanning.native model point.val) point.val.entry point.val.cut
    (controller point.val fallback program environment) (schedule point.val fallback program) rfl)
  challenges_exact : challenges = Normalization.RawAuthority.challengeContinuations (Replanning.native model point.val) point.val.entry point.val.cut
    (controller point.val fallback program environment) (schedule point.val fallback program) rfl
  target_exact : Normalization.RawAuthority.candidate (Replanning.native model point.val) point.val.entry point.val.cut
    (controller point.val fallback program environment) (schedule point.val fallback program) =
      Replanning.native model (completed model domain fallback point environment program)

def migration (program : Program model.source.code) : Migration model domain fallback point environment program :=
  ⟨Normalization.RawAuthority.grantContinuations (Replanning.native model point.val) point.val.entry point.val.cut
      (controller point.val fallback program environment) (schedule point.val fallback program) rfl,rfl,
    Normalization.RawAuthority.challengeContinuations (Replanning.native model point.val) point.val.entry point.val.cut
      (controller point.val fallback program environment) (schedule point.val fallback program) rfl,rfl,
    original_migrations_target_the_selected_actual_source model domain fallback point environment program⟩

def Migrations : CrossCap.Outcome model domain fallback reference party good floor → Type
  | .selected choice => Migration model domain fallback point environment choice.policy.protocol
  | .blocked _ => Unit

def migrations (outcome : CrossCap.Outcome model domain fallback reference party good floor) :
    Migrations model domain fallback reference party good floor point environment outcome := by
  cases outcome with
  | selected choice => exact migration model domain fallback point environment choice.policy.protocol
  | blocked => exact ()

def Protection : CrossCap.Outcome model domain fallback reference party good floor → Prop
  | .selected choice => CrossCap.Accepted model domain fallback reference choice.policy.protocol
  | .blocked _ => True

theorem protection (outcome : CrossCap.Outcome model domain fallback reference party good floor) :
    Protection model domain fallback reference party good floor outcome := by
  cases outcome with
  | selected choice =>
    exact CrossCap.verified_program_protects_every_actual_responsibility model domain fallback reference party good floor
      choice.policy.protocol choice.policy.generated
      (Selection.independently_replayed_choice_is_accepted model domain fallback (Pool model domain fallback reference party good floor) reference choice)
  | blocked => trivial

structure Disposition (n : Nat) where
  outcome : CrossCap.Outcome model domain fallback reference party good floor
  origin : outcome = prepared.outcome
  compiled : outcome = CrossCap.compile model domain fallback reference party good floor
  review : Selection.review model domain fallback (Pool model domain fallback reference party good floor) reference outcome = true
  raw_contract : Contract model domain fallback reference party good floor outcome
  raw_failures : Failures model domain fallback reference party good floor outcome
  raw_failures_exact : raw_failures = failures model domain fallback reference party good floor outcome
  original_migrations : Migrations model domain fallback reference party good floor point environment outcome
  original_migrations_exact : original_migrations = migrations model domain fallback reference party good floor point environment outcome
  actual_protection : Protection model domain fallback reference party good floor outcome
  native : Native.Authority.FullDisposition (bound model domain fallback reference party good floor point environment prepared)
    (depth model domain fallback reference party good floor point environment prepared n)
  native_exact : native = Native.Authority.fullGenerate (bound model domain fallback reference party good floor point environment prepared)
    (depth model domain fallback reference party good floor point environment prepared n)

def generate (n : Nat) : Disposition model domain fallback reference party good floor point environment prepared n where
  outcome := prepared.outcome
  origin := rfl
  compiled := prepared.compiled
  review := Selection.every_generated_outcome_is_independently_reviewable model domain fallback (Pool model domain fallback reference party good floor) reference prepared.outcome
  raw_contract := every_outcome_contract model domain fallback reference party good floor prepared.outcome
  raw_failures := failures model domain fallback reference party good floor prepared.outcome
  raw_failures_exact := rfl
  original_migrations := migrations model domain fallback reference party good floor point environment prepared.outcome
  original_migrations_exact := rfl
  actual_protection := protection model domain fallback reference party good floor prepared.outcome
  native := Native.Authority.fullGenerate (bound model domain fallback reference party good floor point environment prepared)
    (depth model domain fallback reference party good floor point environment prepared n)
  native_exact := rfl

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource ((bound model domain fallback reference party good floor point environment prepared).source).input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (n : Nat) →
    current = (ProgrammeHistory.visitAt ((bound model domain fallback reference party good floor point environment prepared).source).input (depth model domain fallback reference party good floor point environment prepared n+1)).current →
      Disposition model domain fallback reference party good floor point environment prepared n
  project := fun _ {_} _ _ n _ => generate model domain fallback reference party good floor point environment prepared n

def root := (Native.AuthorityRuntime.root (bound model domain fallback reference party good floor point environment prepared)).withProjectionCoface
  (projectionLaw model domain fallback reference party good floor point environment prepared)

theorem actual_emitter_root_is_preserved :
    (root model domain fallback reference party good floor point environment prepared).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot ((bound model domain fallback reference party good floor point environment prepared).source).input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt
    (ProgrammeSource.N ((bound model domain fallback reference party good floor point environment prepared).source).input) :=
  ⟨ProgrammeSource.V ((bound model domain fallback reference party good floor point environment prepared).source).input,
    root model domain fallback reference party good floor point environment prepared,
    ProgrammeHistory.temporalVisit ((bound model domain fallback reference party good floor point environment prepared).source).input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N ((bound model domain fallback reference party good floor point environment prepared).source).input) where
  State := Nat
  stateAt := stateAt model domain fallback reference party good floor point environment prepared
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N ((bound model domain fallback reference party good floor point environment prepared).source).input) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt ((bound model domain fallback reference party good floor point environment prepared).source).input first).current =
        (ProgrammeHistory.visitAt ((bound model domain fallback reference party good floor point environment prepared).source).input second).current :=
      eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : Native.AuthorityRuntime.Face)
  | crossCap

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N ((bound model domain fallback reference party good floor point environment prepared).source).input) where
  process := process model domain fallback reference party good floor point environment prepared
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade (bound model domain fallback reference party good floor point environment prepared)).componentAt
      (Native.AuthorityRuntime.facade (bound model domain fallback reference party good floor point environment prepared)).seed previous
    | .crossCap => projectionLaw model domain fallback reference party good floor point environment prepared
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Native.AuthorityRuntime.facade (bound model domain fallback reference party good floor point environment prepared)).installationAt
        (Native.AuthorityRuntime.facade (bound model domain fallback reference party good floor point environment prepared)).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (Native.AuthorityRuntime.root (bound model domain fallback reference party good floor point environment prepared)).toAuthoritativeRoot.source
          (projectionLaw model domain fallback reference party good floor point environment prepared))
    | crossCap =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Native.AuthorityRuntime.root (bound model domain fallback reference party good floor point environment prepared)).toAuthoritativeRoot.source
        (projectionLaw model domain fallback reference party good floor point environment prepared)
  projectionAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade (bound model domain fallback reference party good floor point environment prepared)).projectionAt
      (Native.AuthorityRuntime.facade (bound model domain fallback reference party good floor point environment prepared)).seed previous
    | .crossCap => ()

def activated (ordinal : Nat) : LivingRuntimeState (process model domain fallback reference party good floor point environment prepared) :=
  (facade model domain fallback reference party good floor point environment prepared).seed.advance ordinal

private theorem activated_state (ordinal : Nat) :
    (activated model domain fallback reference party good floor point environment prepared ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

def atCut (n : Nat) : Disposition model domain fallback reference party good floor point environment prepared n :=
  match (facade model domain fallback reference party good floor point environment prepared).readoutAt
    (activated model domain fallback reference party good floor point environment prepared (depth model domain fallback reference party good floor point environment prepared n+1)) .crossCap with
  | .inl actual => actual.2 n (by
      change (ProgrammeHistory.visitAt ((bound model domain fallback reference party good floor point environment prepared).source).input
        (activated model domain fallback reference party good floor point environment prepared (depth model domain fallback reference party good floor point environment prepared n+1)).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible


theorem the_actual_root_consumes_full_raw_selection_ledger_and_next (n : Nat) :
    let actual := activated model domain fallback reference party good floor point environment prepared (depth model domain fallback reference party good floor point environment prepared n+1)
    let output := atCut model domain fallback reference party good floor point environment prepared n
    output.outcome = CrossCap.compile model domain fallback reference party good floor ∧
      Selection.review model domain fallback (Pool model domain fallback reference party good floor) reference output.outcome = true ∧
      Contract model domain fallback reference party good floor output.outcome ∧
      output.raw_failures = failures model domain fallback reference party good floor output.outcome ∧
      output.original_migrations = migrations model domain fallback reference party good floor point environment output.outcome ∧
      Protection model domain fallback reference party good floor output.outcome ∧
      output.native = Native.Authority.fullGenerate (bound model domain fallback reference party good floor point environment prepared) (depth model domain fallback reference party good floor point environment prepared n) ∧
      HEq ((facade model domain fallback reference party good floor point environment prepared).readoutAt actual .crossCap)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (facade model domain fallback reference party good floor point environment prepared).process.stateAt
        ((facade model domain fallback reference party good floor point environment prepared).process.successor actual.state) := by
  have rooted := (facade model domain fallback reference party good floor point environment prepared).readoutAt_factorizes
    (activated model domain fallback reference party good floor point environment prepared (depth model domain fallback reference party good floor point environment prepared n+1)) .crossCap
  exact ⟨(atCut model domain fallback reference party good floor point environment prepared n).compiled,(atCut model domain fallback reference party good floor point environment prepared n).review,
    (atCut model domain fallback reference party good floor point environment prepared n).raw_contract,
    (atCut model domain fallback reference party good floor point environment prepared n).raw_failures_exact,
    (atCut model domain fallback reference party good floor point environment prepared n).original_migrations_exact,(atCut model domain fallback reference party good floor point environment prepared n).actual_protection,
    (atCut model domain fallback reference party good floor point environment prepared n).native_exact,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

def deploy := facade model domain fallback reference party good floor point environment (prepare model domain fallback reference party good floor)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Runtime
