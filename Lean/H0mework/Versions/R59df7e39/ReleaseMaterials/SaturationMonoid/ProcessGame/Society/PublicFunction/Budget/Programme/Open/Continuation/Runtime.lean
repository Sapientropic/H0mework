import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Continuation
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.AuthorityRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Continuation.Runtime

open Successor
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
  (reference : Program model.source.code) (budget fuel : Nat)
  (point : Replanning.Point model domain) (environment : Opponent model.source.code)

structure Prepared where
  chain : Chain model fallback fuel budget domain reference
  compiled : chain = Continuation.generate model fallback fuel budget domain reference
  finalPoint : Cursor model.source.code
  realized : finalPoint = chain.realize point.val environment

def prepare : Prepared model domain fallback reference budget fuel point environment :=
  let chain := Continuation.generate model fallback fuel budget domain reference
  ⟨chain,rfl,chain.realize point.val environment,rfl⟩

variable (prepared : Prepared model domain fallback reference budget fuel point environment)

abbrev bound := Replanning.native model prepared.finalPoint
abbrev depth (n : Nat) := (bound model domain fallback reference budget fuel point environment prepared).source.history.length+1+
  (prepared.finalPoint.cut+n)

structure Disposition (n : Nat) where
  chain : Chain model fallback fuel budget domain reference
  origin : chain = prepared.chain
  compiled : chain = Continuation.generate model fallback fuel budget domain reference
  reviewed : chain.review = true
  completions : chain.AllCompletions
  actual_coverage : chain.AllCutsCovered point.val environment
  actual_reviewed : chain.replayActual point.val environment = true
  actual_protection : chain.AllCutsProtected point.val environment
  migrations : chain.Migrations point.val environment
  migrations_exact : migrations = chain.migrations point.val environment
  installed_prefixes : chain.InstalledPrefixes point.val environment
  final_covered : Covered chain.finalDomain prepared.finalPoint
  actual_cut : prepared.finalPoint.cut = point.val.cut+chain.rules.length
  actual_remaining : (prepared.finalPoint.source.feedbackState prepared.finalPoint.entry prepared.finalPoint.cut).remaining =
    (point.val.source.feedbackState point.val.entry point.val.cut).remaining-chain.rules.length
  prior_finance : ∀ ordinal ≤ point.val.history.length+2+point.val.cut,
    Native.Coupling.Match model.source.code point.val.source.input prepared.finalPoint.source.input
      (Financial.accountAt point.val.source.input ordinal) (Financial.accountAt prepared.finalPoint.source.input ordinal)
  native : Native.Authority.FullDisposition (bound model domain fallback reference budget fuel point environment prepared)
    (depth model domain fallback reference budget fuel point environment prepared n)
  native_exact : native = Native.Authority.fullGenerate (bound model domain fallback reference budget fuel point environment prepared)
    (depth model domain fallback reference budget fuel point environment prepared n)

def generate (n : Nat) : Disposition model domain fallback reference budget fuel point environment prepared n :=
  let covered : Covered domain point.val := ⟨point.val,point.property,Aligned.refl _⟩
  let chain := prepared.chain
  let coverage := chain.every_query_uses_its_actual_successor_domain point.val environment covered
  { chain := chain
    origin := rfl
    compiled := prepared.compiled
    reviewed := chain.every_new_query_is_independently_reviewable
    completions := chain.every_actual_completion_covers_the_entire_supported_raw_domain
    actual_coverage := coverage.1
    actual_reviewed := chain.every_actual_query_has_an_independent_complete_replay point.val environment covered
    actual_protection := chain.every_installed_cut_is_accepted_with_its_full_actual_responsibility point.val environment covered
    migrations := chain.migrations point.val environment
    migrations_exact := rfl
    installed_prefixes := chain.all_query_updates_are_kept_by_one_actual_source point.val environment
    final_covered := by rw [prepared.realized];exact coverage.2
    actual_cut := by
      rw [prepared.realized,Chain.realization_is_the_original_paid_fold]
      exact Counted.Installation.Chain.fold_cut _ _ _
    actual_remaining := by
      rw [prepared.realized,Chain.realization_is_the_original_paid_fold]
      exact Counted.Installation.Chain.fold_remaining (model := model) point.val environment chain.rules
    prior_finance := by
      intro ordinal earlier
      rw [prepared.realized,Chain.realization_is_the_original_paid_fold]
      exact Counted.Installation.Chain.fold_keeps_the_complete_native_financial_prefix (model := model)
        point.val environment chain.rules ordinal earlier
    native := Native.Authority.fullGenerate (bound model domain fallback reference budget fuel point environment prepared)
      (depth model domain fallback reference budget fuel point environment prepared n)
    native_exact := rfl }

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource ((bound model domain fallback reference budget fuel point environment prepared).source).input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (n : Nat) →
    current = (ProgrammeHistory.visitAt ((bound model domain fallback reference budget fuel point environment prepared).source).input (depth model domain fallback reference budget fuel point environment prepared n+1)).current →
      Disposition model domain fallback reference budget fuel point environment prepared n
  project := fun _ {_} _ _ n _ => generate model domain fallback reference budget fuel point environment prepared n

def root := (Native.AuthorityRuntime.root (bound model domain fallback reference budget fuel point environment prepared)).withProjectionCoface
  (projectionLaw model domain fallback reference budget fuel point environment prepared)

theorem actual_emitter_root_is_preserved :
    (root model domain fallback reference budget fuel point environment prepared).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot ((bound model domain fallback reference budget fuel point environment prepared).source).input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt
    (ProgrammeSource.N ((bound model domain fallback reference budget fuel point environment prepared).source).input) :=
  ⟨ProgrammeSource.V ((bound model domain fallback reference budget fuel point environment prepared).source).input,
    root model domain fallback reference budget fuel point environment prepared,
    ProgrammeHistory.temporalVisit ((bound model domain fallback reference budget fuel point environment prepared).source).input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N ((bound model domain fallback reference budget fuel point environment prepared).source).input) where
  State := Nat
  stateAt := stateAt model domain fallback reference budget fuel point environment prepared
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N ((bound model domain fallback reference budget fuel point environment prepared).source).input) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt ((bound model domain fallback reference budget fuel point environment prepared).source).input first).current =
        (ProgrammeHistory.visitAt ((bound model domain fallback reference budget fuel point environment prepared).source).input second).current :=
      eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : Native.AuthorityRuntime.Face)
  | replanning

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N ((bound model domain fallback reference budget fuel point environment prepared).source).input) where
  process := process model domain fallback reference budget fuel point environment prepared
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade (bound model domain fallback reference budget fuel point environment prepared)).componentAt
      (Native.AuthorityRuntime.facade (bound model domain fallback reference budget fuel point environment prepared)).seed previous
    | .replanning => projectionLaw model domain fallback reference budget fuel point environment prepared
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Native.AuthorityRuntime.facade (bound model domain fallback reference budget fuel point environment prepared)).installationAt
        (Native.AuthorityRuntime.facade (bound model domain fallback reference budget fuel point environment prepared)).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (Native.AuthorityRuntime.root (bound model domain fallback reference budget fuel point environment prepared)).toAuthoritativeRoot.source
          (projectionLaw model domain fallback reference budget fuel point environment prepared))
    | replanning =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Native.AuthorityRuntime.root (bound model domain fallback reference budget fuel point environment prepared)).toAuthoritativeRoot.source
        (projectionLaw model domain fallback reference budget fuel point environment prepared)
  projectionAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade (bound model domain fallback reference budget fuel point environment prepared)).projectionAt
      (Native.AuthorityRuntime.facade (bound model domain fallback reference budget fuel point environment prepared)).seed previous
    | .replanning => ()

def activated (ordinal : Nat) : LivingRuntimeState (process model domain fallback reference budget fuel point environment prepared) :=
  (facade model domain fallback reference budget fuel point environment prepared).seed.advance ordinal

private theorem activated_state (ordinal : Nat) :
    (activated model domain fallback reference budget fuel point environment prepared ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

def atCut (n : Nat) : Disposition model domain fallback reference budget fuel point environment prepared n :=
  match (facade model domain fallback reference budget fuel point environment prepared).readoutAt
    (activated model domain fallback reference budget fuel point environment prepared (depth model domain fallback reference budget fuel point environment prepared n+1)) .replanning with
  | .inl actual => actual.2 n (by
      change (ProgrammeHistory.visitAt ((bound model domain fallback reference budget fuel point environment prepared).source).input
        (activated model domain fallback reference budget fuel point environment prepared (depth model domain fallback reference budget fuel point environment prepared n+1)).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible


theorem the_same_actual_root_consumes_successor_queries_and_paid_updates (n : Nat) :
    let actual := activated model domain fallback reference budget fuel point environment prepared
      (depth model domain fallback reference budget fuel point environment prepared n+1)
    let output := atCut model domain fallback reference budget fuel point environment prepared n
    output.chain = Continuation.generate model fallback fuel budget domain reference ∧
      output.chain.review = true ∧ output.chain.AllCompletions ∧ output.chain.AllCutsCovered point.val environment ∧
      output.chain.AllCutsProtected point.val environment ∧ output.chain.replayActual point.val environment = true ∧
      output.migrations = output.chain.migrations point.val environment ∧
      output.chain.InstalledPrefixes point.val environment ∧
      output.native = Native.Authority.fullGenerate (bound model domain fallback reference budget fuel point environment prepared)
        (depth model domain fallback reference budget fuel point environment prepared n) ∧
      HEq ((facade model domain fallback reference budget fuel point environment prepared).readoutAt actual .replanning)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (facade model domain fallback reference budget fuel point environment prepared).process.stateAt
        ((facade model domain fallback reference budget fuel point environment prepared).process.successor actual.state) := by
  have rooted := (facade model domain fallback reference budget fuel point environment prepared).readoutAt_factorizes
    (activated model domain fallback reference budget fuel point environment prepared
      (depth model domain fallback reference budget fuel point environment prepared n+1)) .replanning
  let output := atCut model domain fallback reference budget fuel point environment prepared n
  exact ⟨output.compiled,output.reviewed,output.completions,output.actual_coverage,output.actual_protection,output.actual_reviewed,output.migrations_exact,
    output.installed_prefixes,output.native_exact,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

def deploy := facade model domain fallback reference budget fuel point environment
  (prepare model domain fallback reference budget fuel point environment)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Continuation.Runtime
