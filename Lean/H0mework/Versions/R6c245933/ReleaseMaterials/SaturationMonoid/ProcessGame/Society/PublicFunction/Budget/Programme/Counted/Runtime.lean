import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Counted.Installation
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.AuthorityRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Counted.Runtime

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
  (reference : Program model.source.code) (fuel : Nat)

/-- A missing counting reading is distinct from a finite search's raw refutations. -/
inductive Result where
  | finite (readings : Gross.Joint.Coverage model.source.code.law (Joint.sourceAxes model) model.source.code.actions)
      (original : Joint.countReadings model = .positive readings)
      (chain : Installation.Chain model fallback (.joint readings) fuel domain reference)
      (compiled : chain = Installation.generate model fallback (.joint readings) fuel domain reference)
  | residual (request : Request Party Good Port (Mandate.State Party Technology) Instrument)
      (original : request ∈ model.source.code.actions)
      (absent : Gross.Joint.read model.source.code.law (Joint.sourceAxes model) request = none)
      (axes : ∀ axis ∈ Joint.sourceAxes model, ¬ Gross.Costly model.source.code.law axis.1 axis.2 request)
      (generated : Joint.countReadings model = .unresolved request original absent axes)

def compile : Result model domain fallback reference fuel :=
  match generated : Joint.countReadings model with
  | .positive readings => .finite readings generated
      (Installation.generate model fallback (.joint readings) fuel domain reference) rfl
  | .unresolved request original absent axes => .residual request original absent axes generated

namespace Result
variable {model domain fallback reference fuel}

def rules : Result model domain fallback reference fuel → List (Program model.source.code)
  | .finite _ _ chain _ => chain.rules
  | .residual _ _ _ _ _ => []

def realize (result : Result model domain fallback reference fuel) (point : Cursor model.source.code)
    (environment : Opponent model.source.code) : Cursor model.source.code := match result with
  | .finite _ _ chain _ => chain.realize point environment
  | .residual _ _ _ _ _ => point

def finalDomain : Result model domain fallback reference fuel → List (Cursor model.source.code)
  | .finite _ _ chain _ => chain.finalDomain
  | .residual _ _ _ _ _ => domain

def Audits : Result model domain fallback reference fuel → Type
  | .finite _ _ chain _ => chain.Audits
  | .residual _ _ _ _ _ => Unit

def audits (result : Result model domain fallback reference fuel) : result.Audits := match result with
  | .finite _ _ chain _ => chain.audits
  | .residual _ _ _ _ _ => ()

def Migrations (result : Result model domain fallback reference fuel) (point : Cursor model.source.code)
    (environment : Opponent model.source.code) : Type := match result with
  | .finite _ _ chain _ => chain.Migrations point environment
  | .residual _ _ _ _ _ => Unit

def migrations (result : Result model domain fallback reference fuel) (point : Cursor model.source.code)
    (environment : Opponent model.source.code) : result.Migrations point environment := match result with
  | .finite _ _ chain _ => chain.migrations point environment
  | .residual _ _ _ _ _ => ()

def Contract (result : Result model domain fallback reference fuel) (point : Cursor model.source.code)
    (environment : Opponent model.source.code) : Prop := match result with
  | .finite _ _ chain _ => chain.review = true ∧ chain.AllCutsCovered point environment ∧
      chain.AllCutsAccepted point environment ∧ chain.replayActual point environment = true ∧
      chain.InstalledPrefixes point environment ∧ Covered chain.finalDomain (chain.realize point environment)
  | .residual request _ _ _ _ => result.realize point environment = point ∧
      ∀ axis ∈ Joint.sourceAxes model, ¬ Gross.Costly model.source.code.law axis.1 axis.2 request

theorem every_generated_branch_has_its_own_exact_contract
    (result : Result model domain fallback reference fuel) (point : Cursor model.source.code)
    (environment : Opponent model.source.code) (covered : Covered domain point) : result.Contract point environment := by
  cases result with
  | finite readings original chain compiled =>
    have coverage := chain.every_cut_retains_an_actual_source_representative point environment covered
    exact ⟨chain.every_compiled_step_is_independently_reviewable,coverage.1,
      chain.every_selected_cut_protects_its_actual_full_responsibility point environment covered,
      chain.every_actual_cut_is_independently_reviewable point environment covered,
      chain.every_installed_cut_is_retained_by_the_one_final_source point environment,coverage.2⟩
  | residual request original absent axes generated => exact ⟨rfl,axes⟩

theorem realization_is_the_actual_installed_fold (result : Result model domain fallback reference fuel)
    (point : Cursor model.source.code) (environment : Opponent model.source.code) :
    result.realize point environment = Installation.Chain.fold (fallback := fallback) point environment result.rules := by
  cases result with
  | finite readings original chain compiled => exact chain.realization_is_the_actual_installed_rule_fold point environment
  | residual => rfl

theorem final_domain_covers_the_actual_source (result : Result model domain fallback reference fuel)
    (point : Cursor model.source.code) (environment : Opponent model.source.code) (covered : Covered domain point) :
    Covered result.finalDomain (result.realize point environment) := by
  cases result with
  | finite readings original chain compiled => exact (chain.every_cut_retains_an_actual_source_representative point environment covered).2
  | residual => exact covered

end Result

variable (point : Replanning.Point model domain) (environment : Opponent model.source.code)

structure Prepared where
  result : Result model domain fallback reference fuel
  compiled : result = compile model domain fallback reference fuel
  finalPoint : Cursor model.source.code
  realized : finalPoint = result.realize point.val environment

def prepare : Prepared model domain fallback reference fuel point environment :=
  let result := compile model domain fallback reference fuel
  ⟨result,rfl,result.realize point.val environment,rfl⟩

variable (prepared : Prepared model domain fallback reference fuel point environment)

abbrev bound := Replanning.native model prepared.finalPoint
abbrev depth (n : Nat) := (bound model domain fallback reference fuel point environment prepared).source.history.length+1+
  (prepared.finalPoint.cut+n)

structure Disposition (n : Nat) where
  result : Result model domain fallback reference fuel
  origin : result = prepared.result
  compiled : result = compile model domain fallback reference fuel
  audits : result.Audits
  audits_exact : audits = result.audits
  migrations : result.Migrations point.val environment
  migrations_exact : migrations = result.migrations point.val environment
  contract : result.Contract point.val environment
  final_covered : Covered result.finalDomain prepared.finalPoint
  actual_cut : prepared.finalPoint.cut = point.val.cut+result.rules.length
  actual_remaining : (prepared.finalPoint.source.feedbackState prepared.finalPoint.entry prepared.finalPoint.cut).remaining =
    (point.val.source.feedbackState point.val.entry point.val.cut).remaining-result.rules.length
  prior_finance : ∀ ordinal ≤ point.val.history.length+2+point.val.cut,
    Native.Coupling.Match model.source.code point.val.source.input prepared.finalPoint.source.input
      (Financial.accountAt point.val.source.input ordinal) (Financial.accountAt prepared.finalPoint.source.input ordinal)
  native : Native.Authority.FullDisposition (bound model domain fallback reference fuel point environment prepared)
    (depth model domain fallback reference fuel point environment prepared n)
  native_exact : native = Native.Authority.fullGenerate (bound model domain fallback reference fuel point environment prepared)
    (depth model domain fallback reference fuel point environment prepared n)

def generate (n : Nat) : Disposition model domain fallback reference fuel point environment prepared n :=
  let covered : Covered domain point.val := ⟨point.val,point.property,Aligned.refl _⟩
  let result := prepared.result
  { result := result
    origin := rfl
    compiled := prepared.compiled
    audits := result.audits
    audits_exact := rfl
    migrations := result.migrations point.val environment
    migrations_exact := rfl
    contract := result.every_generated_branch_has_its_own_exact_contract point.val environment covered
    final_covered := by
      rw [prepared.realized]
      exact result.final_domain_covers_the_actual_source point.val environment covered
    actual_cut := by
      rw [prepared.realized,Result.realization_is_the_actual_installed_fold]
      exact Installation.Chain.fold_cut _ _ _
    actual_remaining := by
      rw [prepared.realized,Result.realization_is_the_actual_installed_fold]
      exact Installation.Chain.fold_remaining (model := model) point.val environment result.rules
    prior_finance := by
      intro ordinal earlier
      rw [prepared.realized,Result.realization_is_the_actual_installed_fold]
      exact Installation.Chain.fold_keeps_the_complete_native_financial_prefix (model := model)
        point.val environment result.rules ordinal earlier
    native := Native.Authority.fullGenerate (bound model domain fallback reference fuel point environment prepared)
      (depth model domain fallback reference fuel point environment prepared n)
    native_exact := rfl }

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource ((bound model domain fallback reference fuel point environment prepared).source).input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (n : Nat) →
    current = (ProgrammeHistory.visitAt ((bound model domain fallback reference fuel point environment prepared).source).input (depth model domain fallback reference fuel point environment prepared n+1)).current →
      Disposition model domain fallback reference fuel point environment prepared n
  project := fun _ {_} _ _ n _ => generate model domain fallback reference fuel point environment prepared n

def root := (Native.AuthorityRuntime.root (bound model domain fallback reference fuel point environment prepared)).withProjectionCoface
  (projectionLaw model domain fallback reference fuel point environment prepared)

theorem actual_emitter_root_is_preserved :
    (root model domain fallback reference fuel point environment prepared).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot ((bound model domain fallback reference fuel point environment prepared).source).input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt
    (ProgrammeSource.N ((bound model domain fallback reference fuel point environment prepared).source).input) :=
  ⟨ProgrammeSource.V ((bound model domain fallback reference fuel point environment prepared).source).input,
    root model domain fallback reference fuel point environment prepared,
    ProgrammeHistory.temporalVisit ((bound model domain fallback reference fuel point environment prepared).source).input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N ((bound model domain fallback reference fuel point environment prepared).source).input) where
  State := Nat
  stateAt := stateAt model domain fallback reference fuel point environment prepared
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N ((bound model domain fallback reference fuel point environment prepared).source).input) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt ((bound model domain fallback reference fuel point environment prepared).source).input first).current =
        (ProgrammeHistory.visitAt ((bound model domain fallback reference fuel point environment prepared).source).input second).current :=
      eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : Native.AuthorityRuntime.Face)
  | replanning

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N ((bound model domain fallback reference fuel point environment prepared).source).input) where
  process := process model domain fallback reference fuel point environment prepared
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade (bound model domain fallback reference fuel point environment prepared)).componentAt
      (Native.AuthorityRuntime.facade (bound model domain fallback reference fuel point environment prepared)).seed previous
    | .replanning => projectionLaw model domain fallback reference fuel point environment prepared
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Native.AuthorityRuntime.facade (bound model domain fallback reference fuel point environment prepared)).installationAt
        (Native.AuthorityRuntime.facade (bound model domain fallback reference fuel point environment prepared)).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (Native.AuthorityRuntime.root (bound model domain fallback reference fuel point environment prepared)).toAuthoritativeRoot.source
          (projectionLaw model domain fallback reference fuel point environment prepared))
    | replanning =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Native.AuthorityRuntime.root (bound model domain fallback reference fuel point environment prepared)).toAuthoritativeRoot.source
        (projectionLaw model domain fallback reference fuel point environment prepared)
  projectionAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade (bound model domain fallback reference fuel point environment prepared)).projectionAt
      (Native.AuthorityRuntime.facade (bound model domain fallback reference fuel point environment prepared)).seed previous
    | .replanning => ()

def activated (ordinal : Nat) : LivingRuntimeState (process model domain fallback reference fuel point environment prepared) :=
  (facade model domain fallback reference fuel point environment prepared).seed.advance ordinal

private theorem activated_state (ordinal : Nat) :
    (activated model domain fallback reference fuel point environment prepared ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

def atCut (n : Nat) : Disposition model domain fallback reference fuel point environment prepared n :=
  match (facade model domain fallback reference fuel point environment prepared).readoutAt
    (activated model domain fallback reference fuel point environment prepared (depth model domain fallback reference fuel point environment prepared n+1)) .replanning with
  | .inl actual => actual.2 n (by
      change (ProgrammeHistory.visitAt ((bound model domain fallback reference fuel point environment prepared).source).input
        (activated model domain fallback reference fuel point environment prepared (depth model domain fallback reference fuel point environment prepared n+1)).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible


theorem the_same_final_source_consumes_joint_count_branch_ledger_and_next (n : Nat) :
    let actual := activated model domain fallback reference fuel point environment prepared
      (depth model domain fallback reference fuel point environment prepared n+1)
    let output := atCut model domain fallback reference fuel point environment prepared n
    output.result = compile model domain fallback reference fuel ∧
      output.audits = output.result.audits ∧
      output.migrations = output.result.migrations point.val environment ∧
      output.result.Contract point.val environment ∧ Covered output.result.finalDomain prepared.finalPoint ∧
      output.native = Native.Authority.fullGenerate (bound model domain fallback reference fuel point environment prepared)
        (depth model domain fallback reference fuel point environment prepared n) ∧
      HEq ((facade model domain fallback reference fuel point environment prepared).readoutAt actual .replanning)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (facade model domain fallback reference fuel point environment prepared).process.stateAt
        ((facade model domain fallback reference fuel point environment prepared).process.successor actual.state) := by
  have rooted := (facade model domain fallback reference fuel point environment prepared).readoutAt_factorizes
    (activated model domain fallback reference fuel point environment prepared
      (depth model domain fallback reference fuel point environment prepared n+1)) .replanning
  let output := atCut model domain fallback reference fuel point environment prepared n
  exact ⟨output.compiled,output.audits_exact,output.migrations_exact,output.contract,output.final_covered,
    output.native_exact,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

def deploy := facade model domain fallback reference fuel point environment
  (prepare model domain fallback reference fuel point environment)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Counted.Runtime
