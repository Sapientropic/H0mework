import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Runtime

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
  (reference : Program model.source.code) (budget : Nat)
  (point : Replanning.Point model domain) (environment : Opponent model.source.code)

def realize (result : Enquiry model domain fallback reference budget) : Cursor model.source.code := match result with
  | .found discovery _ _ _ => Programme.Runtime.completed model domain fallback point environment discovery.program
  | .pending _ => point.val

structure Prepared where
  search : Search model domain fallback reference budget
  compiled : search = compile model domain fallback reference budget
  finalPoint : Cursor model.source.code
  realized : finalPoint = realize model domain fallback reference budget point environment search.result

abbrev Prepared.result (prepared : Prepared model domain fallback reference budget point environment) := prepared.search.result

def prepare : Prepared model domain fallback reference budget point environment :=
  let search := compile model domain fallback reference budget
  ⟨search,rfl,realize model domain fallback reference budget point environment search.result,rfl⟩

variable (prepared : Prepared model domain fallback reference budget point environment)

abbrev bound := Replanning.native model prepared.finalPoint
abbrev depth (n : Nat) := (bound model domain fallback reference budget point environment prepared).source.history.length+1+
  (prepared.finalPoint.cut+n)

def Protection : Enquiry model domain fallback reference budget → Prop
  | .found discovery _ _ _ => Supported model domain fallback discovery.program ∧
      Bounds.Accepted model domain fallback reference discovery.program ∧
      Open.improves model domain fallback reference discovery.program
  | .pending _ => ∀ program ∈ catalogue model domain budget,¬ Checked model domain fallback reference program

theorem protection (result : Enquiry model domain fallback reference budget) : Protection model domain fallback reference budget result := by
  cases result with
  | found discovery _ _ _ => exact ⟨every_catalogue_program_uses_only_original_actions model domain fallback budget discovery.program discovery.generated,
      (checked_exact model domain fallback reference discovery.program).mp discovery.checked⟩
  | pending refuted => exact refuted

def Migrations : Enquiry model domain fallback reference budget → Type
  | .found discovery _ _ _ => Programme.Runtime.Migration model domain fallback point environment discovery.program
  | .pending _ => Unit

def migrations (result : Enquiry model domain fallback reference budget) : Migrations model domain fallback reference budget point environment result :=
  match result with
  | .found discovery _ _ _ => Programme.Runtime.migration model domain fallback point environment discovery.program
  | .pending _ => ()

def review (result : Enquiry model domain fallback reference budget) : Bool := match result with
  | .found _ minimum _ _ => Open.verify model domain fallback reference minimum.budget minimum.discovery.program
  | .pending _ => decide (¬ Within model domain fallback reference budget)

theorem independently_reviewed (result : Enquiry model domain fallback reference budget) :
    review model domain fallback reference budget result = true := by
  cases result with
  | found _ minimum _ _ =>
    simp only [review,Open.verify,decide_eq_true_eq,List.mem_range]
    exact ⟨minimum.discovery.checked,minimum.lower_refuted⟩
  | pending refuted => exact decide_eq_true (fun ⟨program,inside,valid⟩ => refuted program inside valid)

def nextBudget : Enquiry model domain fallback reference budget → Option Nat
  | .found _ _ _ _ => none
  | .pending _ => some (budget+1)

structure Disposition (n : Nat) where
  result : Enquiry model domain fallback reference budget
  origin : result = prepared.result
  compiled : result = (compile model domain fallback reference budget).result
  search : Search model domain fallback reference budget
  search_exact : search = compile model domain fallback reference budget
  search_result : result = search.result
  actual_protection : Protection model domain fallback reference budget result
  reviewed : review model domain fallback reference budget result = true
  original_migrations : Migrations model domain fallback reference budget point environment result
  migrations_exact : original_migrations = migrations model domain fallback reference budget point environment result
  actual_source : prepared.finalPoint = realize model domain fallback reference budget point environment result
  next_budget : Option Nat
  next_budget_exact : next_budget = nextBudget model domain fallback reference budget result
  native : Native.Authority.FullDisposition (bound model domain fallback reference budget point environment prepared)
    (depth model domain fallback reference budget point environment prepared n)
  native_exact : native = Native.Authority.fullGenerate (bound model domain fallback reference budget point environment prepared)
    (depth model domain fallback reference budget point environment prepared n)

def generate (n : Nat) : Disposition model domain fallback reference budget point environment prepared n where
  result := prepared.result
  origin := rfl
  compiled := congrArg (fun search => search.result) prepared.compiled
  search := prepared.search
  search_exact := prepared.compiled
  search_result := rfl
  actual_protection := protection model domain fallback reference budget prepared.result
  reviewed := independently_reviewed model domain fallback reference budget prepared.result
  original_migrations := migrations model domain fallback reference budget point environment prepared.result
  migrations_exact := rfl
  actual_source := prepared.realized
  next_budget := nextBudget model domain fallback reference budget prepared.result
  next_budget_exact := rfl
  native := Native.Authority.fullGenerate (bound model domain fallback reference budget point environment prepared)
    (depth model domain fallback reference budget point environment prepared n)
  native_exact := rfl

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource ((bound model domain fallback reference budget point environment prepared).source).input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (n : Nat) →
    current = (ProgrammeHistory.visitAt ((bound model domain fallback reference budget point environment prepared).source).input (depth model domain fallback reference budget point environment prepared n+1)).current →
      Disposition model domain fallback reference budget point environment prepared n
  project := fun _ {_} _ _ n _ => generate model domain fallback reference budget point environment prepared n

def root := (Native.AuthorityRuntime.root (bound model domain fallback reference budget point environment prepared)).withProjectionCoface
  (projectionLaw model domain fallback reference budget point environment prepared)

theorem actual_emitter_root_is_preserved :
    (root model domain fallback reference budget point environment prepared).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot ((bound model domain fallback reference budget point environment prepared).source).input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt
    (ProgrammeSource.N ((bound model domain fallback reference budget point environment prepared).source).input) :=
  ⟨ProgrammeSource.V ((bound model domain fallback reference budget point environment prepared).source).input,
    root model domain fallback reference budget point environment prepared,
    ProgrammeHistory.temporalVisit ((bound model domain fallback reference budget point environment prepared).source).input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N ((bound model domain fallback reference budget point environment prepared).source).input) where
  State := Nat
  stateAt := stateAt model domain fallback reference budget point environment prepared
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N ((bound model domain fallback reference budget point environment prepared).source).input) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt ((bound model domain fallback reference budget point environment prepared).source).input first).current =
        (ProgrammeHistory.visitAt ((bound model domain fallback reference budget point environment prepared).source).input second).current :=
      eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : Native.AuthorityRuntime.Face)
  | replanning

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N ((bound model domain fallback reference budget point environment prepared).source).input) where
  process := process model domain fallback reference budget point environment prepared
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade (bound model domain fallback reference budget point environment prepared)).componentAt
      (Native.AuthorityRuntime.facade (bound model domain fallback reference budget point environment prepared)).seed previous
    | .replanning => projectionLaw model domain fallback reference budget point environment prepared
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Native.AuthorityRuntime.facade (bound model domain fallback reference budget point environment prepared)).installationAt
        (Native.AuthorityRuntime.facade (bound model domain fallback reference budget point environment prepared)).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (Native.AuthorityRuntime.root (bound model domain fallback reference budget point environment prepared)).toAuthoritativeRoot.source
          (projectionLaw model domain fallback reference budget point environment prepared))
    | replanning =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Native.AuthorityRuntime.root (bound model domain fallback reference budget point environment prepared)).toAuthoritativeRoot.source
        (projectionLaw model domain fallback reference budget point environment prepared)
  projectionAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade (bound model domain fallback reference budget point environment prepared)).projectionAt
      (Native.AuthorityRuntime.facade (bound model domain fallback reference budget point environment prepared)).seed previous
    | .replanning => ()

def activated (ordinal : Nat) : LivingRuntimeState (process model domain fallback reference budget point environment prepared) :=
  (facade model domain fallback reference budget point environment prepared).seed.advance ordinal

private theorem activated_state (ordinal : Nat) :
    (activated model domain fallback reference budget point environment prepared ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

def atCut (n : Nat) : Disposition model domain fallback reference budget point environment prepared n :=
  match (facade model domain fallback reference budget point environment prepared).readoutAt
    (activated model domain fallback reference budget point environment prepared (depth model domain fallback reference budget point environment prepared n+1)) .replanning with
  | .inl actual => actual.2 n (by
      change (ProgrammeHistory.visitAt ((bound model domain fallback reference budget point environment prepared).source).input
        (activated model domain fallback reference budget point environment prepared (depth model domain fallback reference budget point environment prepared n+1)).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible


theorem the_same_actual_root_consumes_open_inquiry_ledger_and_next (n : Nat) :
    let actual := activated model domain fallback reference budget point environment prepared
      (depth model domain fallback reference budget point environment prepared n+1)
    let output := atCut model domain fallback reference budget point environment prepared n
    output.result = (compile model domain fallback reference budget).result ∧
      output.search = compile model domain fallback reference budget ∧ output.result = output.search.result ∧
      Protection model domain fallback reference budget output.result ∧
      review model domain fallback reference budget output.result = true ∧
      output.original_migrations = migrations model domain fallback reference budget point environment output.result ∧
      output.next_budget = nextBudget model domain fallback reference budget output.result ∧
      output.native = Native.Authority.fullGenerate (bound model domain fallback reference budget point environment prepared)
        (depth model domain fallback reference budget point environment prepared n) ∧
      HEq ((facade model domain fallback reference budget point environment prepared).readoutAt actual .replanning)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (facade model domain fallback reference budget point environment prepared).process.stateAt
        ((facade model domain fallback reference budget point environment prepared).process.successor actual.state) := by
  have rooted := (facade model domain fallback reference budget point environment prepared).readoutAt_factorizes
    (activated model domain fallback reference budget point environment prepared
      (depth model domain fallback reference budget point environment prepared n+1)) .replanning
  let output := atCut model domain fallback reference budget point environment prepared n
  exact ⟨output.compiled,output.search_exact,output.search_result,output.actual_protection,output.reviewed,output.migrations_exact,output.next_budget_exact,
    output.native_exact,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

def deploy := facade model domain fallback reference budget point environment
  (prepare model domain fallback reference budget point environment)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Runtime
