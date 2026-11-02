import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Whole.Complete
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation.Whole.Runtime

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument] {fuel : Nat}
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code)
  (reference : Program model.source.code fuel)

structure Prepared where
  outcome : Selection.Outcome model domain original reference
  compiled : outcome = Selection.compile model domain original reference

def prepare : Prepared model domain original reference :=
  ⟨Selection.compile model domain original reference,rfl⟩

def Contract : Selection.Outcome model domain original reference → Prop
  | .selected choice =>
      (∀ other : Program model.source.code fuel,
        Selection.acceptable model domain original choice.policy.protocol other →
          ¬ Distributed.Improves (Selection.axes model domain) (Selection.benefit model domain original) choice.policy.protocol other) ∧
      ((∃ other : Program model.source.code fuel, Selection.acceptable model domain original reference other ∧
        Distributed.Improves (Selection.axes model domain) (Selection.benefit model domain original) reference other) →
          Distributed.Improves (Selection.axes model domain) (Selection.benefit model domain original) reference choice.policy.protocol)
  | .blocked rejected => ∀ program : Program model.source.code fuel,
      (rejected program).row ∈ Replanning.rows model domain ∧
        ¬ Selection.holds model domain original reference program (rejected program).row

theorem every_outcome_carries_its_complete_program_contract (outcome : Selection.Outcome model domain original reference) :
    Contract model domain original reference outcome := by
  cases outcome with
  | selected choice => exact ⟨Selection.selected_has_no_full_responsibility_dominator model domain original reference choice,
      Selection.every_full_responsibility_improvement_is_realized model domain original reference choice⟩
  | blocked rejected => exact fun program => ⟨(rejected program).generated,(rejected program).broken⟩

variable (point : Replanning.Point model domain) (environment : Opponent model.source.code)
  (prepared : Prepared model domain original reference)

def completed (program : Program model.source.code fuel) : Cursor model.source.code :=
  let actual := source point.val original program environment
  ⟨actual.reference,actual.reference_generated,actual.history,actual.original,actual.opponent,actual.side,
    Whole.entry point.val original program environment,actual.feedbackOverrides,
    point.val.cut+Cut.horizon point.val.source point.val.entry point.val.cut,point.val.ownerStart⟩

theorem the_completed_source_is_the_evaluated_program (program : Program model.source.code fuel) :
    (completed model domain original point environment program).source =
      source point.val original program environment := rfl

def finalPoint : Cursor model.source.code := match prepared.outcome with
  | .selected choice => completed model domain original point environment choice.policy.protocol
  | .blocked _ => point.val

abbrev bound := Replanning.native model (finalPoint model domain original reference point environment prepared)
abbrev entry := (finalPoint model domain original reference point environment prepared).entry

def ActualProtection : Selection.Outcome model domain original reference → Prop
  | .selected choice => ∀ rival : Opponent model.source.code,
      Synthesis.accepts model.source.code (economicAxes point.val.source point.val.cut)
        (actualEvaluation model point.val original choice.policy.protocol rival)
        (actualEvaluation model point.val original reference rival)
  | .blocked _ => True

theorem the_selected_whole_program_protects_its_actual_initial_responsibilities
    (outcome : Selection.Outcome model domain original reference) :
    ActualProtection model domain original reference point outcome := by
  cases outcome with
  | selected choice =>
    exact Selection.every_verified_protocol_protects_its_own_actual_full_responsibility model domain original
      reference choice.policy.protocol (Selection.independently_replayed_choice_is_accepted model domain original reference choice) point
  | blocked => trivial

structure Disposition (n : Nat) where
  outcome : Selection.Outcome model domain original reference
  origin : outcome = prepared.outcome
  compiled : outcome = Selection.compile model domain original reference
  review : Selection.review model domain original reference outcome = true
  selection_contract : Contract model domain original reference outcome
  all_finite : Complete.horizon domain ≤ fuel → Complete.Contract model domain original reference outcome
  actual_protection : ActualProtection model domain original reference point outcome
  native : Authority.Disposition (bound model domain original reference point environment prepared)
    (entry model domain original reference point environment prepared)
    ((finalPoint model domain original reference point environment prepared).cut+n) rfl rfl
  native_exact : native = Authority.generate (bound model domain original reference point environment prepared)
    (entry model domain original reference point environment prepared)
    ((finalPoint model domain original reference point environment prepared).cut+n) rfl rfl

def generate (n : Nat) : Disposition model domain original reference point environment prepared n where
  outcome := prepared.outcome
  origin := rfl
  compiled := prepared.compiled
  review := Selection.every_generated_outcome_is_independently_reviewable model domain original reference prepared.outcome
  selection_contract := every_outcome_carries_its_complete_program_contract model domain original reference prepared.outcome
  all_finite := fun enough => Complete.every_generated_outcome_covers_all_finite_programs
    model domain original enough reference prepared.outcome
  actual_protection := the_selected_whole_program_protects_its_actual_initial_responsibilities model domain original reference point prepared.outcome
  native := Authority.generate (bound model domain original reference point environment prepared)
    (entry model domain original reference point environment prepared)
    ((finalPoint model domain original reference point environment prepared).cut+n) rfl rfl
  native_exact := rfl

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (bound model domain original reference point environment prepared).source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (n : Nat) →
    current = (ProgrammeHistory.visitAt (bound model domain original reference point environment prepared).source.input
      ((bound model domain original reference point environment prepared).source.history.length+2+((finalPoint model domain original reference point environment prepared).cut+n))).current →
      Disposition model domain original reference point environment prepared n
  project := fun _ {_} _ _ n _ => generate model domain original reference point environment prepared n

def root := (Authority.Runtime.root (bound model domain original reference point environment prepared) (entry model domain original reference point environment prepared) rfl rfl).withProjectionCoface
  (projectionLaw model domain original reference point environment prepared)

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (bound model domain original reference point environment prepared).source.input) :=
  ⟨ProgrammeSource.V (bound model domain original reference point environment prepared).source.input,root model domain original reference point environment prepared,
    ProgrammeHistory.temporalVisit (bound model domain original reference point environment prepared).source.input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (bound model domain original reference point environment prepared).source.input) where
  State := Nat
  stateAt := stateAt model domain original reference point environment prepared
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (bound model domain original reference point environment prepared).source.input) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (bound model domain original reference point environment prepared).source.input first).current =
        (ProgrammeHistory.visitAt (bound model domain original reference point environment prepared).source.input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : Authority.Runtime.Face)
  | wholeProgram

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (bound model domain original reference point environment prepared).source.input) where
  process := process model domain original reference point environment prepared
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Authority.Runtime.facade (bound model domain original reference point environment prepared) (entry model domain original reference point environment prepared) rfl rfl).componentAt
        (Authority.Runtime.facade (bound model domain original reference point environment prepared) (entry model domain original reference point environment prepared) rfl rfl).seed previous
    | .wholeProgram => projectionLaw model domain original reference point environment prepared
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Authority.Runtime.facade (bound model domain original reference point environment prepared) (entry model domain original reference point environment prepared) rfl rfl).installationAt
        (Authority.Runtime.facade (bound model domain original reference point environment prepared) (entry model domain original reference point environment prepared) rfl rfl).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (Authority.Runtime.root (bound model domain original reference point environment prepared) (entry model domain original reference point environment prepared) rfl rfl).toAuthoritativeRoot.source
            (projectionLaw model domain original reference point environment prepared))
    | wholeProgram =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Authority.Runtime.root (bound model domain original reference point environment prepared) (entry model domain original reference point environment prepared) rfl rfl).toAuthoritativeRoot.source
        (projectionLaw model domain original reference point environment prepared)
  projectionAt := fun _ face => match face with
    | .previous previous => (Authority.Runtime.facade (bound model domain original reference point environment prepared) (entry model domain original reference point environment prepared) rfl rfl).projectionAt
        (Authority.Runtime.facade (bound model domain original reference point environment prepared) (entry model domain original reference point environment prepared) rfl rfl).seed previous
    | .wholeProgram => ()

abbrev activated (ordinal : Nat) := (facade model domain original reference point environment prepared).seed.advance ordinal

theorem activated_state_is_ordinal (ordinal : Nat) : (activated model domain original reference point environment prepared ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
    change Nat.succ (activated model domain original reference point environment prepared ordinal).state = Nat.succ ordinal
    exact congrArg Nat.succ ih

def atCut (n : Nat) : Disposition model domain original reference point environment prepared n :=
  match (facade model domain original reference point environment prepared).readoutAt
    (activated model domain original reference point environment prepared
      ((bound model domain original reference point environment prepared).source.history.length+2+((finalPoint model domain original reference point environment prepared).cut+n))) .wholeProgram with
  | .inl actual => actual.2 n (by
      change (ProgrammeHistory.visitAt (bound model domain original reference point environment prepared).source.input
        (activated model domain original reference point environment prepared _).state).current = _
      exact congrArg (fun ordinal => (ProgrammeHistory.visitAt (bound model domain original reference point environment prepared).source.input ordinal).current)
        (activated_state_is_ordinal model domain original reference point environment prepared _))
  | .inr impossible => nomatch impossible

theorem the_same_actual_source_consumes_whole_program_selection_ledger_and_next (n : Nat) :
    let actual := activated model domain original reference point environment prepared
      ((bound model domain original reference point environment prepared).source.history.length+2+
        ((finalPoint model domain original reference point environment prepared).cut+n))
    let output := atCut model domain original reference point environment prepared n
    output.outcome = Selection.compile model domain original reference ∧
      Selection.review model domain original reference output.outcome = true ∧
      Contract model domain original reference output.outcome ∧
      (Complete.horizon domain ≤ fuel → Complete.Contract model domain original reference output.outcome) ∧
      ActualProtection model domain original reference point output.outcome ∧
      output.native.current = Native.Authority.fullGenerate (bound model domain original reference point environment prepared)
        ((bound model domain original reference point environment prepared).source.history.length+1+
          ((finalPoint model domain original reference point environment prepared).cut+n)) ∧
      HEq ((facade model domain original reference point environment prepared).readoutAt actual .wholeProgram)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (facade model domain original reference point environment prepared).process.stateAt
        ((facade model domain original reference point environment prepared).process.successor actual.state) := by
  have rooted := (facade model domain original reference point environment prepared).readoutAt_factorizes
    (activated model domain original reference point environment prepared
      ((bound model domain original reference point environment prepared).source.history.length+2+
        ((finalPoint model domain original reference point environment prepared).cut+n))) .wholeProgram
  exact ⟨(atCut model domain original reference point environment prepared n).compiled,
    (atCut model domain original reference point environment prepared n).review,
    (atCut model domain original reference point environment prepared n).selection_contract,
    (atCut model domain original reference point environment prepared n).all_finite,
    (atCut model domain original reference point environment prepared n).actual_protection,
    (atCut model domain original reference point environment prepared n).native.current_exact,
    rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

structure Deployment where
  prepared : Prepared model domain original reference
  runtime : SourceNativeLivingRuntimeFacade
    (ProgrammeSource.N (bound model domain original reference point environment prepared).source.input)
  root_exact : runtime = facade model domain original reference point environment prepared

def deploy : Deployment model domain original reference point environment :=
  let prepared := prepare model domain original reference
  ⟨prepared,facade model domain original reference point environment prepared,rfl⟩

def deployComplete : Deployment model domain original (Complete.clip (Complete.horizon domain) reference) point environment :=
  deploy model domain original (Complete.clip (Complete.horizon domain) reference) point environment

theorem the_complete_deployment_root_consumes_all_finite_programs (n : Nat) :
    let normalized := Complete.clip (Complete.horizon domain) reference
    let saved := (deployComplete model domain original reference point environment).prepared
    let final := finalPoint model domain original normalized point environment saved
    let actual := activated model domain original normalized point environment saved
      ((bound model domain original normalized point environment saved).source.history.length+2+(final.cut+n))
    let output := atCut model domain original normalized point environment saved n
    Complete.Contract model domain original normalized output.outcome ∧
      HEq ((facade model domain original normalized point environment saved).readoutAt actual .wholeProgram)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (facade model domain original normalized point environment saved).process.stateAt
        ((facade model domain original normalized point environment saved).process.successor actual.state) := by
  let normalized := Complete.clip (Complete.horizon domain) reference
  let saved := (deployComplete model domain original reference point environment).prepared
  let final := finalPoint model domain original normalized point environment saved
  have rooted := (facade model domain original normalized point environment saved).readoutAt_factorizes
    (activated model domain original normalized point environment saved
      ((bound model domain original normalized point environment saved).source.history.length+2+(final.cut+n))) .wholeProgram
  exact ⟨(atCut model domain original normalized point environment saved n).all_finite (Nat.le_refl _),
    rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation.Whole.Runtime
