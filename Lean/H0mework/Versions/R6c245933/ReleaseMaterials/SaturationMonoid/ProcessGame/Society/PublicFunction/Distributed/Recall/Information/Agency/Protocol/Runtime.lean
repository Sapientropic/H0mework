import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Obstruction
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Acceptance

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]



section OwnExecution
variable (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (input : Input source.code) (cut : Nat) (protocol : Rule source.code) (rival : Opponent source.code)

abbrev state (n : Nat) := (target source input cut protocol rival).feedbackState
  (targetInput source input cut protocol rival) (cut+n)

theorem own_decision_is_generated_from_the_actual_local_record
    (n : Nat) (bounded : n < (source.feedbackState input cut).remaining)
    (site : Fin source.code.sites)
    (owned : ownerAt source.code (start source cut) (state source input cut protocol rival n).history.length = some site) :
    decision source.code (targetInput source input cut protocol rival) (state source input cut protocol rival n) =
      localEvent source.code protocol site ((state source input cut protocol rival n).frame.inbox site) := by
  have complete := Future.the_whole_future_run_is_the_actual_state source input cut
    (controller source cut protocol rival) (term source input cut protocol).val n
  have remaining : (state source input cut protocol rival n).remaining = (source.feedbackState input cut).remaining - n :=
    (congrArg State.remaining complete).trans (Residual.remaining_is_the_seed_budget _ _ _ _ _)
  have historyLength : (state source input cut protocol rival n).history.length = source.history.length+1+cut+n := by
    have historyAt : ∀ (machine : Machine Party Good Port (Mandate.State Party Technology) Instrument)
        (entry : Input machine.code) (index : Nat),
        (machine.feedbackState entry index).history.length = machine.history.length+1+index := by
      intro machine entry index
      induction index with
      | zero => simp [Machine.feedbackState, Machine.feedbackInitial]
      | succ index ih =>
        change (advance machine.code _ _ _).history.length = _
        rw [history_keeps_every_actual_word, List.length_append, List.length_singleton, ih]
        omega
    exact (historyAt (target source input cut protocol rival) _ (cut+n)).trans (by change source.history.length+1+(cut+n) = _; omega)
  have active : (state source input cut protocol rival n).remaining ≠ 0 := by omega
  simp only [decision, if_neg active]
  change (if _ then _ else _) = _
  rw [if_neg (by rw [historyLength]; omega)]
  simp only [controller, driver, owned]

theorem active_control_is_the_selected_work_policy (n : Nat)
    (bounded : n < (source.feedbackState input cut).remaining) :
    Residual.scheduleAt source cut (term source input cut protocol).val n = some protocol.work.val := by
  simp only [Residual.scheduleAt, term, List.getElem?_replicate, if_pos bounded, Option.getD_some]

theorem actual_own_read_submits_the_original_fee
    (empty : source.continuation = []) (n : Nat)
    (bounded : n < (source.feedbackState input cut).remaining)
    (site recipient : Fin source.code.sites)
    (owned : ownerAt source.code (start source cut) (state source input cut protocol rival n).history.length = some site)
    (event : Reaction.Choice source.code)
    (chosen : localEvent source.code protocol site ((state source input cut protocol rival n).frame.inbox site) = some event)
    (reading : event.val = .send site recipient) :
    ((target source input cut protocol rival).actualExecution (source.history.length+1+(cut+n))).submitted = source.code.sendCost site recipient := by
  rw [(target source input cut protocol rival).feedback_word_is_actual (targetInput source input cut protocol rival) rfl empty,
    Execution.policy_at]
  change word source.code (Residual.scheduleAt source cut (term source input cut protocol).val n) _ _ = _
  rw [active_control_is_the_selected_work_policy source input cut protocol n bounded]
  change word source.code (some protocol.work.val) (targetInput source input cut protocol rival) (state source input cut protocol rival n) = _
  simp only [word, own_decision_is_generated_from_the_actual_local_record source input cut protocol rival n bounded site owned, chosen]
  simp only [stepLocal, reading, Code.step, List.nil_append]

theorem actual_own_activation_submits_the_selected_local_work
    (empty : source.continuation = []) (n : Nat)
    (bounded : n < (source.feedbackState input cut).remaining) (site : Fin source.code.sites)
    (owned : ownerAt source.code (start source cut) (state source input cut protocol rival n).history.length = some site)
    (event : Reaction.Choice source.code)
    (chosen : localEvent source.code protocol site ((state source input cut protocol rival n).frame.inbox site) = some event)
    (activation : event.val = .activate site) :
    ((target source input cut protocol rival).actualExecution (source.history.length+1+(cut+n))).submitted =
      source.code.action protocol.work.val site ((state source input cut protocol rival n).frame.inbox site) := by
  rw [(target source input cut protocol rival).feedback_word_is_actual (targetInput source input cut protocol rival) rfl empty,
    Execution.policy_at]
  change word source.code (Residual.scheduleAt source cut (term source input cut protocol).val n) _ _ = _
  rw [active_control_is_the_selected_work_policy source input cut protocol n bounded]
  simp only [word, own_decision_is_generated_from_the_actual_local_record source input cut protocol rival n bounded site owned, chosen]
  simp only [stepLocal, activation, Code.step, Code.action, List.nil_append]

end OwnExecution

structure Context (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (budget : Nat) (reference : Rule model.source.code) where
  world : World model budget
  protocol : Rule model.source.code
  verified : Synthesis.verify model budget reference protocol = true
  environment : Opponent model.source.code

namespace Context
variable {model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {budget : Nat} {reference : Rule model.source.code}
    (context : Context model budget reference)
abbrev bound := context.world.native model budget
abbrev entry := context.world.input model budget
abbrev source := (context.bound).source
abbrev cut := context.world.phase.val
end Context

namespace Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) (budget : Nat) (reference : Rule model.source.code)
  (context : Context model budget reference)

abbrev actualBound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) :=
  {(context.bound) with source := target (context.source) (context.entry) (context.cut) context.protocol context.environment}

abbrev actualInput := targetInput (context.source) (context.entry) (context.cut) context.protocol context.environment

def query (n : Nat) : Option (Fin (context.source).code.sites × Fin (context.source).code.signals × Move (context.source).code) :=
  if (state (context.source) (context.entry) (context.cut) context.protocol context.environment n).remaining = 0 then none else
  (ownerAt (context.source).code (start (context.source) (context.cut)) (state (context.source) (context.entry) (context.cut) context.protocol context.environment n).history.length).map
    fun site => (site,(state (context.source) (context.entry) (context.cut) context.protocol context.environment n).frame.inbox site,
      localEvent (context.source).code context.protocol site ((state (context.source) (context.entry) (context.cut) context.protocol context.environment n).frame.inbox site))

def environmentAttempt (n : Nat) : Option (Move (context.source).code) :=
  let actual := state (context.source) (context.entry) (context.cut) context.protocol context.environment n
  if actual.remaining = 0 then none else
  match ownerAt (context.source).code (start (context.source) (context.cut)) actual.history.length with
  | some _ => none
  | none => some (context.environment actual.history actual.past actual.frame)

structure Disposition (n : Nat) where
  successor_information : Continuation.Transition model budget context.world context.protocol context.environment
  successor_source_transport : ∃ next ∈ successor_information.domain,
    Continuation.Acceptance.SourceMatch model (Continuation.ofWorld model budget context.world)
      context.protocol context.environment next
  successor_replanning : Continuation.Replanning.Outcome model successor_information.domain context.protocol
  successor_replanning_exact : successor_replanning =
    Continuation.Replanning.compile model successor_information.domain context.protocol
  successor_replanning_review :
    Continuation.Replanning.review model successor_information.domain context.protocol successor_replanning = true
  successor_actual_protection : Continuation.Acceptance.ActualProtection model
    (Continuation.ofWorld model budget context.world) context.protocol context.environment
    successor_information.domain successor_replanning
  verified : Synthesis.verify model budget reference context.protocol = true
  protection : Synthesis.accepts model.source.code
    (economicAxes (context.source) (context.cut))
    (actualEvaluation (context.bound) (context.entry)
      (context.cut) rfl context.protocol context.environment)
    (actualEvaluation (context.bound) (context.entry)
      (context.cut) rfl reference context.environment)
  execution : Future.Execution (context.source) (context.entry) (context.cut) (controller (context.source) (context.cut) context.protocol context.environment) (term (context.source) (context.entry) (context.cut) context.protocol).val
  native : Authority.Disposition (actualBound model budget reference context) (actualInput model budget reference context) ((context.cut)+n) rfl rfl
  native_exact : native = Authority.generate (actualBound model budget reference context) (actualInput model budget reference context) ((context.cut)+n) rfl rfl
  query : Option (Fin (context.source).code.sites × Fin (context.source).code.signals × Move (context.source).code)
  query_exact : query = Runtime.query model budget reference context n
  environment_attempt : Option (Move (context.source).code)
  environment_attempt_exact : environment_attempt = environmentAttempt model budget reference context n
  own_decision : ∀ (_bounded : n < ((context.source).feedbackState (context.entry) (context.cut)).remaining)
    (site : Fin (context.source).code.sites)
    (_owned : ownerAt (context.source).code (start (context.source) (context.cut)) (state (context.source) (context.entry) (context.cut) context.protocol context.environment n).history.length = some site),
    decision (context.source).code (actualInput model budget reference context) (state (context.source) (context.entry) (context.cut) context.protocol context.environment n) =
      localEvent (context.source).code context.protocol site ((state (context.source) (context.entry) (context.cut) context.protocol context.environment n).frame.inbox site)

def generate (n : Nat) : Disposition model budget reference context n :=
  let information := Continuation.generate model budget context.world context.protocol context.environment
  let sources := Continuation.Acceptance.one_public_successor_preserves_every_complete_evaluation model
    (Continuation.ofWorld model budget context.world) context.protocol context.environment (Continuation.initial model budget)
    (Continuation.every_original_world_is_in_the_initial_domain model budget context.world)
  let replan := Continuation.Replanning.compile model information.domain context.protocol
  { successor_information := information
    successor_source_transport := sources
    successor_replanning := replan
    successor_replanning_exact := rfl
    successor_replanning_review := Continuation.Replanning.every_generated_outcome_is_independently_reviewable model
      information.domain context.protocol replan
    successor_actual_protection := Continuation.Acceptance.every_public_outcome_transports_its_selected_actual_protection
      model (Continuation.ofWorld model budget context.world) context.protocol context.environment
      information.domain sources replan
    verified := context.verified
    protection := Synthesis.every_verified_protocol_protects_its_own_actual_full_responsibility
      model budget reference context.protocol context.verified context.world context.environment
    execution := Future.execute (context.source) (context.entry) (context.cut) (controller (context.source) (context.cut) context.protocol context.environment) (term (context.source) (context.entry) (context.cut) context.protocol).val rfl rfl
    native := Authority.generate (actualBound model budget reference context) (actualInput model budget reference context) ((context.cut)+n) rfl rfl
    native_exact := rfl
    query := query model budget reference context n
    query_exact := rfl
    environment_attempt := environmentAttempt model budget reference context n
    environment_attempt_exact := rfl
    own_decision := own_decision_is_generated_from_the_actual_local_record (context.source) (context.entry) (context.cut) context.protocol context.environment n }

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (actualBound model budget reference context).source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (n : Nat) →
    current = (ProgrammeHistory.visitAt (actualBound model budget reference context).source.input
      ((context.source).history.length+2+((context.cut)+n))).current → Disposition model budget reference context n
  project := fun _ {_} _ _ n _ => generate model budget reference context n

def root := (Authority.Runtime.root (actualBound model budget reference context) (actualInput model budget reference context) rfl rfl).withProjectionCoface
  (projectionLaw model budget reference context)

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (actualBound model budget reference context).source.input) :=
  ⟨ProgrammeSource.V (actualBound model budget reference context).source.input, root model budget reference context,
    ProgrammeHistory.temporalVisit (actualBound model budget reference context).source.input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (actualBound model budget reference context).source.input) where
  State := Nat
  stateAt := stateAt model budget reference context
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (actualBound model budget reference context).source.input) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (actualBound model budget reference context).source.input first).current =
        (ProgrammeHistory.visitAt (actualBound model budget reference context).source.input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : Authority.Runtime.Face)
  | protocol

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (actualBound model budget reference context).source.input) where
  process := process model budget reference context
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Authority.Runtime.facade (actualBound model budget reference context) (actualInput model budget reference context) rfl rfl).componentAt
        (Authority.Runtime.facade (actualBound model budget reference context) (actualInput model budget reference context) rfl rfl).seed previous
    | .protocol => projectionLaw model budget reference context
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Authority.Runtime.facade (actualBound model budget reference context) (actualInput model budget reference context) rfl rfl).installationAt
        (Authority.Runtime.facade (actualBound model budget reference context) (actualInput model budget reference context) rfl rfl).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (Authority.Runtime.root (actualBound model budget reference context) (actualInput model budget reference context) rfl rfl).toAuthoritativeRoot.source
            (projectionLaw model budget reference context))
    | protocol =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Authority.Runtime.root (actualBound model budget reference context) (actualInput model budget reference context) rfl rfl).toAuthoritativeRoot.source
        (projectionLaw model budget reference context)
  projectionAt := fun _ face => match face with
    | .previous previous => (Authority.Runtime.facade (actualBound model budget reference context) (actualInput model budget reference context) rfl rfl).projectionAt
        (Authority.Runtime.facade (actualBound model budget reference context) (actualInput model budget reference context) rfl rfl).seed previous
    | .protocol => ()

abbrev activated (ordinal : Nat) := (facade model budget reference context).seed.advance ordinal

theorem activated_state_is_ordinal (ordinal : Nat) :
    (activated model budget reference context ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
    change Nat.succ (activated model budget reference context ordinal).state = Nat.succ ordinal
    exact congrArg Nat.succ ih

def atCut (n : Nat) : Disposition model budget reference context n :=
  match (facade model budget reference context).readoutAt
    (activated model budget reference context ((context.source).history.length+2+((context.cut)+n))) .protocol with
  | .inl actual => actual.2 n (by
      change (ProgrammeHistory.visitAt (actualBound model budget reference context).source.input
        (activated model budget reference context ((context.source).history.length+2+((context.cut)+n))).state).current = _
      exact congrArg (fun ordinal => (ProgrammeHistory.visitAt (actualBound model budget reference context).source.input ordinal).current)
        (activated_state_is_ordinal model budget reference context _))
  | .inr impossible => nomatch impossible

theorem same_actual_root_consumes_own_query_full_liability_ledger_and_next (n : Nat) :
    let actual := activated model budget reference context ((context.source).history.length+2+((context.cut)+n))
    Synthesis.verify model budget reference context.protocol = true ∧
      (atCut model budget reference context n).query = query model budget reference context n ∧
      (atCut model budget reference context n).environment_attempt = environmentAttempt model budget reference context n ∧
      (atCut model budget reference context n).native.current =
        Native.Authority.fullGenerate (actualBound model budget reference context) ((context.source).history.length+1+((context.cut)+n)) ∧
      HEq ((facade model budget reference context).readoutAt actual .protocol)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (facade model budget reference context).process.stateAt
        ((facade model budget reference context).process.successor actual.state) := by
  have rooted := (facade model budget reference context).readoutAt_factorizes
    (activated model budget reference context ((context.source).history.length+2+((context.cut)+n))) .protocol
  exact ⟨(atCut model budget reference context n).verified,
    (atCut model budget reference context n).query_exact,
    (atCut model budget reference context n).environment_attempt_exact,
    (atCut model budget reference context n).native.current_exact,
    rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

theorem same_actual_root_emits_the_public_domain_for_its_generated_next :
    let actual := activated model budget reference context ((context.source).history.length+2+context.cut)
    let output := (atCut model budget reference context 0).successor_information
    output.domain = Continuation.history model budget [context.protocol] ∧
      (∃ next ∈ output.domain,
        Continuation.Covers (Continuation.ofWorld model budget context.world) context.protocol context.environment next) ∧
      HEq ((facade model budget reference context).readoutAt actual .protocol)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (facade model budget reference context).process.stateAt
        ((facade model budget reference context).process.successor actual.state) := by
  have rooted := (facade model budget reference context).readoutAt_factorizes
    (activated model budget reference context ((context.source).history.length+2+context.cut)) .protocol
  exact ⟨(atCut model budget reference context 0).successor_information.public_history,
    (atCut model budget reference context 0).successor_information.actual_covered,
    rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

theorem same_actual_root_replans_on_its_own_nonempty_successor_domain :
    let actual := activated model budget reference context ((context.source).history.length+2+context.cut)
    let output := atCut model budget reference context 0
    (∃ next ∈ output.successor_information.domain,
      Continuation.Covers (Continuation.ofWorld model budget context.world) context.protocol context.environment next) ∧
      output.successor_replanning = Continuation.Replanning.compile model output.successor_information.domain context.protocol ∧
      Continuation.Replanning.review model output.successor_information.domain context.protocol
        output.successor_replanning = true ∧
      HEq ((facade model budget reference context).readoutAt actual .protocol)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (facade model budget reference context).process.stateAt
        ((facade model budget reference context).process.successor actual.state) := by
  have rooted := (facade model budget reference context).readoutAt_factorizes
    (activated model budget reference context ((context.source).history.length+2+context.cut)) .protocol
  exact ⟨(atCut model budget reference context 0).successor_information.actual_covered,
    (atCut model budget reference context 0).successor_replanning_exact,
    (atCut model budget reference context 0).successor_replanning_review,
    rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

theorem same_actual_root_consumes_the_uniform_successor_source_transport :
    let actual := activated model budget reference context ((context.source).history.length+2+context.cut)
    let output := atCut model budget reference context 0
    (∃ next ∈ output.successor_information.domain,
      Continuation.Acceptance.SourceMatch model (Continuation.ofWorld model budget context.world)
        context.protocol context.environment next) ∧
      Continuation.Acceptance.ActualProtection model (Continuation.ofWorld model budget context.world)
        context.protocol context.environment output.successor_information.domain output.successor_replanning ∧
      HEq ((facade model budget reference context).readoutAt actual .protocol)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (facade model budget reference context).process.stateAt
        ((facade model budget reference context).process.successor actual.state) := by
  have rooted := (facade model budget reference context).readoutAt_factorizes
    (activated model budget reference context ((context.source).history.length+2+context.cut)) .protocol
  exact ⟨(atCut model budget reference context 0).successor_source_transport,
    (atCut model budget reference context 0).successor_actual_protection,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩

end Runtime

namespace Deployment
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) (budget : Nat) (reference : Rule model.source.code)
  (world : World model budget) (environment : Opponent model.source.code)

def selectedContext (choice : Synthesis.Choice model budget reference) : Context model budget reference :=
  ⟨world,choice.policy.protocol,Synthesis.independently_replayed_choice_is_accepted model budget reference choice,environment⟩

inductive Result : Type 4 where
  | selected (choice : Synthesis.Choice model budget reference)
      (runtime : SourceNativeLivingRuntimeFacade
        (ProgrammeSource.N (Runtime.actualBound model budget reference
          (selectedContext model budget reference world environment choice)).source.input))
      (root_exact : runtime = Runtime.facade model budget reference (selectedContext model budget reference world environment choice))
  | blocked (context : Obstruction.Context model budget reference)
      (runtime : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (world.source model budget).input))
      (root_exact : runtime = Obstruction.facade model budget reference world context)

def Result.outcome : Result model budget reference world environment → Synthesis.Outcome model budget reference
  | .selected choice _ _ => .selected choice
  | .blocked context _ _ => .blocked context.rejected

def generate : Result model budget reference world environment :=
  match generated : Synthesis.compile model budget reference with
  | .selected choice => .selected choice (Runtime.facade model budget reference
      (selectedContext model budget reference world environment choice)) rfl
  | .blocked rejected =>
      let context : Obstruction.Context model budget reference := ⟨rejected,generated⟩
      .blocked context (Obstruction.facade model budget reference world context) rfl

theorem generated_result_is_the_source_compilers_own_result :
    (generate model budget reference world environment).outcome model budget reference world environment =
      Synthesis.compile model budget reference := by
  unfold generate
  split <;> simp_all only [Result.outcome]

def independentlyVerified (protocol : Rule model.source.code)
    (checked : Synthesis.verify model budget reference protocol = true) :=
  Runtime.facade model budget reference ⟨world,protocol,checked,environment⟩

end Deployment

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol
