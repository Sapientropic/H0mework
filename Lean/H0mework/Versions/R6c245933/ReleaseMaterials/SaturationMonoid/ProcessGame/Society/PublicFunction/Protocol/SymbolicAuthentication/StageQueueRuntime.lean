import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageQueueProgress

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageQueueRuntime

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

variable (foundation : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor (AdmissionRuntime.profile foundation).source.code)
  (pastStages : List (EventHistory.Stage (code := (AdmissionRuntime.profile foundation).source.code)))
  (protocols : Nat → Rule (AdmissionRuntime.profile foundation).source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := (AdmissionRuntime.profile foundation).source.code))
  (law : StageReception.Law (AdmissionRuntime.profile foundation).source.code) (scope : Scope) (threshold : Nat)

abbrev full := StageQueueProgress.completeStages start pastStages protocols
abbrev windowStart := EventHistory.execute start pastStages
abbrev final := EventHistory.execute start (full foundation start pastStages protocols)
abbrev actualBound := LocalContentRuntime.native (AdmissionRuntime.profile foundation) (final foundation start pastStages protocols)
abbrev actualInput := (final foundation start pastStages protocols).entry
abbrev ordinal := EventStep.boundary (final foundation start pastStages protocols)

structure Census where
  private mk ::
  source : AdmissionRuntime.Census foundation start (full foundation start pastStages protocols) vocabulary encoding law scope threshold
  source_exact : source = AdmissionRuntime.generate foundation start (full foundation start pastStages protocols) vocabulary encoding law scope threshold
  plans : Fin foundation.source.code.sites → StageQueueProgress.Plan
  plans_exact : plans = fun receiver => StageQueueProgress.windowPlan vocabulary foundation.source.code encoding law start pastStages protocols receiver scope threshold

def generate : Census foundation start pastStages protocols vocabulary encoding law scope threshold :=
  ⟨AdmissionRuntime.generate foundation start (full foundation start pastStages protocols) vocabulary encoding law scope threshold, rfl,
    fun receiver => StageQueueProgress.windowPlan vocabulary foundation.source.code encoding law start pastStages protocols receiver scope threshold, rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (actualBound foundation start pastStages protocols).source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (actualBound foundation start pastStages protocols).source.input (ordinal foundation start pastStages protocols)).current →
      Census foundation start pastStages protocols vocabulary encoding law scope threshold
  project := fun _ {_} _ _ _own => generate foundation start pastStages protocols vocabulary encoding law scope threshold

def root := (AdmissionRuntime.root foundation start (full foundation start pastStages protocols) vocabulary encoding law scope threshold).withProjectionCoface
    (projectionLaw foundation start pastStages protocols vocabulary encoding law scope threshold)

theorem original_emitter_root_is_preserved :
    (root foundation start pastStages protocols vocabulary encoding law scope threshold).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (actualBound foundation start pastStages protocols).source.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt
    (ProgrammeSource.N (actualBound foundation start pastStages protocols).source.input) :=
  ⟨ProgrammeSource.V (actualBound foundation start pastStages protocols).source.input,
    root foundation start pastStages protocols vocabulary encoding law scope threshold,
    ProgrammeHistory.temporalVisit (actualBound foundation start pastStages protocols).source.input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (actualBound foundation start pastStages protocols).source.input) where
  State := Nat
  stateAt := stateAt foundation start pastStages protocols vocabulary encoding law scope threshold
  stateAt_injective := by
    intro first second same
    have labels := congrArg (fun state : SourceNativeLivingRootCurrentAt
        (ProgrammeSource.N (actualBound foundation start pastStages protocols).source.input) =>
      (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (actualBound foundation start pastStages protocols).source.input first).current =
        (ProgrammeHistory.visitAt (actualBound foundation start pastStages protocols).source.input second).current :=
      eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : AdmissionRuntime.Face)
  | queue

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (actualBound foundation start pastStages protocols).source.input) where
  process := process foundation start pastStages protocols vocabulary encoding law scope threshold
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous =>
      (AdmissionRuntime.facade foundation start (full foundation start pastStages protocols) vocabulary encoding law scope threshold).componentAt
        (AdmissionRuntime.facade foundation start (full foundation start pastStages protocols) vocabulary encoding law scope threshold).seed previous
    | .queue => projectionLaw foundation start pastStages protocols vocabulary encoding law scope threshold
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((AdmissionRuntime.facade foundation start (full foundation start pastStages protocols) vocabulary encoding law scope threshold).installationAt
        (AdmissionRuntime.facade foundation start (full foundation start pastStages protocols) vocabulary encoding law scope threshold).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (AdmissionRuntime.root foundation start (full foundation start pastStages protocols) vocabulary encoding law scope threshold).toAuthoritativeRoot.source
          (projectionLaw foundation start pastStages protocols vocabulary encoding law scope threshold))
    | queue =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (AdmissionRuntime.root foundation start (full foundation start pastStages protocols) vocabulary encoding law scope threshold).toAuthoritativeRoot.source
        (projectionLaw foundation start pastStages protocols vocabulary encoding law scope threshold)
  projectionAt := fun _ face => match face with
    | .previous previous => (AdmissionRuntime.facade foundation start (full foundation start pastStages protocols) vocabulary encoding law scope threshold).projectionAt
        (AdmissionRuntime.facade foundation start (full foundation start pastStages protocols) vocabulary encoding law scope threshold).seed previous
    | .queue => ()

def activated (ordinal : Nat) : LivingRuntimeState (process foundation start pastStages protocols vocabulary encoding law scope threshold) :=
  (facade foundation start pastStages protocols vocabulary encoding law scope threshold).seed.advance ordinal

theorem activated_state_is_the_generated_ordinal (ordinal : Nat) :
    (activated foundation start pastStages protocols vocabulary encoding law scope threshold ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
    change Nat.succ (activated foundation start pastStages protocols vocabulary encoding law scope threshold ordinal).state = Nat.succ ordinal
    exact congrArg Nat.succ ih

def rooted : Census foundation start pastStages protocols vocabulary encoding law scope threshold :=
  match (facade foundation start pastStages protocols vocabulary encoding law scope threshold).readoutAt
      (activated foundation start pastStages protocols vocabulary encoding law scope threshold (ordinal foundation start pastStages protocols)) .queue with
  | .inl value => value.2 (by
      change (ProgrammeHistory.visitAt (actualBound foundation start pastStages protocols).source.input
        (activated foundation start pastStages protocols vocabulary encoding law scope threshold (ordinal foundation start pastStages protocols)).state).current = _
      rw [activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

theorem rooted_eq_generated : rooted foundation start pastStages protocols vocabulary encoding law scope threshold = generate foundation start pastStages protocols vocabulary encoding law scope threshold := rfl

theorem the_generated_attempt_is_in_the_same_roots_actual_trace
    (serial : Nat)
    (enough : StageQueue.horizon (windowStart foundation start pastStages) ≤
      (EventStep.seed (windowStart foundation start pastStages)).remaining)
    (present : serial < (EventStep.seed (windowStart foundation start pastStages)).frame.sent.length)
    (supported : serial ∈ QueueScheduler.admitted (AdmissionRuntime.profile foundation).source.code) :
    ∃ row ∈ (rooted foundation start pastStages protocols vocabulary encoding law scope threshold).source.source.rows,
      StageReception.delivered row serial = true := by
  obtain ⟨index, before, delivered⟩ := StageQueue.the_source_window_generates_an_actual_delivery_attempt
    (windowStart foundation start pastStages) protocols serial enough present supported
  refine ⟨StageQueue.row (windowStart foundation start pastStages) protocols index, ?_, delivered⟩
  change _ ∈ StageTrace.records start (pastStages ++ StageQueue.stages
    (windowStart foundation start pastStages) protocols (StageQueue.horizon (windowStart foundation start pastStages)))
  rw [StageQueue.records_append]
  exact List.mem_append_right _ (List.mem_of_getElem? (StageQueue.row_at_its_actual_index
    (windowStart foundation start pastStages) protocols _ index before))

def authority : Feedback.Authority.Disposition (actualBound foundation start pastStages protocols) (actualInput foundation start pastStages protocols)
    (final foundation start pastStages protocols).cut rfl rfl :=
  match (facade foundation start pastStages protocols vocabulary encoding law scope threshold).readoutAt
      (activated foundation start pastStages protocols vocabulary encoding law scope threshold (ordinal foundation start pastStages protocols)) (.previous (.previous (.previous .responsibilities))) with
  | .inl payload => payload.2 (final foundation start pastStages protocols).cut (by
      change (ProgrammeHistory.visitAt (actualBound foundation start pastStages protocols).source.input
        (activated foundation start pastStages protocols vocabulary encoding law scope threshold (ordinal foundation start pastStages protocols)).state).current = _
      rw [activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

theorem the_original_root_consumes_the_generated_window_completion_responsibilities_ledger_and_next :
    let runtime := activated foundation start pastStages protocols vocabulary encoding law scope threshold (ordinal foundation start pastStages protocols)
    (∀ receiver value,
      (rooted foundation start pastStages protocols vocabulary encoding law scope threshold).plans receiver = .ready value →
      (rooted foundation start pastStages protocols vocabulary encoding law scope threshold).source.decisions receiver = .decided value) ∧
      (∀ serial,
        StageQueue.horizon (windowStart foundation start pastStages) ≤ (EventStep.seed (windowStart foundation start pastStages)).remaining →
        serial < (EventStep.seed (windowStart foundation start pastStages)).frame.sent.length →
        serial ∈ QueueScheduler.admitted (AdmissionRuntime.profile foundation).source.code →
        ∃ row ∈ (rooted foundation start pastStages protocols vocabulary encoding law scope threshold).source.source.rows,
          StageReception.delivered row serial = true) ∧
      (authority foundation start pastStages protocols vocabulary encoding law scope threshold).current = Native.Authority.fullGenerate
        (actualBound foundation start pastStages protocols)
        ((final foundation start pastStages protocols).source.history.length + 1 + (final foundation start pastStages protocols).cut) ∧
      HEq ((facade foundation start pastStages protocols vocabulary encoding law scope threshold).readoutAt runtime .queue)
        (runtime.tick.generated.projectionOutcome (.component ())) ∧
      HEq ((facade foundation start pastStages protocols vocabulary encoding law scope threshold).readoutAt runtime (.previous .communication))
        (runtime.tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq ((facade foundation start pastStages protocols vocabulary encoding law scope threshold).readoutAt runtime (.previous (.previous (.previous .responsibilities))))
        (runtime.tick.generated.projectionOutcome (.inherited (.inherited (.inherited (.component ()))))) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (facade foundation start pastStages protocols vocabulary encoding law scope threshold).process.stateAt
        ((facade foundation start pastStages protocols vocabulary encoding law scope threshold).process.successor runtime.state) := by
  have installed := (facade foundation start pastStages protocols vocabulary encoding law scope threshold).readoutAt_factorizes
    (activated foundation start pastStages protocols vocabulary encoding law scope threshold (ordinal foundation start pastStages protocols)) .queue
  have online := (facade foundation start pastStages protocols vocabulary encoding law scope threshold).readoutAt_factorizes
    (activated foundation start pastStages protocols vocabulary encoding law scope threshold (ordinal foundation start pastStages protocols)) (.previous .communication)
  have inherited := (facade foundation start pastStages protocols vocabulary encoding law scope threshold).readoutAt_factorizes
    (activated foundation start pastStages protocols vocabulary encoding law scope threshold (ordinal foundation start pastStages protocols)) (.previous (.previous (.previous .responsibilities)))
  refine ⟨?_, the_generated_attempt_is_in_the_same_roots_actual_trace foundation start pastStages protocols vocabulary encoding law scope threshold,
    (authority foundation start pastStages protocols vocabulary encoding law scope threshold).current_exact,
    installed.2.2.2.1, online.2.2.2.1, inherited.2.2.2.1, installed.2.2.1, installed.2.2.2.2⟩
  intro receiver value ready
  exact StageQueueProgress.a_generated_ready_window_completes_the_online_quorum vocabulary foundation.source.code
    encoding law start pastStages protocols receiver scope threshold value ready

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageQueueRuntime
