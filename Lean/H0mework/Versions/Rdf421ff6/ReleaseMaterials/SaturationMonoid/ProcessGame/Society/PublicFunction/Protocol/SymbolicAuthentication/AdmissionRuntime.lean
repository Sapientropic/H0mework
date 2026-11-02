import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmissionQuorum

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmissionRuntime

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

/-- Install a fresh profile over the same material genesis and its actual public prefix. -/
abbrev profileSource (foundation : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) :
    Machine Party Good Port (Mandate.State Party Technology) Instrument where
  code := AdmissionCode.lift foundation.source.code
  reference := fun _ _ => []
  reference_generated := by
    apply (AdmissionCode.lift foundation.source.code).every_local_policy_is_enumerated
    intro key member
    exact (mem_words_iff _ _ _).mpr (by simp)
  history := (AdmissionCode.lift foundation.source.code).publicPrefix
  original := (AdmissionCode.lift foundation.source.code).public_prefix_is_an_actual_generated_history
  opponent := fun _ _ _ => none
  side := .original

abbrev profile (foundation : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) : Native.Authority.Bound
      (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  ⟨foundation.base, foundation.scope, profileSource foundation, foundation.law_exact, foundation.task_exact⟩

variable (foundation : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor (profile foundation).source.code)
  (stages : List (EventHistory.Stage (code := (profile foundation).source.code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := (profile foundation).source.code))
  (law : StageReception.Law (profile foundation).source.code) (scope : Scope) (threshold : Nat)

abbrev final := EventHistory.execute start stages
abbrev actualBound := LocalContentRuntime.native (profile foundation) (final foundation start stages)
abbrev actualInput := (final foundation start stages).entry
abbrev ordinal := EventStep.boundary (final foundation start stages)

structure Census where
  private mk ::
  source : StageRuntime.Census (profile foundation) start stages vocabulary
  source_exact : source = StageRuntime.generate (profile foundation) start stages vocabulary
  admittedKeys : Finset (Fin foundation.source.code.sites)
  admittedKeys_exact : admittedKeys = AdmissionCode.affected foundation.source.code
  receivers : Fin (profile foundation).source.code.sites → StageReception.Receiver (code := (profile foundation).source.code)
  receivers_exact : receivers = fun receiver => StageReception.run vocabulary encoding law start stages receiver stages.length
  decisions : Fin (profile foundation).source.code.sites → Quorum.ReadoutData Bool
  decisions_exact : decisions = fun receiver => AdmissionQuorum.produce foundation.source.code vocabulary encoding law start stages receiver scope threshold

def generate : Census foundation start stages vocabulary encoding law scope threshold :=
  ⟨StageRuntime.generate (profile foundation) start stages vocabulary, rfl,
    AdmissionCode.affected foundation.source.code, rfl,
    fun receiver => StageReception.run vocabulary encoding law start stages receiver stages.length, rfl,
    fun receiver => AdmissionQuorum.produce foundation.source.code vocabulary encoding law start stages receiver scope threshold, rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (actualBound foundation start stages).source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (actualBound foundation start stages).source.input (ordinal foundation start stages)).current →
      Census foundation start stages vocabulary encoding law scope threshold
  project := fun _ {_} _ _ _own => generate foundation start stages vocabulary encoding law scope threshold

def root := (StageRuntime.root (profile foundation) start stages vocabulary).withProjectionCoface
    (projectionLaw foundation start stages vocabulary encoding law scope threshold)

theorem original_emitter_root_is_preserved :
    (root foundation start stages vocabulary encoding law scope threshold).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (actualBound foundation start stages).source.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt
    (ProgrammeSource.N (actualBound foundation start stages).source.input) :=
  ⟨ProgrammeSource.V (actualBound foundation start stages).source.input,
    root foundation start stages vocabulary encoding law scope threshold,
    ProgrammeHistory.temporalVisit (actualBound foundation start stages).source.input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (actualBound foundation start stages).source.input) where
  State := Nat
  stateAt := stateAt foundation start stages vocabulary encoding law scope threshold
  stateAt_injective := by
    intro first second same
    have labels := congrArg (fun state : SourceNativeLivingRootCurrentAt
        (ProgrammeSource.N (actualBound foundation start stages).source.input) =>
      (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (actualBound foundation start stages).source.input first).current =
        (ProgrammeHistory.visitAt (actualBound foundation start stages).source.input second).current :=
      eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : StageRuntime.Face)
  | communication

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (actualBound foundation start stages).source.input) where
  process := process foundation start stages vocabulary encoding law scope threshold
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous =>
      (StageRuntime.facade (profile foundation) start stages vocabulary).componentAt
        (StageRuntime.facade (profile foundation) start stages vocabulary).seed previous
    | .communication => projectionLaw foundation start stages vocabulary encoding law scope threshold
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((StageRuntime.facade (profile foundation) start stages vocabulary).installationAt
        (StageRuntime.facade (profile foundation) start stages vocabulary).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (StageRuntime.root (profile foundation) start stages vocabulary).toAuthoritativeRoot.source
          (projectionLaw foundation start stages vocabulary encoding law scope threshold))
    | communication =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (StageRuntime.root (profile foundation) start stages vocabulary).toAuthoritativeRoot.source
        (projectionLaw foundation start stages vocabulary encoding law scope threshold)
  projectionAt := fun _ face => match face with
    | .previous previous => (StageRuntime.facade (profile foundation) start stages vocabulary).projectionAt
        (StageRuntime.facade (profile foundation) start stages vocabulary).seed previous
    | .communication => ()

def activated (ordinal : Nat) : LivingRuntimeState (process foundation start stages vocabulary encoding law scope threshold) :=
  (facade foundation start stages vocabulary encoding law scope threshold).seed.advance ordinal

theorem activated_state_is_the_generated_ordinal (ordinal : Nat) :
    (activated foundation start stages vocabulary encoding law scope threshold ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
    change Nat.succ (activated foundation start stages vocabulary encoding law scope threshold ordinal).state = Nat.succ ordinal
    exact congrArg Nat.succ ih

def rooted : Census foundation start stages vocabulary encoding law scope threshold :=
  match (facade foundation start stages vocabulary encoding law scope threshold).readoutAt
      (activated foundation start stages vocabulary encoding law scope threshold (ordinal foundation start stages)) .communication with
  | .inl value => value.2 (by
      change (ProgrammeHistory.visitAt (actualBound foundation start stages).source.input
        (activated foundation start stages vocabulary encoding law scope threshold (ordinal foundation start stages)).state).current = _
      rw [activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

theorem rooted_eq_generated : rooted foundation start stages vocabulary encoding law scope threshold = generate foundation start stages vocabulary encoding law scope threshold := rfl

def authority : Feedback.Authority.Disposition (actualBound foundation start stages) (actualInput foundation start stages)
    (final foundation start stages).cut rfl rfl :=
  match (facade foundation start stages vocabulary encoding law scope threshold).readoutAt
      (activated foundation start stages vocabulary encoding law scope threshold (ordinal foundation start stages)) (.previous (.previous .responsibilities)) with
  | .inl payload => payload.2 (final foundation start stages).cut (by
      change (ProgrammeHistory.visitAt (actualBound foundation start stages).source.input
        (activated foundation start stages vocabulary encoding law scope threshold (ordinal foundation start stages)).state).current = _
      rw [activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

theorem the_original_root_consumes_online_agreement_responsibilities_ledger_and_next :
    let runtime := activated foundation start stages vocabulary encoding law scope threshold (ordinal foundation start stages)
    (∀ left right a b,
      (rooted foundation start stages vocabulary encoding law scope threshold).decisions left = .decided a →
      (rooted foundation start stages vocabulary encoding law scope threshold).decisions right = .decided b → a = b) ∧
      (authority foundation start stages vocabulary encoding law scope threshold).current = Native.Authority.fullGenerate (actualBound foundation start stages)
        ((final foundation start stages).source.history.length + 1 + (final foundation start stages).cut) ∧
      HEq ((facade foundation start stages vocabulary encoding law scope threshold).readoutAt runtime .communication)
        (runtime.tick.generated.projectionOutcome (.component ())) ∧
      HEq ((facade foundation start stages vocabulary encoding law scope threshold).readoutAt runtime (.previous .deviation))
        (runtime.tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq ((facade foundation start stages vocabulary encoding law scope threshold).readoutAt runtime (.previous (.previous .responsibilities)))
        (runtime.tick.generated.projectionOutcome (.inherited (.inherited (.component ()))) ) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (facade foundation start stages vocabulary encoding law scope threshold).process.stateAt
        ((facade foundation start stages vocabulary encoding law scope threshold).process.successor runtime.state) := by
  have installed := (facade foundation start stages vocabulary encoding law scope threshold).readoutAt_factorizes
    (activated foundation start stages vocabulary encoding law scope threshold (ordinal foundation start stages)) .communication
  have deviation := (facade foundation start stages vocabulary encoding law scope threshold).readoutAt_factorizes
    (activated foundation start stages vocabulary encoding law scope threshold (ordinal foundation start stages)) (.previous .deviation)
  have inherited := (facade foundation start stages vocabulary encoding law scope threshold).readoutAt_factorizes
    (activated foundation start stages vocabulary encoding law scope threshold (ordinal foundation start stages)) (.previous (.previous .responsibilities))
  refine ⟨?_, (authority foundation start stages vocabulary encoding law scope threshold).current_exact,
    installed.2.2.2.1, deviation.2.2.2.1, inherited.2.2.2.1, installed.2.2.1, installed.2.2.2.2⟩
  intro left right a b one two
  exact AdmissionQuorum.produced_decisions_agree foundation.source.code vocabulary encoding law start stages left right scope threshold a b one two

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmissionRuntime
