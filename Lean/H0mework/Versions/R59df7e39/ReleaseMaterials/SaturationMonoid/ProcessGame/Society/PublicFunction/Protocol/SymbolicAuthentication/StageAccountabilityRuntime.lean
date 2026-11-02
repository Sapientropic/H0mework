import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageAttribution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageAccountabilityRuntime

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
  source : StageDutyRuntime.Census foundation start pastStages protocols vocabulary encoding law scope threshold
  source_exact : source = StageDutyRuntime.generate foundation start pastStages protocols vocabulary encoding law scope threshold
  incidents : List (StageAccountability.Incident start vocabulary encoding law)
  incidents_exact : incidents = StageAccountability.ledger start vocabulary encoding law (full foundation start pastStages protocols)

def generate : Census foundation start pastStages protocols vocabulary encoding law scope threshold :=
  ⟨StageDutyRuntime.generate foundation start pastStages protocols vocabulary encoding law scope threshold, rfl,
    StageAccountability.ledger start vocabulary encoding law (full foundation start pastStages protocols), rfl⟩

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

def root := (StageDutyRuntime.root foundation start pastStages protocols vocabulary encoding law scope threshold).withProjectionCoface
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
  | previous (face : StageDutyRuntime.Face)
  | accountability

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (actualBound foundation start pastStages protocols).source.input) where
  process := process foundation start pastStages protocols vocabulary encoding law scope threshold
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous =>
      (StageDutyRuntime.facade foundation start pastStages protocols vocabulary encoding law scope threshold).componentAt
        (StageDutyRuntime.facade foundation start pastStages protocols vocabulary encoding law scope threshold).seed previous
    | .accountability => projectionLaw foundation start pastStages protocols vocabulary encoding law scope threshold
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((StageDutyRuntime.facade foundation start pastStages protocols vocabulary encoding law scope threshold).installationAt
        (StageDutyRuntime.facade foundation start pastStages protocols vocabulary encoding law scope threshold).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (StageDutyRuntime.root foundation start pastStages protocols vocabulary encoding law scope threshold).toAuthoritativeRoot.source
          (projectionLaw foundation start pastStages protocols vocabulary encoding law scope threshold))
    | accountability =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (StageDutyRuntime.root foundation start pastStages protocols vocabulary encoding law scope threshold).toAuthoritativeRoot.source
        (projectionLaw foundation start pastStages protocols vocabulary encoding law scope threshold)
  projectionAt := fun _ face => match face with
    | .previous previous => (StageDutyRuntime.facade foundation start pastStages protocols vocabulary encoding law scope threshold).projectionAt
        (StageDutyRuntime.facade foundation start pastStages protocols vocabulary encoding law scope threshold).seed previous
    | .accountability => ()

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
      (activated foundation start pastStages protocols vocabulary encoding law scope threshold (ordinal foundation start pastStages protocols)) .accountability with
  | .inl value => value.2 (by
      change (ProgrammeHistory.visitAt (actualBound foundation start pastStages protocols).source.input
        (activated foundation start pastStages protocols vocabulary encoding law scope threshold (ordinal foundation start pastStages protocols)).state).current = _
      rw [activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

theorem rooted_eq_generated : rooted foundation start pastStages protocols vocabulary encoding law scope threshold = generate foundation start pastStages protocols vocabulary encoding law scope threshold := rfl


def authority : Feedback.Authority.Disposition (actualBound foundation start pastStages protocols) (actualInput foundation start pastStages protocols)
    (final foundation start pastStages protocols).cut rfl rfl :=
  match (facade foundation start pastStages protocols vocabulary encoding law scope threshold).readoutAt
      (activated foundation start pastStages protocols vocabulary encoding law scope threshold (ordinal foundation start pastStages protocols)) (.previous (.previous (.previous (.previous (.previous .responsibilities))))) with
  | .inl payload => payload.2 (final foundation start pastStages protocols).cut (by
      change (ProgrammeHistory.visitAt (actualBound foundation start pastStages protocols).source.input
        (activated foundation start pastStages protocols vocabulary encoding law scope threshold (ordinal foundation start pastStages protocols)).state).current = _
      rw [activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

theorem the_original_root_consumes_local_incidents_source_budget_duties_ledger_and_next
    (entry : StageAccountability.Incident start vocabulary encoding law)
    (inside : entry ∈ (rooted foundation start pastStages protocols vocabulary encoding law scope threshold).incidents) :
    let runtime := activated foundation start pastStages protocols vocabulary encoding law scope threshold (ordinal foundation start pastStages protocols)
    StageAccountability.OwnedOrigin start vocabulary (full foundation start pastStages protocols) entry.pair.1.wire.ballot ∧
      StageAccountability.OwnedOrigin start vocabulary (full foundation start pastStages protocols) entry.pair.2.wire.ballot ∧
      entry.pair.1 ∈ ((rooted foundation start pastStages protocols vocabulary encoding law scope threshold).source.source.source.receivers entry.receiver).receipts ∧
      entry.pair.2 ∈ ((rooted foundation start pastStages protocols vocabulary encoding law scope threshold).source.source.source.receivers entry.receiver).receipts ∧
      entry.slot.1 ∈ AdmissionCode.affected foundation.source.code ∧
      (rooted foundation start pastStages protocols vocabulary encoding law scope threshold).source.duties =
        (StageDutyRuntime.rooted foundation start pastStages protocols vocabulary encoding law scope threshold).duties ∧
      (authority foundation start pastStages protocols vocabulary encoding law scope threshold).current = Native.Authority.fullGenerate
        (actualBound foundation start pastStages protocols)
        ((final foundation start pastStages protocols).source.history.length + 1 + (final foundation start pastStages protocols).cut) ∧
      HEq ((facade foundation start pastStages protocols vocabulary encoding law scope threshold).readoutAt runtime .accountability)
        (runtime.tick.generated.projectionOutcome (.component ())) ∧
      HEq ((facade foundation start pastStages protocols vocabulary encoding law scope threshold).readoutAt runtime (.previous .duties))
        (runtime.tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (facade foundation start pastStages protocols vocabulary encoding law scope threshold).process.stateAt
        ((facade foundation start pastStages protocols vocabulary encoding law scope threshold).process.successor runtime.state) := by
  have actual : entry ∈ StageAccountability.ledger start vocabulary encoding law (full foundation start pastStages protocols) := inside
  have origins := StageAccountability.every_incident_has_two_actual_owned_paid_origins_and_two_actual_deliveries
    start vocabulary encoding law _ entry actual
  have received := StageAccountability.incident_receipts_are_in_the_same_whole_history start vocabulary encoding law _ entry actual
  have installed := (facade foundation start pastStages protocols vocabulary encoding law scope threshold).readoutAt_factorizes
    (activated foundation start pastStages protocols vocabulary encoding law scope threshold (ordinal foundation start pastStages protocols)) .accountability
  have duties := (facade foundation start pastStages protocols vocabulary encoding law scope threshold).readoutAt_factorizes
    (activated foundation start pastStages protocols vocabulary encoding law scope threshold (ordinal foundation start pastStages protocols)) (.previous .duties)
  exact ⟨origins.1, origins.2.1, received.1, received.2,
    StageAccountability.every_incident_is_in_the_genesis_admission_budget vocabulary foundation.source.code start encoding law _ entry actual,
    rfl, (authority foundation start pastStages protocols vocabulary encoding law scope threshold).current_exact,
    installed.2.2.2.1, duties.2.2.2.1, installed.2.2.1, installed.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageAccountabilityRuntime
