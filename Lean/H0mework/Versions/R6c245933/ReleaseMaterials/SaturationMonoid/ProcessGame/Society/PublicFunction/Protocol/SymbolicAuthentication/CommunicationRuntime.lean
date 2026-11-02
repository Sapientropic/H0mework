import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationHistory
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationRuntime

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input bound.source.code) (cut : Nat)
  (protocol : Distributed.Recall.Information.Agency.Protocol.Rule bound.source.code)
  (rival : Opponent bound.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : AttestationTransport.Encoding bound.source)
  (law : AttestationReception.ReceptionLaw bound.source)
  (empty : bound.source.continuation = [])

abbrev actualBound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) :=
  {bound with source := OwnedAttestation.actual bound.source input cut protocol rival}
abbrev actualInput := AttestationTransport.actualInput bound.source input cut protocol rival

structure Census (horizon : Nat) where
  private mk ::
  duties : List (Sigma fun emission : CommunicationDuty.Emission bound.source input cut protocol rival vocabulary encoding =>
    CommunicationDuty.Prefix bound.source input cut protocol rival vocabulary encoding law emission (horizon - emission.send))
  duties_exact : duties = CommunicationDuty.histories bound.source input cut protocol rival vocabulary encoding law horizon
  reception : Fin bound.source.code.sites → AttestationReception.Receiver bound.source
  reception_exact : reception = fun receiver =>
    AttestationReception.run bound.source input cut protocol rival vocabulary encoding law receiver horizon
  requests : (n : Fin horizon) → List
    (ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument ×
      OwnedAttestation.OutcomeData (OwnedAttestation.Ballot bound.source))
  requests_exact : requests = fun (n : Fin horizon) => OwnedAttestation.audit bound.source input cut protocol rival vocabulary n.val

def generate (horizon : Nat) : Census bound input cut protocol rival vocabulary encoding law horizon :=
  ⟨CommunicationDuty.histories bound.source input cut protocol rival vocabulary encoding law horizon, rfl,
    fun receiver => AttestationReception.run bound.source input cut protocol rival vocabulary encoding law receiver horizon, rfl,
    fun n => OwnedAttestation.audit bound.source input cut protocol rival vocabulary n.val, rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (actualBound bound input cut protocol rival).source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (horizon : Nat) →
    current = (ProgrammeHistory.visitAt (actualBound bound input cut protocol rival).source.input
      (bound.source.history.length + 2 + (cut + horizon))).current →
        Census bound input cut protocol rival vocabulary encoding law horizon
  project := fun _ {_} _ _ horizon _own => generate bound input cut protocol rival vocabulary encoding law horizon

def root := (Feedback.Authority.Runtime.root (actualBound bound input cut protocol rival)
  (actualInput bound input cut protocol rival) rfl empty).withProjectionCoface
    (projectionLaw bound input cut protocol rival vocabulary encoding law)

theorem original_emitter_root_is_preserved :
    (root bound input cut protocol rival vocabulary encoding law empty).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (actualBound bound input cut protocol rival).source.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt
    (ProgrammeSource.N (actualBound bound input cut protocol rival).source.input) :=
  ⟨ProgrammeSource.V (actualBound bound input cut protocol rival).source.input,
    root bound input cut protocol rival vocabulary encoding law empty,
    ProgrammeHistory.temporalVisit (actualBound bound input cut protocol rival).source.input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (actualBound bound input cut protocol rival).source.input) where
  State := Nat
  stateAt := stateAt bound input cut protocol rival vocabulary encoding law empty
  stateAt_injective := by
    intro first second same
    have labels := congrArg (fun state : SourceNativeLivingRootCurrentAt
        (ProgrammeSource.N (actualBound bound input cut protocol rival).source.input) =>
      (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (actualBound bound input cut protocol rival).source.input first).current =
        (ProgrammeHistory.visitAt (actualBound bound input cut protocol rival).source.input second).current :=
      eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : Feedback.Authority.Runtime.Face)
  | communication

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (actualBound bound input cut protocol rival).source.input) where
  process := process bound input cut protocol rival vocabulary encoding law empty
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous =>
      (Feedback.Authority.Runtime.facade (actualBound bound input cut protocol rival)
        (actualInput bound input cut protocol rival) rfl empty).componentAt
        (Feedback.Authority.Runtime.facade (actualBound bound input cut protocol rival)
          (actualInput bound input cut protocol rival) rfl empty).seed previous
    | .communication => projectionLaw bound input cut protocol rival vocabulary encoding law
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((Feedback.Authority.Runtime.facade (actualBound bound input cut protocol rival)
        (actualInput bound input cut protocol rival) rfl empty).installationAt
        (Feedback.Authority.Runtime.facade (actualBound bound input cut protocol rival)
          (actualInput bound input cut protocol rival) rfl empty).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (Feedback.Authority.Runtime.root (actualBound bound input cut protocol rival)
            (actualInput bound input cut protocol rival) rfl empty).toAuthoritativeRoot.source
          (projectionLaw bound input cut protocol rival vocabulary encoding law))
    | communication =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (Feedback.Authority.Runtime.root (actualBound bound input cut protocol rival)
          (actualInput bound input cut protocol rival) rfl empty).toAuthoritativeRoot.source
        (projectionLaw bound input cut protocol rival vocabulary encoding law)
  projectionAt := fun _ face => match face with
    | .previous previous => (Feedback.Authority.Runtime.facade (actualBound bound input cut protocol rival)
        (actualInput bound input cut protocol rival) rfl empty).projectionAt
        (Feedback.Authority.Runtime.facade (actualBound bound input cut protocol rival)
          (actualInput bound input cut protocol rival) rfl empty).seed previous
    | .communication => ()

def activated (ordinal : Nat) : LivingRuntimeState (process bound input cut protocol rival vocabulary encoding law empty) :=
  (facade bound input cut protocol rival vocabulary encoding law empty).seed.advance ordinal

theorem activated_state_is_the_generated_ordinal (ordinal : Nat) :
    (activated bound input cut protocol rival vocabulary encoding law empty ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
    change Nat.succ (activated bound input cut protocol rival vocabulary encoding law empty ordinal).state = Nat.succ ordinal
    exact congrArg Nat.succ ih

abbrev ordinal (horizon : Nat) := bound.source.history.length + 2 + (cut + horizon)

def rooted (horizon : Nat) : Census bound input cut protocol rival vocabulary encoding law horizon :=
  match (facade bound input cut protocol rival vocabulary encoding law empty).readoutAt
      (activated bound input cut protocol rival vocabulary encoding law empty (ordinal bound cut horizon)) .communication with
  | .inl value => value.2 horizon (by
      change (ProgrammeHistory.visitAt (actualBound bound input cut protocol rival).source.input
        (activated bound input cut protocol rival vocabulary encoding law empty (ordinal bound cut horizon)).state).current = _
      rw [activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

theorem rooted_eq_generated (horizon : Nat) :
    rooted bound input cut protocol rival vocabulary encoding law empty horizon =
      generate bound input cut protocol rival vocabulary encoding law horizon := rfl

/-- This consumer reads a generated row from the installed face, not a caller's
certificate. The inherited authority census and the original ledger/next use
the very same sealed occurrence. -/
theorem rooted_row_consumes_receipt_lifecycle_and_original_next (horizon : Nat)
    (row : Sigma fun emission : CommunicationDuty.Emission bound.source input cut protocol rival vocabulary encoding =>
      CommunicationDuty.Prefix bound.source input cut protocol rival vocabulary encoding law emission (horizon - emission.send))
    (present : row ∈ (rooted bound input cut protocol rival vocabulary encoding law empty horizon).duties) :
    let actual := activated bound input cut protocol rival vocabulary encoding law empty (ordinal bound cut horizon)
    (row.2.state.TerminalAt 0 ↔ CommunicationDuty.Acknowledged bound.source input cut protocol rival vocabulary encoding law row.1 horizon) ∧
      HEq ((facade bound input cut protocol rival vocabulary encoding law empty).readoutAt actual .communication)
        (actual.tick.generated.projectionOutcome (.component ())) ∧
      HEq ((facade bound input cut protocol rival vocabulary encoding law empty).readoutAt actual (.previous .responsibilities))
        (actual.tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (facade bound input cut protocol rival vocabulary encoding law empty).process.stateAt
        ((facade bound input cut protocol rival vocabulary encoding law empty).process.successor actual.state) := by
  have installed := (facade bound input cut protocol rival vocabulary encoding law empty).readoutAt_factorizes
    (activated bound input cut protocol rival vocabulary encoding law empty (ordinal bound cut horizon)) .communication
  have inherited := (facade bound input cut protocol rival vocabulary encoding law empty).readoutAt_factorizes
    (activated bound input cut protocol rival vocabulary encoding law empty (ordinal bound cut horizon)) (.previous .responsibilities)
  rw [(rooted bound input cut protocol rival vocabulary encoding law empty horizon).duties_exact] at present
  obtain ⟨emission, inside, same⟩ := List.mem_map.mp present
  cases same
  obtain ⟨n, bounded, born⟩ := List.mem_filterMap.mp inside
  have identity := (CommunicationDuty.birth_is_first bound.source input cut protocol rival vocabulary encoding n emission born).1
  exact ⟨CommunicationDuty.terminal_iff_actual_content_receipt bound.source input cut protocol rival vocabulary encoding law
    emission horizon (by rw [identity]; exact List.mem_range.mp bounded),
    installed.2.2.2.1, inherited.2.2.2.1, installed.2.2.1, installed.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationRuntime
