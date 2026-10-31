import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Review
import H0mework.Foundation.Responsibility.Lifecycle

/-! One native lifecycle slot per original issued liability.  Creditor
assignments change its finite residual shares; debtor, original commitment,
beneficiary contract and source lineage remain the same. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial

open ResponsibilityLifecycle ComplementObservation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

inductive Event
  | birth (claim : IssuedClaim input)
  | review (claim : IssuedClaim input) (review : Review input claim)
      (before : Balance input) (remaining : ℚ)

namespace Event

def claim : Event input → IssuedClaim input
  | .birth claim => claim
  | .review claim _ _ _ => claim

def before : Event input → Balance input
  | .birth claim => initialBalance input claim
  | .review _ _ balance _ => balance

def after : Event input → Balance input
  | .birth claim => initialBalance input claim
  | .review _ receipt balance remaining => receipt.after input balance remaining

def Lawful : Event input → Prop
  | .birth _ => True
  | .review _ receipt balance remaining =>
      Nonnegative input balance ∧ 0 ≤ remaining ∧ remaining ≤ receipt.quantity

def SourceAt : Event input → InstructionOrigin input
  | .birth claim => claim.origin
  | .review _ receipt _ _ => receipt.origin

def CommitmentAt : Event input → IssuedClaim input → Type
  | .birth original, claim => PLift (original = claim)
  | .review .., _ => PEmpty

end Event

abbrev vocabulary : ResponsibilityLifecycle.Vocabulary where
  SourceEvent := Event input
  Content := IssuedClaim input
  Residual := Balance input
  Bearer := BirthActor input
  ProtectedInterest := IssuedClaim input
  Scope := InstructionOrigin input
  Lineage := InstructionOrigin input
  Incidence := InstructionOrigin input
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun event => MinimalRegistrableSourceAnchor.canonical
    (event.claim input).origin (event.claim input).origin
  sourceIncidence := fun event => (event.claim input).origin
  ObstructionAt := fun _ => PEmpty
  demandContent := fun impossible => impossible.elim
  demandResidual := fun impossible => impossible.elim
  CommitmentAt := Event.CommitmentAt input
  MandateOriginAt := fun _ _ => PEmpty
  AcceptedTaskAt := fun _ _ => PEmpty
  ActiveDependencyAt := fun _ _ => PEmpty
  ProtectedRiskAt := fun _ _ => PEmpty
  AdmissionAuthorityAt := fun event scope => PLift (scope = (event.claim input).origin)
  AcceptedAt := fun bearer event scope =>
    PLift (bearer = (event.claim input).debtorActor input ∧ scope = (event.claim input).origin)
  StandingMandateAt := fun _ _ _ => PEmpty
  DischargeJurisdiction := fun claim scope => PLift (scope = claim.origin)
  ProgressAt := fun event content before after =>
    PLift (event.Lawful input ∧ event.claim input = content ∧
      before = event.before input ∧ after = event.after input)
  MaintenanceAt := fun _ _ _ => PEmpty
  TypedDeferAt := fun _ _ _ => PEmpty
  ScopeNarrowingAt := fun _ _ _ => PEmpty
  TransferAcceptedAt := fun _ _ _ _ => PEmpty
  FulfilledAt := fun event content scope =>
    PLift (event.Lawful input ∧ event.claim input = content ∧
      scope = content.origin ∧ event.after input = 0)
  WaivedAt := fun _ _ _ => PEmpty
  InvalidatedAt := fun _ _ _ => PEmpty
  AbandonedAt := fun _ _ _ => PEmpty
  ImpossibleResidueAcceptedAt := fun _ _ _ => PEmpty
  SupersessionAt := fun _ _ _ _ _ _ _ => PEmpty
  ReopenAt := fun _ _ _ _ _ _ _ => PEmpty
  JurisdictionEndedAt := fun _ _ _ => PEmpty
  ConsentRevokedAt := fun _ _ _ => PEmpty
  CapacityReleasedAt := fun _ _ _ => PEmpty
  UpperRouteAt := fun _ _ _ => PEmpty
  NextActorSignal := PEmpty
  AgeSignal := PEmpty
  TransferOfferSignal := PEmpty

def admission (claim : IssuedClaim input) : NativeAdmissionPayload (vocabulary input) where
  sourceEvent := .birth claim
  content := claim
  residual := initialBalance input claim
  bearer := claim.debtorActor input
  beneficiary := claim
  scope := claim.origin
  lineage := claim.origin
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment ⟨rfl⟩
  authority := ⟨rfl⟩
  assumption := .accepted ⟨rfl, rfl⟩
  dischargeJurisdiction := ⟨rfl⟩

def Coherent (obligation : AdmittedObligation (vocabulary input)) : Prop :=
  (obligation.admission.sourceEvent).claim input = obligation.content ∧
  obligation.scope = obligation.content.origin ∧
  obligation.beneficiary = obligation.content ∧
  obligation.bearer = obligation.content.debtorActor input

theorem admission_coherent (claim : IssuedClaim input) :
    Coherent input (admission input claim).toObligation := ⟨rfl, rfl, rfl, rfl⟩

structure Boundary (obligation : AdmittedObligation (vocabulary input)) where
  event : Event input
  lawful : event.Lawful input
  content_eq : event.claim input = obligation.content
  before_eq : obligation.residual = event.before input
  owns : SourceOwnsResponsibilityIncidence (vocabulary input) event obligation
  scope_eq : obligation.scope = obligation.content.origin

def boundaryDisposition {obligation : AdmittedObligation (vocabulary input)}
    (boundary : Boundary input obligation) :
    BoundaryDisposition (vocabulary input) obligation boundary.event := by
  by_cases cleared : boundary.event.after input = 0
  · exact .terminal (.final (.fulfilled
      ⟨boundary.lawful, boundary.content_eq, boundary.scope_eq, cleared⟩))
  · exact .carry (.progressed (boundary.event.after input)
      ⟨boundary.lawful, boundary.content_eq, boundary.before_eq, rfl⟩)

def process : NativeResponsibilityProcess (vocabulary input) where
  AdmissionEvent := IssuedClaim input
  admissionPayload := admission input
  BoundaryEvent := Boundary input
  boundarySource := fun boundary => boundary.event
  boundary_anchor_eq := fun boundary => boundary.owns.anchor_eq
  boundary_incidence_eq := fun boundary => boundary.owns.incidence_eq
  boundaryDisposition := boundaryDisposition input
  ReopenEvent := fun _ => PEmpty
  reopenPayload := fun impossible => impossible.elim

def admit (state : (process input).GeneratedState) (claim : IssuedClaim input) :
    (process input).GeneratedState :=
  state.step (process input) (.admit claim)

def reviewBoundary (obligation : AdmittedObligation (vocabulary input))
    (coherent : Coherent input obligation) (review : Review input obligation.content)
    (remaining : ℚ) (nonnegative : Nonnegative input obligation.residual)
    (available : 0 ≤ remaining) (withinSource : remaining ≤ review.quantity) :
    Boundary input obligation where
  event := .review obligation.content review obligation.residual remaining
  lawful := ⟨nonnegative, available, withinSource⟩
  content_eq := rfl
  before_eq := rfl
  owns := {
    anchor_eq := by
      change MinimalRegistrableSourceAnchor.canonical obligation.content.origin obligation.content.origin =
        MinimalRegistrableSourceAnchor.canonical
          (obligation.admission.sourceEvent.claim input).origin
          (obligation.admission.sourceEvent.claim input).origin
      rw [coherent.1]
    incidence_eq := by
      change obligation.content.origin = (obligation.admission.sourceEvent.claim input).origin
      rw [coherent.1] }
  scope_eq := coherent.2.1

def cross (state : (process input).GeneratedState)
    (slot : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary input))
    (present : state.current.slots.get slot = .live obligation)
    (boundary : Boundary input obligation) : (process input).GeneratedState :=
  state.step (process input) (.cross slot obligation present boundary)

theorem admit_keeps_original_bearer (state : (process input).GeneratedState)
    (claim : IssuedClaim input) :
    (admit input state claim).current.slots[state.current.slots.length]? =
      some (.live (admission input claim).toObligation) :=
  (process input).admit_target_slot claim

theorem admission_residual_is_actual_issued_quantity (claim : IssuedClaim input) :
    total input (admission input claim).residual = claim.quantity :=
  initial_total input claim

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial
