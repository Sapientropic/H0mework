import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Election.MandatePower
import H0mework.Foundation.Responsibility.Lifecycle

/-!
# Source-owned mandate responsibility

Every election event admits one exact standing-mandate obligation.  The
installed responsibility process derives continuation or exit from that same
event's disposition and exposes the existing M1 source-ownership consumer.
No mandate registry, term table, or caller-selected lifecycle verdict exists.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Election

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power
open ComplementObservation

universe u

inductive MandateReceipt (_Scale : Type u) : Type u where
  | generated

inductive NoMandateReopen (_Scale : Type u) : Type u

inductive ExactMandateOriginAt {Event : Type u} : Event → Event → Type u
  | generated (event : Event) : ExactMandateOriginAt event event

inductive ExactStandingMandateAt
    {Period OfficeSeed ControllerSeed Office Controller : Type u}
    (lineageCompiler : ElectionLineageCompiler
      (Period := Period) (OfficeSeed := OfficeSeed)
      (ControllerSeed := ControllerSeed)
      (Office := Office) (Controller := Controller)) :
    Controller →
      Event (Period := Period) (OfficeSeed := OfficeSeed)
        (ControllerSeed := ControllerSeed) →
      Office → Type u
  | generated (event) : ExactStandingMandateAt lineageCompiler
      (lineageCompiler.controllerOf event.controllerSeed) event
      (lineageCompiler.officeOf event.officeSeed)

variable {Period OfficeSeed ControllerSeed Office Controller : Type u}

variable
  (lineageCompiler : ElectionLineageCompiler
    (Period := Period) (OfficeSeed := OfficeSeed)
    (ControllerSeed := ControllerSeed)
    (Office := Office) (Controller := Controller))

abbrev ElectionEvent :=
  Event (Period := Period) (OfficeSeed := OfficeSeed)
    (ControllerSeed := ControllerSeed)

def mandateVocabulary : Vocabulary where
  SourceEvent := ElectionEvent (Period := Period) (OfficeSeed := OfficeSeed)
    (ControllerSeed := ControllerSeed)
  Content := ElectionEvent (Period := Period) (OfficeSeed := OfficeSeed)
    (ControllerSeed := ControllerSeed)
  Residual := ElectionEvent (Period := Period) (OfficeSeed := OfficeSeed)
    (ControllerSeed := ControllerSeed)
  Bearer := Controller
  ProtectedInterest := Office
  Scope := Office
  Lineage := OfficeControllerLineage Office Controller
  Incidence := ElectionEvent (Period := Period) (OfficeSeed := OfficeSeed)
    (ControllerSeed := ControllerSeed)
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun event =>
    MinimalRegistrableSourceAnchor.canonical
      (lineageCompiler.officeOf event.officeSeed)
      { office := lineageCompiler.officeOf event.officeSeed
        controller := lineageCompiler.controllerOf event.controllerSeed
        disposition := event.disposition }
  sourceIncidence := id
  ObstructionAt := fun _ => MandateReceipt Period
  demandContent := fun {source} _ => source
  demandResidual := fun {source} _ => source
  CommitmentAt := fun _ _ => MandateReceipt Period
  MandateOriginAt := ExactMandateOriginAt
  AcceptedTaskAt := fun _ _ => MandateReceipt Period
  ActiveDependencyAt := fun _ _ => MandateReceipt Period
  ProtectedRiskAt := fun _ _ => MandateReceipt Period
  AdmissionAuthorityAt := fun _ _ => MandateReceipt Period
  AcceptedAt := fun _ _ _ => MandateReceipt Period
  StandingMandateAt := ExactStandingMandateAt lineageCompiler
  DischargeJurisdiction := fun _ _ => MandateReceipt Period
  ProgressAt := fun _ _ _ _ => MandateReceipt Period
  MaintenanceAt := fun _ _ _ => MandateReceipt Period
  TypedDeferAt := fun _ _ _ => MandateReceipt Period
  ScopeNarrowingAt := fun _ _ _ => MandateReceipt Period
  TransferAcceptedAt := fun _ _ _ _ => MandateReceipt Period
  FulfilledAt := fun _ _ _ => MandateReceipt Period
  WaivedAt := fun _ _ _ => MandateReceipt Period
  InvalidatedAt := fun _ _ _ => MandateReceipt Period
  AbandonedAt := fun _ _ _ => MandateReceipt Period
  ImpossibleResidueAcceptedAt := fun _ _ _ => MandateReceipt Period
  SupersessionAt := fun _ _ _ _ _ _ _ => MandateReceipt Period
  ReopenAt := fun _ _ _ _ _ _ _ => MandateReceipt Period
  JurisdictionEndedAt := fun _ _ _ => MandateReceipt Period
  ConsentRevokedAt := fun _ _ _ => MandateReceipt Period
  CapacityReleasedAt := fun _ _ _ => MandateReceipt Period
  UpperRouteAt := fun _ _ _ => MandateReceipt Period
  NextActorSignal := Period
  AgeSignal := Period
  TransferOfferSignal := Period

def mandateAdmissionPayload
    (event : ElectionEvent (Period := Period) (OfficeSeed := OfficeSeed)
      (ControllerSeed := ControllerSeed)) :
    NativeAdmissionPayload (mandateVocabulary lineageCompiler) where
  sourceEvent := event
  content := event
  residual := event
  bearer := lineageCompiler.controllerOf event.controllerSeed
  beneficiary := lineageCompiler.officeOf event.officeSeed
  scope := lineageCompiler.officeOf event.officeSeed
  lineage :=
    { office := lineageCompiler.officeOf event.officeSeed
      controller := lineageCompiler.controllerOf event.controllerSeed
      disposition := event.disposition }
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .standingMandate (.generated event)
  authority := .generated
  assumption := .mandated (.generated event)
  dischargeJurisdiction := .generated

def mandateObligation
    (event : ElectionEvent (Period := Period) (OfficeSeed := OfficeSeed)
      (ControllerSeed := ControllerSeed)) :
    AdmittedObligation (mandateVocabulary lineageCompiler) :=
  (mandateAdmissionPayload lineageCompiler event).toObligation

/-- Boundary event is indexed by the obligation's exact admission source. -/
structure MandateReviewAt
    (obligation : AdmittedObligation (mandateVocabulary lineageCompiler)) where
  sourceEvent : ElectionEvent (Period := Period) (OfficeSeed := OfficeSeed)
    (ControllerSeed := ControllerSeed)
  source_eq : sourceEvent = obligation.admission.sourceEvent

def exactMandateReview
    (event : ElectionEvent (Period := Period) (OfficeSeed := OfficeSeed)
      (ControllerSeed := ControllerSeed)) :
    MandateReviewAt lineageCompiler (mandateObligation lineageCompiler event) :=
  ⟨event, rfl⟩

def mandateBoundaryDisposition
    {obligation : AdmittedObligation (mandateVocabulary lineageCompiler)}
    (review : MandateReviewAt lineageCompiler obligation) :
    BoundaryDisposition (mandateVocabulary lineageCompiler) obligation
      review.sourceEvent :=
  match review.sourceEvent.disposition with
  | .continue => .carry (.maintained .generated)
  | .exit => .terminal (.final (.fulfilled .generated))

def mandateProcess :
    NativeResponsibilityProcess (mandateVocabulary lineageCompiler) where
  AdmissionEvent := ElectionEvent (Period := Period)
    (OfficeSeed := OfficeSeed) (ControllerSeed := ControllerSeed)
  admissionPayload := mandateAdmissionPayload lineageCompiler
  BoundaryEvent := MandateReviewAt lineageCompiler
  boundarySource := fun review => review.sourceEvent
  boundary_anchor_eq := by
    intro obligation review
    rw [review.source_eq]
  boundary_incidence_eq := by
    intro obligation review
    rw [review.source_eq]
  boundaryDisposition := mandateBoundaryDisposition lineageCompiler
  ReopenEvent := fun _ => NoMandateReopen Period
  reopenPayload := fun event => nomatch event

def mandateAdmissionEdge
    (event : ElectionEvent (Period := Period) (OfficeSeed := OfficeSeed)
      (ControllerSeed := ControllerSeed)) :
    (mandateProcess lineageCompiler).Edge
      (ResponsibilityState.empty (mandateVocabulary lineageCompiler)) :=
  .admit event

def admittedMandateState
    (event : ElectionEvent (Period := Period) (OfficeSeed := OfficeSeed)
      (ControllerSeed := ControllerSeed)) :=
  (mandateAdmissionEdge lineageCompiler event).target

def mandateSlot
    (event : ElectionEvent (Period := Period) (OfficeSeed := OfficeSeed)
      (ControllerSeed := ControllerSeed)) :
    Fin (admittedMandateState lineageCompiler event).slots.length :=
  ⟨0, by simp [admittedMandateState, mandateAdmissionEdge,
    NativeResponsibilityProcess.Edge.target]⟩

theorem admittedMandate_present
    (event : ElectionEvent (Period := Period) (OfficeSeed := OfficeSeed)
      (ControllerSeed := ControllerSeed)) :
    (admittedMandateState lineageCompiler event).slots.get
        (mandateSlot lineageCompiler event) =
      .live (mandateObligation lineageCompiler event) :=
  rfl

def mandateReviewEdge
    (event : ElectionEvent (Period := Period) (OfficeSeed := OfficeSeed)
      (ControllerSeed := ControllerSeed)) :
    (mandateProcess lineageCompiler).Edge
      (admittedMandateState lineageCompiler event) :=
  .cross (mandateSlot lineageCompiler event)
    (mandateObligation lineageCompiler event)
    (admittedMandate_present lineageCompiler event)
    (exactMandateReview lineageCompiler event)

def mandateSourceOwnership
    (event : ElectionEvent (Period := Period) (OfficeSeed := OfficeSeed)
      (ControllerSeed := ControllerSeed)) :
    SourceOwnsResponsibilityIncidence (mandateVocabulary lineageCompiler)
      event (mandateObligation lineageCompiler event) :=
  (mandateProcess lineageCompiler).boundarySourceOwnership
    (exactMandateReview lineageCompiler event)

theorem mandateReview_history_append
    (event : ElectionEvent (Period := Period) (OfficeSeed := OfficeSeed)
      (ControllerSeed := ControllerSeed)) :
    (mandateReviewEdge lineageCompiler event).target.history =
      (admittedMandateState lineageCompiler event).history ++
        [(mandateReviewEdge lineageCompiler event).lifecycleEvent] :=
  (mandateReviewEdge lineageCompiler event).history_append

theorem continued_mandate_is_live
    (event : ElectionEvent (Period := Period) (OfficeSeed := OfficeSeed)
      (ControllerSeed := ControllerSeed))
    (continued : event.disposition = .continue) :
    (mandateReviewEdge lineageCompiler event).target.slots[(mandateSlot
        lineageCompiler event).val]? =
      some (.live (mandateObligation lineageCompiler event)) := by
  have targetSlot := NativeResponsibilityProcess.cross_target_slot
    (P := mandateProcess lineageCompiler)
    (mandateSlot lineageCompiler event)
    (mandateObligation lineageCompiler event)
    (admittedMandate_present lineageCompiler event)
    (exactMandateReview lineageCompiler event)
  simpa [mandateReviewEdge, mandateProcess, mandateBoundaryDisposition,
    exactMandateReview, BoundaryDisposition.targetSlot,
    ActiveCarryDisposition.target, continued] using targetSlot

theorem exited_mandate_is_terminal
    (event : ElectionEvent (Period := Period) (OfficeSeed := OfficeSeed)
      (ControllerSeed := ControllerSeed))
    (exited : event.disposition = .exit) :
    ∃ archive,
      (mandateReviewEdge lineageCompiler event).target.slots[(mandateSlot
          lineageCompiler event).val]? = some (.terminal archive) := by
  refine ⟨⟨mandateObligation lineageCompiler event, event,
    .fulfilled .generated⟩, ?_⟩
  have targetSlot := NativeResponsibilityProcess.cross_target_slot
    (P := mandateProcess lineageCompiler)
    (mandateSlot lineageCompiler event)
    (mandateObligation lineageCompiler event)
    (admittedMandate_present lineageCompiler event)
    (exactMandateReview lineageCompiler event)
  simpa [mandateReviewEdge, mandateProcess, mandateBoundaryDisposition,
    exactMandateReview, BoundaryDisposition.targetSlot, exited] using targetSlot

end Election
end Society
end ProcessGame
end SaturationMonoid
