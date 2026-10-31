import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Power.Critical.SourceGeneratedCriticalRelationBearer

/-!
# Source-generated terminal updates for arbitrary critical relations

An already generated critical-relation power and its dependent bearer may
enter one existing responsibility lifecycle without inventing a domain
registry.  The relation's own event admits one obligation whose bearer is
computed by a supplied source map; the exact boundary event then makes that
obligation terminal.  Reopening is uninhabited.

This is a stable local kernel.  It creates no living root, ledger, target
representation, Payment, scheduler or completed future.  A domain root must
generate the event, critical power and bearer internally before using the
generic `generate` transporter.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Power

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations

universe u v wa wc x y b

section TerminalResponsibility

variable {Event : Type}

/-- Reuse the existing actor-lifecycle vocabulary.  Only the event-to-bearer
map is domain supplied; source anchor, debt lineage and lifecycle receipts are
the already installed framework types. -/
def criticalRelationAdmissionPayload
    (bearerOf : Event → Lifecycle.ActorBearer) (event : Event) :
    NativeAdmissionPayload Lifecycle.LifecycleVocabulary where
  sourceEvent := .after
  content := ()
  residual := ()
  bearer := bearerOf event
  beneficiary := ()
  scope := ()
  lineage := .debt
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment ()
  authority := ()
  assumption := .accepted ()
  dischargeJurisdiction := ()

def criticalRelationObligation
    (bearerOf : Event → Lifecycle.ActorBearer) (event : Event) :
    AdmittedObligation Lifecycle.LifecycleVocabulary :=
  (criticalRelationAdmissionPayload bearerOf event).toObligation

/-- Boundary witness tied to the exact event which created the obligation. -/
structure CriticalRelationTerminalReviewAt
    (bearerOf : Event → Lifecycle.ActorBearer)
    (obligation : AdmittedObligation Lifecycle.LifecycleVocabulary) where
  event : Event
  source_eq : obligation.admission.sourceEvent = .after
  bearer_eq : obligation.bearer = bearerOf event

def exactCriticalRelationTerminalReview
    (bearerOf : Event → Lifecycle.ActorBearer) (event : Event) :
    CriticalRelationTerminalReviewAt bearerOf
      (criticalRelationObligation bearerOf event) :=
  ⟨event, rfl, rfl⟩

def criticalRelationTerminalProcess
    (bearerOf : Event → Lifecycle.ActorBearer) :
    NativeResponsibilityProcess Lifecycle.LifecycleVocabulary where
  AdmissionEvent := Event
  admissionPayload := criticalRelationAdmissionPayload bearerOf
  BoundaryEvent := CriticalRelationTerminalReviewAt bearerOf
  boundarySource := fun _ => .after
  boundary_anchor_eq := by
    intro _obligation _review
    rfl
  boundary_incidence_eq := by
    intro _obligation _review
    rfl
  boundaryDisposition := fun _ => .terminal (.final (.fulfilled ()))
  ReopenEvent := fun _ => PEmpty
  reopenPayload := fun event => nomatch event

def criticalRelationAdmissionEdge
    (bearerOf : Event → Lifecycle.ActorBearer) (event : Event) :
    (criticalRelationTerminalProcess bearerOf).Edge
      (ResponsibilityState.empty Lifecycle.LifecycleVocabulary) :=
  .admit event

def admittedCriticalRelationState
    (bearerOf : Event → Lifecycle.ActorBearer) (event : Event) :=
  (criticalRelationAdmissionEdge bearerOf event).target

def criticalRelationSlot
    (bearerOf : Event → Lifecycle.ActorBearer) (event : Event) :
    Fin (admittedCriticalRelationState bearerOf event).slots.length :=
  ⟨0, by simp [admittedCriticalRelationState,
    criticalRelationAdmissionEdge, NativeResponsibilityProcess.Edge.target]⟩

theorem admittedCriticalRelation_present
    (bearerOf : Event → Lifecycle.ActorBearer) (event : Event) :
    (admittedCriticalRelationState bearerOf event).slots.get
        (criticalRelationSlot bearerOf event) =
      .live (criticalRelationObligation bearerOf event) :=
  rfl

def criticalRelationTerminalEdge
    (bearerOf : Event → Lifecycle.ActorBearer) (event : Event) :
    (criticalRelationTerminalProcess bearerOf).Edge
      (admittedCriticalRelationState bearerOf event) :=
  .cross (criticalRelationSlot bearerOf event)
    (criticalRelationObligation bearerOf event)
    (admittedCriticalRelation_present bearerOf event)
    (exactCriticalRelationTerminalReview bearerOf event)

theorem criticalRelationTerminalEdge_is_terminal
    (bearerOf : Event → Lifecycle.ActorBearer) (event : Event) :
    ∃ archive,
      (criticalRelationTerminalEdge bearerOf event).target.slots[
          (criticalRelationSlot bearerOf event).val]? =
        some (.terminal archive) := by
  refine ⟨⟨criticalRelationObligation bearerOf event, .after,
    .fulfilled ()⟩, ?_⟩
  have targetSlot := NativeResponsibilityProcess.cross_target_slot
    (P := criticalRelationTerminalProcess bearerOf)
    (criticalRelationSlot bearerOf event)
    (criticalRelationObligation bearerOf event)
    (admittedCriticalRelation_present bearerOf event)
    (exactCriticalRelationTerminalReview bearerOf event)
  simpa [criticalRelationTerminalEdge, criticalRelationTerminalProcess,
    BoundaryDisposition.targetSlot] using targetSlot

theorem criticalRelationTerminal_has_no_reopen
    (bearerOf : Event → Lifecycle.ActorBearer)
    (archive : TerminalArchive Lifecycle.LifecycleVocabulary) :
    IsEmpty ((criticalRelationTerminalProcess bearerOf).ReopenEvent archive) :=
  ⟨fun event => nomatch event⟩

/-- Zero-choice terminal carrier for one already generated relation event. -/
structure SourceGeneratedCriticalRelationTerminalAt
    (bearerOf : Event → Lifecycle.ActorBearer) (event : Event) : Type where
  private mk ::
  admission : (criticalRelationTerminalProcess bearerOf).Edge
    (ResponsibilityState.empty Lifecycle.LifecycleVocabulary)
  admissionExact : admission = criticalRelationAdmissionEdge bearerOf event
  terminal : (criticalRelationTerminalProcess bearerOf).Edge
    (admittedCriticalRelationState bearerOf event)
  terminalExact : terminal = criticalRelationTerminalEdge bearerOf event
  terminalDisposition : ∃ archive,
    terminal.target.slots[(criticalRelationSlot bearerOf event).val]? =
      some (.terminal archive)
  noReopen : ∀ archive : TerminalArchive Lifecycle.LifecycleVocabulary,
    IsEmpty ((criticalRelationTerminalProcess bearerOf).ReopenEvent archive)

def SourceGeneratedCriticalRelationTerminalAt.generate
    (bearerOf : Event → Lifecycle.ActorBearer) (event : Event) :
    SourceGeneratedCriticalRelationTerminalAt bearerOf event :=
  { admission := criticalRelationAdmissionEdge bearerOf event
    admissionExact := rfl
    terminal := criticalRelationTerminalEdge bearerOf event
    terminalExact := rfl
    terminalDisposition := criticalRelationTerminalEdge_is_terminal
      bearerOf event
    noReopen := criticalRelationTerminal_has_no_reopen bearerOf }

end TerminalResponsibility

section CriticalUpdate

variable {Source : Type u} {State : Type v}
variable {occurrenceOf : Source → RootedAccountedUnfolding State}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {affectedFace : M0BoundaryFace.{u, v, wa} occurrenceOf}
variable {controllerFace : M0BoundaryFace.{u, v, wc} occurrenceOf}
variable
  {relationCompiler : SourceOwnedRelationRoleCompiler.{u, v, wa, x}
    occurrenceOf game affectedFace}
variable
  {controllerCompiler : SourceOwnedActionControllerCompiler.{u, v, wc, y}
    game controllerFace}
variable [Zero (relationCompiler.Phase game.source)]
variable {controller : controllerCompiler.Actor}
variable {affected : relationCompiler.Actor}
variable {relation : relationCompiler.GeneratedRelation}
variable {power : ActionPowerOverAt relationCompiler controllerCompiler
  controller affected relation}
variable {BearerLineageAt : relationCompiler.GeneratedRelation →
  Lifecycle.ActorBearer → Type b}
variable {Event : Type} {bearerOf : Event → Lifecycle.ActorBearer}
variable {event : Event}

/-- Minimal common carrier joining the exact critical power/bearer occurrence
to a new-admission terminal lifecycle.  A root-specific producer must
generate both indexed inputs before calling `generate`. -/
structure SourceGeneratedCriticalRelationActualUpdateAt
    (criticalBearer : SourceGeneratedCriticalRelationBearerAt
      relationCompiler controllerCompiler controller affected relation power
        BearerLineageAt)
    (terminal : SourceGeneratedCriticalRelationTerminalAt bearerOf event) :
    Type (max x y b) where
  private mk ::
  bearerCommutes : criticalBearer.commonBearer = bearerOf event

def SourceGeneratedCriticalRelationActualUpdateAt.generate
    (criticalBearer : SourceGeneratedCriticalRelationBearerAt
      relationCompiler controllerCompiler controller affected relation power
        BearerLineageAt)
    (terminal : SourceGeneratedCriticalRelationTerminalAt bearerOf event)
    (bearerCommutes : criticalBearer.commonBearer = bearerOf event) :
    SourceGeneratedCriticalRelationActualUpdateAt criticalBearer terminal :=
  ⟨bearerCommutes⟩

theorem SourceGeneratedCriticalRelationActualUpdateAt.exact_provenance
    {criticalBearer : SourceGeneratedCriticalRelationBearerAt
      relationCompiler controllerCompiler controller affected relation power
        BearerLineageAt}
    {terminal : SourceGeneratedCriticalRelationTerminalAt bearerOf event}
    (_update : SourceGeneratedCriticalRelationActualUpdateAt
      criticalBearer terminal) :
    (∃ seed : relationCompiler.ExactRelationSeed,
      (∃ state ∈ game.occurrence.trace,
        state = affectedFace.state game.source ∧
        relationCompiler.relationSeedAt game.source state seed.1 ∧
        affectedFace.SeedAt game.source state
          (relationCompiler.beneficiaryActorSeed seed.1)) ∧
      seed.actor relationCompiler = affected ∧
      relationCompiler.relationOf seed = relation) ∧
    (∃ state ∈ game.occurrence.trace,
      state = controllerCompiler.actionState game.source ∧
      controllerCompiler.actionAdmittedAt power.action.1) :=
  ⟨SourceGeneratedCriticalRelationBearerAt.exact_relation_provenance
      criticalBearer,
    SourceGeneratedCriticalRelationBearerAt.exact_controller_provenance
      criticalBearer⟩

end CriticalUpdate

end Power
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.Power.SourceGeneratedCriticalRelationTerminalAt.generate
#print axioms SaturationMonoid.ProcessGame.Society.Power.criticalRelationTerminalEdge_is_terminal
#print axioms SaturationMonoid.ProcessGame.Society.Power.SourceGeneratedCriticalRelationActualUpdateAt.generate
#print axioms SaturationMonoid.ProcessGame.Society.Power.SourceGeneratedCriticalRelationActualUpdateAt.exact_provenance
