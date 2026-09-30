import H0mework.Foundation.Agency.Lineage

/-!
# Source-generated local renewal faces

A local social-domain renewal face is only a projection of one exact
`ProcessGame.SourceSeed`.  Its event is present in the source occurrence
trace, its lineage carrier is the existing `GeneratedActor`, and its
responsibility consumer and disposition remain indexed by that same seed.

This module grants no operational standing authority.  A local face becomes
operational only through the separate living-root installation layer.  In
particular, arbitrary standing, time, and event carriers below are readouts
of an exact source seed, not stored world state or a completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Renewal

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

universe uSource uState uSeed uLineage uStanding uConsumer uDisposition
  uParty

variable {Source : Type uSource}
variable {State : Type uState}
variable {occurrenceOf : Source → RootedAccountedUnfolding State}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}

/-- One local renewal face generated from an exact occurrence seed.

`ConsumerAt` and `DispositionAt` are dependent interfaces so domain
consumers can use the existing M1 responsibility incidence and lifecycle
disposition types directly.  They are not reified into a second registry. -/
structure SourceGeneratedRenewalFace
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type uSeed)
    (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type uLineage)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source)
    (Standing : Type uStanding)
    (standingOf : SourceSeed occurrenceOf Seed SeedAt game.source →
      Standing)
    (ConsumerAt : SourceSeed occurrenceOf Seed SeedAt game.source →
      Type uConsumer)
    (DispositionAt : SourceSeed occurrenceOf Seed SeedAt game.source →
      Type uDisposition) : Type
      (max uSeed uLineage uConsumer uDisposition) where
  private mk ::
  sourceSeed : SourceSeed occurrenceOf Seed SeedAt game.source
  consumer : ConsumerAt sourceSeed
  disposition : DispositionAt sourceSeed

namespace SourceGeneratedRenewalFace

variable {Seed : Type uSeed}
variable {SeedAt : Source → State → Seed → Prop}
variable {Lineage : Source → Type uLineage}
variable {lineageOf : ∀ source,
  SourceSeed occurrenceOf Seed SeedAt source → Lineage source}
variable {Standing : Type uStanding}
variable {standingOf : SourceSeed occurrenceOf Seed SeedAt game.source →
  Standing}
variable {ConsumerAt : SourceSeed occurrenceOf Seed SeedAt game.source →
  Type uConsumer}
variable {DispositionAt : SourceSeed occurrenceOf Seed SeedAt game.source →
  Type uDisposition}

/-- Generate the local face from an already occurrence-witnessed source seed
and existing seed-indexed responsibility data. -/
def generate
    (sourceSeed : SourceSeed occurrenceOf Seed SeedAt game.source)
    (consumer : ConsumerAt sourceSeed)
    (disposition : DispositionAt sourceSeed) :
    SourceGeneratedRenewalFace game Seed SeedAt Lineage lineageOf
      Standing standingOf ConsumerAt DispositionAt :=
  ⟨sourceSeed, consumer, disposition⟩

variable
  (face : SourceGeneratedRenewalFace game Seed SeedAt Lineage lineageOf
    Standing standingOf ConsumerAt DispositionAt)

/-- Domain event readout.  Its occurrence membership is retained by
`sourceSeed`; no separate event carrier is authoritative. -/
def event : Seed :=
  face.sourceSeed.1

/-- Standing is computed from the exact source seed rather than stored as a
durable stock field. -/
def standing : Standing :=
  standingOf face.sourceSeed

/-- The M0 lineage-generated actor at the exact renewal seed. -/
def actor : GeneratedActor game Seed SeedAt Lineage lineageOf :=
  generatedActorOf game Seed SeedAt Lineage lineageOf face.sourceSeed

/-- Exact event membership in the actual local occurrence trace. -/
theorem event_mem_source_trace :
    ∃ state ∈ (occurrenceOf game.source).trace,
      SeedAt game.source state face.event :=
  face.sourceSeed.2

/-- The responsibility consumer is the exact seed-indexed consumer supplied
by the installed M1/domain interface. -/
def responsibilityConsumer : ConsumerAt face.sourceSeed :=
  face.consumer

/-- Local disposition remains indexed by the same exact seed. -/
def exactDisposition : DispositionAt face.sourceSeed :=
  face.disposition

end SourceGeneratedRenewalFace

/-- No occurrence-generated seed means no local renewal face.  This is the
local no-free-standing law; it does not attempt to manufacture a root row. -/
theorem noSourceSeed_noRenewalFace
    {Seed : Type uSeed}
    {SeedAt : Source → State → Seed → Prop}
    {Lineage : Source → Type uLineage}
    {lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source}
    {Standing : Type uStanding}
    {standingOf : SourceSeed occurrenceOf Seed SeedAt game.source →
      Standing}
    {ConsumerAt : SourceSeed occurrenceOf Seed SeedAt game.source →
      Type uConsumer}
    {DispositionAt : SourceSeed occurrenceOf Seed SeedAt game.source →
      Type uDisposition}
    (noSeed : SourceSeed occurrenceOf Seed SeedAt game.source → False) :
    SourceGeneratedRenewalFace game Seed SeedAt Lineage lineageOf
      Standing standingOf ConsumerAt DispositionAt → False :=
  fun face => noSeed face.sourceSeed

/-- Renewal-control asymmetry is indexed by the exact renewal event.  It is
not a post-hoc label on an unrooted relationship. -/
structure RenewalControlAsymmetryAt
    {Seed : Type uSeed}
    {SeedAt : Source → State → Seed → Prop}
    {Lineage : Source → Type uLineage}
    {lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source}
    {Standing : Type uStanding}
    {standingOf : SourceSeed occurrenceOf Seed SeedAt game.source →
      Standing}
    {ConsumerAt : SourceSeed occurrenceOf Seed SeedAt game.source →
      Type uConsumer}
    {DispositionAt : SourceSeed occurrenceOf Seed SeedAt game.source →
      Type uDisposition}
    (face : SourceGeneratedRenewalFace game Seed SeedAt Lineage lineageOf
      Standing standingOf ConsumerAt DispositionAt)
    (Party : Type uParty)
    (ControlsRenewalAt : Seed → Party → Party → Prop)
    (controller subject : Party) : Prop where
  controls : ControlsRenewalAt face.event controller subject
  noReverseControl : ¬ ControlsRenewalAt face.event subject controller

namespace RenewalControlAsymmetryAt

theorem parties_ne
    {Seed : Type uSeed}
    {SeedAt : Source → State → Seed → Prop}
    {Lineage : Source → Type uLineage}
    {lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source}
    {Standing : Type uStanding}
    {standingOf : SourceSeed occurrenceOf Seed SeedAt game.source →
      Standing}
    {ConsumerAt : SourceSeed occurrenceOf Seed SeedAt game.source →
      Type uConsumer}
    {DispositionAt : SourceSeed occurrenceOf Seed SeedAt game.source →
      Type uDisposition}
    {face : SourceGeneratedRenewalFace game Seed SeedAt Lineage lineageOf
      Standing standingOf ConsumerAt DispositionAt}
    {Party : Type uParty}
    {ControlsRenewalAt : Seed → Party → Party → Prop}
    {controller subject : Party}
    (asymmetry : RenewalControlAsymmetryAt face Party ControlsRenewalAt
      controller subject) :
    controller ≠ subject := by
  intro equalParties
  apply asymmetry.noReverseControl
  simpa [equalParties] using asymmetry.controls

end RenewalControlAsymmetryAt

/-- Debt-flow asymmetry is independently indexed by the same exact renewal
event.  Control direction and debt direction therefore cannot be conflated
or added as ungrounded global tags. -/
structure DebtFlowAsymmetryAt
    {Seed : Type uSeed}
    {SeedAt : Source → State → Seed → Prop}
    {Lineage : Source → Type uLineage}
    {lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source}
    {Standing : Type uStanding}
    {standingOf : SourceSeed occurrenceOf Seed SeedAt game.source →
      Standing}
    {ConsumerAt : SourceSeed occurrenceOf Seed SeedAt game.source →
      Type uConsumer}
    {DispositionAt : SourceSeed occurrenceOf Seed SeedAt game.source →
      Type uDisposition}
    (face : SourceGeneratedRenewalFace game Seed SeedAt Lineage lineageOf
      Standing standingOf ConsumerAt DispositionAt)
    (Party : Type uParty)
    (DebtFlowsAt : Seed → Party → Party → Prop)
    (debtor beneficiary : Party) : Prop where
  flows : DebtFlowsAt face.event debtor beneficiary
  noReverseFlow : ¬ DebtFlowsAt face.event beneficiary debtor

/-- The structural exploitation signature keeps renewal control and debt
flow as two independently evidenced directions on one exact source event. -/
structure RenewalDebtAsymmetryAt
    {Seed : Type uSeed}
    {SeedAt : Source → State → Seed → Prop}
    {Lineage : Source → Type uLineage}
    {lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source}
    {Standing : Type uStanding}
    {standingOf : SourceSeed occurrenceOf Seed SeedAt game.source →
      Standing}
    {ConsumerAt : SourceSeed occurrenceOf Seed SeedAt game.source →
      Type uConsumer}
    {DispositionAt : SourceSeed occurrenceOf Seed SeedAt game.source →
      Type uDisposition}
    (face : SourceGeneratedRenewalFace game Seed SeedAt Lineage lineageOf
      Standing standingOf ConsumerAt DispositionAt)
    (Party : Type uParty)
    (ControlsRenewalAt DebtFlowsAt : Seed → Party → Party → Prop)
    (controller subject debtor beneficiary : Party) : Prop where
  renewalControl : RenewalControlAsymmetryAt face Party ControlsRenewalAt
    controller subject
  debtFlow : DebtFlowAsymmetryAt face Party DebtFlowsAt debtor beneficiary

end Renewal
end Society
end ProcessGame
end SaturationMonoid
