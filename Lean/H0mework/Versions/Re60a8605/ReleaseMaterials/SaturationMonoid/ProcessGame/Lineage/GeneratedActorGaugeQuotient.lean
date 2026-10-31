import H0mework.Foundation.Agency.MaximalActor

/-!
# Trace-seed lineage gauge quotient

This separated readout quotients exact occurrence-witnessed source seeds by
equality of their generated lineage values.  The canonical map from quotient
classes to generated actors is constructively injective and surjective.  The
quotient is not used to define the source, lineage compiler, or raw maximality
authority theorem.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

universe u v w x

/-- Fixed gauge relation: two trace seeds are equivalent exactly when the
dependent lineage compiler generates the same value. -/
def generatedLineageSetoid
    {Source : Type u} {State : Type v}
    {occurrenceOf : Source → RootedAccountedUnfolding State}
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type w) (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type x)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source) :
    Setoid (SourceSeed occurrenceOf Seed SeedAt game.source) where
  r := fun left right =>
    lineageOf game.source left = lineageOf game.source right
  iseqv := ⟨fun _ => rfl, fun equality => equality.symm,
    fun first second => first.trans second⟩

/-- Gauge classes of exact occurrence-trace seeds. -/
def TraceSeedGauge
    {Source : Type u} {State : Type v}
    {occurrenceOf : Source → RootedAccountedUnfolding State}
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type w) (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type x)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source) :=
  Quotient (generatedLineageSetoid game Seed SeedAt Lineage lineageOf)

/-- Canonical class of one exact trace seed. -/
def traceSeedGaugeMk
    {Source : Type u} {State : Type v}
    {occurrenceOf : Source → RootedAccountedUnfolding State}
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type w) (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type x)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source)
    (seed : SourceSeed occurrenceOf Seed SeedAt game.source) :
    TraceSeedGauge game Seed SeedAt Lineage lineageOf :=
  Quotient.mk _ seed

/-- A lineage-gauge class generates its canonical actor. -/
def gaugeToActor
    {Source : Type u} {State : Type v}
    {occurrenceOf : Source → RootedAccountedUnfolding State}
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type w) (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type x)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source) :
    TraceSeedGauge game Seed SeedAt Lineage lineageOf →
      GeneratedActor game Seed SeedAt Lineage lineageOf :=
  Quotient.lift
    (generatedActorOf game Seed SeedAt Lineage lineageOf)
    (fun left right related => by
      apply (generatedActorOf_eq_iff_lineageOf_eq
        game Seed SeedAt Lineage lineageOf left right).mpr
      exact related)

@[simp] theorem gaugeToActor_mk
    {Source : Type u} {State : Type v}
    {occurrenceOf : Source → RootedAccountedUnfolding State}
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type w) (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type x)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source)
    (seed : SourceSeed occurrenceOf Seed SeedAt game.source) :
    gaugeToActor game Seed SeedAt Lineage lineageOf
        (traceSeedGaugeMk game Seed SeedAt Lineage lineageOf seed) =
      generatedActorOf game Seed SeedAt Lineage lineageOf seed :=
  rfl

/-- Quotient classes are separated by their generated actors. -/
theorem gaugeToActor_injective
    {Source : Type u} {State : Type v}
    {occurrenceOf : Source → RootedAccountedUnfolding State}
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type w) (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type x)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source) :
    Function.Injective (gaugeToActor game Seed SeedAt Lineage lineageOf) := by
  intro left right actorsEqual
  revert right
  refine Quotient.inductionOn left ?_
  intro leftSeed right
  refine Quotient.inductionOn right ?_
  intro rightSeed actorsEqual
  apply Quotient.sound
  exact (generatedActorOf_eq_iff_lineageOf_eq
    game Seed SeedAt Lineage lineageOf leftSeed rightSeed).mp actorsEqual

/-- Every generated actor is reached by its exact seed's gauge class. -/
theorem gaugeToActor_surjective
    {Source : Type u} {State : Type v}
    {occurrenceOf : Source → RootedAccountedUnfolding State}
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type w) (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type x)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source) :
    Function.Surjective (gaugeToActor game Seed SeedAt Lineage lineageOf) := by
  intro actor
  rcases generatedActorOf_surjective game Seed SeedAt Lineage lineageOf actor with
    ⟨seed, generated⟩
  exact ⟨traceSeedGaugeMk game Seed SeedAt Lineage lineageOf seed, by
    simpa using generated⟩

/-- Constructive bijectivity pair for the canonical gauge-to-actor map. -/
theorem gaugeToActor_bijective
    {Source : Type u} {State : Type v}
    {occurrenceOf : Source → RootedAccountedUnfolding State}
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type w) (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type x)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source) :
    Function.Injective (gaugeToActor game Seed SeedAt Lineage lineageOf) ∧
      Function.Surjective
        (gaugeToActor game Seed SeedAt Lineage lineageOf) :=
  ⟨gaugeToActor_injective game Seed SeedAt Lineage lineageOf,
    gaugeToActor_surjective game Seed SeedAt Lineage lineageOf⟩

end ProcessGame
end SaturationMonoid
